#!/usr/bin/env python3
"""Complete the compatible Kummer-image sieve with the fifth elliptic quotient.

For the four-row curve with affine equations u_i^2=t+r_i^2, let
p=r_1^2-r_0^2, q=r_2^2-r_0^2, s=r_3^2-r_0^2.  The fifth quotient is the
Jacobian of y^2=x(x+p)(x+q)(x+s), with explicit model

    E5: Y^2=(X+16pq)(X+16ps)(X+16qs),
    X=16pqs/u_0^2,
    Y=64pqs*u_0*u_1*u_2*u_3/u_0^4.

The four triple factors first reduce the global product to 32 classes.  We then
pair them with all 64 classes of E5(Q)/2E5(Q) and apply complete local images.
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer, QQ

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc

KNOWN_T = [-5585184, 0, 35994816]


def quartic_input_curve():
    a, b, c, d = kc.ROWS
    p = b*b-a*a
    q = c*c-a*a
    s = d*d-a*a
    E = EllipticCurve(QQ, [0,
        16*(p*q+p*s+q*s),
        0,
        256*p*q*s*(p+q+s),
        4096*p*p*q*q*s*s,
    ])
    return E, p, q, s


def quartic_classes(E, p, q, free_gens):
    # Roots are -16pq, -16ps, -16qs; choose two independent 2-torsion points.
    # s is recovered from the curve closure in main; the first two roots suffice.
    roots = [x for x, mult in E.two_division_polynomial().roots(QQ)]
    if len(roots) != 3:
        raise RuntimeError(f"expected three rational 2-torsion roots, got {roots}")
    basis = list(free_gens) + [E(roots[0], 0), E(roots[1], 0)]
    reps=[]
    for mask in range(1 << len(basis)):
        P=E(0)
        for j,G in enumerate(basis):
            if (mask >> j) & 1:
                P += G
        reps.append(P)
    return basis,reps


def local_context(prime, factors4, reps4, E5, reps5, p, q, s):
    F=GF(prime)
    curves4=[]
    glabs4=[]
    for (inds,E0,pp,qq), reps in zip(factors4,reps4):
        Ep=EllipticCurve(F,[F(x) for x in E0.a_invariants()])
        labels,_,_=kc.quotient_labels(Ep)
        curves4.append((inds,Ep,F(pp),F(qq),labels))
        glabs4.append([labels[kc.reduce_projective_point(P,Ep,prime)] for P in reps])
    E5p=EllipticCurve(F,[F(x) for x in E5.a_invariants()])
    labels5,_,_=kc.quotient_labels(E5p)
    glabs5=[labels5[kc.reduce_projective_point(P,E5p,prime)] for P in reps5]
    return F,curves4,glabs4,E5p,labels5,glabs5,F(p),F(q),F(s)


def quartic_local_point(us,E5p,p,q,s):
    u0,u1,u2,u3=us
    if u0 == 0:
        return E5p(0)
    X=E5p.base_field()(16)*p*q*s/(u0*u0)
    Y=E5p.base_field()(64)*p*q*s*(u0*u1*u2*u3)/(u0**4)
    return E5p(X,Y)


def quartic_infinity_point(signs,E5p,p,q,s):
    F=E5p.base_field()
    return E5p(F(0),F(64)*p*q*s*F(math.prod(signs)))


def known_points():
    out=[]
    for t in KNOWN_T:
        rs=[]
        for r in kc.ROWS:
            n=Integer(t)+r*r
            if n < 0 or not n.is_square():
                raise RuntimeError("invalid known column")
            rs.append(Integer(n.sqrt()))
        for signs in itertools.product([1,-1],repeat=4):
            out.append({"id":f"t={t};{signs}","kind":"affine","us":[signs[i]*rs[i] for i in range(4)]})
    for tail in itertools.product([1,-1],repeat=3):
        signs=(1,)+tail
        out.append({"id":f"infinity;{signs}","kind":"infinity","signs":signs})
    return out


def known_tuple(P,F,curves4,E5p,labels5,p,q,s):
    labs=[]
    if P["kind"]=="affine":
        us=[F(x) for x in P["us"]]
        for inds,Ep,pp,qq,labels in curves4:
            ia,ib,ic=inds
            u,v,w=us[ia],us[ib],us[ic]
            X=F(4)*(v-u)*(w-u)
            Y=F(8)*(v-u)*(w-u)*(v+w)
            labs.append(labels[Ep(X,Y)])
        labs.append(labels5[quartic_local_point(us,E5p,p,q,s)])
    else:
        signs=P["signs"]
        for inds,Ep,pp,qq,labels in curves4:
            ia,ib,ic=inds
            labs.append(labels[kc.infinity_image(Ep,pp,qq,signs[ia],signs[ib],signs[ic])])
        labs.append(labels5[quartic_infinity_point(signs,E5p,p,q,s)])
    return tuple(labs)


def main():
    factors4=[]; reps4=[]; dims4=[]
    for inds in kc.TRIPLES:
        E0,p,q=kc.input_curve(inds)
        gens,rank=kc.certified_basis_on_input(E0)
        basis,reps=kc.global_classes(E0,p,gens)
        factors4.append((inds,E0,p,q)); reps4.append(reps); dims4.append(len(reps))

    E5,p,q,s=quartic_input_curve()
    gens5,rank5=kc.certified_basis_on_input(E5)
    basis5,reps5=quartic_classes(E5,p,q,gens5)
    if rank5 != 4 or len(reps5) != 64:
        raise RuntimeError(f"unexpected fifth factor rank/classes {rank5}/{len(reps5)}")

    survivors4=None
    survivors5=None
    signatures_by_prime=[]
    known=known_points()
    known_sigs={P["id"]:[] for P in known}
    used=[]

    for prime in kc.PRIMES:
        allcurves=[E0 for _,E0,_,_ in factors4]+[E5]
        if any(Integer(E.discriminant()) % prime == 0 for E in allcurves):
            continue
        if len({int((r*r)%prime) for r in kc.ROWS}) < 4:
            continue
        F,curves4,glabs4,E5p,labels5,glabs5,pp,qq,ss=local_context(
            prime,factors4,reps4,E5,reps5,p,q,s)

        roots={F(x):[] for x in range(prime)}
        for y in F: roots[y*y].append(y)
        allowed4=set(); allowed5=set()
        for t0 in F:
            rlists=[roots[t0+F(r*r)] for r in kc.ROWS]
            if any(not xs for xs in rlists): continue
            for us in itertools.product(*rlists):
                labs=[]
                for inds,Ep,a1,a2,labels in curves4:
                    ia,ib,ic=inds
                    u,v,w=us[ia],us[ib],us[ic]
                    labs.append(labels[Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))])
                allowed4.add(tuple(labs))
                allowed5.add(tuple(labs)+(labels5[quartic_local_point(us,E5p,pp,qq,ss)],))
        for tail in itertools.product([1,-1],repeat=3):
            signs=(1,)+tail
            labs=[]
            for inds,Ep,a1,a2,labels in curves4:
                ia,ib,ic=inds
                labs.append(labels[kc.infinity_image(Ep,a1,a2,signs[ia],signs[ib],signs[ic])])
            allowed4.add(tuple(labs))
            allowed5.add(tuple(labs)+(labels5[quartic_infinity_point(signs,E5p,pp,qq,ss)],))

        if survivors4 is None:
            survivors4=[]
            for vals in itertools.product(*[range(n) for n in dims4]):
                if tuple(glabs4[j][vals[j]] for j in range(4)) in allowed4:
                    survivors4.append(kc.encode(vals,dims4))
        else:
            survivors4=[code for code in survivors4 if tuple(
                glabs4[j][kc.decode(code,dims4)[j]] for j in range(4)) in allowed4]

        if survivors5 is None:
            survivors5=[]
            for code4 in survivors4:
                vals=kc.decode(code4,dims4)
                first=tuple(glabs4[j][vals[j]] for j in range(4))
                for i5 in range(len(reps5)):
                    if first+(glabs5[i5],) in allowed5:
                        survivors5.append((code4,i5))
        else:
            survivors5=[(code4,i5) for code4,i5 in survivors5 if (
                tuple(glabs4[j][kc.decode(code4,dims4)[j]] for j in range(4))+(glabs5[i5],)
            ) in allowed5]

        signatures_by_prime.append((prime,glabs4,glabs5))
        used.append(prime)
        for P in known:
            known_sigs[P["id"]].append(known_tuple(P,F,curves4,E5p,labels5,pp,qq,ss))
        print(f"p={prime}: four={len(survivors4)} five={len(survivors5)}",flush=True)

    sig_to_survivors={}
    for code4,i5 in survivors5:
        vals=kc.decode(code4,dims4)
        sig=tuple(tuple(gl4[j][vals[j]] for j in range(4))+(gl5[i5],)
                  for _,gl4,gl5 in signatures_by_prime)
        sig_to_survivors.setdefault(sig,[]).append((code4,i5))
    known_sig_to_ids={}
    for P in known:
        sig=tuple(known_sigs[P["id"]])
        known_sig_to_ids.setdefault(sig,[]).append(P["id"])

    matched=[]; unmatched=[]
    for code4,i5 in survivors5:
        vals=kc.decode(code4,dims4)
        sig=tuple(tuple(gl4[j][vals[j]] for j in range(4))+(gl5[i5],)
                  for _,gl4,gl5 in signatures_by_prime)
        rec={"four_indices":vals,"fifth_index":i5,
             "known_points":known_sig_to_ids.get(sig,[]),
             "signature_collision_count":len(sig_to_survivors[sig])}
        (matched if rec["known_points"] else unmatched).append(rec)

    out={
        "rows":[int(x) for x in kc.ROWS],
        "used_primes":used,
        "four_factor_survivors":len(survivors4),
        "five_factor_survivors":len(survivors5),
        "fifth_factor_rank_proved":rank5,
        "fifth_factor_class_count":len(reps5),
        "distinct_survivor_signatures":len(sig_to_survivors),
        "signature_injective":len(sig_to_survivors)==len(survivors5),
        "matched_count":len(matched),
        "unmatched_count":len(unmatched),
        "matched":matched,
        "unmatched":unmatched,
        "known_projective_points":len(known),
        "distinct_known_signatures":len(known_sig_to_ids),
    }
    Path("results").mkdir(exist_ok=True)
    Path("results/kummer_five.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"four":len(survivors4),"five":len(survivors5),
                      "matched":len(matched),"unmatched":len(unmatched)},sort_keys=True))

if __name__=="__main__":
    main()
