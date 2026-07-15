#!/usr/bin/env python3
"""Lift the complete five-factor Kummer set from mod 2 to mod 4.

The preceding certified computation leaves exactly 32 classes in
  prod_i E_i(Q)/2E_i(Q),
all represented by known projective points.  Each such class has 2^17 lifts
through the free Mordell-Weil directions, for 4,194,304 total candidates in
  prod_i E_i(Q)/4E_i(Q).

At every usable good prime this program enumerates the full projective curve
C(F_p), maps every point to all five elliptic quotients, and retains only
global mod-4 tuples occurring in the complete local image.  It also compares
survivors with the 32 known projective rational points by their full reduction
signatures.
"""
from __future__ import annotations

import itertools
import json
import math
import sys
import time
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer, QQ

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5

MOD2_SURVIVORS = [
 ([0,0,0,8],28),([0,48,48,16],28),([1,3,54,10],28),([1,51,6,18],28),
 ([2,13,57,22],28),([2,61,9,14],28),([3,8,62,9],28),([3,56,14,17],28),
 ([4,16,16,8],28),([4,32,32,16],28),([5,19,38,10],28),([5,35,22,18],28),
 ([6,29,41,22],28),([6,45,25,14],28),([7,24,46,9],28),([7,40,30,17],28),
 ([8,16,48,24],28),([8,32,0,0],28),([9,19,6,26],28),([9,35,54,2],28),
 ([10,29,9,6],28),([10,45,57,30],28),([11,24,14,25],28),([11,40,62,1],28),
 ([12,0,32,24],28),([12,48,16,0],28),([13,3,22,26],28),([13,51,38,2],28),
 ([14,13,25,6],28),([14,61,41,30],28),([15,8,30,25],28),([15,56,46,1],28),
]
PRIMES = [31,43,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]


def quotient_labels_n(Ep, n):
    pts=list(Ep)
    H={n*P for P in pts}
    labels={}; lab=0
    for P in pts:
        if P in labels: continue
        for Q in H: labels[P+Q]=lab
        lab += 1
    return labels,len(H),lab


def torsion_basis_triple(E0,p):
    return [E0(0,0),E0(-4*p,0)]


def torsion_basis_fifth(E5):
    roots=[x for x,m in E5.two_division_polynomial().roots(QQ)]
    if len(roots)!=3: raise RuntimeError("fifth quotient lacks full rational 2-torsion")
    return [E5(roots[0],0),E5(roots[1],0)]


def mod4_classes(E,free_gens,torsion_basis):
    rank=len(free_gens)
    points=[]; mod2=[]; lifts={}
    for coeffs in itertools.product(range(4),repeat=rank):
      for tb in itertools.product(range(2),repeat=2):
        P=E(0)
        for c,G in zip(coeffs,free_gens): P += c*G
        for c,T in zip(tb,torsion_basis): P += c*T
        idx=len(points); points.append(P)
        mask=sum((coeffs[j]&1)<<j for j in range(rank))
        mask += sum(tb[j]<<(rank+j) for j in range(2))
        mod2.append(mask); lifts.setdefault(mask,[]).append(idx)
    for mask,xs in lifts.items():
        if len(xs)!=(1<<rank): raise RuntimeError(f"bad lift count {mask}: {len(xs)}")
    return points,mod2,lifts


def encode(vals,sizes):
    c=0;m=1
    for v,s in zip(vals,sizes): c += m*v; m*=s
    return c


def decode(c,sizes):
    out=[]
    for s in sizes: out.append(c%s); c//=s
    return out


def known_projective_points():
    pts=[]
    for t in k5.KNOWN_T:
        roots=[]
        for r in kc.ROWS:
            z=Integer(t)+r*r
            if z<0 or not z.is_square(): raise RuntimeError("bad known point")
            roots.append(Integer(z.sqrt()))
        # normalize the first sign to +1 to quotient by overall projective sign
        for tail in itertools.product([1,-1],repeat=3):
            signs=(1,)+tail
            pts.append({"id":f"t={t};signs={signs}","kind":"affine",
                        "us":[signs[i]*roots[i] for i in range(4)]})
    for tail in itertools.product([1,-1],repeat=3):
        signs=(1,)+tail
        pts.append({"id":f"infinity;signs={signs}","kind":"infinity","signs":signs})
    if len(pts)!=32: raise RuntimeError("expected 32 known projective points")
    return pts


def local_context(prime,factors4,reps4,E5,reps5,p,q,s):
    F=GF(prime); curves=[]; glabs=[]
    for (inds,E0,pp,qq),reps in zip(factors4,reps4):
        Ep=EllipticCurve(F,[F(x) for x in E0.a_invariants()])
        labels,_,_=quotient_labels_n(Ep,4)
        curves.append((inds,Ep,F(pp),F(qq),labels))
        glabs.append([labels[kc.reduce_projective_point(P,Ep,prime)] for P in reps])
    E5p=EllipticCurve(F,[F(x) for x in E5.a_invariants()])
    labels5,_,_=quotient_labels_n(E5p,4)
    glabs5=[labels5[kc.reduce_projective_point(P,E5p,prime)] for P in reps5]
    return F,curves,glabs,E5p,labels5,glabs5,F(p),F(q),F(s)


def point_tuple(P,F,curves,E5p,labels5,p,q,s):
    labs=[]
    if P["kind"]=="affine":
        us=[F(x) for x in P["us"]]
        for inds,Ep,pp,qq,labels in curves:
            ia,ib,ic=inds;u,v,w=us[ia],us[ib],us[ic]
            labs.append(labels[Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))])
        labs.append(labels5[k5.quartic_local_point(us,E5p,p,q,s)])
    else:
        signs=P["signs"]
        for inds,Ep,pp,qq,labels in curves:
            ia,ib,ic=inds
            labs.append(labels[kc.infinity_image(Ep,pp,qq,signs[ia],signs[ib],signs[ic])])
        labs.append(labels5[k5.quartic_infinity_point(signs,E5p,p,q,s)])
    return tuple(labs)


def main():
    started=time.time()
    factors4=[]; reps4=[]; lifts4=[]; sizes=[]; ranks=[]
    for inds in kc.TRIPLES:
        E0,p,q=kc.input_curve(inds)
        gens,rank=kc.certified_basis_on_input(E0)
        reps,_,lifts=mod4_classes(E0,gens,torsion_basis_triple(E0,p))
        factors4.append((inds,E0,p,q));reps4.append(reps);lifts4.append(lifts)
        sizes.append(len(reps));ranks.append(rank)
    E5,p,q,s=k5.quartic_input_curve()
    gens5,rank5=kc.certified_basis_on_input(E5)
    reps5,_,lifts5=mod4_classes(E5,gens5,torsion_basis_fifth(E5))
    sizes5=sizes+[len(reps5)]
    known=known_projective_points()

    survivors=None; used=[]; local_label_cache=[]
    known_sigs={P["id"]:[] for P in known}
    progress=[]

    for prime in PRIMES:
        allcurves=[x[1] for x in factors4]+[E5]
        if any(Integer(E.discriminant())%prime==0 for E in allcurves): continue
        if len({int((r*r)%prime) for r in kc.ROWS})<4: continue
        F,curves,glabs,E5p,labels5,glabs5,pp,qq,ss=local_context(prime,factors4,reps4,E5,reps5,p,q,s)
        roots={F(x):[] for x in range(prime)}
        for y in F: roots[y*y].append(y)
        allowed=set()
        for t0 in F:
            rlists=[roots[t0+F(r*r)] for r in kc.ROWS]
            if any(not z for z in rlists): continue
            for us in itertools.product(*rlists):
                labs=[]
                for inds,Ep,a1,a2,labels in curves:
                    ia,ib,ic=inds;u,v,w=us[ia],us[ib],us[ic]
                    labs.append(labels[Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))])
                labs.append(labels5[k5.quartic_local_point(us,E5p,pp,qq,ss)])
                allowed.add(tuple(labs))
        for tail in itertools.product([1,-1],repeat=3):
            signs=(1,)+tail;labs=[]
            for inds,Ep,a1,a2,labels in curves:
                ia,ib,ic=inds
                labs.append(labels[kc.infinity_image(Ep,a1,a2,signs[ia],signs[ib],signs[ic])])
            labs.append(labels5[k5.quartic_infinity_point(signs,E5p,pp,qq,ss)])
            allowed.add(tuple(labs))

        if survivors is None:
            survivors=[]
            for four,i5 in MOD2_SURVIVORS:
                liftlists=[lifts4[j][four[j]] for j in range(4)]+[lifts5[i5]]
                for vals in itertools.product(*liftlists):
                    if tuple(glabs[j][vals[j]] for j in range(4))+(glabs5[vals[4]],) in allowed:
                        survivors.append(encode(vals,sizes5))
        else:
            kept=[]
            for code in survivors:
                vals=decode(code,sizes5)
                if tuple(glabs[j][vals[j]] for j in range(4))+(glabs5[vals[4]],) in allowed:
                    kept.append(code)
            survivors=kept
        used.append(prime);local_label_cache.append((glabs,glabs5))
        for P in known: known_sigs[P["id"]].append(point_tuple(P,F,curves,E5p,labels5,pp,qq,ss))
        progress.append({"prime":prime,"local_image_size":len(allowed),"survivors":len(survivors)})
        print(f"p={prime} local={len(allowed)} survivors={len(survivors)}",flush=True)

    sig_to_codes={};code_sig={}
    for code in survivors:
        vals=decode(code,sizes5)
        sig=tuple(tuple(gl[j][vals[j]] for j in range(4))+(gl5[vals[4]],)
                  for gl,gl5 in local_label_cache)
        code_sig[code]=sig;sig_to_codes.setdefault(sig,[]).append(code)
    known_by_sig={}
    for P in known: known_by_sig.setdefault(tuple(known_sigs[P["id"]]),[]).append(P["id"])
    matched=[];unmatched=[]
    for code in survivors:
        rec={"indices":decode(code,sizes5),"known_points":known_by_sig.get(code_sig[code],[]),
             "signature_collision_count":len(sig_to_codes[code_sig[code]])}
        (matched if rec["known_points"] else unmatched).append(rec)

    out={"rows":[int(x) for x in kc.ROWS],"ranks":ranks+[rank5],
         "initial_mod4_lift_candidates":32*(1<<sum(ranks+[rank5])),
         "used_primes":used,"progress":progress,"survivor_count":len(survivors),
         "distinct_survivor_signatures":len(sig_to_codes),"signature_injective":len(sig_to_codes)==len(survivors),
         "known_point_count":len(known),"distinct_known_signatures":len(known_by_sig),
         "matched_count":len(matched),"unmatched_count":len(unmatched),
         "matched":matched,"unmatched":unmatched,"elapsed_seconds":round(time.time()-started,3)}
    Path("results").mkdir(exist_ok=True)
    Path("results/kummer_mod4.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"survivors":len(survivors),"matched":len(matched),"unmatched":len(unmatched),
                      "elapsed":out["elapsed_seconds"]},sort_keys=True))

if __name__=="__main__": main()
