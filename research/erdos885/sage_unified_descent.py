#!/usr/bin/env python3
"""Basis-stable five-factor Mordell--Weil descent for Erdős #885.

Construct each certified Mordell--Weil basis exactly once, compute the complete
compatible mod-2 set, and lift it to mod 4 in the same process. No
basis-dependent class index is imported from another workflow.
"""
from __future__ import annotations
import itertools, json, sys, time
from pathlib import Path
from sage.all import EllipticCurve, GF, Integer, QQ, proof
sys.path.insert(0, str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5

PRIMES=[31,43,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251]

def quotient_labels_n(Ep,n):
    pts=list(Ep);H={n*P for P in pts};labels={};lab=0
    for P in pts:
        if P in labels: continue
        for Q in H: labels[P+Q]=lab
        lab+=1
    return labels,len(H),lab

def torsion_basis_triple(E,p): return [E(0,0),E(-4*p,0)]
def torsion_basis_fifth(E):
    roots=[x for x,m in E.two_division_polynomial().roots(QQ)]
    if len(roots)!=3: raise RuntimeError(f"expected full rational 2-torsion, got {roots}")
    return [E(roots[0],0),E(roots[1],0)]
def point_json(P): return ["0"] if P.is_zero() else [str(P[0]),str(P[1]),str(P[2])]

def certified_factor_data():
    factors=[]
    for inds in kc.TRIPLES:
        E,p,q=kc.input_curve(inds);gens,rank=kc.certified_basis_on_input(E)
        if len(gens)!=rank: raise RuntimeError("basis length/rank mismatch")
        factors.append({"kind":"triple","inds":tuple(inds),"E":E,"p":p,"q":q,
                        "gens":tuple(gens),"tors":tuple(torsion_basis_triple(E,p)),"rank":rank})
    E,p,q,s=k5.quartic_input_curve();gens,rank=kc.certified_basis_on_input(E)
    if len(gens)!=rank: raise RuntimeError("fifth basis length/rank mismatch")
    factors.append({"kind":"fifth","E":E,"p":p,"q":q,"s":s,"gens":tuple(gens),
                    "tors":tuple(torsion_basis_fifth(E)),"rank":rank})
    return factors

def factor_classes(FD,modulus):
    out=[];by_parent={};r=FD["rank"]
    for coeffs in itertools.product(range(modulus),repeat=r):
        P0=FD["E"](0)
        for c,G in zip(coeffs,FD["gens"]): P0+=c*G
        for tb in itertools.product(range(2),repeat=2):
            P=P0
            for b,T in zip(tb,FD["tors"]):
                if b: P+=T
            idx=len(out);rec={"coeffs":tuple(coeffs),"torsion":tuple(tb),"point":P};out.append(rec)
            if modulus>2:
                parent=(tuple(c%(modulus//2) for c in coeffs),tuple(tb))
                by_parent.setdefault(parent,[]).append(idx)
    return out,by_parent

def encode(vals,sizes):
    z=0;m=1
    for v,s in zip(vals,sizes): z+=m*v;m*=s
    return z
def decode(z,sizes):
    vals=[]
    for s in sizes: vals.append(z%s);z//=s
    return vals

def local_context(prime,modulus,factors,classes):
    F=GF(prime);locals_=[];class_labels=[]
    for FD,reps in zip(factors,classes):
        Ep=EllipticCurve(F,[F(x) for x in FD["E"].a_invariants()])
        labels,_,qsize=quotient_labels_n(Ep,modulus)
        labs=[labels[kc.reduce_projective_point(rec["point"],Ep,prime)] for rec in reps]
        locals_.append((FD,Ep,labels,qsize));class_labels.append(labs)
    return F,locals_,class_labels

def complete_local_image(prime,locals_):
    F=GF(prime);roots={F(x):[] for x in range(prime)}
    for y in F: roots[y*y].append(y)
    allowed=set()
    for t0 in F:
        rlists=[roots[t0+F(r*r)] for r in kc.ROWS]
        if any(not xs for xs in rlists): continue
        for us in itertools.product(*rlists):
            labs=[]
            for FD,Ep,labels,_ in locals_:
                if FD["kind"]=="triple":
                    ia,ib,ic=FD["inds"];u,v,w=us[ia],us[ib],us[ic]
                    Q=Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))
                else:
                    Q=k5.quartic_local_point(us,Ep,F(FD["p"]),F(FD["q"]),F(FD["s"]))
                labs.append(labels[Q])
            allowed.add(tuple(labs))
    for tail in itertools.product([1,-1],repeat=3):
        signs=(1,)+tail;labs=[]
        for FD,Ep,labels,_ in locals_:
            if FD["kind"]=="triple":
                ia,ib,ic=FD["inds"]
                Q=kc.infinity_image(Ep,F(FD["p"]),F(FD["q"]),signs[ia],signs[ib],signs[ic])
            else:
                Q=k5.quartic_infinity_point(signs,Ep,F(FD["p"]),F(FD["q"]),F(FD["s"]))
            labs.append(labels[Q])
        allowed.add(tuple(labs))
    return allowed

def usable_prime(prime,factors):
    if any(Integer(FD["E"].discriminant())%prime==0 for FD in factors): return False
    return len({int((r*r)%prime) for r in kc.ROWS})==4

def filter_level(modulus,factors,classes,initial_candidates=None):
    sizes=[len(x) for x in classes];survivors=initial_candidates;progress=[];used=[]
    for prime in PRIMES:
        if not usable_prime(prime,factors): continue
        _,locals_,labs=local_context(prime,modulus,factors,classes)
        allowed=complete_local_image(prime,locals_);allowed4={a[:4] for a in allowed}
        if survivors is None:
            four=[]
            for vals in itertools.product(*[range(s) for s in sizes[:4]]):
                if tuple(labs[j][vals[j]] for j in range(4)) in allowed4: four.append(tuple(vals))
            survivors=[]
            for vals4 in four:
                prefix=tuple(labs[j][vals4[j]] for j in range(4))
                for i5 in range(sizes[4]):
                    if prefix+(labs[4][i5],) in allowed: survivors.append(encode(vals4+(i5,),sizes))
        else:
            kept=[]
            for code in survivors:
                vals=decode(code,sizes)
                if tuple(labs[j][vals[j]] for j in range(5)) in allowed: kept.append(code)
            survivors=kept
        used.append(prime);progress.append({"prime":prime,"local_image_size":len(allowed),"survivors":len(survivors)})
        print(f"mod={modulus} p={prime} local={len(allowed)} survivors={len(survivors)}",flush=True)
    return survivors,sizes,progress,used

def lift_candidates(parent_codes,parent_sizes,parent_classes,child_parent_maps,child_sizes):
    out=[]
    for code in parent_codes:
        pidx=decode(code,parent_sizes);lists=[]
        for j in range(5):
            rec=parent_classes[j][pidx[j]];key=(rec["coeffs"],rec["torsion"])
            xs=child_parent_maps[j].get(key)
            if xs is None: raise RuntimeError(f"missing child factor {j} key {key}")
            lists.append(xs)
        for vals in itertools.product(*lists): out.append(encode(vals,child_sizes))
    return out

def known_projective_points(factors):
    out=[]
    for t in k5.KNOWN_T:
        mags=[]
        for r in kc.ROWS:
            n=Integer(t)+r*r
            if n<0 or not n.is_square(): raise RuntimeError("bad known affine point")
            mags.append(Integer(n.sqrt()))
        # z=1 is fixed, so all 16 sign choices are distinct.
        for signs in itertools.product([1,-1],repeat=4):
            us=[signs[i]*mags[i] for i in range(4)];pts=[]
            for FD in factors:
                if FD["kind"]=="triple":
                    ia,ib,ic=FD["inds"];u,v,w=[QQ(us[z]) for z in (ia,ib,ic)]
                    pts.append(FD["E"](4*(v-u)*(w-u),8*(v-u)*(w-u)*(v+w)))
                else:
                    pts.append(k5.quartic_local_point([QQ(x) for x in us],FD["E"],QQ(FD["p"]),QQ(FD["q"]),QQ(FD["s"])))
            out.append({"id":f"t={t};signs={signs}","points":pts})
    for tail in itertools.product([1,-1],repeat=3):
        signs=(1,)+tail;pts=[]
        for FD in factors:
            if FD["kind"]=="triple":
                ia,ib,ic=FD["inds"]
                pts.append(kc.infinity_image(FD["E"],QQ(FD["p"]),QQ(FD["q"]),signs[ia],signs[ib],signs[ic]))
            else:
                pts.append(k5.quartic_infinity_point(signs,FD["E"],QQ(FD["p"]),QQ(FD["q"]),QQ(FD["s"])))
        out.append({"id":f"infinity;signs={signs}","points":pts})
    if len(out)!=56: raise RuntimeError(f"expected 56 known points, got {len(out)}")
    return out

def exact_known_matches(modulus,survivor_codes,sizes,classes,known):
    matches=[];errors=[]
    for code in survivor_codes:
        idx=decode(code,sizes);reps=[classes[j][idx[j]]["point"] for j in range(5)];ids=[]
        for K in known:
            ok=True
            try:
                for Q,R in zip(K["points"],reps):
                    if not (Q-R).division_points(modulus): ok=False;break
            except Exception as exc:
                errors.append(f"{type(exc).__name__}: {exc}");ok=False;break
            if ok: ids.append(K["id"])
        matches.append({"indices":idx,"known_points":ids})
    return matches,sorted(set(errors))

def main():
    started=time.time();proof.all(True);factors=certified_factor_data();factor_report=[]
    for FD in factors:
        factor_report.append({"kind":FD["kind"],"indices":list(FD.get("inds",())),"rank":FD["rank"],
          "ainvs":[str(x) for x in FD["E"].a_invariants()],"generators":[point_json(P) for P in FD["gens"]],
          "torsion_basis":[point_json(P) for P in FD["tors"]]})
    classes2=[]
    for FD in factors: classes2.append(factor_classes(FD,2)[0])
    surv2,sizes2,prog2,used2=filter_level(2,factors,classes2)
    classes4=[];maps4=[]
    for FD in factors:
        reps,mp=factor_classes(FD,4);classes4.append(reps);maps4.append(mp)
    sizes4=[len(x) for x in classes4]
    initial4=lift_candidates(surv2,sizes2,classes2,maps4,sizes4)
    surv4,sizes4b,prog4,used4=filter_level(4,factors,classes4,initial4)
    if sizes4!=sizes4b: raise RuntimeError("size mismatch")
    known=known_projective_points(factors)
    exact,div_errors=exact_known_matches(4,surv4,sizes4,classes4,known)
    out={"rows":[int(x) for x in kc.ROWS],"known_columns":list(k5.KNOWN_T),
      "known_projective_point_count":len(known),"factors":factor_report,
      "basis_stability":"All levels use the same certified generator objects in one Sage process.",
      "mod2":{"class_sizes":sizes2,"survivor_count":len(surv2),"progress":prog2,"used_primes":used2},
      "mod4":{"initial_lift_count":len(initial4),"class_sizes":sizes4,"survivor_count":len(surv4),"progress":prog4,"used_primes":used4},
      "exact_mod4_known_matches":exact,"division_point_errors":div_errors,
      "elapsed_seconds":round(time.time()-started,3),
      "soundness":"Every local deletion uses the complete projective curve image in all five quotient groups; no class index is imported from another basis computation."}
    Path("results").mkdir(exist_ok=True);Path("results/unified_descent.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"mod2":len(surv2),"mod4":len(surv4),"known":len(known),"division_errors":div_errors,"elapsed":out["elapsed_seconds"]},sort_keys=True))
if __name__=="__main__": main()
