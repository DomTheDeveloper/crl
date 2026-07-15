#!/usr/bin/env python3
"""Test the 56 mod-4 survivors at primes where the genus-5 curve or some
elliptic quotients have bad reduction.

A prime was previously skipped if any one of the five factors was bad.  This
script retains every factor with good reduction and compares the projection of
each global tuple with the complete image of the (possibly singular) diagonal
curve over F_p.  This is a rigorous necessary local condition: reducing a
Q_p-point gives an F_p solution, and every used quotient has good reduction.
"""
from __future__ import annotations
import itertools,json,sys,time
from pathlib import Path
from sage.all import EllipticCurve,GF,Integer
sys.path.insert(0,str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5
import sage_kummer_mod4 as m4
import sage_kummer_mod4_continue as cont

PRIMES=[3,5,7,11,13,17,19,23,29,37,41,47,127,173]


def main():
    started=time.time(); factors=[];reps=[]
    for inds in kc.TRIPLES:
        E0,p,q=kc.input_curve(inds);gens,_=kc.certified_basis_on_input(E0)
        rr,_,_=m4.mod4_classes(E0,gens,m4.torsion_basis_triple(E0,p))
        factors.append((inds,E0,p,q));reps.append(rr)
    E5,p,q,s=k5.quartic_input_curve();gens5,_=kc.certified_basis_on_input(E5)
    reps5,_,_=m4.mod4_classes(E5,gens5,m4.torsion_basis_fifth(E5))
    all_factors=factors+[(None,E5,p,q)]
    all_reps=reps+[reps5]
    survivors=[tuple(x) for x in cont.SURVIVORS]
    known=cont.KNOWN; progress=[]

    for prime in PRIMES:
        F=GF(prime); used=[]; glabs={}; contexts={}
        for fi,((inds,E,a,b),rr) in enumerate(zip(all_factors,all_reps)):
            if Integer(E.discriminant())%prime==0: continue
            Ep=EllipticCurve(F,[F(x) for x in E.a_invariants()])
            labels,_,_=m4.quotient_labels_n(Ep,4)
            glabs[fi]=[labels[kc.reduce_projective_point(P,Ep,prime)] for P in rr]
            contexts[fi]=(inds,Ep,F(a),F(b),labels)
            used.append(fi)
        if not used: continue
        roots={F(x):[] for x in range(prime)}
        for y in F: roots[y*y].append(y)
        allowed=set()
        for t0 in F:
            rlists=[roots[t0+F(r*r)] for r in kc.ROWS]
            if any(not z for z in rlists): continue
            for us in itertools.product(*rlists):
                labs=[]
                for fi in used:
                    inds,Ep,a,b,labels=contexts[fi]
                    if fi<4:
                        ia,ib,ic=inds;u,v,w=us[ia],us[ib],us[ic]
                        Q=Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))
                    else:
                        Q=k5.quartic_local_point(us,Ep,F(p),F(q),F(s))
                    labs.append(labels[Q])
                allowed.add(tuple(labs))
        for tail in itertools.product([1,-1],repeat=3):
            signs=(1,)+tail;labs=[]
            for fi in used:
                inds,Ep,a,b,labels=contexts[fi]
                if fi<4:
                    ia,ib,ic=inds;Q=kc.infinity_image(Ep,a,b,signs[ia],signs[ib],signs[ic])
                else: Q=k5.quartic_infinity_point(signs,Ep,F(p),F(q),F(s))
                labs.append(labels[Q])
            allowed.add(tuple(labs))
        kept=[]
        for vals in survivors:
            lt=tuple(glabs[fi][vals[fi]] for fi in used)
            if lt in allowed: kept.append(vals)
        survivors=kept
        unknown=sum(v not in known for v in survivors)
        progress.append({"prime":prime,"good_factor_indices":used,"local_image_size":len(allowed),
                         "survivors":len(survivors),"unknown":unknown})
        print(f"p={prime} factors={used} survivors={len(survivors)} unknown={unknown}",flush=True)
    unknowns=[list(v) for v in survivors if v not in known]
    out={"initial_survivors":56,"initial_unknown":24,"progress":progress,
         "final_survivors":len(survivors),"known_left":sum(v in known for v in survivors),
         "unknown_left":len(unknowns),"unknown_survivors":unknowns,
         "elapsed_seconds":round(time.time()-started,3)}
    Path('results').mkdir(exist_ok=True)
    Path('results/kummer_mod4_badpartial.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
