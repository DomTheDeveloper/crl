#!/usr/bin/env python3
"""Continue the rigorous mod-4 Mordell-Weil sieve from its 56 survivors.

The first 32 tuples below are the known projective rational points; the final
24 are the higher-cover classes left after all good primes below 200.  We test
complete local images at every usable good prime below 5000 and stop as soon
as all 24 unknown classes are eliminated.
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer, QQ, prime_range

sys.path.insert(0,str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5
import sage_kummer_mod4 as m4

SURVIVORS = [
[0,0,0,2,30],[0,3,3,1,54],[48,960,243,50,62],[48,323,80,17,22],
[4,308,943,61,694],[4,799,420,22,670],[20,4,87,194,158],[20,15,252,65,182],
[2,2,2,2,54],[2,1,1,1,30],[50,962,241,18,22],[50,321,82,49,62],
[6,310,941,21,670],[6,797,422,62,694],[22,6,85,66,182],[22,13,254,193,158],
[1,2,3,3,30],[1,1,0,0,54],[17,962,80,51,62],[17,321,243,16,22],
[13,310,420,60,694],[13,797,943,23,670],[61,6,252,195,158],[61,13,87,64,182],
[3,0,1,3,54],[3,3,2,0,30],[19,960,82,19,22],[19,323,241,48,62],
[15,308,422,20,670],[15,799,941,63,694],[63,4,254,67,182],[63,15,85,192,158],
[16,320,83,18,62],[16,963,240,49,22],[12,796,423,21,694],[12,311,940,62,670],
[60,12,255,66,158],[60,7,84,193,182],[18,322,81,50,22],[18,961,242,17,62],
[14,798,421,61,670],[14,309,942,22,694],[62,14,253,194,182],[62,5,86,65,158],
[49,322,240,19,62],[49,961,83,48,22],[5,798,940,20,694],[5,309,423,63,670],
[21,14,84,67,158],[21,5,255,192,182],[51,320,242,51,22],[51,963,81,16,62],
[7,796,942,60,670],[7,311,421,23,694],[23,12,86,195,182],[23,7,253,64,158],
]
KNOWN = {tuple(x) for x in SURVIVORS[:32]}


def main():
    started=time.time()
    factors=[];reps4=[]
    for inds in kc.TRIPLES:
        E0,p,q=kc.input_curve(inds)
        gens,_=kc.certified_basis_on_input(E0)
        reps,_,_=m4.mod4_classes(E0,gens,m4.torsion_basis_triple(E0,p))
        factors.append((inds,E0,p,q));reps4.append(reps)
    E5,p,q,s=k5.quartic_input_curve()
    gens5,_=kc.certified_basis_on_input(E5)
    reps5,_,_=m4.mod4_classes(E5,gens5,m4.torsion_basis_fifth(E5))

    survivors=[tuple(x) for x in SURVIVORS]
    progress=[]
    for prime0 in prime_range(211,5001):
        prime=int(prime0)
        allcurves=[x[1] for x in factors]+[E5]
        if any(Integer(E.discriminant())%prime==0 for E in allcurves): continue
        if len({int((r*r)%prime) for r in kc.ROWS})<4: continue
        F,curves,glabs,E5p,labels5,glabs5,pp,qq,ss=m4.local_context(
            prime,factors,reps4,E5,reps5,p,q,s)
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
        kept=[]
        for vals in survivors:
            lt=tuple(glabs[j][vals[j]] for j in range(4))+(glabs5[vals[4]],)
            if lt in allowed: kept.append(vals)
        if len(kept)<len(survivors):
            survivors=kept
            unknown=sum(v not in KNOWN for v in survivors)
            progress.append({"prime":prime,"survivors":len(survivors),"unknown":unknown,
                             "local_image_size":len(allowed)})
            print(f"p={prime}: survivors={len(survivors)} unknown={unknown}",flush=True)
            if unknown==0: break
    known_left=[list(v) for v in survivors if v in KNOWN]
    unknown_left=[list(v) for v in survivors if v not in KNOWN]
    out={"tested_prime_upper_bound":5000,"initial_survivors":56,"initial_unknown":24,
         "progress":progress,"final_survivors":len(survivors),"known_left":len(known_left),
         "unknown_left":len(unknown_left),"unknown_survivors":unknown_left,
         "elapsed_seconds":round(time.time()-started,3)}
    Path("results").mkdir(exist_ok=True)
    Path("results/kummer_mod4_continue.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,sort_keys=True))

if __name__=="__main__": main()
