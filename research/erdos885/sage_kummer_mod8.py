#!/usr/bin/env python3
"""Lift the certified 56 compatible mod-4 classes to mod 8.

All five elliptic quotient factors are used. For each good prime, every
projective point of the diagonal genus-5 curve over F_p is enumerated, so every
deletion is rigorous. The 56 starting classes are the complete output of the
preceding mod-4 computation.
"""
from __future__ import annotations
import itertools, json, sys, time
from pathlib import Path
from sage.all import EllipticCurve, GF, Integer, QQ
sys.path.insert(0, str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5

MOD4_SURVIVORS = [[0,0,0,2,30],[0,3,3,1,54],[48,960,243,50,62],[48,323,80,17,22],[4,308,943,61,694],[4,799,420,22,670],[20,4,87,194,158],[20,15,252,65,182],[2,2,2,2,54],[2,1,1,1,30],[50,962,241,18,22],[50,321,82,49,62],[6,310,941,21,670],[6,797,422,62,694],[22,6,85,66,182],[22,13,254,193,158],[1,2,3,3,30],[1,1,0,0,54],[17,962,80,51,62],[17,321,243,16,22],[13,310,420,60,694],[13,797,943,23,670],[61,6,252,195,158],[61,13,87,64,182],[3,0,1,3,54],[3,3,2,0,30],[19,960,82,19,22],[19,323,241,48,62],[15,308,422,20,670],[15,799,941,63,694],[63,4,254,67,182],[63,15,85,192,158],[16,320,83,18,62],[16,963,240,49,22],[12,796,423,21,694],[12,311,940,62,670],[60,12,255,66,158],[60,7,84,193,182],[18,322,81,50,22],[18,961,242,17,62],[14,798,421,61,670],[14,309,942,22,694],[62,14,253,194,182],[62,5,86,65,158],[49,322,240,19,62],[49,961,83,48,22],[5,798,940,20,694],[5,309,423,63,670],[21,14,84,67,158],[21,5,255,192,182],[51,320,242,51,22],[51,963,81,16,62],[7,796,942,60,670],[7,311,421,23,694],[23,12,86,195,182],[23,7,253,64,158]]
PRIMES=[31,43,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307]

def quotient_labels_n(Ep,n):
    pts=list(Ep); H={n*P for P in pts}; labels={}; lab=0
    for P in pts:
        if P in labels: continue
        for Q in H: labels[P+Q]=lab
        lab+=1
    return labels

def torsion_basis_triple(E0,p): return [E0(0,0),E0(-4*p,0)]
def torsion_basis_fifth(E5):
    roots=[x for x,m in E5.two_division_polynomial().roots(QQ)]
    if len(roots)!=3: raise RuntimeError('fifth quotient lacks full rational 2-torsion')
    return [E5(roots[0],0),E5(roots[1],0)]

def product_index(vals,base):
    z=0
    for v in vals: z=z*base+v
    return z

def mod8_classes(E,free_gens,torsion_basis):
    rank=len(free_gens); points=[]; lifts={}
    mults=[[c*G for c in range(8)] for G in free_gens]
    for coeffs in itertools.product(range(8),repeat=rank):
      base=E(0)
      for c,ms in zip(coeffs,mults): base += ms[c]
      for tb in itertools.product(range(2),repeat=2):
        P=base
        for c,T in zip(tb,torsion_basis):
            if c: P += T
        idx=len(points); points.append(P)
        idx4=product_index([c&3 for c in coeffs],4)*4+tb[0]*2+tb[1]
        lifts.setdefault(idx4,[]).append(idx)
    if any(len(v)!=(1<<rank) for v in lifts.values()): raise RuntimeError('bad lift count')
    return points,lifts

def encode(vals,sizes):
    c=0;m=1
    for v,s in zip(vals,sizes): c+=m*v; m*=s
    return c

def decode(c,sizes):
    out=[]
    for s in sizes: out.append(c%s); c//=s
    return out

def main():
    started=time.time(); factors4=[]; reps4=[]; lifts4=[]; sizes=[]; ranks=[]
    for inds in kc.TRIPLES:
        E0,p,q=kc.input_curve(inds); gens,rank=kc.certified_basis_on_input(E0)
        reps,lifts=mod8_classes(E0,gens,torsion_basis_triple(E0,p))
        factors4.append((inds,E0,p,q)); reps4.append(reps); lifts4.append(lifts); sizes.append(len(reps)); ranks.append(rank)
    E5,p,q,s=k5.quartic_input_curve(); gens5,rank5=kc.certified_basis_on_input(E5)
    reps5,lifts5=mod8_classes(E5,gens5,torsion_basis_fifth(E5)); sizes5=sizes+[len(reps5)]
    survivors=None; progress=[]; used=[]
    for prime in PRIMES:
        allcurves=[x[1] for x in factors4]+[E5]
        if any(Integer(E.discriminant())%prime==0 for E in allcurves): continue
        if len({int((r*r)%prime) for r in kc.ROWS})<4: continue
        F=GF(prime); curves=[]; glabs=[]
        for (inds,E0,pp,qq),reps in zip(factors4,reps4):
            Ep=EllipticCurve(F,[F(x) for x in E0.a_invariants()]); labels=quotient_labels_n(Ep,8)
            curves.append((inds,Ep,F(pp),F(qq),labels)); glabs.append([labels[kc.reduce_projective_point(P,Ep,prime)] for P in reps])
        E5p=EllipticCurve(F,[F(x) for x in E5.a_invariants()]); labels5=quotient_labels_n(E5p,8)
        glabs5=[labels5[kc.reduce_projective_point(P,E5p,prime)] for P in reps5]; pp,qq,ss=F(p),F(q),F(s)
        roots={F(x):[] for x in range(prime)}
        for y in F: roots[y*y].append(y)
        allowed=set()
        for t0 in F:
            rlists=[roots[t0+F(r*r)] for r in kc.ROWS]
            if any(not z for z in rlists): continue
            for us in itertools.product(*rlists):
                labs=[]
                for inds,Ep,a1,a2,labels in curves:
                    ia,ib,ic=inds; u,v,w=us[ia],us[ib],us[ic]
                    labs.append(labels[Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))])
                labs.append(labels5[k5.quartic_local_point(us,E5p,pp,qq,ss)]); allowed.add(tuple(labs))
        for tail in itertools.product([1,-1],repeat=3):
            signs=(1,)+tail; labs=[]
            for inds,Ep,a1,a2,labels in curves:
                ia,ib,ic=inds; labs.append(labels[kc.infinity_image(Ep,a1,a2,signs[ia],signs[ib],signs[ic])])
            labs.append(labels5[k5.quartic_infinity_point(signs,E5p,pp,qq,ss)]); allowed.add(tuple(labs))
        if survivors is None:
            survivors=[]; tested=0
            for vals4 in MOD4_SURVIVORS:
                ll=[lifts4[j][vals4[j]] for j in range(4)]+[lifts5[vals4[4]]]
                for vals in itertools.product(*ll):
                    tested+=1
                    if tuple(glabs[j][vals[j]] for j in range(4))+(glabs5[vals[4]],) in allowed: survivors.append(encode(vals,sizes5))
            expected=len(MOD4_SURVIVORS)*(1<<sum(ranks+[rank5]))
            if tested!=expected: raise RuntimeError(f'candidate count {tested} != {expected}')
        else:
            kept=[]
            for code in survivors:
                vals=decode(code,sizes5)
                if tuple(glabs[j][vals[j]] for j in range(4))+(glabs5[vals[4]],) in allowed: kept.append(code)
            survivors=kept
        used.append(prime); progress.append({'prime':prime,'local_image_size':len(allowed),'survivors':len(survivors)})
        print(f'p={prime} local={len(allowed)} survivors={len(survivors)}',flush=True)
    out={'rows':[int(x) for x in kc.ROWS],'ranks':ranks+[rank5],'starting_mod4_classes':len(MOD4_SURVIVORS),'initial_mod8_lift_candidates':len(MOD4_SURVIVORS)*(1<<sum(ranks+[rank5])),'sizes':sizes5,'used_primes':used,'progress':progress,'survivor_count':len(survivors),'survivor_indices':[decode(c,sizes5) for c in survivors] if len(survivors)<=10000 else None,'elapsed_seconds':round(time.time()-started,3),'soundness':'Every deletion uses the complete image of C(F_p) in all five quotient groups modulo 8.'}
    Path('results').mkdir(exist_ok=True); Path('results/kummer_mod8.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'survivors':len(survivors),'elapsed':out['elapsed_seconds']},sort_keys=True))
if __name__=='__main__': main()
