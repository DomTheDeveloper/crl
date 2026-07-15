#!/usr/bin/env python3
"""Lift the 56 exact known projective point classes from mod 8 to mod 16.

For a known point Q, every child of its class in E(Q)/8E(Q) is represented by
Q + 8*sum(e_i G_i), e_i in {0,1}. This description is geometric and remains
valid for any certified integral Mordell--Weil basis chosen in this run.
"""
from __future__ import annotations
import itertools,json,time
from pathlib import Path
from sage.all import EllipticCurve,GF,Integer,QQ,proof
import sage_kummer_compat as kc
import sage_kummer_five as k5
from sage_unified_descent import (certified_factor_data,known_projective_points,
    quotient_labels_n,usable_prime,complete_local_image)

PARENT_MODULUS=8
MODULUS=16
PRIMES=[31,43,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397]

def make_children(FD,Q):
    r=FD['rank'];out=[]
    increments=[]
    for bits in itertools.product([0,1],repeat=r):
        H=FD['E'](0)
        for b,G in zip(bits,FD['gens']):
            if b:H+=PARENT_MODULUS*G
        increments.append((bits,H))
    for bits,H in increments:out.append({'bits':bits,'point':Q+H})
    return out

def local_image(prime,factors):
    F=GF(prime);locals_=[]
    for FD in factors:
        Ep=EllipticCurve(F,[F(x) for x in FD['E'].a_invariants()])
        labels,_,_=quotient_labels_n(Ep,MODULUS)
        locals_.append((FD,Ep,labels,0))
    return complete_local_image(prime,locals_),locals_

def reduce_point(P,Ep,prime,labels):
    return labels[kc.reduce_projective_point(P,Ep,prime)]

def known_id_map(known):return {K['id']:i for i,K in enumerate(known)}

def main():
    st=time.time();proof.all(True);factors=certified_factor_data();known=known_projective_points(factors)
    child_tables=[]
    for pi,K in enumerate(known):
        child_tables.append([make_children(FD,Q) for FD,Q in zip(factors,K['points'])])
    offsets=[];z=0
    for FD in factors:offsets.append(z);z+=FD['rank']
    total_bits=z;BASE=1<<total_bits
    def choice(mask,f):return (mask>>offsets[f])&((1<<factors[f]['rank'])-1)
    survivors=list(range(len(known)*BASE));progress=[];used=[]
    for prime in PRIMES:
        if not usable_prime(prime,factors):continue
        allowed,locals_=local_image(prime,factors);labs=[]
        for pi in range(len(known)):
            per=[]
            for f,(FD,Ep,label,_) in enumerate(locals_):
                per.append([reduce_point(rec['point'],Ep,prime,label) for rec in child_tables[pi][f]])
            labs.append(per)
        kept=[]
        for code in survivors:
            pi,mask=divmod(code,BASE)
            tup=tuple(labs[pi][f][choice(mask,f)] for f in range(5))
            if tup in allowed:kept.append(code)
        survivors=kept;used.append(prime)
        progress.append({'prime':prime,'local_image_size':len(allowed),'survivors':len(survivors)})
        print(f'p={prime} local={len(allowed)} survivors={len(survivors)}',flush=True)
    decoded=[]
    for code in survivors:
        pi,mask=divmod(code,BASE);bits=[]
        for f,FD in enumerate(factors):bits.append(list(child_tables[pi][f][choice(mask,f)]['bits']))
        decoded.append({'known_point':known[pi]['id'],'free_bits':bits,'all_zero':mask==0})
    out={'rows':[int(x) for x in kc.ROWS],'known_columns':list(k5.KNOWN_T),
      'parent_modulus':PARENT_MODULUS,'modulus':MODULUS,'known_parent_count':len(known),
      'total_free_rank':total_bits,'initial_child_count':len(known)*BASE,
      'survivor_count':len(decoded),'zero_child_count':sum(x['all_zero'] for x in decoded),
      'nonzero_child_count':sum(not x['all_zero'] for x in decoded),'survivors':decoded,
      'used_primes':used,'progress':progress,'elapsed_seconds':round(time.time()-st,3),
      'soundness':'Parents are exact known quotient tuples. Every child is Q + 8 times a subset of one certified MW basis; every deletion uses the complete projective local image modulo 16.'}
    Path('results').mkdir(exist_ok=True);Path('results/known_centered_mod16.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'survivors':len(decoded),'zero':out['zero_child_count'],'nonzero':out['nonzero_child_count'],'elapsed':out['elapsed_seconds']}))
if __name__=='__main__':main()
