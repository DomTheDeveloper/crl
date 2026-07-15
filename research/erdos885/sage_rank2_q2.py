#!/usr/bin/env python3
"""Test the rank-two quotient's global mod-2 classes over Q_2.

This checks the kernel condition in Stoll's Chabauty-without-Mordell-Weil
criterion for the single rank-two elliptic quotient.
"""
from __future__ import annotations
import itertools,json,traceback
from pathlib import Path
from sage.all import EllipticCurve,Qp,QQ,proof
import sage_kummer_compat as kc
from sage_unified_descent import point_json

def main():
    E,p,q=kc.input_curve(kc.TRIPLES[0])  # rows 2578,5553,5922, certified rank 2
    gens,rank=kc.certified_basis_on_input(E)
    tors=[E(0,0),E(-4*p,0)]
    K=Qp(2,prec=120,type='capped-rel');EK=E.change_ring(K)
    classes=[]
    for free in itertools.product([0,1],repeat=rank):
      P=E(0)
      for b,G in zip(free,gens):
        if b:P+=G
      for tb in itertools.product([0,1],repeat=2):
        Q=P
        for b,T in zip(tb,tors):
          if b:Q+=T
        rec={'free_bits':list(free),'torsion_bits':list(tb),'point':point_json(Q)}
        try:
          Q2=EK(Q); halves=Q2.division_points(2)
          rec['q2_half_count']=len(halves)
          rec['q2_halves']=[point_json(H) for H in halves]
          rec['locally_divisible_by_2']=bool(halves)
        except Exception as exc:
          rec['division_error']=f'{type(exc).__name__}: {exc}'
          rec['division_traceback']=traceback.format_exc(limit=8)
        classes.append(rec)
    kernel=[x for x in classes if x.get('locally_divisible_by_2')]
    torsion_kernel=[x for x in kernel if x['free_bits']==[0]*rank]
    out={'rows':[2578,5553,5922],'rank':rank,'global_class_count':len(classes),
      'q2_precision':120,'kernel_count':len(kernel),'torsion_kernel_count':len(torsion_kernel),
      'non_torsion_kernel_count':len(kernel)-len(torsion_kernel),'classes':classes,
      'kernel_condition_holds':len(kernel)==len(torsion_kernel),
      'interpretation':'Kernel condition holds iff every global class locally divisible by 2 at Q2 is represented by rational torsion.'}
    Path('results').mkdir(exist_ok=True);Path('results/rank2_q2.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ['kernel_count','torsion_kernel_count','non_torsion_kernel_count','kernel_condition_holds']}))
if __name__=='__main__':main()
