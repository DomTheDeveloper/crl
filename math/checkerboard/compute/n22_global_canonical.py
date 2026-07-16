#!/usr/bin/env python3
"""Global symmetry-broken exact CNFs for the two possible boundary regimes."""
import sys,time,json
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType as CEnc
from pysat.solvers import Solver
import n22_data as d
import n22_exact_core as core

def add_double_mask_side(cnf,vp,name,ids):
 sels=[vp.id(('mask',name,m)) for m in d.DOUBLES]
 cnf.extend(CardEnc.equals(sels,1,vpool=vp,encoding=CEnc.seqcounter).clauses)
 for s,m in zip(sels,d.DOUBLES):
  for i,v in enumerate(ids):cnf.append([-s,v if (m>>i)&1 else -v])
 return sels

def build_double():
 vp=IDPool(start_from=len(d.P)+1);cnf,info=core.base_cnf(vp)
 S={nm:add_double_mask_side(cnf,vp,nm,d.BIDS[nm]) for nm in ('top','left','rb','rr')}
 for nm in ('left','rb','rr'):
  for j,s in enumerate(S[nm]):cnf.append([-s]+S['top'][:j+1])
 for ti in range(len(d.DOUBLES)):
  for ri in range(len(d.DOUBLES)):
   cnf.append([-S['top'][ti],-S['left'][ti],-S['rr'][ri]]+S['rb'][:ri+1])
   cnf.append([-S['top'][ti],-S['rb'][ti],-S['rr'][ri]]+S['left'][:ri+1])
   cnf.append([-S['top'][ti],-S['rr'][ti],-S['rb'][ri]]+S['left'][:ri+1])
 cnf.nv=max(cnf.nv,vp.top);return cnf,info

def build_singleton():
 vp=IDPool(start_from=len(d.P)+1);cnf,info=core.base_cnf(vp)
 cnf.extend(CardEnc.equals(d.BIDS['top'],1,vpool=vp,encoding=CEnc.seqcounter).clauses)
 for nm in ('left','rb','rr'):add_double_mask_side(cnf,vp,nm,d.BIDS[nm])
 cnf.nv=max(cnf.nv,vp.top);return cnf,info

def main():
 regime=sys.argv[1];solver=sys.argv[2] if len(sys.argv)>2 else 'cadical300'
 t=time.time();cnf,info=build_double() if regime=='double' else build_singleton()
 print(json.dumps({'event':'built','regime':regime,'solver':solver,'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':info,'build_sec':time.time()-t}),flush=True)
 t=time.time()
 with Solver(name=solver,bootstrap_with=cnf.clauses) as s:
  z=s.solve();rec={'event':'result','regime':regime,'solver':solver,'status':'SAT' if z else 'UNSAT','sec':time.time()-t}
  if z:
   M={q for q in s.get_model() if q>0};rec['points']=[d.P[i-1] for i in range(1,len(d.P)+1) if i in M]
  print(json.dumps(rec),flush=True);raise SystemExit(2 if z else 0)
if __name__=='__main__':main()
