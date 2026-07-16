#!/usr/bin/env python3
import sys,time,json,os
from pysat.solvers import Solver
import n22_exact_core as core, n22_data as d

def timed_solve(s, assumptions, budget):
 assumptions=list(dict.fromkeys(assumptions))
 s.conf_budget(int(budget)); t=time.time(); r=s.solve_limited(assumptions=assumptions); return r,time.time()-t

def mask_assump(nm,m): return [d.BIDS[nm][i] for i in range(11) if (m>>i)&1]
def verify_model(model):
 M={v for v in model if v>0}; pts=[d.P[i-1] for i in range(1,len(d.P)+1) if i in M]
 assert len(pts)==34 and all(sum(1 for v in L if v in M)<=2 for L in d.LINES)
 return pts

def main():
 top=int(sys.argv[1]); shard=int(sys.argv[2]); shards=int(sys.argv[3]); solver=os.getenv('SOLVER','glucose42')
 left_bud=int(os.getenv('LEFT_BUD','2000000'));rb_bud=int(os.getenv('RB_BUD','500000'));leaf_bud=int(os.getenv('LEAF_BUD','5000000'))
 cnf,info=core.build_double(top);allowed=[m for m in d.DOUBLES if m>=top]
 lefts=[m for m in allowed if (m&1)==(top&1)]; assigned=[m for i,m in enumerate(lefts) if i%shards==shard]
 print(json.dumps({'event':'built','top':top,'shard':shard,'shards':shards,'solver':solver,'assigned_lefts':assigned,'allowed':len(allowed),'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':info,'budgets':[left_bud,rb_bud,leaf_bud]}),flush=True)
 unknown=[]; counts={'left_unsat':0,'rb_unsat':0,'leaf_unsat':0,'covered':0}; start=time.time()
 with Solver(name=solver,bootstrap_with=cnf.clauses) as s:
  for left in assigned:
   A1=mask_assump('left',left)
   r,dt=timed_solve(s,A1,left_bud)
   if r is True:
    pts=verify_model(s.get_model());print(json.dumps({'event':'WITNESS','top':top,'left':left,'points':pts}),flush=True);return 2
   if r is False:
    counts['left_unsat']+=1;print(json.dumps({'event':'left','top':top,'left':left,'status':'UNSAT','sec':dt}),flush=True);continue
   for rb in allowed:
    A2=A1+mask_assump('rb',rb)
    r,dt=timed_solve(s,A2,rb_bud)
    if r is True:
     pts=verify_model(s.get_model());print(json.dumps({'event':'WITNESS','top':top,'left':left,'rb':rb,'points':pts}),flush=True);return 2
    if r is False:
     counts['rb_unsat']+=1;print(json.dumps({'event':'rb','top':top,'left':left,'rb':rb,'status':'UNSAT','sec':dt}),flush=True);continue
    for rr in allowed:
     if (rr&1)!=(rb&1): counts['covered']+=1;continue
     if (left==top and rr<rb) or (rb==top and rr<left) or (rr==top and rb<left): counts['covered']+=1;continue
     A3=A2+mask_assump('rr',rr)
     r,dt=timed_solve(s,A3,leaf_bud)
     if r is True:
      pts=verify_model(s.get_model());print(json.dumps({'event':'WITNESS','top':top,'left':left,'rb':rb,'rr':rr,'points':pts}),flush=True);return 2
     if r is False:
      counts['leaf_unsat']+=1;print(json.dumps({'event':'leaf','top':top,'left':left,'rb':rb,'rr':rr,'status':'UNSAT','sec':dt}),flush=True)
     else:
      unknown.append((left,rb,rr));print(json.dumps({'event':'leaf','top':top,'left':left,'rb':rb,'rr':rr,'status':'UNKNOWN','sec':dt}),flush=True)
 rec={'event':'shard_summary','top':top,'shard':shard,'assigned_lefts':assigned,'counts':counts,'unknown':unknown,'closed':not unknown,'elapsed':time.time()-start}
 print(json.dumps(rec),flush=True);return 0 if not unknown else 1
if __name__=='__main__':raise SystemExit(main())
