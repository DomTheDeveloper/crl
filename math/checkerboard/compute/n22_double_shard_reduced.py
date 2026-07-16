#!/usr/bin/env python3
"""Exact all-double boundary shard for D_mono(22) target 34.

Each invocation fixes one canonical top mask and processes one residue class of
admissible left masks. Every branch is either proved UNSAT directly or split
by the two remaining boundary masks until every terminal leaf is UNSAT.
"""
import argparse, json, sys, time
from pathlib import Path
from pysat.solvers import Solver
import n22_data as c
import n22_exact_core as rcore
ap=argparse.ArgumentParser();ap.add_argument('--top',type=int,required=True);ap.add_argument('--shard',type=int,required=True);ap.add_argument('--shards',type=int,default=4);ap.add_argument('--out',required=True);ap.add_argument('--solver',default='cadical195');ap.add_argument('--left-conflicts',type=int,default=10000);ap.add_argument('--rb-conflicts',type=int,default=3000);a=ap.parse_args()
assert a.top in c.DOUBLES and 0<=a.shard<a.shards
out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True);cnf,info=rcore.build_double(a.top)
allm=[m for m in c.DOUBLES if m>=a.top];lefts_all=[m for m in allm if (m&1)==(a.top&1)];lefts=[m for i,m in enumerate(lefts_all) if i%a.shards==a.shard]
def ass(nm,m):return [c.BIDS[nm][i] for i in range(11) if (m>>i)&1]
def required_rrs(left,rb):
 ans=[]
 for rr in allm:
  if (rr&1)!=(rb&1):continue
  if left==a.top and rr<rb:continue
  if rb==a.top and rr<left:continue
  if rr==a.top and rb<left:continue
  ans.append(rr)
 return ans
def limited(s,A,b):s.conf_budget(b);t=time.time();z=s.solve_limited(assumptions=A,expect_interrupt=True);return z,time.time()-t
start=time.time();stats={'left_direct':0,'rb_direct':0,'leaves':0,'witness':0}
print(json.dumps({'event':'built','top':a.top,'shard':a.shard,'shards':a.shards,'lefts':lefts,'left_total_global':len(lefts_all),'rb_total':len(allm),'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':info,'solver':a.solver}),flush=True)
with Solver(name=a.solver,bootstrap_with=cnf.clauses) as s,out.open('w',buffering=1) as f:
 for left in lefts:
  al=ass('left',left);z,dt=limited(s,al,a.left_conflicts)
  if z is False:
   rec={'event':'left','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['left_direct']+=1;print(json.dumps(rec),flush=True);continue
  if z is True:
   M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'left','top':a.top,'shard':a.shard,'left':left,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
  closed_rb=0
  for rb in allm:
   alb=al+ass('rb',rb);z,dt=limited(s,alb,a.rb_conflicts)
   if z is False:
    rec={'event':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['rb_direct']+=1;closed_rb+=1;continue
   if z is True:
    M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
   for rr in required_rrs(left,rb):
    t=time.time();z=s.solve(assumptions=alb+ass('rr',rr));dt=time.time()-t;rec={'event':'leaf','top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'status':'SAT' if z else 'UNSAT','sec':dt}
    if z:
     M={q for q in s.get_model() if q>0};rec['points']=[c.P[i-1] for i in range(1,len(c.P)+1) if i in M];f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
    f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['leaves']+=1
   closed_rb+=1
  rec={'event':'left_summary','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','rb_closed':closed_rb,'rb_total':len(allm),'elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
 rec={'event':'shard_summary','top':a.top,'shard':a.shard,'shards':a.shards,'status':'UNSAT','assigned_lefts':lefts,'assigned_count':len(lefts),'closed':True,**stats,'elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
