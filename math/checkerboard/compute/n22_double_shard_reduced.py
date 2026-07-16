#!/usr/bin/env python3
"""Exact all-double boundary shard with deterministic boundary prechecks."""
import argparse,json,sys,time,itertools,gc
from pathlib import Path
from pysat.solvers import Solver
import n22_data as c
import n22_exact_core as rcore
ap=argparse.ArgumentParser();ap.add_argument('--top',type=int,required=True);ap.add_argument('--shard',type=int,required=True);ap.add_argument('--shards',type=int,default=4);ap.add_argument('--out',required=True);ap.add_argument('--solver',default='cadical195');ap.add_argument('--left-conflicts',type=int,default=10000);ap.add_argument('--rb-conflicts',type=int,default=3000);a=ap.parse_args()
assert a.top in c.DOUBLES and 0<=a.shard<a.shards
out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True);cnf,info=rcore.build_double(a.top)
allm=[m for m in c.DOUBLES if m>=a.top];lefts_all=[m for m in allm if (m&1)==(a.top&1)];lefts=[m for i,m in enumerate(lefts_all) if i%a.shards==a.shard]
def ass(nm,m):return [c.BIDS[nm][i] for i in range(11) if (m>>i)&1]
BOUNDARY_IDS=set(v for ids in c.BIDS.values() for v in ids)
BOUNDARY_TRIPLES=set()
for _L in c.LINES:
 _q=[v for v in _L if v in BOUNDARY_IDS]
 BOUNDARY_TRIPLES.update(frozenset(t) for t in itertools.combinations(_q,3))
def boundary_ids(*pairs):
 S=set()
 for nm,m in pairs:S.update(ass(nm,m))
 return S
def boundary_reason(S):
 if any(t<=S for t in BOUNDARY_TRIPLES):return 'boundary_collinear_triple'
 e=sum(c.COVERAGE[v-1]-c.DEN for v in S)
 if e>c.BUD:return f'boundary_excess_{e}'
 return None
def rrs(left,rb):
 return [rr for rr in allm if (rr&1)==(rb&1) and not (left==a.top and rr<rb) and not (rb==a.top and rr<left) and not (rr==a.top and rb<left)]
def limited(s,A,b):s.conf_budget(b);t=time.time();z=s.solve_limited(assumptions=A,expect_interrupt=True);return z,time.time()-t
start=time.time();stats={'left_direct':0,'rb_direct':0,'leaves':0,'witness':0}
print(json.dumps({'event':'built','top':a.top,'shard':a.shard,'shards':a.shards,'lefts':lefts,'left_total_global':len(lefts_all),'rb_total':len(allm),'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':info,'solver':a.solver}),flush=True)
s=Solver(name=a.solver,bootstrap_with=cnf.clauses);del cnf;gc.collect()
with s,out.open('w',buffering=1) as f:
 for left in lefts:
  _reason=boundary_reason(boundary_ids(('top',a.top),('left',left)))
  if _reason:
   rec={'event':'left','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','reason':_reason};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['left_direct']+=1;print(json.dumps(rec),flush=True);continue
  al=ass('left',left);z,dt=limited(s,al,a.left_conflicts)
  if z is False:
   rec={'event':'left','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['left_direct']+=1;print(json.dumps(rec),flush=True);continue
  if z is True:
   M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'left','top':a.top,'shard':a.shard,'left':left,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
  closed=0
  for rb in allm:
   _reason=boundary_reason(boundary_ids(('top',a.top),('left',left),('rb',rb)))
   if _reason:
    rec={'event':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','reason':_reason};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['rb_direct']+=1;closed+=1;continue
   alb=al+ass('rb',rb);z,dt=limited(s,alb,a.rb_conflicts)
   if z is False:
    rec={'event':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['rb_direct']+=1;closed+=1;continue
   if z is True:
    M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
   for rr in rrs(left,rb):
    _reason=boundary_reason(boundary_ids(('top',a.top),('left',left),('rb',rb),('rr',rr)))
    if _reason:
     rec={'event':'leaf','top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'status':'UNSAT','sec':0.0,'reason':_reason};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['leaves']+=1;continue
    t=time.time();z=s.solve(assumptions=alb+ass('rr',rr));dt=time.time()-t;rec={'event':'leaf','top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'status':'SAT' if z else 'UNSAT','sec':dt}
    if z:
     M={q for q in s.get_model() if q>0};rec['points']=[c.P[i-1] for i in range(1,len(c.P)+1) if i in M];f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
    f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['leaves']+=1
   closed+=1
  rec={'event':'left_summary','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','rb_closed':closed,'rb_total':len(allm),'elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
 rec={'event':'shard_summary','top':a.top,'shard':a.shard,'shards':a.shards,'status':'UNSAT','assigned_lefts':lefts,'assigned_count':len(lefts),'closed':True,**stats,'elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
