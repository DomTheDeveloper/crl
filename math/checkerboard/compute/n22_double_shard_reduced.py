#!/usr/bin/env python3
"""Exact all-double boundary shard with prechecks and learned parent re-probing."""
import argparse,json,sys,time,itertools,gc
from pathlib import Path
from pysat.solvers import Solver
import n22_data as c
import n22_exact_core as rcore

ap=argparse.ArgumentParser()
ap.add_argument('--top',type=int,required=True)
ap.add_argument('--shard',type=int,required=True)
ap.add_argument('--shards',type=int,default=4)
ap.add_argument('--out',required=True)
ap.add_argument('--solver',default='cadical195')
ap.add_argument('--left-conflicts',type=int,default=10000)
ap.add_argument('--rb-conflicts',type=int,default=3000)
ap.add_argument('--left-recheck-conflicts',type=int,default=100000)
ap.add_argument('--rb-recheck-conflicts',type=int,default=20000)
ap.add_argument('--left-recheck-every',type=int,default=4)
ap.add_argument('--rb-recheck-every',type=int,default=8)
a=ap.parse_args()
assert a.top in c.DOUBLES and 0<=a.shard<a.shards
assert min(a.left_conflicts,a.rb_conflicts,a.left_recheck_conflicts,a.rb_recheck_conflicts)>0
assert a.left_recheck_every>0 and a.rb_recheck_every>0
out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True);cnf,info=rcore.build_double(a.top)
allm=[m for m in c.DOUBLES if m>=a.top]
lefts_all=[m for m in allm if (m&1)==(a.top&1)]
lefts=[m for i,m in enumerate(lefts_all) if i%a.shards==a.shard]
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
def limited(s,A,b):
 s.conf_budget(b);t=time.time();z=s.solve_limited(assumptions=A,expect_interrupt=True);return z,time.time()-t
def witness(s,scope,left,rb=None,rr=None):
 M={q for q in s.get_model() if q>0}
 return {'event':'WITNESS','scope':scope,'top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]}
def emit(f,rec,echo=False):
 f.write(json.dumps(rec,separators=(',',':'))+'\n')
 if echo:print(json.dumps(rec),flush=True)

start=time.time();stats={'left_direct':0,'left_refined':0,'rb_direct':0,'rb_refined':0,'leaves':0,'witness':0}
print(json.dumps({'event':'built','top':a.top,'shard':a.shard,'shards':a.shards,'lefts':lefts,'left_total_global':len(lefts_all),'rb_total':len(allm),'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':info,'solver':a.solver,'left_conflicts':a.left_conflicts,'rb_conflicts':a.rb_conflicts,'left_recheck_conflicts':a.left_recheck_conflicts,'rb_recheck_conflicts':a.rb_recheck_conflicts,'left_recheck_every':a.left_recheck_every,'rb_recheck_every':a.rb_recheck_every}),flush=True)
s=Solver(name=a.solver,bootstrap_with=cnf.clauses);del cnf;gc.collect()
with s,out.open('w',buffering=1) as f:
 for left in lefts:
  reason=boundary_reason(boundary_ids(('top',a.top),('left',left)))
  if reason:
   rec={'event':'left','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','reason':reason};emit(f,rec,True);stats['left_direct']+=1;continue
  al=ass('left',left);z,dt=limited(s,al,a.left_conflicts)
  if z is False:
   rec={'event':'left','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','sec':dt};emit(f,rec,True);stats['left_direct']+=1;continue
  if z is True:
   rec=witness(s,'left',left);emit(f,rec,True);sys.exit(2)
  closed=0;left_closed=False
  for rb in allm:
   reason=boundary_reason(boundary_ids(('top',a.top),('left',left),('rb',rb)))
   if reason:
    rec={'event':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','reason':reason};emit(f,rec);stats['rb_direct']+=1;closed+=1
   else:
    alb=al+ass('rb',rb);z,dt=limited(s,alb,a.rb_conflicts)
    if z is False:
     rec={'event':'rb','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','sec':dt};emit(f,rec);stats['rb_direct']+=1;closed+=1
    elif z is True:
     rec=witness(s,'rb',left,rb);emit(f,rec,True);sys.exit(2)
    else:
     rr_list=rrs(left,rb);tested=0
     for rr in rr_list:
      reason=boundary_reason(boundary_ids(('top',a.top),('left',left),('rb',rb),('rr',rr)))
      if reason:
       rec={'event':'leaf','top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'status':'UNSAT','sec':0.0,'reason':reason};emit(f,rec);stats['leaves']+=1
      else:
       t=time.time();z=s.solve(assumptions=alb+ass('rr',rr));dt=time.time()-t
       rec={'event':'leaf','top':a.top,'shard':a.shard,'left':left,'rb':rb,'rr':rr,'status':'SAT' if z else 'UNSAT','sec':dt}
       if z:
        M={q for q in s.get_model() if q>0};rec['points']=[c.P[i-1] for i in range(1,len(c.P)+1) if i in M];emit(f,rec,True);sys.exit(2)
       emit(f,rec);stats['leaves']+=1
      tested+=1
      if tested%a.rb_recheck_every==0 and tested<len(rr_list):
       rz,rdt=limited(s,alb,a.rb_recheck_conflicts)
       if rz is True:
        rec=witness(s,'rb_recheck',left,rb);emit(f,rec,True);sys.exit(2)
       if rz is False:
        rec={'event':'rb_refined','top':a.top,'shard':a.shard,'left':left,'rb':rb,'status':'UNSAT','tested_rr':tested,'rr_total':len(rr_list),'sec':rdt};emit(f,rec);stats['rb_refined']+=1;break
     closed+=1
   if closed<len(allm) and closed%a.left_recheck_every==0:
    lz,ldt=limited(s,al,a.left_recheck_conflicts)
    if lz is True:
     rec=witness(s,'left_recheck',left);emit(f,rec,True);sys.exit(2)
    if lz is False:
     rec={'event':'left_refined','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','rb_closed_before_recheck':closed,'rb_total':len(allm),'sec':ldt};emit(f,rec,True);stats['left_refined']+=1;closed=len(allm);left_closed=True;break
  rec={'event':'left_summary','top':a.top,'shard':a.shard,'left':left,'status':'UNSAT','rb_closed':closed,'rb_total':len(allm),'refined_parent':left_closed,'elapsed':time.time()-start};emit(f,rec,True)
 rec={'event':'shard_summary','top':a.top,'shard':a.shard,'shards':a.shards,'status':'UNSAT','assigned_lefts':lefts,'assigned_count':len(lefts),'closed':True,**stats,'elapsed':time.time()-start};emit(f,rec,True)
