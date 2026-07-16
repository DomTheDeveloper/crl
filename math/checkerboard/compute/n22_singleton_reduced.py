#!/usr/bin/env python3
"""Exact singleton-top-boundary regime for D_mono(22) target 34."""
import argparse,json,sys,time
from pathlib import Path
from pysat.solvers import Solver
import n22_data as c
import n22_exact_core as rcore
ap=argparse.ArgumentParser();ap.add_argument('--bit',type=int,required=True);ap.add_argument('--out',required=True);ap.add_argument('--solver',default='cadical195');ap.add_argument('--left-conflicts',type=int,default=10000);ap.add_argument('--rb-conflicts',type=int,default=3000);a=ap.parse_args();assert 0<=a.bit<11
def ass(nm,m):return [c.BIDS[nm][i] for i in range(11) if (m>>i)&1]
def limited(s,A,b):s.conf_budget(b);t=time.time();z=s.solve_limited(assumptions=A,expect_interrupt=True);return z,time.time()-t
cnf,pb=rcore.build_singleton(a.bit);out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True)
corner=1 if a.bit==0 else 0;lefts=[m for m in c.DOUBLES if (m&1)==corner];rbs=list(c.DOUBLES)
start=time.time();stats={'left_direct':0,'rb_direct':0,'leaves':0}
print(json.dumps({'event':'built','bit':a.bit,'lefts':lefts,'vars':cnf.nv,'clauses':len(cnf.clauses),'pb':pb}),flush=True)
with Solver(name=a.solver,bootstrap_with=cnf.clauses) as s,out.open('w',buffering=1) as f:
 for left in lefts:
  al=ass('left',left);z,dt=limited(s,al,a.left_conflicts)
  if z is False:
   rec={'event':'left','bit':a.bit,'left':left,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['left_direct']+=1;continue
  if z is True:
   M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'left','bit':a.bit,'left':left,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
  for rb in rbs:
   alb=al+ass('rb',rb);z,dt=limited(s,alb,a.rb_conflicts)
   if z is False:
    rec={'event':'rb','bit':a.bit,'left':left,'rb':rb,'status':'UNSAT','sec':dt};f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['rb_direct']+=1;continue
   if z is True:
    M={q for q in s.get_model() if q>0};rec={'event':'WITNESS','scope':'rb','bit':a.bit,'left':left,'rb':rb,'points':[c.P[i-1] for i in range(1,len(c.P)+1) if i in M]};f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
   for rr in [m for m in rbs if (m&1)==(rb&1)]:
    t=time.time();z=s.solve(assumptions=alb+ass('rr',rr));dt=time.time()-t;rec={'event':'leaf','bit':a.bit,'left':left,'rb':rb,'rr':rr,'status':'SAT' if z else 'UNSAT','sec':dt}
    if z:
     M={q for q in s.get_model() if q>0};rec['points']=[c.P[i-1] for i in range(1,len(c.P)+1) if i in M];f.write(json.dumps(rec)+'\n');print(json.dumps(rec));sys.exit(2)
    f.write(json.dumps(rec,separators=(',',':'))+'\n');stats['leaves']+=1
  rec={'event':'left_summary','bit':a.bit,'left':left,'status':'UNSAT','elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
 rec={'event':'summary','bit':a.bit,'status':'UNSAT','left_total':len(lefts),'closed':True,**stats,'elapsed':time.time()-start};f.write(json.dumps(rec,separators=(',',':'))+'\n');print(json.dumps(rec),flush=True)
