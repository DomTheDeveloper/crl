#!/usr/bin/env python3
"""Exact certificates for checkerboard D_mono(17)=26 and D_mono(21)=32.

`verify` is standard-library only. `generate` uses SciPy/HiGHS only to discover
LP branch trees, then rounds and checks every leaf with exact integer arithmetic.
`solve` cross-checks witnesses and upper bounds with CP-SAT and HiGHS.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, math, subprocess, sys
from itertools import combinations
from math import gcd
from pathlib import Path

ROOT=Path(__file__).resolve().parent; ART=ROOT/'artifacts'; DEN=10**8
DATA={
 'values':{'17':{'0':26,'1':26,'unrestricted':26},'21':{'0':32,'1':32,'unrestricted':32}},
 'constructions':{
 '17-0':[[0,8],[0,12],[1,1],[1,5],[2,12],[2,14],[3,1],[3,11],[4,0],[5,3],[6,16],[7,13],[8,2],[8,14],[9,3],[10,0],[11,13],[12,16],[13,5],[13,15],[14,2],[14,4],[15,11],[15,15],[16,4],[16,8]],
 '17-1':[[0,5],[0,7],[1,10],[1,14],[2,1],[2,3],[3,10],[3,14],[5,16],[6,1],[6,3],[7,16],[8,5],[8,11],[9,0],[10,13],[10,15],[11,0],[13,2],[13,6],[14,13],[14,15],[15,2],[15,6],[16,9],[16,11]],
 '21-0':[[0,10],[0,14],[1,5],[1,7],[2,2],[2,20],[3,11],[3,19],[4,12],[4,16],[5,3],[6,0],[6,18],[7,3],[7,5],[9,19],[11,1],[13,15],[13,17],[14,2],[14,20],[15,17],[16,4],[16,8],[17,1],[17,9],[18,0],[18,18],[19,13],[19,15],[20,6],[20,10]],
 '21-1':[[0,3],[0,7],[1,6],[1,16],[2,3],[3,14],[3,18],[4,7],[5,10],[5,16],[6,5],[6,19],[7,20],[8,1],[9,0],[9,18],[11,2],[11,20],[12,19],[13,0],[14,1],[14,15],[15,4],[15,10],[16,13],[17,2],[17,6],[18,17],[19,4],[19,14],[20,13],[20,17]]},
 'duals':{
 '17-0':{'d':67,'a':[0,0,10,18,24,29,35,38,39],'b':[20,14,9,5,2,0,0,0,0],'obj':1788},
 '17-1':{'d':33,'a':[0,0,5,9,12,15,17,18],'b':[12,9,6,4,2,1,0,0,0],'obj':880},
 '21-0':{'d':75,'a':[0,0,0,10,18,24,30,36,41,44,45],'b':[28,21,15,10,6,3,1,0,0,0,0],'obj':2476,'budget':1},
 '21-1':{'d':48,'a':[0,0,6,11,15,18,22,25,27,28],'b':[15,12,8,6,3,2,0,0,0,0,0],'obj':1584,'budget':0}}}

def points(n,p): return [(x,y) for x in range(n) for y in range(n) if (x+y)%2==p]
def lkey(P,Q):
 x1,y1=P;x2,y2=Q;a,b=y2-y1,x1-x2;c=-(a*x1+b*y1);g=gcd(gcd(abs(a),abs(b)),abs(c));a//=g;b//=g;c//=g
 return (-a,-b,-c) if a<0 or (a==0 and b<0) else (a,b,c)
def lines(P):
 d={}
 for a,b in combinations(P,2): d.setdefault(lkey(a,b),set()).update((a,b))
 return sorted(tuple(sorted(s)) for s in d.values() if len(s)>=3)
def cover(n,p,P,a,b):
 m=(n-1)//2;x,y=P;dx,dy=min(x,n-1-x),min(y,n-1-y);xx,yy=max(dx,dy),min(dx,dy)
 if p==0:
  u,v=(xx+yy)//2,(xx-yy)//2;return a[u]+a[m-v]+b[u+v]+b[u-v]
 u,v=(xx+yy-1)//2,(xx-yy-1)//2;return a[u]+a[m-v-1]+b[u+v+1]+b[u-v]
def objective(n,p,a,b):
 m=(n-1)//2
 return 8*sum(a[:m])+8*sum(b[:m])+4*(a[m]+b[m]) if p==0 else 8*sum(a)+8*sum(b[:m])+4*b[m]
def model(n,p,target):
 q=DATA['duals'][f'{n}-{p}']; allp=points(n,p); sl={x:cover(n,p,x,q['a'],q['b'])-q['d'] for x in allp}
 P=[x for x in allp if sl[x]<=q['budget']] if n==21 else allp; L=lines(P); I={x:i+1 for i,x in enumerate(P)}
 return {'n':n,'p':p,'target':target,'P':P,'L':L,'I':I,'sl':sl}
def opb(n,p,target):
 M=model(n,p,target); C=[]
 for L in M['L']: C.append(' '.join(f'+1 x{M["I"][x]}' for x in L)+' <= 2 ;')
 C.append(' '.join(f'+1 x{M["I"][x]}' for x in M['P'])+f' = {target} ;')
 if n==21 and p==0: C.append(' '.join(f'+1 x{M["I"][x]}' for x in M['P'] if M['sl'][x])+' <= 1 ;')
 return f'* #variable= {len(M["P"])} #constraint= {len(C)}\n* n={n} parity={p} target={target}\n'+'\n'.join(C)+'\n'
def gzwrite(path,payload):
 path.parent.mkdir(parents=True,exist_ok=True)
 with path.open('wb') as f:
  with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0,compresslevel=9) as g:g.write(payload)

def check_constructions():
 for k,raw in sorted(DATA['constructions'].items()):
  n,p=map(int,k.split('-'));P=[tuple(x) for x in raw];assert len(P)==len(set(P))==DATA['values'][str(n)][str(p)]
  assert all(0<=x<n and 0<=y<n and (x+y)%2==p for x,y in P)
  assert all((b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]) for a,b,c in combinations(P,3))
  d={}
  for a,b in combinations(P,2):d.setdefault(lkey(a,b),set()).update((a,b))
  assert max(map(len,d.values()))<=2;print('PASS witness',k,len(P))
def check_duals():
 exp={(21,0):(136,548,116,20),(21,1):(132,508,132,16)}
 for k,q in sorted(DATA['duals'].items()):
  n,p=map(int,k.split('-'));cov=[cover(n,p,x,q['a'],q['b']) for x in points(n,p)];assert min(cov)>=q['d'];assert objective(n,p,q['a'],q['b'])==q['obj']
  if n==17: assert q['obj']<27*q['d'];print('PASS dual',k,f"{q['obj']}/{q['d']} < 27")
  else:
   M=model(n,p,33);E=exp[(n,p)];sl=[x-q['d'] for x in cov];assert q['budget']==q['obj']-33*q['d'];assert (len(M['P']),len(M['L']),sl.count(0),sl.count(1))==E
   print('PASS reduction',k,len(M['P']),len(M['L']))
def check_bnb(p):
 M=model(21,p,33);P,L,I=M['P'],M['L'],M['I'];rows=[([I[x]-1 for x in l],2) for l in L]
 if p==0:rows.append(([i for i,x in enumerate(P) if M['sl'][x]],1))
 with gzip.open(ART/f'n21-p{p}-target33.bbcert.json.gz','rt') as f:C=json.load(f)
 assert C['point_order']==[list(x) for x in P] and C['denominator']==DEN;seen=set()
 def walk(N,F):
  if 'leaf'in N:
   z=N['leaf'];assert z not in seen;seen.add(z);Q=C['leaves'][z];la=dict(Q['lambda']);up=dict(Q['upper']);rhs=[]
   for vs,b in rows:
    r=b-sum(F.get(j,0) for j in vs);assert r>=0;rhs.append(r)
   cv={j:up.get(j,0) for j in range(len(P)) if j not in F}
   for i,v in la.items():
    for j in rows[i][0]:
     if j not in F:cv[j]+=v
   assert all(v>=DEN for v in cv.values());o=sum(F.values())*DEN+sum(rhs[i]*v for i,v in la.items())+sum(up.values());assert o==Q['objective']<33*DEN;return
  j=N['branch'];assert j not in F;G=dict(F);G[j]=1;walk(N['one'],G);G=dict(F);G[j]=0;walk(N['zero'],G)
 walk(C['tree'],{});assert len(seen)==len(C['leaves']);print('PASS exact BnB',p,C['stats'])
def manifest(write=False):
 fs=sorted(x for x in ART.rglob('*') if x.is_file() and x.name!='SHA256SUMS');text=''.join(f'{hashlib.sha256(x.read_bytes()).hexdigest()}  {x.relative_to(ART)}\n' for x in fs);path=ART/'SHA256SUMS'
 if write:path.write_text(text)
 else:assert path.read_text()==text

def generate():
 import numpy as np
 from scipy.optimize import linprog
 ART.mkdir(exist_ok=True);(ART/'instances').mkdir(exist_ok=True)
 (ART/'results.json').write_text(json.dumps(DATA,sort_keys=True,indent=2)+'\n')
 for n,p,t in [(17,0,27),(17,1,27),(21,0,33),(21,1,33)]: (ART/'instances'/f'n{n}-p{p}-target{t}.opb').write_text(opb(n,p,t))
 for p in (0,1):
  M=model(21,p,33);R=[([M['I'][x]-1 for x in l],2) for l in M['L']]
  if p==0:R.append(([i for i,x in enumerate(M['P']) if M['sl'][x]],1))
  A=np.zeros((len(R),len(M['P'])));
  for i,(vs,_) in enumerate(R):A[i,vs]=1
  leaves=[];nodes=0;depth=0
  def rec(F,d):
   nonlocal nodes,depth;nodes+=1;depth=max(depth,d);free=[j for j in range(A.shape[1]) if j not in F];rhs=np.array([b-sum(F.get(j,0) for j in vs) for vs,b in R],float);assert min(rhs)>=0
   z=linprog(-np.ones(len(free)),A_ub=A[:,free],b_ub=rhs,bounds=(0,1),method='highs');assert z.success;val=sum(F.values())-z.fun
   if val<33-1e-7:
    la={i:math.ceil((float(v)+1e-10)*DEN) for i,v in enumerate(-z.ineqlin.marginals) if v>1e-12};up={free[i]:math.ceil((float(v)+1e-10)*DEN) for i,v in enumerate(-z.upper.marginals) if v>1e-12};cv={j:up.get(j,0) for j in free}
    S=set(free)
    for i,v in la.items():
     for j in R[i][0]:
      if j in S:cv[j]+=v
    for j in free:
     if cv[j]<DEN:up[j]=up.get(j,0)+DEN-cv[j];cv[j]=DEN
    ri=[b-sum(F.get(j,0) for j in vs) for vs,b in R];o=sum(F.values())*DEN+sum(ri[i]*v for i,v in la.items())+sum(up.values());assert o<33*DEN;k=len(leaves);leaves.append({'lambda':sorted(la.items()),'upper':sorted(up.items()),'objective':o});return {'leaf':k}
   frac=[(abs(float(v)-.5),j) for j,v in zip(free,z.x) if 1e-7<v<1-1e-7];assert frac;_,j=min(frac);G=dict(F);G[j]=1;a=rec(G,d+1);G=dict(F);G[j]=0;return {'branch':j,'one':a,'zero':rec(G,d+1)}
  tree=rec({},0);C={'schema':1,'n':21,'parity':p,'denominator':DEN,'point_order':[list(x) for x in M['P']],'tree':tree,'leaves':leaves,'stats':{'nodes':nodes,'leaves':len(leaves),'depth':depth}};gzwrite(ART/f'n21-p{p}-target33.bbcert.json.gz',json.dumps(C,sort_keys=True,separators=(',',':')).encode());print('WROTE proof',p,C['stats'])
 manifest(True)
def solve(seconds):
 import numpy as np
 from ortools.sat.python import cp_model
 from scipy.optimize import Bounds,LinearConstraint,milp
 out={'policy':'UNKNOWN/time limit/interruption = NO_RESULT','cpsat':{},'highs':{}}
 for n,p in [(17,0),(17,1),(21,0),(21,1)]:
  P=points(n,p);L=lines(P);I={x:i for i,x in enumerate(P)};W={tuple(x) for x in DATA['constructions'][f'{n}-{p}']};cm=cp_model.CpModel();x=[cm.new_bool_var(f'x{i}') for i in range(len(P))]
  for l in L:cm.add(sum(x[I[q]] for q in l)<=2)
  for i,q in enumerate(P):cm.add(x[i]==int(q in W))
  cs=cp_model.CpSolver();cs.parameters.max_time_in_seconds=seconds;cs.parameters.num_search_workers=1;s=cs.solve(cm);assert s in (cp_model.OPTIMAL,cp_model.FEASIBLE);out['cpsat'][f'witness-{n}-{p}']='VERIFIED_WITNESS'
  rows=[];lo=[];hi=[]
  for l in L:r=np.zeros(len(P));r[[I[q] for q in l]]=1;rows.append(r);lo.append(-np.inf);hi.append(2)
  for i,q in enumerate(P):r=np.zeros(len(P));r[i]=1;rows.append(r);lo.append(int(q in W));hi.append(int(q in W))
  h=milp(np.zeros(len(P)),integrality=np.ones(len(P)),bounds=Bounds(np.zeros(len(P)),np.ones(len(P))),constraints=LinearConstraint(np.array(rows),np.array(lo),np.array(hi)),options={'time_limit':seconds});assert h.status==0;out['highs'][f'witness-{n}-{p}']='VERIFIED_WITNESS'
  t=27 if n==17 else 33;M=model(n,p,t);cm=cp_model.CpModel();x=[cm.new_bool_var(f'x{i}') for i in range(len(M['P']))]
  for l in M['L']:cm.add(sum(x[M['I'][q]-1] for q in l)<=2)
  cm.add(sum(x)==t)
  if n==21 and p==0:cm.add(sum(M['sl'][q]*x[i] for i,q in enumerate(M['P']))<=1)
  cs=cp_model.CpSolver();cs.parameters.max_time_in_seconds=seconds;cs.parameters.num_search_workers=1;s=cs.solve(cm);assert s==cp_model.INFEASIBLE,('NO_RESULT',cs.status_name(s));out['cpsat'][f'upper-{n}-{p}']='PROVED_INFEASIBLE'
  rows=[];lo=[];hi=[]
  for l in M['L']:r=np.zeros(len(M['P']));r[[M['I'][q]-1 for q in l]]=1;rows.append(r);lo.append(-np.inf);hi.append(2)
  rows.append(np.ones(len(M['P'])));lo.append(t);hi.append(t)
  if n==21 and p==0:rows.append(np.array([M['sl'][q] for q in M['P']]));lo.append(-np.inf);hi.append(1)
  h=milp(np.zeros(len(M['P'])),integrality=np.ones(len(M['P'])),bounds=Bounds(np.zeros(len(M['P'])),np.ones(len(M['P']))),constraints=LinearConstraint(np.array(rows),np.array(lo),np.array(hi)),options={'time_limit':seconds});assert h.status==2,('NO_RESULT',h.status,h.message);out['highs'][f'upper-{n}-{p}']='PROVED_INFEASIBLE'
 (ART/'solver_results.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');manifest(True);print(json.dumps(out,indent=2))
def verify():
 check_constructions();check_duals()
 for n,p,t in [(17,0,27),(17,1,27),(21,0,33),(21,1,33)]:assert (ART/'instances'/f'n{n}-p{p}-target{t}.opb').read_text()==opb(n,p,t)
 check_bnb(0);check_bnb(1);manifest(False);print('ALL_DETERMINISTIC_CHECKS_PASS')
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('command',choices=['generate','verify','solve']);a.add_argument('--seconds',type=float,default=120);z=a.parse_args();{'generate':generate,'verify':verify,'solve':lambda:solve(z.seconds)}[z.command]()
