#!/usr/bin/env python3
"""Independent exact MIP/CP-SAT formulation for the n=22 target-34 exclusion."""
import argparse, itertools, json, math, time

def data():
    N=22; DEN=187; OBJ=6470; BUD=112
    A=[63,48,35,24,15,8,3,0,0,0,0]
    B=[0,0,0,22,40,54,67,80,92,100,104]
    C=[117,115,109,99,85,72,60,44,24,0,0]
    P=[(x,y) for x in range(N) for y in range(N) if (x+y)%2==0]
    idx={p:i for i,p in enumerate(P)}
    def key(p,q):
        x1,y1=p;x2,y2=q;a=y2-y1;b=x1-x2;c=-(a*x1+b*y1)
        g=math.gcd(math.gcd(abs(a),abs(b)),abs(c));a//=g;b//=g;c//=g
        if a<0 or (a==0 and b<0):a,b,c=-a,-b,-c
        return a,b,c
    D={}
    for i,p in enumerate(P):
        for q in P[i+1:]:
            s=D.setdefault(key(p,q),set());s.add(i);s.add(idx[q])
    lines=sorted(tuple(sorted(s)) for s in D.values() if len(s)>=3)
    WL=[]
    for x0 in range(N):
        w=A[min(x0,N-1-x0)];L=[idx[(x0,y)] for y in range(N) if (x0+y)%2==0]
        if w: WL.append((w,L,f'x{x0}'))
    for y0 in range(N):
        w=A[min(y0,N-1-y0)];L=[idx[(x,y0)] for x in range(N) if (x+y0)%2==0]
        if w: WL.append((w,L,f'y{y0}'))
    for sm in range(0,2*N-1,2):
        w=B[min(sm//2,N-1-sm//2)];L=[idx[(x,sm-x)] for x in range(N) if 0<=sm-x<N]
        if w: WL.append((w,L,f's{sm}'))
    for dd in range(-(N-2),N-1,2):
        w=C[abs(dd)//2];L=[idx[(x,x-dd)] for x in range(N) if 0<=x-dd<N]
        if w: WL.append((w,L,f'd{dd}'))
    cov=[sum(w for w,L,_ in WL if i in L) for i in range(len(P))]
    sides={
      'top':[idx[(0,2*i)] for i in range(11)],
      'left':[idx[(2*i,0)] for i in range(11)],
      'rb':[idx[(21,21-2*i)] for i in range(11)],
      'rr':[idx[(21-2*i,21)] for i in range(11)]}
    assert len(P)==242 and len(lines)==2455 and len(WL)==61
    assert min(cov)>=DEN and 2*sum(w for w,_,_ in WL)==OBJ and OBJ-34*DEN==BUD
    return P,lines,WL,cov,sides,DEN,BUD

def solve_cpsat(limit):
    from ortools.sat.python import cp_model
    P,lines,WL,cov,sides,DEN,BUD=data();m=cp_model.CpModel();x=[m.NewBoolVar(f'x{i}') for i in range(len(P))]
    for L in lines:m.Add(sum(x[i] for i in L)<=2)
    m.Add(sum(x)==34)
    for ids in sides.values():m.Add(sum(x[i] for i in ids)==2)
    weights=[1<<i for i in range(11)]
    top=sum(weights[i]*x[v] for i,v in enumerate(sides['top']))
    for nm in ('left','rb','rr'):m.Add(top<=sum(weights[i]*x[v] for i,v in enumerate(sides[nm])))
    slack=[]
    for k,(w,L,nm) in enumerate(WL):
        q0=m.NewBoolVar(f'q0_{k}');q1=m.NewBoolVar(f'q1_{k}');cnt=sum(x[i] for i in L)
        m.Add(cnt<=len(L)*(1-q0));m.Add(cnt>=1-q0)
        m.Add(cnt<=1+(1-q1));m.Add(cnt>=2*(1-q1));m.Add(q0<=q1)
        slack += [(w,q0),(w,q1)]
    m.Add(sum((cov[i]-DEN)*x[i] for i in range(len(P)))+sum(w*q for w,q in slack)==BUD)
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=limit;s.parameters.num_search_workers=4;s.parameters.log_search_progress=True
    t=time.time();st=s.Solve(m);rec={'solver':'cpsat','status':s.StatusName(st),'seconds':time.time()-t,'branches':s.NumBranches(),'conflicts':s.NumConflicts()}
    if st in (cp_model.FEASIBLE,cp_model.OPTIMAL):rec['points']=[P[i] for i in range(len(P)) if s.Value(x[i])]
    print(json.dumps(rec),flush=True);return 2 if st in (cp_model.FEASIBLE,cp_model.OPTIMAL) else (0 if st==cp_model.INFEASIBLE else 124)

def solve_highs(limit):
    import numpy as np
    from scipy.optimize import milp,Bounds,LinearConstraint
    from scipy.sparse import lil_matrix
    P,lines,WL,cov,sides,DEN,BUD=data();nx=len(P);nq=2*len(WL);n=nx+nq
    rows=[];lo=[];hi=[]
    def add(co,l=-np.inf,h=np.inf):rows.append(co);lo.append(l);hi.append(h)
    for L in lines:add({i:1 for i in L},h=2)
    add({i:1 for i in range(nx)},34,34)
    for ids in sides.values():add({i:1 for i in ids},2,2)
    weights=[1<<i for i in range(11)];tc={v:weights[i] for i,v in enumerate(sides['top'])}
    for nm in ('left','rb','rr'):
        co=dict(tc)
        for i,v in enumerate(sides[nm]):co[v]=co.get(v,0)-weights[i]
        add(co,h=0)
    for k,(w,L,nm) in enumerate(WL):
        q0=nx+2*k;q1=q0+1
        co={i:1 for i in L};co[q0]=len(L);add(co,h=len(L))
        co={i:1 for i in L};co[q0]=1;add(co,l=1)
        co={i:1 for i in L};co[q1]=1;add(co,h=2)
        co={i:1 for i in L};co[q1]=2;add(co,l=2)
        add({q0:1,q1:-1},h=0)
    co={i:cov[i]-DEN for i in range(nx)}
    for k,(w,L,nm) in enumerate(WL):co[nx+2*k]=w;co[nx+2*k+1]=w
    add(co,BUD,BUD)
    M=lil_matrix((len(rows),n),dtype=float)
    for r,co in enumerate(rows):
        for j,v in co.items():M[r,j]=v
    M=M.tocsr();t=time.time();res=milp(np.zeros(n),integrality=np.ones(n),bounds=Bounds(np.zeros(n),np.ones(n)),constraints=LinearConstraint(M,np.array(lo),np.array(hi)),options={'time_limit':limit,'mip_rel_gap':0.0,'presolve':True,'disp':True})
    rec={'solver':'highs','status_code':int(res.status),'message':res.message,'seconds':time.time()-t}
    if res.x is not None and res.status==0:rec['points']=[P[i] for i in range(nx) if res.x[i]>.5]
    print(json.dumps(rec),flush=True);return 2 if rec.get('points') else (0 if res.status==2 else 124)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('solver',choices=['cpsat','highs']);ap.add_argument('--limit',type=float,default=18000);a=ap.parse_args()
    raise SystemExit(solve_cpsat(a.limit) if a.solver=='cpsat' else solve_highs(a.limit))
