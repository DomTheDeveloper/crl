#!/usr/bin/env python3
"""Exact SAT model for a fixed transition-system orbit.

A representative lists only defective base-point transition matchings. All
unlisted rows use the six fixed matching edges. The resulting transition
2-factor C is fixed. The remaining disjoint-label edges are Boolean variables.
Every root-incidence and common-neighbor equation is encoded exactly.

Typed singleton sentinels are deliberately used for fixed Boolean constants.
Integer 1 is a valid DIMACS variable and must never represent fixed truth.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from collections import Counter
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

LABELS = [(a,b) for a,b in combinations(range(14),2) if b != (a ^ 1)]
INDEX = {e:i for i,e in enumerate(LABELS)}
N = 84
TRUE = object()
FALSE = object()

def key(u:int,v:int)->tuple[int,int]: return (u,v) if u<v else (v,u)
def intersection(u:int,v:int)->int: return len(set(LABELS[u]) & set(LABELS[v]))
def cell(u:int)->tuple[int,int]: return tuple(sorted((LABELS[u][0]//2,LABELS[u][1]//2)))
CELLS = sorted({cell(u) for u in range(N)})
MEMBERS = {c:[u for u in range(N) if cell(u)==c] for c in CELLS}
INCIDENT = [[u for u,e in enumerate(LABELS) if i in e] for i in range(14)]

def normalize_state(raw):
    return tuple(sorted((int(r), tuple(sorted(tuple(sorted(map(int,e))) for e in mt))) for r,mt in raw))

def transition_edges(state) -> set[tuple[int,int]]:
    specified = dict(normalize_state(state)); edges=set()
    for r in range(14):
        matching = specified.get(r, tuple((2*g,2*g+1) for g in range(7) if g != r//2))
        assert len(matching)==6
        used=[]
        for x,y in matching:
            assert x!=y and x//2 != r//2 and y//2 != r//2 and (x^1)!=y
            used += [x,y]
            u=INDEX[tuple(sorted((r,x)))]; v=INDEX[tuple(sorted((r,y)))]
            edges.add(key(u,v))
        assert len(set(used))==12
    assert len(edges)==84
    deg=Counter()
    for u,v in edges: deg[u]+=1;deg[v]+=1
    assert len(deg)==84 and set(deg.values())=={2}
    return edges

def build(state):
    C=transition_edges(state)
    intact=[]; affected=[]
    for c in CELLS:
        vs=MEMBERS[c]
        ce=[key(u,v) for u,v in combinations(vs,2) if key(u,v) in C]
        deg=Counter()
        for u,v in ce:deg[u]+=1;deg[v]+=1
        (intact if len(ce)==4 and all(deg[u]==2 for u in vs) else affected).append(c)
    intact=set(intact); affected=set(affected)
    pool=IDPool(); cnf=CNF(); d={}
    for u,v in combinations(range(N),2):
        if intersection(u,v): continue
        cu,cv=cell(u),cell(v)
        if set(cu).isdisjoint(cv) or (cu in affected and cv in affected):
            d[(u,v)] = pool.id(('d',u,v))
    def E(u,v):
        if u==v:return FALSE
        p=key(u,v)
        if p in C:return TRUE
        return d.get(p,FALSE)
    def exact(lits,bound):
        if bound<0 or bound>len(lits): cnf.append([])
        else: cnf.extend(CardEnc.equals(lits,bound,vpool=pool,encoding=EncType.seqcounter).clauses)
    for u in range(N):
        a,b=LABELS[u]
        for i in range(14):
            rhs=2-int(i in (a,b))-int((i^1) in (a,b)); lits=[]; const=0
            for q in INCIDENT[i]:
                if q==u: continue
                x=E(u,q)
                if x is TRUE: const+=1
                elif x is not FALSE: lits.append(x)
            exact(lits,rhs-const)
    for c in sorted(intact):
        vs=MEMBERS[c]
        for u in range(N):
            if u in vs:continue
            rhs=1 if set(cell(u)).isdisjoint(c) else 0; lits=[]; const=0
            for v in vs:
                x=E(u,v)
                if x is TRUE:const+=1
                elif x is not FALSE:lits.append(x)
            exact(lits,rhs-const)
    products=0
    for u,v in combinations(range(N),2):
        terms=[]; const=0
        for w in range(N):
            if w in (u,v):continue
            a,b=E(u,w),E(v,w)
            if a is FALSE or b is FALSE:continue
            if a is TRUE and b is TRUE:const+=1
            elif a is TRUE:terms.append(b)
            elif b is TRUE:terms.append(a)
            else:
                z=pool.id(('and',u,v,w));products+=1;terms.append(z)
                cnf.append([-z,a]);cnf.append([-z,b]);cnf.append([z,-a,-b])
        uv=E(u,v); rhs=2-intersection(u,v)-const
        if uv is TRUE: rhs-=1; arr=terms
        elif uv is FALSE: arr=terms
        else: arr=terms+[uv]
        exact(arr,rhs)
    cnf.nv=max(cnf.nv,pool.top)
    return cnf,{'intact_cells':len(intact),'affected_cells':len(affected),
                'D_variables':len(d),'product_auxiliaries':products,
                'variables':cnf.nv,'clauses':len(cnf.clauses)}

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):h.update(block)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--representatives',required=True)
    ap.add_argument('--orbit',type=int,required=True)
    ap.add_argument('--cnf')
    ap.add_argument('--solver',default='cadical195')
    ap.add_argument('--proof')
    ap.add_argument('--witness')
    ap.add_argument('--emit-only',action='store_true')
    args=ap.parse_args()
    reps=json.loads(Path(args.representatives).read_text())
    state=normalize_state(reps[args.orbit])
    started=time.time();cnf,meta=build(state);meta['build_seconds']=time.time()-started
    if args.cnf:
        cnf.to_file(args.cnf);meta['cnf_sha256']=sha256(args.cnf)
    if args.emit_only:
        print('RESULT_JSON '+json.dumps({'orbit':args.orbit,'status':'EMITTED',**meta},sort_keys=True));return
    if any(len(c)==0 for c in cnf.clauses):
        result={'orbit':args.orbit,'status':'UNSAT_ROOT','solve_seconds':0.0,**meta}
        if args.proof: Path(args.proof).write_text('0\n')
        print('RESULT_JSON '+json.dumps(result,sort_keys=True));return
    with Solver(name=args.solver,bootstrap_with=cnf.clauses,with_proof=bool(args.proof)) as solver:
        t=time.time();sat=solver.solve();elapsed=time.time()-t
        result={'orbit':args.orbit,'status':'SAT' if sat else 'UNSAT','solve_seconds':elapsed,**meta}
        if sat and args.witness:
            Path(args.witness).write_text(json.dumps({'model':solver.get_model()},indent=2)+'\n')
            result['model_sha256']=sha256(args.witness)
        if not sat and args.proof:
            proof=solver.get_proof() or ['0'];Path(args.proof).write_text('\n'.join(proof)+'\n')
            result['proof_lines']=len(proof);result['proof_sha256']=sha256(args.proof)
    print('RESULT_JSON '+json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
