#!/usr/bin/env python3
"""Exact certificate-oriented CNF for the extremal overlap branch ``s = 84``.

This is a complete decision encoding for the branch, not a relaxation. Fixed
Boolean constants are represented by typed singleton objects: DIMACS variable
``1`` is a genuine edge variable and is never confused with fixed truth.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

LABELS=[(a,b) for a,b in combinations(range(14),2) if b!=(a^1)]
INDEX={e:i for i,e in enumerate(LABELS)}
N=84
TRUE=object(); FALSE=object()

def key(u,v): return (u,v) if u<v else (v,u)
def intersection(u,v): return len(set(LABELS[u])&set(LABELS[v]))
def yval(u,v): return sum(1 for a in LABELS[u] for b in LABELS[v] if (a^1)==b)
def cell(u): return tuple(sorted((LABELS[u][0]//2,LABELS[u][1]//2)))
CELLS=sorted({cell(u) for u in range(N)})
MEMBERS={c:[u for u in range(N) if cell(u)==c] for c in CELLS}
C0={key(u,v) for u,v in combinations(range(N),2) if intersection(u,v)==1 and yval(u,v)==1}
BLOCKS=[(a,b) for a,b in combinations(CELLS,2) if set(a).isdisjoint(b)]
DPOSS={key(u,v) for a,b in BLOCKS for u in MEMBERS[a] for v in MEMBERS[b]}
assert len(CELLS)==21 and len(BLOCKS)==105 and len(C0)==84 and len(DPOSS)==1680

def build(symmetry=True):
    pool=IDPool(); cnf=CNF(); d={p:pool.id(('d',)+p) for p in sorted(DPOSS)}
    def exact(lits,bound):
        if bound<0 or bound>len(lits): cnf.append([])
        else: cnf.extend(CardEnc.equals(lits,bound,vpool=pool,encoding=EncType.seqcounter).clauses)
    for a,b in BLOCKS:
        for u in MEMBERS[a]: exact([d[key(u,v)] for v in MEMBERS[b]],1)
        for v in MEMBERS[b]: exact([d[key(u,v)] for u in MEMBERS[a]],1)
    def edge(u,v):
        if u==v: return FALSE
        p=key(u,v)
        if p in C0: return TRUE
        return d.get(p,FALSE)
    products=0
    for u,v in combinations(range(N),2):
        terms=[]; const=0
        for w in range(N):
            if w in (u,v): continue
            a,b=edge(u,w),edge(v,w)
            if a is FALSE or b is FALSE: continue
            if a is TRUE and b is TRUE: const+=1
            elif a is TRUE: terms.append(b)
            elif b is TRUE: terms.append(a)
            else:
                z=pool.id(('and',u,v,w)); products+=1; terms.append(z)
                cnf.append([-z,a]); cnf.append([-z,b]); cnf.append([z,-a,-b])
        uv=edge(u,v); rhs=2-intersection(u,v)-const
        if uv is TRUE: exact(terms,rhs-1)
        elif uv is FALSE: exact(terms,rhs)
        else: exact(terms+[uv],rhs)
    if symmetry:
        triangle=[INDEX[(0,2)],INDEX[(4,6)],INDEX[(8,10)]]
        for u,v in combinations(triangle,2): cnf.append([d[key(u,v)]])
    cnf.nv=max(cnf.nv,pool.top)
    return cnf,d,products

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for block in iter(lambda:f.read(1<<20),b''): h.update(block)
    return h.hexdigest()

def run(args):
    started=time.time(); cnf,d,products=build(not args.no_symmetry)
    meta={'branch':'s=84','symmetry':not args.no_symmetry,'fixed_C_edges':len(C0),
          'D_edge_variables':len(d),'cross_blocks':len(BLOCKS),
          'product_auxiliaries':products,'variables':cnf.nv,
          'clauses':len(cnf.clauses),'build_seconds':time.time()-started}
    if args.cnf:
        cnf.to_file(args.cnf); meta['cnf']=args.cnf; meta['cnf_sha256']=sha256(args.cnf)
    print('RESULT_JSON '+json.dumps({'event':'emitted',**meta},sort_keys=True),flush=True)
    if args.emit_only: return
    if any(len(c)==0 for c in cnf.clauses):
        result={'status':'UNSAT_ROOT','solver':None,'seconds':0.0}
        if args.proof: Path(args.proof).write_text('0\n'); result['proof_sha256']=sha256(args.proof)
        print('RESULT_JSON '+json.dumps(result,sort_keys=True)); return
    with Solver(name=args.solver,bootstrap_with=cnf.clauses,with_proof=bool(args.proof)) as solver:
        t=time.time(); sat=solver.solve()
        result={'solver':args.solver,'status':'SAT' if sat else 'UNSAT','seconds':time.time()-t}
        if sat:
            positive={x for x in solver.get_model() if x>0}
            edges=sorted(C0|{p for p,var in d.items() if var in positive})
            if args.witness:
                Path(args.witness).write_text(json.dumps({'k':14,'edges':[list(e) for e in edges]},indent=2,sort_keys=True)+'\n')
                result['witness']=args.witness; result['witness_sha256']=sha256(args.witness)
        elif args.proof:
            proof=solver.get_proof()
            if not proof: raise RuntimeError('UNSAT returned without a proof trace')
            Path(args.proof).write_text('\n'.join(proof)+'\n')
            result['proof']=args.proof; result['proof_lines']=len(proof); result['proof_sha256']=sha256(args.proof)
    print('RESULT_JSON '+json.dumps(result,sort_keys=True),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cnf')
    ap.add_argument('--solver',default='cadical195')
    ap.add_argument('--proof')
    ap.add_argument('--witness')
    ap.add_argument('--emit-only',action='store_true')
    ap.add_argument('--no-symmetry',action='store_true')
    args=ap.parse_args()
    if args.emit_only and not args.cnf: ap.error('--emit-only requires --cnf')
    run(args)
if __name__=='__main__': main()
