#!/usr/bin/env python3
"""Exact certificate-oriented CNF for the extremal short-transition branch s=84.

This is a complete decision encoding for the branch, not a relaxation. A SAT
model is exported in the standard reduced-edge witness format. An UNSAT result
is acceptable only with a retained trace checked against the exact CNF.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from itertools import combinations
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from model import make_root_model


def key(u,v):return (u,v) if u<v else (v,u)
def sha256(path):
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for block in iter(lambda:f.read(1<<20),b""):h.update(block)
    return h.hexdigest()

def build(symmetry=True):
    rm=make_root_model(14);labels=rm.labels;n=rm.m
    def inter(u,v):return rm.intersection(u,v)
    def yval(u,v):
        return sum(1 for a in labels[u] for b in labels[v] if (a^1)==b)
    def cell(u):
        a,b=labels[u];return tuple(sorted((a//2,b//2)))
    cells=sorted({cell(u) for u in range(n)})
    members={c:[u for u in range(n) if cell(u)==c] for c in cells}
    blocks=[(a,b) for a,b in combinations(cells,2) if set(a).isdisjoint(b)]
    C0={key(u,v) for u,v in combinations(range(n),2)
        if inter(u,v)==1 and yval(u,v)==1}
    Dposs={key(u,v) for a,b in blocks for u in members[a] for v in members[b]}
    assert len(cells)==21 and len(blocks)==105
    assert len(C0)==84 and len(Dposs)==1680

    pool=IDPool();cnf=CNF()
    d={p:pool.id(("d",)+p) for p in sorted(Dposs)}
    def extend(enc):cnf.extend(enc.clauses)

    for a,b in blocks:
        for u in members[a]:
            extend(CardEnc.equals([d[key(u,v)] for v in members[b]],1,
                                  vpool=pool,encoding=EncType.seqcounter))
        for v in members[b]:
            extend(CardEnc.equals([d[key(u,v)] for u in members[a]],1,
                                  vpool=pool,encoding=EncType.seqcounter))

    def edge(u,v):
        if u==v:return 0
        p=key(u,v)
        if p in C0:return 1
        return d.get(p,0)

    products=0
    for u,v in combinations(range(n),2):
        terms=[];constant=0
        for w in range(n):
            if w in (u,v):continue
            a=edge(u,w);b=edge(v,w)
            if a==0 or b==0:continue
            if a==1 and b==1:constant+=1
            elif a==1:terms.append(b)
            elif b==1:terms.append(a)
            else:
                z=pool.id(("and",u,v,w));products+=1;terms.append(z)
                cnf.append([-z,a]);cnf.append([-z,b]);cnf.append([z,-a,-b])
        uv=edge(u,v);bound=2-inter(u,v)-constant
        if uv==1:
            bound-=1
            extend(CardEnc.equals(terms,bound,vpool=pool,
                                  encoding=EncType.seqcounter))
        elif uv==0:
            extend(CardEnc.equals(terms,bound,vpool=pool,
                                  encoding=EncType.seqcounter))
        else:
            extend(CardEnc.equals(terms+[uv],bound,vpool=pool,
                                  encoding=EncType.seqcounter))

    if symmetry:
        index=rm.label_index
        triangle=[index[(0,2)],index[(4,6)],index[(8,10)]]
        for u,v in combinations(triangle,2):cnf.append([d[key(u,v)]])

    cnf.nv=max(cnf.nv,pool.top)
    metadata={"branch":"s=84","symmetry":symmetry,"fixed_C_edges":len(C0),
      "D_edge_variables":len(d),"cross_blocks":len(blocks),
      "product_auxiliaries":products,"variables":cnf.nv,
      "clauses":len(cnf.clauses)}
    return rm,cnf,C0,d,metadata

def run(args):
    rm,cnf,C0,d,metadata=build(not args.no_symmetry)
    cnf.to_file(args.cnf);metadata["cnf_sha256"]=sha256(args.cnf)
    metadata["cnf_path"]=args.cnf
    print("RESULT_JSON "+json.dumps({"event":"emitted",**metadata},sort_keys=True),flush=True)
    if args.emit_only:return
    with Solver(name=args.solver,bootstrap_with=cnf.clauses,
                with_proof=bool(args.proof)) as solver:
        started=time.time();sat=solver.solve()
        result={"solver":args.solver,"status":"SAT" if sat else "UNSAT",
                "seconds":time.time()-started}
        if sat:
            positive={x for x in solver.get_model() if x>0}
            edges=sorted(C0|{p for p,var in d.items() if var in positive})
            if args.witness:
                with open(args.witness,"w") as f:
                    json.dump({"k":14,"edges":[list(e) for e in edges]},f,
                              indent=2,sort_keys=True)
                result["witness"]=args.witness
                result["witness_sha256"]=sha256(args.witness)
        elif args.proof:
            proof=solver.get_proof()
            if not proof:raise RuntimeError("UNSAT returned without a proof trace")
            with open(args.proof,"w") as f:f.write("\n".join(proof)+"\n")
            result["proof"]=args.proof;result["proof_lines"]=len(proof)
            result["proof_sha256"]=sha256(args.proof)
        print("RESULT_JSON "+json.dumps(result,sort_keys=True),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--cnf",required=True)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--proof")
    ap.add_argument("--witness")
    ap.add_argument("--emit-only",action="store_true")
    ap.add_argument("--no-symmetry",action="store_true")
    run(ap.parse_args())
if __name__=="__main__":main()
