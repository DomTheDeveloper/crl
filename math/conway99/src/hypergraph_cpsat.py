#!/usr/bin/env python3
"""Strong necessary CP-SAT relaxation using transitions and D-triangles.

A solution here is NOT a Conway graph: the omitted common-neighbor equations
must still be checked. An infeasible branch would become a mathematical
obstruction only after independent, checkable certification; CP-SAT alone does
not currently emit such a certificate.
"""
from __future__ import annotations
import argparse,json,time
from collections import defaultdict
from itertools import combinations
from ortools.sat.python import cp_model
from model import make_root_model

BRANCHES={
 "A1":((0,3),(1,2)),"A2":((0,3),(2,4)),"B2":((0,4),(2,4)),
 "B3":((0,4),(2,5)),"B4":((0,4),(2,6)),
}
def key(a,b): return (a,b) if a<b else (b,a)

def build(branch=None):
    rm=make_root_model(14); n=rm.m
    model=cp_model.CpModel()
    c={key(u,v):model.NewBoolVar(f"c_{u}_{v}")
       for u,v in combinations(range(n),2) if rm.intersection(u,v)==1}
    triples=[]; pair_to_tri=defaultdict(list); vertex_to_tri=defaultdict(list)
    for a,b,d in combinations(range(n),3):
        if len(set(rm.labels[a]+rm.labels[b]+rm.labels[d]))==6:
            z=model.NewBoolVar(f"t_{a}_{b}_{d}")
            triples.append((a,b,d,z))
            for p in ((a,b),(a,d),(b,d)): pair_to_tri[key(*p)].append(z)
            for u in (a,b,d): vertex_to_tri[u].append(z)
    assert len(c)==924 and len(triples)==35560
    for lits in pair_to_tri.values(): model.Add(sum(lits)<=1)
    for u in range(n): model.Add(sum(vertex_to_tri[u])==5)

    for u in range(n):
        for i in range(14):
            terms=[]
            for q in rm.incidence[i]:
                if q==u: continue
                p=key(u,q)
                if rm.intersection(u,q)==1: terms.append(c[p])
                else: terms.extend(pair_to_tri[p])
            model.Add(sum(terms)==rm.rhs_incidence(u,i))
    if branch:
        seed=rm.label_index[(0,2)]
        for q in BRANCHES[branch]:
            v=rm.label_index[tuple(sorted(q))]
            model.Add(c[key(seed,v)]==1)
    return rm,model,c,triples

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--branch",choices=sorted(BRANCHES))
    ap.add_argument("--seconds",type=float,default=60);ap.add_argument("--workers",type=int,default=1)
    ap.add_argument("--out")
    a=ap.parse_args();rm,model,c,triples=build(a.branch)
    solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=a.seconds
    solver.parameters.num_search_workers=a.workers;solver.parameters.random_seed=0
    t=time.time();status=solver.Solve(model)
    result={"model":"necessary transition-triangle relaxation","branch":a.branch,
      "status":solver.StatusName(status),"seconds":time.time()-t,
      "variables":len(model.Proto().variables),"constraints":len(model.Proto().constraints),
      "qualification":"SAT/FEASIBLE is only a relaxation witness; UNKNOWN is no result."}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL) and a.out:
        selected_c=[list(p) for p,v in c.items() if solver.Value(v)]
        selected_t=[list((x,y,z)) for x,y,z,v in triples if solver.Value(v)]
        with open(a.out,"w") as f: json.dump({"C_edges":selected_c,"D_triangles":selected_t},f,indent=2)
        result["relaxation_witness"]=a.out
    print("RESULT_JSON "+json.dumps(result,sort_keys=True))
if __name__=="__main__":main()
