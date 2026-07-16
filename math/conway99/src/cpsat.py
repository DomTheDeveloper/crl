#!/usr/bin/env python3
"""OR-Tools CP-SAT encoding of the exact reduced equations.

Modes:
  full       all incidence and all pair equations (complete decision model)
  root       all incidence equations and pair equations involving one seed
  incidence  only the linear incidence equations (relaxation)
"""
from __future__ import annotations
import argparse, json, time
from ortools.sat.python import cp_model
from model import make_root_model, SEED_BRANCHES

def edge_key(a, b): return (a, b) if a < b else (b, a)

def build(k: int, mode: str = "full", seed: int = 0, branch: str | None = None):
    rm = make_root_model(k)
    m = rm.m
    model = cp_model.CpModel()
    e = {(u, v): model.NewBoolVar(f"e_{u}_{v}") for u in range(m) for v in range(u + 1, m)}
    def E(u, v):
        if u == v: return 0
        return e[edge_key(u, v)]

    for u in range(m):
        for i in range(k):
            model.Add(sum(E(u, q) for q in rm.incidence[i] if q != u) == rm.rhs_incidence(u, i))

    if branch:
        if k != 14 or rm.labels[seed] != (0, 2):
            raise ValueError("seed branches require k=14 and seed label (0,2)")
        q0, q2 = SEED_BRANCHES[branch]
        model.Add(E(seed, rm.label_index[tuple(sorted(q0))]) == 1)
        model.Add(E(seed, rm.label_index[tuple(sorted(q2))]) == 1)

    if mode == "full":
        pairs = [(u, v) for u in range(m) for v in range(u + 1, m)]
    elif mode == "root":
        pairs = [edge_key(seed, v) for v in range(m) if v != seed]
    elif mode == "incidence":
        pairs = []
    else:
        raise ValueError(mode)

    for u, v in pairs:
        products = []
        for w in range(m):
            if w in (u, v):
                continue
            z = model.NewBoolVar(f"z_{u}_{v}_{w}")
            model.AddMultiplicationEquality(z, [E(u, w), E(v, w)])
            products.append(z)
        model.Add(sum(products) + E(u, v) == 2 - rm.intersection(u, v))
    return rm, model, e

def solve(k: int, mode: str, seconds: float, workers: int, branch: str | None,
          out: str | None, log: bool = False):
    rm, model, e = build(k, mode, 0, branch)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.log_search_progress = log
    solver.parameters.random_seed = 0
    t = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t
    result = {
        "solver": "OR-Tools CP-SAT", "k": k, "v": rm.v, "mode": mode, "branch": branch,
        "status": solver.StatusName(status), "seconds": elapsed,
        "conflicts": solver.NumConflicts(), "branches": solver.NumBranches(),
        "wall_time": solver.WallTime(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        edges = [list(uv) for uv, var in e.items() if solver.Value(var)]
        result["edge_count"] = len(edges)
        if out:
            with open(out, "w") as f:
                json.dump({"k": k, "edges": edges}, f, indent=2, sort_keys=True)
            result["witness"] = out
    print("RESULT_JSON " + json.dumps(result, sort_keys=True))
    return status

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=14)
    ap.add_argument("--mode", choices=["full", "root", "incidence"], default="full")
    ap.add_argument("--seconds", type=float, default=60)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--branch", choices=sorted(SEED_BRANCHES))
    ap.add_argument("--out")
    ap.add_argument("--log", action="store_true")
    a = ap.parse_args()
    solve(a.k, a.mode, a.seconds, a.workers, a.branch, a.out, a.log)

if __name__ == "__main__":
    main()
