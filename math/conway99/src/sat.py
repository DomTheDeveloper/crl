#!/usr/bin/env python3
"""Certificate-oriented CNF encoding of the exact reduced equations."""
from __future__ import annotations
import argparse, json, time
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from model import make_root_model, SEED_BRANCHES

def edge_key(a, b): return (a, b) if a < b else (b, a)

def build_cnf(k: int, mode: str = "full", seed: int = 0, branch: str | None = None):
    rm = make_root_model(k)
    m = rm.m
    pool = IDPool()
    cnf = CNF()
    e = {(u, v): pool.id(("e", u, v)) for u in range(m) for v in range(u + 1, m)}
    def E(u, v):
        if u == v: return None
        return e[edge_key(u, v)]
    def equals(lits, bound):
        enc = CardEnc.equals(lits=lits, bound=bound, vpool=pool, encoding=EncType.seqcounter)
        cnf.extend(enc.clauses)

    for u in range(m):
        for i in range(k):
            equals([E(u, q) for q in rm.incidence[i] if q != u], rm.rhs_incidence(u, i))

    if branch:
        if k != 14 or rm.labels[seed] != (0, 2):
            raise ValueError("seed branches require k=14 and seed label (0,2)")
        q0, q2 = SEED_BRANCHES[branch]
        cnf.append([E(seed, rm.label_index[tuple(sorted(q0))])])
        cnf.append([E(seed, rm.label_index[tuple(sorted(q2))])])

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
            a, b = E(u, w), E(v, w)
            z = pool.id(("and", u, v, w))
            products.append(z)
            cnf.append([-z, a])
            cnf.append([-z, b])
            cnf.append([z, -a, -b])
        equals(products + [E(u, v)], 2 - rm.intersection(u, v))
    cnf.nv = max(cnf.nv, pool.top)
    return rm, cnf, e, pool

def solve(k: int, mode: str, solver_name: str, branch: str | None,
          cnf_path: str | None, witness_path: str | None, proof_path: str | None,
          no_solve: bool = False):
    rm, cnf, e, _ = build_cnf(k, mode, 0, branch)
    if cnf_path:
        cnf.to_file(cnf_path)
    base = {"solver": solver_name, "k": k, "v": rm.v, "mode": mode, "branch": branch,
            "vars": cnf.nv, "clauses": len(cnf.clauses), "cnf": cnf_path}
    if no_solve:
        base["status"] = "EMITTED"
        print("RESULT_JSON " + json.dumps(base, sort_keys=True))
        return base
    t = time.time()
    with Solver(name=solver_name, bootstrap_with=cnf.clauses, with_proof=bool(proof_path)) as solver:
        sat = solver.solve()
        result = dict(base)
        result.update(status="SAT" if sat else "UNSAT", seconds=time.time() - t)
        if sat:
            positive = {x for x in solver.get_model() if x > 0}
            edges = [list(uv) for uv, var in e.items() if var in positive]
            result["edge_count"] = len(edges)
            if witness_path:
                with open(witness_path, "w") as f:
                    json.dump({"k": k, "edges": edges}, f, indent=2, sort_keys=True)
                result["witness"] = witness_path
        elif proof_path:
            proof = solver.get_proof()
            if not proof:
                raise RuntimeError(f"solver {solver_name} returned UNSAT without a proof trace")
            with open(proof_path, "w") as f:
                f.write("\n".join(proof) + "\n")
            result["proof"] = proof_path
            result["proof_lines"] = len(proof)
    print("RESULT_JSON " + json.dumps(result, sort_keys=True))
    return result

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=14)
    ap.add_argument("--mode", choices=["full", "root", "incidence"], default="full")
    ap.add_argument("--solver", default="cadical195")
    ap.add_argument("--branch", choices=sorted(SEED_BRANCHES))
    ap.add_argument("--cnf", help="write exact DIMACS CNF")
    ap.add_argument("--witness", help="write SAT reduced-edge witness")
    ap.add_argument("--proof", help="write solver proof trace on UNSAT")
    ap.add_argument("--no-solve", action="store_true", help="emit CNF without invoking a solver")
    a = ap.parse_args()
    if a.no_solve and not a.cnf:
        ap.error("--no-solve requires --cnf")
    solve(a.k, a.mode, a.solver, a.branch, a.cnf, a.witness, a.proof, a.no_solve)

if __name__ == "__main__":
    main()
