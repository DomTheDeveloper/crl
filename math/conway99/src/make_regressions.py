#!/usr/bin/env python3
"""Generate and independently verify small exact regression certificates."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
import ortools, pysat
from pysat.solvers import Solver
from cpsat import solve as cpsat_solve
from sat import build_cnf, solve as sat_solve
from model import make_root_model
from verify import verify_reduced
from verify_matrix import verify_matrix
from rup_check import check as check_rup

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="certificates")
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)

    cp_w = out / "paley9_cpsat.json"
    sat_w = out / "paley9_sat.json"
    cpsat_solve(4, "full", 10, 1, None, str(cp_w), False)
    sat_solve(4, "full", "cadical195", None, None, str(sat_w), None, False)

    rm = make_root_model(4)
    for witness in (cp_w, sat_w):
        d = json.loads(witness.read_text())
        edges = [tuple(e) for e in d["edges"]]
        verify_reduced(rm, edges)
        verify_matrix(4, edges)

    rm, cnf, edge_vars, _ = build_cnf(4, "full")
    for v in range(1, rm.m):
        cnf.append([-edge_vars[(0, v)]])
    cnf_path = out / "paley9_impossible_branch.cnf"
    proof_path = out / "paley9_impossible_branch.drup"
    cnf.to_file(str(cnf_path))
    with Solver(name="cadical195", bootstrap_with=cnf.clauses, with_proof=True) as solver:
        assert solver.solve() is False
        proof = solver.get_proof()
        assert proof
        proof_path.write_text("\n".join(proof) + "\n")
    rup_result = check_rup(str(cnf_path), str(proof_path))

    files = [cp_w, sat_w, cnf_path, proof_path]
    report = {
        "PASS": True,
        "ortools_version": ortools.__version__,
        "pysat_version": pysat.__version__,
        "paley9": {"k": 4, "v": 9, "verified_by": ["combinatorial", "integer-matrix"]},
        "unsat_regression": rup_result,
        "sha256": {p.name: sha(p) for p in files},
    }
    (out / "regression_report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
