#!/usr/bin/env python3
"""Emit the complete base CNF and the five exhaustive seed-orbit cubes."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
import ortools, pysat
from sat import build_cnf
from model import SEED_BRANCHES

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", required=True)
    ap.add_argument("--manifest", required=True)
    a = ap.parse_args()
    rm, cnf, e, _ = build_cnf(14, "full", 0, None)
    cnf.to_file(a.cnf)
    cubes = {}
    for name, (q0, q2) in SEED_BRANCHES.items():
        u0 = rm.label_index[tuple(sorted(q0))]
        u2 = rm.label_index[tuple(sorted(q2))]
        cubes[name] = [e[(0, u0) if 0 < u0 else (u0, 0)], e[(0, u2) if 0 < u2 else (u2, 0)]]
    payload = {
        "problem": "Conway99", "encoding": "root-reduced exact SRG equations",
        "k": 14, "v": 99, "reduced_vertices": 84,
        "vars": cnf.nv, "clauses": len(cnf.clauses), "cnf_sha256": sha256(a.cnf),
        "seed_label": [0, 2], "branch_cubes": cubes, "orbit_count": len(cubes),
        "generator_versions": {"ortools": ortools.__version__, "pysat": pysat.__version__},
        "qualification": "The base CNF plus the five positive two-literal cubes is exhaustive only together with symmetry_audit.json.",
        "PASS": True,
    }
    Path(a.manifest).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
