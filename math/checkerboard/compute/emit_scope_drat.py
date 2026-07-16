#!/usr/bin/env python3
"""Emit one exact n=22 boundary-scope CNF and a solver proof.

The boundary masks are added as ordinary unit clauses before solving, so the
resulting proof is checked directly against the emitted DIMACS formula without
special assumption semantics.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver

import n22_data as d
import n22_exact_core as core


def mask_units(side: str, mask: int) -> list[int]:
    return [d.BIDS[side][i] for i in range(11) if (mask >> i) & 1]


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


ap = argparse.ArgumentParser()
ap.add_argument('--top', type=int, required=True)
ap.add_argument('--left', type=int)
ap.add_argument('--rb', type=int)
ap.add_argument('--rr', type=int)
ap.add_argument('--solver', default='cadical195')
ap.add_argument('--out', required=True)
a = ap.parse_args()

cnf, info = core.build_double(a.top)
units: list[int] = []
for side, mask in (('left', a.left), ('rb', a.rb), ('rr', a.rr)):
    if mask is not None:
        units.extend(mask_units(side, mask))
for lit in units:
    cnf.append([lit])
cnf.nv = max(cnf.nv, max((abs(x) for x in units), default=0))

prefix = Path(a.out)
prefix.parent.mkdir(parents=True, exist_ok=True)
cnf_path = Path(str(prefix) + '.cnf')
proof_path = Path(str(prefix) + '.drat')
meta_path = Path(str(prefix) + '.json')
cnf.to_file(str(cnf_path))

t0 = time.time()
with Solver(name=a.solver, with_proof=True, bootstrap_with=cnf.clauses) as solver:
    result = solver.solve()
    if result:
        model = {x for x in solver.get_model() if x > 0}
        points = [d.P[i - 1] for i in range(1, len(d.P) + 1) if i in model]
        meta = {
            'status': 'SAT',
            'solver': a.solver,
            'seconds': time.time() - t0,
            'top': a.top,
            'left': a.left,
            'rb': a.rb,
            'rr': a.rr,
            'points': points,
        }
        meta_path.write_text(json.dumps(meta, indent=2) + '\n')
        print(json.dumps(meta))
        raise SystemExit(2)
    proof = solver.get_proof()

if not proof or proof[-1].strip() != '0':
    raise RuntimeError('solver returned UNSAT without a terminating empty clause')
proof_path.write_text('\n'.join(proof) + '\n')
meta = {
    'status': 'UNSAT',
    'solver': a.solver,
    'seconds': time.time() - t0,
    'top': a.top,
    'left': a.left,
    'rb': a.rb,
    'rr': a.rr,
    'units': units,
    'variables': cnf.nv,
    'clauses': len(cnf.clauses),
    'proof_lines': len(proof),
    'cnf': cnf_path.name,
    'cnf_sha256': digest(cnf_path),
    'proof': proof_path.name,
    'proof_sha256': digest(proof_path),
    'encoding': info,
}
meta_path.write_text(json.dumps(meta, indent=2) + '\n')
print(json.dumps(meta))
