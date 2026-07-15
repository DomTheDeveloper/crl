#!/usr/bin/env python3
"""Export the certified rank-2 basis on the original triple quotient model."""
from __future__ import annotations

import json
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

A, B, C = map(Integer, [2578, 5553, 5922])
P = B*B - A*A
Q = C*C - A*A
E0 = EllipticCurve(QQ, [0, 4*(P+Q), 0, 16*P*Q, 0])
E = E0.global_minimal_model()

proof.all(True)
rank = E.rank(proof=True)
gens = E.gens(proof=True)
if rank != 2 or len(gens) != 2 or not E.gens_certain():
    raise RuntimeError(f"expected certified rank-2 basis, got rank={rank}, gens={len(gens)}, certain={E.gens_certain()}")

iso = E.isomorphism_to(E0)
torsion = E.torsion_subgroup()
torsion_points = list(torsion)


def pj(Pt):
    if Pt.is_zero():
        return ["0"]
    return [str(Pt[0]), str(Pt[1]), str(Pt[2])]

out = {
    "rows": [int(A), int(B), int(C)],
    "remaining_rows": [2422, 3222, 8678],
    "p": str(P),
    "q": str(Q),
    "input_ainvs": [str(x) for x in E0.a_invariants()],
    "minimal_ainvs": [str(x) for x in E.a_invariants()],
    "rank_proved": int(rank),
    "gens_certain": bool(E.gens_certain()),
    "generators_minimal": [pj(G) for G in gens],
    "generators_input": [pj(iso(G)) for G in gens],
    "torsion_order": int(torsion.order()),
    "torsion_minimal": [pj(T) for T in torsion_points],
    "torsion_input": [pj(iso(T)) for T in torsion_points],
    "known_columns": [-5585184, 0, 35994816],
    "inverse_map": "u=(16*p*q-X^2)/(4*Y), t=u^2-a^2",
}
Path("results").mkdir(exist_ok=True)
Path("results/rank2_basis.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
print(json.dumps(out, sort_keys=True))
