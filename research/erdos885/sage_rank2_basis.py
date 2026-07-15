#!/usr/bin/env python3
"""Export the certified rank-2 basis on the original triple quotient model.

Every Sage API step is recorded independently so a representation mismatch cannot
silently discard the rank certificate or the generators.
"""
from __future__ import annotations

import json
import traceback
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

A, B, C = map(Integer, [2578, 5553, 5922])
P = B*B - A*A
Q = C*C - A*A
E0 = EllipticCurve(QQ, [0, 4*(P+Q), 0, 16*P*Q, 0])
E = E0.global_minimal_model()


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
    "known_columns": [-5585184, 0, 35994816],
    "inverse_map": "u=(16*p*q-X^2)/(4*Y), t=u^2-a^2",
}

try:
    proof.all(True)
    out["rank_proved"] = int(E.rank(proof=True))
except Exception as exc:
    out["rank_error"] = f"{type(exc).__name__}: {exc}"
    out["rank_traceback"] = traceback.format_exc()

try:
    # This call already returned two generators with gens_certain=True in the
    # independent triple-rank job.  Use the same supported Sage interface here.
    proof.all(False)
    gens = E.gens(proof=False)
    out["gens_certain"] = bool(E.gens_certain())
    out["generators_minimal"] = [pj(G) for G in gens]
except Exception as exc:
    gens = []
    out["gens_error"] = f"{type(exc).__name__}: {exc}"
    out["gens_traceback"] = traceback.format_exc()
finally:
    proof.all(True)

iso = None
try:
    iso = E.isomorphism_to(E0)
    out["isomorphism_method"] = "E.isomorphism_to(E0)"
except Exception as exc1:
    out["isomorphism_to_error"] = f"{type(exc1).__name__}: {exc1}"
    try:
        candidates = E.isomorphisms(E0)
        iso = candidates[0]
        out["isomorphism_method"] = "E.isomorphisms(E0)[0]"
        out["isomorphism_count"] = len(candidates)
    except Exception as exc2:
        out["isomorphisms_error"] = f"{type(exc2).__name__}: {exc2}"
        out["isomorphism_traceback"] = traceback.format_exc()

if iso is not None and gens:
    try:
        out["generators_input"] = [pj(iso(G)) for G in gens]
    except Exception as exc:
        out["generator_map_error"] = f"{type(exc).__name__}: {exc}"
        out["generator_map_traceback"] = traceback.format_exc()

try:
    torsion_points = E.torsion_points()
    out["torsion_order"] = len(torsion_points)
    out["torsion_minimal"] = [pj(T) for T in torsion_points]
    if iso is not None:
        out["torsion_input"] = [pj(iso(T)) for T in torsion_points]
except Exception as exc:
    out["torsion_error"] = f"{type(exc).__name__}: {exc}"
    out["torsion_traceback"] = traceback.format_exc()

Path("results").mkdir(exist_ok=True)
Path("results/rank2_basis.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
print(json.dumps(out, sort_keys=True))
