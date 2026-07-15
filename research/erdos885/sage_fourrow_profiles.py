#!/usr/bin/env python3
"""Certify the five elliptic quotient ranks for the three four-row curves
containing the unique rank-2 triple [2578, 5553, 5922].
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

BASE = [2578, 5553, 5922]
EXTRA = [2422, 3222, 8678]


def triple_curve(rows):
    a, b, c = map(Integer, rows)
    p = b*b-a*a
    q = c*c-a*a
    return EllipticCurve(QQ, [0, 4*(p+q), 0, 16*p*q, 0]).global_minimal_model()


def quartic_curve(rows):
    a, b, c, d = map(Integer, rows)
    B = 4*(b*b-a*a)
    C = 4*(c*c-a*a)
    D = 4*(d*d-a*a)
    A = B*C*D
    S1 = B+C+D
    S2 = B*C+B*D+C*D
    return EllipticCurve(QQ, [0, S2, 0, A*S1, A*A]).global_minimal_model()


proof.all(True)
out=[]
for d in EXTRA:
    rows=BASE+[d]
    triples=[]
    for inds in itertools.combinations(range(4),3):
        rr=[rows[i] for i in inds]
        E=triple_curve(rr)
        triples.append({
            "indices": list(inds),
            "rows": rr,
            "rank_proved": int(E.rank(proof=True)),
            "gens_certain": bool(E.gens_certain()),
            "minimal_ainvs": [str(x) for x in E.a_invariants()],
        })
    Q=quartic_curve(rows)
    out.append({
        "rows": rows,
        "triple_factors": triples,
        "quartic_factor": {
            "rank_proved": int(Q.rank(proof=True)),
            "gens_certain": bool(Q.gens_certain()),
            "minimal_ainvs": [str(x) for x in Q.a_invariants()],
        },
        "rank_profile": [x["rank_proved"] for x in triples]+[int(Q.rank(proof=True))],
    })
Path("results").mkdir(exist_ok=True)
Path("results/fourrow_profiles.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
print(json.dumps(out,sort_keys=True))
