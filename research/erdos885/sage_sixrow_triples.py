#!/usr/bin/env python3
"""Certify elliptic ranks for the 20 triple projections of a six-row fiber.

For rows a,b,c and a prospective column t, write
  a^2+t = A^2, b^2+t = B^2, c^2+t = C^2.
The standard elliptic quotient is
  Y^2 = X (X + 4p) (X + 4q),
where p=b^2-a^2 and q=c^2-a^2.

Low-rank projections are the best entry points for a Mordell--Weil sieve
against the remaining three rows.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

ROWS = [2422, 2578, 3222, 5553, 5922, 8678]
KNOWN_COLUMNS = [-5585184, 0, 35994816]
TRIPLES = list(itertools.combinations(range(6), 3))


def point_json(P):
    if P.is_zero():
        return ["0"]
    return [str(P[0]), str(P[1]), str(P[2])]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--triple", type=int, required=True, choices=range(20))
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    indices = TRIPLES[args.triple]
    a, b, c = [Integer(ROWS[i]) for i in indices]
    p = b*b - a*a
    q = c*c - a*a
    ainvs = [Integer(0), 4*(p+q), Integer(0), 16*p*q, Integer(0)]
    E0 = EllipticCurve(QQ, ainvs)
    E = E0.global_minimal_model()

    result = {
        "triple_index": args.triple,
        "row_indices": list(indices),
        "rows": [int(a), int(b), int(c)],
        "p": str(p),
        "q": str(q),
        "input_ainvs": [str(x) for x in E0.a_invariants()],
        "minimal_ainvs": [str(x) for x in E.a_invariants()],
        "discriminant": str(E.discriminant()),
        "known_columns": KNOWN_COLUMNS,
    }

    started = time.time()
    try:
        proof.all(False)
        gens = E.gens(proof=False)
        result["gens_heuristic"] = [point_json(P) for P in gens]
        result["rank_lower_bound_from_gens"] = len(gens)
        result["gens_certain"] = bool(E.gens_certain())
        result["rank_heuristic"] = int(E.rank(proof=False))
    except Exception as exc:
        result["heuristic_error"] = f"{type(exc).__name__}: {exc}"

    try:
        proof.all(True)
        result["rank_proved"] = int(E.rank(proof=True))
        result["rank_proved_success"] = True
    except Exception as exc:
        result["rank_proved_success"] = False
        result["rank_proved_error"] = f"{type(exc).__name__}: {exc}"
    finally:
        proof.all(True)

    result["torsion_order"] = str(E.torsion_order())
    try:
        result["root_number"] = str(E.root_number())
    except Exception as exc:
        result["root_number_error"] = f"{type(exc).__name__}: {exc}"
    result["elapsed_seconds"] = round(time.time() - started, 3)

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
