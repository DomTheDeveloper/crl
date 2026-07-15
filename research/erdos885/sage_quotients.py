#!/usr/bin/env python3
"""Screen the five elliptic quotient factors of a genus-5 row-extension curve.

For a normalized 5x4 square-addition packet with columns {0,B,C,D}, a sixth
row has u=x^2 satisfying that u, u+B, u+C, and u+D are all rational squares.
The genus-5 curve has five elliptic quotient factors: four cubic products of
three branch factors and one quotient of the four-factor quartic.

This script records exact curve models and reproducible Sage/mwrank rank data.
Heuristic rank calls are explicitly marked and are not treated as proofs.
"""
from __future__ import annotations

import argparse
import json
import time
import traceback
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof


def load_packet(packet_id: int) -> dict:
    path = Path(__file__).with_name("packets.json")
    packets = json.loads(path.read_text())
    for packet in packets:
        if packet["id"] == packet_id:
            return packet
    raise ValueError(f"unknown packet id {packet_id}")


def quotient_models(columns: list[int]):
    if len(columns) != 4 or columns[0] != 0:
        raise ValueError("expected normalized columns [0,B,C,D]")
    B, C, D = map(Integer, columns[1:])

    def triple(label: str, a: Integer, b: Integer):
        # y^2 = u(u+a)(u+b)
        return label, [Integer(0), a + b, Integer(0), a * b, Integer(0)]

    models = [
        triple("u(u+B)(u+C)", B, C),
        triple("u(u+B)(u+D)", B, D),
        triple("u(u+C)(u+D)", C, D),
        (
            "(u+B)(u+C)(u+D)",
            [Integer(0), B + C + D, Integer(0), B*C + B*D + C*D, B*C*D],
        ),
    ]

    # For v^2=u(u+B)(u+C)(u+D), put A=BCD, X=A/u, Y=A*v/u^2.
    # Then Y^2=X^3+(BC+BD+CD)X^2+A(B+C+D)X+A^2.
    A = B*C*D
    models.append((
        "u(u+B)(u+C)(u+D)",
        [Integer(0), B*C + B*D + C*D, Integer(0), A*(B+C+D), A*A],
    ))
    return models


def point_json(P):
    if P.is_zero():
        return ["0"]
    return [str(P[0]), str(P[1]), str(P[2])]


def screen_curve(label: str, ainvs: list[Integer]) -> dict:
    started = time.time()
    E0 = EllipticCurve(QQ, ainvs)
    E = E0.global_minimal_model()
    out = {
        "label": label,
        "input_ainvs": [str(x) for x in E0.a_invariants()],
        "minimal_ainvs": [str(x) for x in E.a_invariants()],
        "minimal_discriminant": str(E.discriminant()),
        "j_invariant": str(E.j_invariant()),
    }

    for key, call in [
        ("torsion_order", lambda: E.torsion_order()),
        ("root_number", lambda: E.root_number()),
        ("conductor", lambda: E.conductor()),
    ]:
        try:
            out[key] = str(call())
        except Exception as exc:
            out[key + "_error"] = f"{type(exc).__name__}: {exc}"

    # Screening only: proof=False can establish a lower bound by finding
    # independent points, but its returned rank is not itself a certificate.
    try:
        proof.all(False)
        gens = E.gens(proof=False)
        out["gens_heuristic"] = [point_json(P) for P in gens]
        out["rank_lower_bound_from_gens"] = len(gens)
        out["gens_certain"] = bool(E.gens_certain())
    except Exception as exc:
        out["gens_error"] = f"{type(exc).__name__}: {exc}"
        out["gens_traceback"] = traceback.format_exc(limit=4)

    try:
        out["rank_heuristic"] = int(E.rank(proof=False))
    except Exception as exc:
        out["rank_error"] = f"{type(exc).__name__}: {exc}"

    # This may certify a rank cheaply when descent has already closed the gap.
    # Otherwise the exact exception/status is retained for a focused stage two.
    try:
        proof.all(True)
        out["rank_proved"] = int(E.rank(proof=True))
        out["rank_proved_success"] = True
    except Exception as exc:
        out["rank_proved_success"] = False
        out["rank_proved_error"] = f"{type(exc).__name__}: {exc}"
    finally:
        proof.all(True)

    out["elapsed_seconds"] = round(time.time() - started, 3)
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=int, required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    packet = load_packet(args.packet)
    result = {
        "packet_id": packet["id"],
        "rows": packet["rows"],
        "columns": packet["columns"],
        "sage_version": None,
        "quotients": [],
    }
    try:
        from sage.env import SAGE_VERSION
        result["sage_version"] = SAGE_VERSION
    except Exception:
        pass

    for label, ainvs in quotient_models(packet["columns"]):
        print(f"packet={packet['id']} quotient={label}", flush=True)
        result["quotients"].append(screen_curve(label, ainvs))

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "packet_id": packet["id"],
        "summary": [
            {
                "label": q["label"],
                "rank_lower_bound": q.get("rank_lower_bound_from_gens"),
                "rank_heuristic": q.get("rank_heuristic"),
                "rank_proved": q.get("rank_proved"),
                "gens_certain": q.get("gens_certain"),
                "elapsed_seconds": q.get("elapsed_seconds"),
            }
            for q in result["quotients"]
        ],
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
