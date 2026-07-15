#!/usr/bin/env python3
"""Probe the final odd-prime Mordell--Weil cosets over Q_2.

The odd-prime sieve fixes m modulo 2^9 and n modulo 2^10.  We first test the
21 remaining residue pairs on the certified rank-two quotient.  The output
records valuations and square tests for the three remaining row conditions.
"""
from __future__ import annotations

import json
from pathlib import Path

from sage.all import EllipticCurve, Integer, Qp

PREC = 160
K = Qp(2, prec=PREC)
A2 = Integer(210454900)
A4 = Integer(11001099894400000)
E = EllipticCurve(K, [0, A2, 0, A4, 0])
P1 = E(K(-101150000), K(-74648700000))
P2 = E(K(70312000), K(1470223920000))
A = Integer(2578)
REMAINING = [Integer(2422), Integer(3222), Integer(8678)]
RESIDUES = [
    (0,511),(0,512),(0,513),(1,512),(1,513),
    (255,0),(255,511),(255,512),(255,1023),
    (256,0),(256,1),(256,511),(256,512),(256,513),(256,1023),
    (257,0),(257,1),(257,512),(257,513),(511,511),(511,512),
]


def q2_square_info(z):
    if z == 0:
        return {"zero": True, "is_square": True, "valuation": "Infinity"}
    v = int(z.valuation())
    return {
        "zero": False,
        "is_square": bool(z.is_square()),
        "valuation": v,
        "unit_mod_8": int((z / (K(2) ** v)).lift() % 8),
    }


def point_info(m, n):
    Z = m*P1 + n*P2
    if Z.is_zero():
        return {"point_zero": True, "passes_all": True}
    X, Y = Z[0], Z[1]
    if Y == 0:
        return {"point_2torsion": True, "passes_all": True}
    u = (K(A4) - X*X) / (K(4)*Y)
    t = u*u - K(A*A)
    checks = []
    for d in REMAINING:
        z = t + K(d*d)
        info = q2_square_info(z)
        info["row"] = int(d)
        checks.append(info)
    return {
        "point_zero": False,
        "t_valuation": "Infinity" if t == 0 else int(t.valuation()),
        "checks": checks,
        "passes_all": all(c["is_square"] for c in checks),
    }


out = {
    "precision": PREC,
    "fixed_moduli": {"m": 512, "n": 1024},
    "results": [],
}
for m,n in RESIDUES:
    item = {"m": m, "n": n}
    try:
        item.update(point_info(m,n))
    except Exception as exc:
        item["error"] = f"{type(exc).__name__}: {exc}"
    out["results"].append(item)

out["survivors"] = [
    [r["m"],r["n"]] for r in out["results"] if r.get("passes_all")
]
Path("results").mkdir(exist_ok=True)
Path("results/two_adic_probe.json").write_text(json.dumps(out, indent=2, sort_keys=True)+"\n")
print(json.dumps(out, sort_keys=True))
