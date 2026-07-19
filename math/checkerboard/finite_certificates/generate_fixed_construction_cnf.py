#!/usr/bin/env python3
"""Encode a stored coordinate certificate as a fully fixed SAT instance.

The CNF contains the independently regenerated all-slope collinearity clauses
and one unit clause for every eligible board point. Thus SAT means the exact
stored construction satisfies the regenerated geometric instance; no search
or untrusted model extraction is involved.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


def line_key(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int, int]:
    x1, y1 = p
    x2, y2 = q
    dx, dy = x2 - x1, y2 - y1
    divisor = math.gcd(abs(dx), abs(dy))
    a, b = dy // divisor, -dx // divisor
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * x1 + b * y1


def maximal_lines(points: list[tuple[int, int]]) -> list[tuple[int, ...]]:
    groups: dict[tuple[int, int, int], set[int]] = {}
    for i, j in itertools.combinations(range(len(points)), 2):
        groups.setdefault(line_key(points[i], points[j]), set()).update((i, j))
    return sorted({tuple(sorted(indices)) for indices in groups.values()
                   if len(indices) >= 3})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("metadata", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.certificate.read_text(encoding="utf-8"))
    n = int(payload["n"])
    parity = int(payload["parity"])
    chosen = {tuple(map(int, point)) for point in payload["points"]}
    points = [(x, y) for x in range(n) for y in range(n)
              if (x + y) % 2 == parity]
    lines = maximal_lines(points)
    clauses: list[tuple[int, ...]] = []
    for line in lines:
        for i, j, k in itertools.combinations(line, 3):
            clauses.append((-(i + 1), -(j + 1), -(k + 1)))
    for index, point in enumerate(points, start=1):
        clauses.append((index if point in chosen else -index,))

    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    with args.cnf.open("w", encoding="ascii", newline="\n") as handle:
        handle.write(f"p cnf {len(points)} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(map(str, clause)) + " 0\n")
    digest = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    metadata = {
        "format": "checkerboard-fixed-construction-cnf-v1",
        "source": args.certificate.name,
        "n": n,
        "parity": parity,
        "selected": len(chosen),
        "point_variables": len(points),
        "maximal_lines": len(lines),
        "clauses": len(clauses),
        "cnf_sha256": digest,
    }
    args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n",
                             encoding="utf-8")
    print(json.dumps(metadata, sort_keys=True))


if __name__ == "__main__":
    main()
