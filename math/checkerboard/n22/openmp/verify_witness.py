#!/usr/bin/env python3
"""Independent exact determinant checker for checkerboard point sets."""
from __future__ import annotations

import argparse
import itertools
import math
import sys
from pathlib import Path


def load(path: Path) -> list[tuple[int, int]]:
    points: list[tuple[int, int]] = []
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"{path}:{line_number}: expected two integers")
        points.append((int(fields[0]), int(fields[1])))
    return points


def determinant(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("point_set", type=Path)
    ap.add_argument("--n", type=int, default=22)
    ap.add_argument("--parity", type=int, choices=(0, 1), default=0)
    ap.add_argument("--size", type=int, required=True)
    ap.add_argument("--expect-collinear-triples", type=int, default=0)
    ap.add_argument("--show-conflicts", action="store_true")
    args = ap.parse_args()

    try:
        pts = load(args.point_set)
        if len(pts) != args.size:
            raise ValueError(f"size mismatch: got {len(pts)}, expected {args.size}")
        if len(set(pts)) != len(pts):
            raise ValueError("duplicate point")
        for p in pts:
            x, y = p
            if not (0 <= x < args.n and 0 <= y < args.n):
                raise ValueError(f"out-of-bounds point: {p}")
            if (x + y) % 2 != args.parity:
                raise ValueError(f"wrong-parity point: {p}")

        conflicts: list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]] = []
        for a, b, c in itertools.combinations(pts, 3):
            if determinant(a, b, c) == 0:
                conflicts.append((a, b, c))

        if args.show_conflicts:
            for conflict in conflicts:
                print("COLLINEAR", *conflict)
        if len(conflicts) != args.expect_collinear_triples:
            raise ValueError(
                f"collinear-triple mismatch: got {len(conflicts)}, "
                f"expected {args.expect_collinear_triples}"
            )

        print(
            f"VERIFIED n={args.n} parity={args.parity} size={len(pts)} "
            f"triples={math.comb(len(pts), 3)} collinear_triples={len(conflicts)}"
        )
        return 0
    except (OSError, ValueError) as exc:
        print(f"VERIFY_FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
