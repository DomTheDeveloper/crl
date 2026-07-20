#!/usr/bin/env python3
"""Deterministically verify the 33-point lower-bound witness for D_mono(22)."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def read_points(path: Path) -> list[tuple[int, int]]:
    points: list[tuple[int, int]] = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"malformed witness line: {raw!r}")
        points.append((int(fields[0]), int(fields[1])))
    return points


def determinant(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "witness",
        type=Path,
        nargs="?",
        default=Path("../n22/openmp/examples/n22_33.txt"),
    )
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args()

    data = args.witness.read_bytes()
    points = read_points(args.witness)

    if len(points) != 33:
        raise SystemExit(f"expected 33 points, found {len(points)}")
    if len(set(points)) != len(points):
        raise SystemExit("witness contains duplicate points")
    for p in points:
        if not (0 <= p[0] < 22 and 0 <= p[1] < 22):
            raise SystemExit(f"point outside 22x22 grid: {p}")
        if (p[0] + p[1]) % 2 != 0:
            raise SystemExit(f"point has wrong checkerboard parity: {p}")

    checked = 0
    for a, b, c in itertools.combinations(points, 3):
        checked += 1
        if determinant(a, b, c) == 0:
            raise SystemExit(f"collinear triple: {a}, {b}, {c}")

    expected_triples = 33 * 32 * 31 // 6
    if checked != expected_triples:
        raise AssertionError((checked, expected_triples))

    report = {
        "n": 22,
        "parity": 0,
        "size": len(points),
        "unique": True,
        "all_points_in_grid": True,
        "all_points_correct_parity": True,
        "triples_checked": checked,
        "collinear_triples": 0,
        "witness_sha256": hashlib.sha256(data).hexdigest(),
        "witness": str(args.witness),
    }
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text)
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
