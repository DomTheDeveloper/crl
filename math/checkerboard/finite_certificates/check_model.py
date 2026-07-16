#!/usr/bin/env python3
"""Check a SAT model or coordinate construction for a checkerboard NTIL instance."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def determinant(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def parse_solver_model(path: Path) -> set[int]:
    positive: set[int] = set()
    status = None
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line.startswith("s "):
            status = line[2:].strip()
        if line.startswith("v "):
            for token in line[2:].split():
                lit = int(token)
                if lit > 0:
                    positive.add(lit)
    if status not in {"SATISFIABLE", "SAT"}:
        raise ValueError(f"solver output is not SAT: {status!r}")
    return positive


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--metadata", type=Path, required=True)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--solver-output", type=Path)
    source.add_argument("--coordinates", type=Path)
    parser.add_argument("--write-coordinates", type=Path)
    args = parser.parse_args()

    metadata = json.loads(args.metadata.read_text(encoding="utf-8"))
    n = int(metadata["n"])
    parity = int(metadata["parity"])
    minimum = int(metadata["minimum_selected"])
    points = [tuple(p) for p in metadata["points"]]

    if args.solver_output:
        model = parse_solver_model(args.solver_output)
        chosen = [point for index, point in enumerate(points, start=1) if index in model]
    else:
        payload = json.loads(args.coordinates.read_text(encoding="utf-8"))
        chosen = [tuple(p) for p in payload["points"]]

    if len(chosen) != len(set(chosen)):
        raise SystemExit("duplicate selected point")
    for x, y in chosen:
        if not (0 <= x < n and 0 <= y < n):
            raise SystemExit(f"out-of-board point {(x, y)}")
        if (x + y) % 2 != parity:
            raise SystemExit(f"wrong-parity point {(x, y)}")
    if len(chosen) < minimum:
        raise SystemExit(f"model has {len(chosen)} selected points, expected at least {minimum}")
    for a, b, c in itertools.combinations(chosen, 3):
        if determinant(a, b, c) == 0:
            raise SystemExit(f"collinear triple: {a}, {b}, {c}")

    chosen = sorted(chosen)
    result = {
        "format": "checkerboard-ntil-construction-v1",
        "n": n,
        "parity": parity,
        "size": len(chosen),
        "points": chosen,
    }
    if args.write_coordinates:
        args.write_coordinates.parent.mkdir(parents=True, exist_ok=True)
        args.write_coordinates.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "points"}, sort_keys=True))


if __name__ == "__main__":
    main()
