#!/usr/bin/env python3
"""Deterministic exhaustive checker for the forbidden size 2n-3.

For one checkerboard color, every no-three-in-line set has at most two points in
any row. A hypothetical set of size 2n-3 therefore has row deficit exactly 3
relative to two points per row. This program enumerates every row-count vector
with that deficit, every compatible choice of points in each row, and rejects a
partial choice as soon as a column contains three points or any determinant
triple is collinear.

A completed search with no witness is an exact finite proof for the requested
(n, color) instance. No solver, floating point arithmetic, randomization, or
symmetry assumption is used.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

Point = tuple[int, int]


def collinear(a: Point, b: Point, c: Point) -> bool:
    """Exact integer determinant test."""
    return (b[0] - a[0]) * (c[1] - a[1]) == (b[1] - a[1]) * (c[0] - a[0])


def verify_no_three(points: Sequence[Point]) -> bool:
    """Independent direct verification of a proposed point set."""
    return all(
        not collinear(a, b, c)
        for a, b, c in itertools.combinations(points, 3)
    )


def row_count_vectors(n: int, target: int) -> Iterable[tuple[int, ...]]:
    """All vectors in {0,1,2}^n whose sum is target."""
    vector: list[int] = []

    def rec(row: int, remaining: int) -> Iterable[tuple[int, ...]]:
        if row == n:
            if remaining == 0:
                yield tuple(vector)
            return
        rows_left = n - row - 1
        for count in range(3):
            next_remaining = remaining - count
            if 0 <= next_remaining <= 2 * rows_left:
                vector.append(count)
                yield from rec(row + 1, next_remaining)
                vector.pop()

    yield from rec(0, target)


@dataclass(frozen=True)
class SearchResult:
    n: int
    color: int
    target: int
    row_count_vectors: int
    search_nodes: int
    witness: tuple[Point, ...] | None
    elapsed_seconds: float

    @property
    def proved_unsat(self) -> bool:
        return self.witness is None


def search(n: int, color: int) -> SearchResult:
    if n < 1:
        raise ValueError("n must be positive")
    if color not in (0, 1):
        raise ValueError("color must be 0 or 1")

    target = 2 * n - 3
    points_by_row: list[list[Point]] = [
        [(x, y) for x in range(n) if (x + y) % 2 == color]
        for y in range(n)
    ]
    options = {
        (row, count): tuple(itertools.combinations(points_by_row[row], count))
        for row in range(n)
        for count in range(3)
    }

    vectors = tuple(row_count_vectors(n, target))
    nodes = 0
    started = time.perf_counter()

    for counts in vectors:
        # This ordering changes only traversal order, not the search space.
        rows = sorted(
            range(n), key=lambda row: (len(options[row, counts[row]]), row)
        )
        selected: list[Point] = []
        column_counts = [0] * n

        def dfs(depth: int) -> tuple[Point, ...] | None:
            nonlocal nodes
            nodes += 1
            if depth == n:
                assert len(selected) == target
                assert verify_no_three(selected)
                return tuple(sorted(selected))

            row = rows[depth]
            for choice in options[row, counts[row]]:
                if any(column_counts[x] >= 2 for x, _ in choice):
                    continue

                combined = selected + list(choice)
                valid = True
                # Only triples containing a newly added point can be new.
                for p in choice:
                    others = [q for q in combined if q != p]
                    if any(
                        collinear(a, b, p)
                        for a, b in itertools.combinations(others, 2)
                    ):
                        valid = False
                        break
                if not valid:
                    continue

                for x, y in choice:
                    selected.append((x, y))
                    column_counts[x] += 1
                witness = dfs(depth + 1)
                if witness is not None:
                    return witness
                for x, _ in reversed(choice):
                    selected.pop()
                    column_counts[x] -= 1
            return None

        witness = dfs(0)
        if witness is not None:
            return SearchResult(
                n=n,
                color=color,
                target=target,
                row_count_vectors=len(vectors),
                search_nodes=nodes,
                witness=witness,
                elapsed_seconds=time.perf_counter() - started,
            )

    return SearchResult(
        n=n,
        color=color,
        target=target,
        row_count_vectors=len(vectors),
        search_nodes=nodes,
        witness=None,
        elapsed_seconds=time.perf_counter() - started,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-min", type=int, default=6)
    parser.add_argument("--n-max", type=int, default=9)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    results: list[SearchResult] = []
    for n in range(args.n_min, args.n_max + 1):
        for color in (0, 1):
            result = search(n, color)
            results.append(result)
            if not args.json:
                status = "UNSAT" if result.proved_unsat else "WITNESS"
                print(
                    f"n={n} color={color} target={result.target}: {status}; "
                    f"vectors={result.row_count_vectors} "
                    f"nodes={result.search_nodes} "
                    f"seconds={result.elapsed_seconds:.3f}"
                )
                if result.witness is not None:
                    print(result.witness)

    if args.json:
        print(
            json.dumps(
                [
                    asdict(result) | {"proved_unsat": result.proved_unsat}
                    for result in results
                ],
                indent=2,
            )
        )

    return 1 if any(result.witness is not None for result in results) else 0


if __name__ == "__main__":
    raise SystemExit(main())
