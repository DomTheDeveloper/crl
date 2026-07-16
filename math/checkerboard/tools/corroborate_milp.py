#!/usr/bin/env python3
"""Independent MILP corroboration for checkerboard no-three-in-line instances.

This is deliberately labelled corroboration rather than a proof certificate:
SciPy/HiGHS reports an integer optimum, and every returned incumbent is checked
again with exact integer determinants. The universal theorem does not depend
on this program.
"""
from __future__ import annotations

import argparse
import itertools
import math
from typing import Sequence

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix

Point = tuple[int, int]


def normalized_line(p: Point, q: Point) -> tuple[int, int, int]:
    x1, y1 = p
    x2, y2 = q
    a = y2 - y1
    b = x1 - x2
    c = -(a * x1 + b * y1)
    g = math.gcd(math.gcd(abs(a), abs(b)), abs(c))
    if g:
        a //= g
        b //= g
        c //= g
    if a < 0 or (a == 0 and b < 0) or (a == 0 and b == 0 and c < 0):
        a, b, c = -a, -b, -c
    return a, b, c


def collinear(a: Point, b: Point, c: Point) -> bool:
    return (b[0] - a[0]) * (c[1] - a[1]) == (b[1] - a[1]) * (c[0] - a[0])


def verify(points: Sequence[Point]) -> None:
    assert len(set(points)) == len(points)
    assert all(
        not collinear(a, b, c)
        for a, b, c in itertools.combinations(points, 3)
    )


def model(n: int, color: int) -> tuple[list[Point], list[tuple[int, ...]]]:
    points = [
        (x, y)
        for x in range(n)
        for y in range(n)
        if (x + y) % 2 == color
    ]
    point_index = {point: index for index, point in enumerate(points)}
    keys = {
        normalized_line(p, q)
        for p, q in itertools.combinations(points, 2)
    }
    lines = []
    for a, b, c in keys:
        members = tuple(
            point_index[p]
            for p in points
            if a * p[0] + b * p[1] + c == 0
        )
        if len(members) >= 3:
            lines.append(members)
    return points, sorted(set(lines))


def solve(
    n: int, color: int, time_limit: float
) -> tuple[int, list[Point], str, int]:
    points, lines = model(n, color)
    rows: list[int] = []
    columns: list[int] = []
    values: list[float] = []
    for row, line in enumerate(lines):
        for column in line:
            rows.append(row)
            columns.append(column)
            values.append(1.0)
    matrix = csr_matrix(
        (values, (rows, columns)), shape=(len(lines), len(points))
    )
    result = milp(
        c=-np.ones(len(points)),
        integrality=np.ones(len(points)),
        bounds=Bounds(np.zeros(len(points)), np.ones(len(points))),
        constraints=LinearConstraint(
            matrix,
            -np.inf * np.ones(len(lines)),
            2 * np.ones(len(lines)),
        ),
        options={"time_limit": time_limit, "mip_rel_gap": 0.0},
    )
    if result.x is None or result.fun is None:
        raise RuntimeError(f"HiGHS returned no incumbent: {result.message}")
    chosen = [
        points[i]
        for i, value in enumerate(result.x)
        if value > 0.5
    ]
    verify(chosen)
    optimum = int(round(-float(result.fun)))
    if len(chosen) != optimum:
        raise AssertionError((len(chosen), optimum))
    return optimum, chosen, str(result.message), len(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-min", type=int, default=6)
    parser.add_argument("--n-max", type=int, default=12)
    parser.add_argument("--time-limit", type=float, default=120.0)
    args = parser.parse_args()

    for n in range(args.n_min, args.n_max + 1):
        for color in (0, 1):
            optimum, chosen, message, line_count = solve(
                n, color, args.time_limit
            )
            print(
                f"n={n} color={color}: optimum={optimum}; "
                f"bound={2 * n - 4}; lines={line_count}; "
                f"status={message}"
            )
            print(f"  witness={chosen}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
