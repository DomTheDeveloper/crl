#!/usr/bin/env python3
"""Independently reconstruct and solve the four finite upper-bound models.

Exit status 0 means the selected solver returned a completed infeasibility
result. A timeout/limit returns 2 and is deliberately not accepted as a proof.
"""
from __future__ import annotations

import argparse
import itertools
import math

from generate_reduced_n21 import build as build_n21


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


def instance(n: int, parity: int, target: int):
    if n == 21 and target == 33:
        candidates, slacks, lines, _, _ = build_n21(parity)
        return candidates, lines, slacks, 1 if parity == 0 else 0
    points = [(x, y) for x in range(n) for y in range(n)
              if (x + y) % 2 == parity]
    return points, maximal_lines(points), [0] * len(points), 0


def solve_cpsat(n: int, parity: int, target: int, seconds: float) -> int:
    from ortools.sat.python import cp_model

    points, lines, slacks, budget = instance(n, parity, target)
    model = cp_model.CpModel()
    selected = [model.NewBoolVar(f"z{i}") for i in range(len(points))]
    for line in lines:
        model.Add(sum(selected[index] for index in line) <= 2)
    model.Add(sum(selected) == target)
    if any(slacks):
        model.Add(sum(slacks[index] * selected[index]
                      for index in range(len(selected))) <= budget)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 1
    solver.parameters.random_seed = 1
    status = solver.Solve(model)
    name = solver.StatusName(status)
    print(f"solver=cp-sat n={n} parity={parity} target={target} "
          f"candidates={len(points)} lines={len(lines)} status={name} "
          f"wall={solver.WallTime():.6f}")
    if status == cp_model.INFEASIBLE:
        return 0
    if status == cp_model.UNKNOWN:
        return 2
    return 1


def solve_highs(n: int, parity: int, target: int, seconds: float) -> int:
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import lil_matrix

    points, lines, slacks, budget = instance(n, parity, target)
    row_count = len(lines) + 1 + (1 if any(slacks) else 0)
    matrix = lil_matrix((row_count, len(points)), dtype=float)
    lower: list[float] = []
    upper: list[float] = []
    row = 0
    for line in lines:
        for index in line:
            matrix[row, index] = 1
        lower.append(-np.inf)
        upper.append(2)
        row += 1
    matrix[row, :] = 1
    lower.append(target)
    upper.append(target)
    row += 1
    if any(slacks):
        for index, slack in enumerate(slacks):
            matrix[row, index] = slack
        lower.append(-np.inf)
        upper.append(budget)

    result = milp(
        c=np.zeros(len(points)),
        integrality=np.ones(len(points)),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(matrix.tocsr(), np.asarray(lower), np.asarray(upper)),
        options={"time_limit": seconds, "presolve": True, "mip_rel_gap": 0.0},
    )
    names = {0: "OPTIMAL", 1: "LIMIT", 2: "INFEASIBLE", 3: "UNBOUNDED", 4: "ERROR"}
    status = names.get(result.status, str(result.status))
    print(f"solver=highs n={n} parity={parity} target={target} "
          f"candidates={len(points)} lines={len(lines)} status={status} "
          f"message={result.message!r}")
    if result.status == 2:
        return 0
    if result.status == 1:
        return 2
    return 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", choices=("cpsat", "highs"), required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--parity", type=int, choices=(0, 1), required=True)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--seconds", type=float, default=1800)
    args = parser.parse_args()
    function = solve_cpsat if args.solver == "cpsat" else solve_highs
    raise SystemExit(function(args.n, args.parity, args.target, args.seconds))


if __name__ == "__main__":
    main()
