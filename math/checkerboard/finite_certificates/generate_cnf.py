#!/usr/bin/env python3
"""Deterministically generate checkerboard no-three-in-line CNF instances.

Variables 1..|C_p| correspond lexicographically to points (x,y) with
0 <= x,y < n and (x+y) mod 2 = parity. Every collinear triple receives a
negative 3-clause. An exact dynamic-programming counter enforces a lower
bound on the number of selected points.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
from typing import Sequence


def point_set(n: int, parity: int) -> list[tuple[int, int]]:
    return [(x, y) for x in range(n) for y in range(n) if (x + y) % 2 == parity]


def line_key(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int, int]:
    x1, y1 = p
    x2, y2 = q
    dx, dy = x2 - x1, y2 - y1
    g = math.gcd(abs(dx), abs(dy))
    if g == 0:
        raise ValueError("distinct points required")
    a, b = dy // g, -dx // g
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * x1 + b * y1


def maximal_lines(points: Sequence[tuple[int, int]]) -> list[tuple[int, ...]]:
    groups: dict[tuple[int, int, int], set[int]] = {}
    for i, j in itertools.combinations(range(len(points)), 2):
        groups.setdefault(line_key(points[i], points[j]), set()).update((i, j))
    lines = {tuple(sorted(indices)) for indices in groups.values() if len(indices) >= 3}
    return sorted(lines, key=lambda line: (len(line), line))


class CnfBuilder:
    def __init__(self, primary_variables: int) -> None:
        self.variable_count = primary_variables
        self.clauses: list[tuple[int, ...]] = []

    def new_var(self) -> int:
        self.variable_count += 1
        return self.variable_count

    def add(self, *literals: int) -> None:
        if not literals:
            self.clauses.append(())
            return
        if any(lit == 0 for lit in literals):
            raise ValueError("literal zero is reserved as a DIMACS terminator")
        normalized = tuple(dict.fromkeys(literals))
        if any(-lit in normalized for lit in normalized):
            return
        self.clauses.append(normalized)


def add_at_least(builder: CnfBuilder, literals: Sequence[int], bound: int) -> int:
    """Encode sum(literals) >= bound with an O(n*bound) exact counter.

    State variable s[i,j] denotes that at least j of the first i literals are
    true. Each state is equivalent to

        s[i-1,j] OR (literals[i-1] AND s[i-1,j-1]).

    Boundary states s[i,0] are true and s[0,j] are false.
    """
    n = len(literals)
    before = builder.variable_count
    if bound <= 0:
        return 0
    if bound > n:
        builder.add()
        return 0

    states: dict[tuple[int, int], int] = {}
    for i in range(1, n + 1):
        for j in range(1, min(i, bound) + 1):
            states[(i, j)] = builder.new_var()

    for i in range(1, n + 1):
        x = literals[i - 1]
        for j in range(1, min(i, bound) + 1):
            curr = states[(i, j)]
            prev_same = states.get((i - 1, j))
            prev_less: int | bool
            prev_less = True if j == 1 else states.get((i - 1, j - 1), False)

            if prev_same is None:
                if prev_less is False:
                    builder.add(-curr)
                elif prev_less is True:
                    builder.add(-curr, x)
                    builder.add(-x, curr)
                else:
                    builder.add(-curr, x)
                    builder.add(-curr, prev_less)
                    builder.add(-x, -prev_less, curr)
            else:
                builder.add(-prev_same, curr)
                if prev_less is True:
                    builder.add(-x, curr)
                    builder.add(-curr, prev_same, x)
                elif prev_less is False:
                    builder.add(-curr, prev_same)
                else:
                    builder.add(-x, -prev_less, curr)
                    builder.add(-curr, prev_same, x)
                    builder.add(-curr, prev_same, prev_less)

    builder.add(states[(n, bound)])
    return builder.variable_count - before


def build_instance(n: int, parity: int, minimum: int) -> tuple[list[tuple[int, int]], list[tuple[int, ...]], CnfBuilder, dict[str, object]]:
    if n < 1:
        raise ValueError("n must be positive")
    if parity not in (0, 1):
        raise ValueError("parity must be 0 or 1")
    points = point_set(n, parity)
    if minimum < 0 or minimum > len(points):
        raise ValueError("minimum must lie between 0 and the parity-class size")
    lines = maximal_lines(points)
    builder = CnfBuilder(len(points))
    triple_clause_count = 0
    for line in lines:
        for i, j, k in itertools.combinations(line, 3):
            builder.add(-(i + 1), -(j + 1), -(k + 1))
            triple_clause_count += 1

    selected_literals = [i + 1 for i in range(len(points))]
    aux_count = add_at_least(builder, selected_literals, minimum)
    metadata: dict[str, object] = {
        "format": "checkerboard-ntil-cnf-v1",
        "n": n,
        "parity": parity,
        "minimum_selected": minimum,
        "point_count": len(points),
        "maximal_line_count": len(lines),
        "collinear_triple_clause_count": triple_clause_count,
        "auxiliary_variable_count": aux_count,
        "variable_count": builder.variable_count,
        "clause_count": len(builder.clauses),
        "point_variable_order": "lexicographic (x,y), x outer then y",
        "encoding": "negative clause for each collinear triple; exact dynamic-programming sequential counter for the lower cardinality bound",
    }
    return points, lines, builder, metadata


def write_dimacs(path: Path, builder: CnfBuilder) -> str:
    with path.open("w", encoding="ascii", newline="\n") as handle:
        handle.write(f"p cnf {builder.variable_count} {len(builder.clauses)}\n")
        for clause in builder.clauses:
            handle.write(" ".join(map(str, clause)))
            if clause:
                handle.write(" ")
            handle.write("0\n")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--parity", type=int, choices=(0, 1), required=True)
    parser.add_argument("--at-least", dest="minimum", type=int, required=True)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    args = parser.parse_args()

    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    points, lines, builder, metadata = build_instance(args.n, args.parity, args.minimum)
    metadata["cnf_sha256"] = write_dimacs(args.cnf, builder)
    metadata["points"] = points
    metadata["maximal_lines"] = lines
    args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in metadata.items() if k not in {"points", "maximal_lines"}}, sort_keys=True))


if __name__ == "__main__":
    main()
