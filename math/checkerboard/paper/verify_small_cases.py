#!/usr/bin/env python3
"""Exact standard-library checks for the finite exceptions in the 2n-4 proof."""
from __future__ import annotations

from itertools import combinations


def parity_points(n: int, parity: int) -> list[tuple[int, int]]:
    return [(x, y) for x in range(n) for y in range(n) if (x + y) % 2 == parity]


def principal_lines(n: int) -> list[set[tuple[int, int]]]:
    points = [(x, y) for x in range(n) for y in range(n)]
    lines: list[set[tuple[int, int]]] = []
    for x in range(n):
        lines.append({p for p in points if p[0] == x})
    for y in range(n):
        lines.append({p for p in points if p[1] == y})
    for c in range(-(n - 1), n):
        lines.append({p for p in points if p[0] - p[1] == c})
    for c in range(2 * n - 1):
        lines.append({p for p in points if p[0] + p[1] == c})
    return [line for line in lines if line]


def verify_n6() -> None:
    lines = principal_lines(6)
    for parity in (0, 1):
        points = parity_points(6, parity)
        assert len(points) == 18
        for chosen_tuple in combinations(points, 9):
            chosen = set(chosen_tuple)
            if all(len(chosen & line) <= 2 for line in lines):
                raise AssertionError(f"unexpected 9-point packing: parity={parity}, set={chosen}")
    print("PASS n=6: all 48,620 nine-subsets rejected in each parity class")


def boundary_weight(t: int) -> int:
    return int(t in (0, 6))


def diagonal_weight(j: int) -> int:
    distance = abs(j - 6)
    if distance == 1:
        return 2
    if distance == 3:
        return 1
    return 0


def verify_n7_thin() -> None:
    total_weight = 4 + 2 * sum(diagonal_weight(j) for j in range(13))
    assert total_weight == 16
    assert 2 * total_weight == 32
    for x, y in parity_points(7, 1):
        coverage = (
            boundary_weight(x)
            + boundary_weight(y)
            + diagonal_weight(x + y)
            + diagonal_weight(x - y + 6)
        )
        assert coverage >= 3, ((x, y), coverage)
    print("PASS n=7 thin: coverage >= 3 and capacity-two cost = 32 < 33")


def main() -> None:
    verify_n6()
    verify_n7_thin()


if __name__ == "__main__":
    main()
