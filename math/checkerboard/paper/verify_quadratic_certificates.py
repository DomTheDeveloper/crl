#!/usr/bin/env python3
"""Exact arithmetic audit of the quadratic four-direction certificates.

This is an independent computational cross-check of the manuscript formulas.
The all-n proof is the symbolic argument in the paper and Lean development.
"""
from __future__ import annotations

from fractions import Fraction


def odd_axis(m: int, i: int) -> int:
    return (2 * i - 2 * m) ** 2


def odd_diag(m: int, j: int) -> int:
    return 2 * ((2 * m) ** 2 - (j - 2 * m) ** 2)


def verify_odd(m: int, parity: int) -> None:
    q = 16 * m * m
    axis_sum = sum(odd_axis(m, i) for i in range(2 * m + 1))
    diag_sum = sum(odd_diag(m, j) for j in range(4 * m + 1) if j % 2 == parity)
    cost = 2 * (2 * axis_sum + 2 * diag_sum)

    expected_axis = Fraction(4 * m * (m + 1) * (2 * m + 1), 3)
    if parity == 0:
        expected_diag = Fraction(8 * m * (2 * m - 1) * (2 * m + 1), 3)
        expected_cost = Fraction(16 * m * (10 * m * m + 3 * m - 1), 3)
    else:
        expected_diag = Fraction(4 * m * (8 * m * m + 1), 3)
        expected_cost = Fraction(16 * m * (10 * m * m + 3 * m + 2), 3)
    assert axis_sum == expected_axis
    assert diag_sum == expected_diag
    assert cost == expected_cost

    for x in range(2 * m + 1):
        for y in range(2 * m + 1):
            if (x + y) % 2 != parity:
                continue
            coverage = (
                odd_axis(m, x)
                + odd_axis(m, y)
                + odd_diag(m, x + y)
                + odd_diag(m, x - y + 2 * m)
            )
            assert coverage == q

    if parity == 0 and m >= 3:
        assert cost < q * (4 * m - 1)
    if parity == 1 and m >= 4:
        assert cost < q * (4 * m - 1)


def even_axis(m: int, i: int) -> int:
    n_center = 2 * m - 1
    return (2 * i - n_center) ** 2


def even_diag(m: int, j: int) -> int:
    n_center = 2 * m - 1
    return 2 * (n_center * n_center - (j - n_center) ** 2)


def verify_even(m: int, parity: int) -> None:
    n_center = 2 * m - 1
    q = 4 * n_center * n_center
    axis_sum = sum(even_axis(m, i) for i in range(2 * m))
    sum_diag_sum = sum(even_diag(m, j) for j in range(4 * m - 1) if j % 2 == parity)
    diff_diag_sum = sum(
        even_diag(m, j) for j in range(4 * m - 1) if j % 2 == (parity + 1) % 2
    )
    cost = 2 * (2 * axis_sum + sum_diag_sum + diff_diag_sum)

    expected_axis = Fraction(2 * m * (4 * m * m - 1), 3)
    expected_all_diag = Fraction(2 * n_center * (4 * m - 3) * (4 * m - 1), 3)
    expected_cost = Fraction(4 * n_center * (20 * m * m - 14 * m + 3), 3)
    assert axis_sum == expected_axis
    assert sum_diag_sum + diff_diag_sum == expected_all_diag
    assert cost == expected_cost

    for x in range(2 * m):
        for y in range(2 * m):
            if (x + y) % 2 != parity:
                continue
            coverage = (
                even_axis(m, x)
                + even_axis(m, y)
                + even_diag(m, x + y)
                + even_diag(m, x - y + n_center)
            )
            assert coverage == q

    if m >= 4:
        assert cost < q * (4 * m - 3)


def main() -> None:
    for m in range(1, 101):
        verify_odd(m, 0)
        verify_odd(m, 1)
        verify_even(m, 0)
        verify_even(m, 1)
    print("PASS: exact quadratic coverage, sums, costs, and threshold gaps for m=1..100")


if __name__ == "__main__":
    main()
