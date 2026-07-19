#!/usr/bin/env python3
"""Brute-force regression tests for the independent binary proof search."""
from __future__ import annotations

import random

from verify_exhaustive_upper_bounds import ExactConstraint, mask_of
from verify_exhaustive_upper_bounds_binary import BinarySearch


def brute(n: int, exact: list[ExactConstraint], lines: list[int],
          selected: int, rejected: int) -> bool:
    for assignment in range(1 << n):
        if assignment & selected != selected or assignment & rejected:
            continue
        if any((assignment & equation.mask).bit_count() != equation.target
               for equation in exact):
            continue
        if any((assignment & line).bit_count() > 2 for line in lines):
            continue
        return True
    return False


def main() -> None:
    rng = random.Random(210321)
    for case in range(500):
        n = rng.randint(1, 8)
        exact = []
        for index in range(rng.randint(1, 5)):
            members = [i for i in range(n) if rng.randrange(2)] or [rng.randrange(n)]
            exact.append(ExactConstraint(
                f"E{index}", mask_of(members), rng.randrange(len(members) + 1)))
        lines = []
        for _ in range(rng.randint(0, 5)):
            members = [i for i in range(n) if rng.randrange(2)]
            if members:
                lines.append(mask_of(members))
        selected = 0
        rejected = 0
        for variable in range(n):
            state = rng.randrange(3)
            if state == 1:
                selected |= 1 << variable
            elif state == 2:
                rejected |= 1 << variable

        expected = brute(n, exact, lines, selected, rejected)
        actual = BinarySearch(tuple(exact), tuple(lines)).solve(selected, rejected)
        if actual != expected:
            raise AssertionError((case, n, expected, actual, selected, rejected,
                                  exact, lines))

    print("binary proof search matches brute force on 500 random systems")


if __name__ == "__main__":
    main()
