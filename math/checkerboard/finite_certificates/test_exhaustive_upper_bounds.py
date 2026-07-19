#!/usr/bin/env python3
"""Brute-force regression tests for the exhaustive cardinality search engine."""
from __future__ import annotations

import random

from verify_exhaustive_upper_bounds import ExactConstraint, ExhaustiveSolver, mask_of


def satisfies(assignment: int, exact: list[ExactConstraint], at_most_two: list[int]) -> bool:
    return (all((assignment & constraint.mask).bit_count() == constraint.target
                for constraint in exact)
            and all((assignment & mask).bit_count() <= 2 for mask in at_most_two))


def brute_force(n: int, exact: list[ExactConstraint], at_most_two: list[int],
                true_mask: int, false_mask: int) -> bool:
    return any((assignment & true_mask) == true_mask
               and (assignment & false_mask) == 0
               and satisfies(assignment, exact, at_most_two)
               for assignment in range(1 << n))


def main() -> None:
    rng = random.Random(20260716)
    for case in range(500):
        n = rng.randint(1, 8)
        exact: list[ExactConstraint] = []
        for index in range(rng.randint(1, 5)):
            members = [i for i in range(n) if rng.randrange(2)]
            if not members:
                members = [rng.randrange(n)]
            target = rng.randrange(len(members) + 1)
            exact.append(ExactConstraint(f"E{index}", mask_of(members), target))
        at_most_two: list[int] = []
        for _ in range(rng.randint(0, 5)):
            members = [i for i in range(n) if rng.randrange(2)]
            if members:
                at_most_two.append(mask_of(members))

        true_mask = 0
        false_mask = 0
        for variable in range(n):
            state = rng.randrange(3)
            if state == 1:
                true_mask |= 1 << variable
            elif state == 2:
                false_mask |= 1 << variable

        expected = brute_force(n, exact, at_most_two, true_mask, false_mask)
        solver = ExhaustiveSolver(exact, at_most_two)
        actual = solver.search(true_mask, false_mask)
        if actual != expected:
            raise AssertionError(
                f"case {case}: search={actual}, brute_force={expected}, n={n}, "
                f"true={true_mask}, false={false_mask}, exact={exact}, "
                f"at_most_two={at_most_two}")

    for n in range(1, 8):
        full = mask_of(range(n))
        for target in range(n + 1):
            exact = [ExactConstraint("all", full, target)]
            solver = ExhaustiveSolver(exact, [])
            if not solver.search(0, 0):
                raise AssertionError((n, target))

    print("exhaustive search engine matches brute force on 500 random systems")


if __name__ == "__main__":
    main()
