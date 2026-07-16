#!/usr/bin/env python3
"""Independently expand and verify all four exact rational dual profiles.

Unlike verify_profiles.py, this checker constructs every actual row, column,
sum-diagonal, and difference-diagonal with its lifted integer weight. It then
sums the expanded line weights directly and checks every eligible point cover.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Profile:
    n: int
    parity: int
    denominator: int
    diagonal: tuple[int, ...]
    axis: tuple[int, ...]
    objective_numerator: int


PROFILES = (
    Profile(17, 0, 67, (0, 0, 10, 18, 24, 29, 35, 38, 39),
            (20, 14, 9, 5, 2, 0, 0, 0, 0), 1788),
    Profile(17, 1, 33, (0, 0, 5, 9, 12, 15, 17, 18),
            (12, 9, 6, 4, 2, 1, 0, 0, 0), 880),
    Profile(21, 0, 75, (0, 0, 0, 10, 18, 24, 30, 36, 41, 44, 45),
            (28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0), 2476),
    Profile(21, 1, 48, (0, 0, 6, 11, 15, 18, 22, 25, 27, 28),
            (15, 12, 8, 6, 3, 2, 0, 0, 0, 0, 0), 1584),
)


def axis_weight(profile: Profile, coordinate: int) -> int:
    return profile.axis[min(coordinate, profile.n - 1 - coordinate)]


def sum_weight(profile: Profile, total: int) -> int:
    folded = min(total, 2 * profile.n - 2 - total)
    if profile.parity == 0:
        assert folded % 2 == 0
        index = folded // 2
    else:
        assert folded % 2 == 1
        index = (folded - 1) // 2
    return profile.diagonal[index]


def difference_weight(profile: Profile, difference: int) -> int:
    distance = abs(difference)
    middle = (profile.n - 1) // 2
    if profile.parity == 0:
        assert distance % 2 == 0
        index = middle - distance // 2
    else:
        assert distance % 2 == 1
        index = middle - (distance + 1) // 2
    return profile.diagonal[index]


def expanded_line_weights(profile: Profile) -> list[tuple[str, int, int]]:
    result: list[tuple[str, int, int]] = []
    for coordinate in range(profile.n):
        result.append(("row", coordinate, axis_weight(profile, coordinate)))
        result.append(("column", coordinate, axis_weight(profile, coordinate)))
    for total in range(2 * profile.n - 1):
        if total % 2 == profile.parity:
            result.append(("sum", total, sum_weight(profile, total)))
    for difference in range(-(profile.n - 1), profile.n):
        if difference % 2 == profile.parity:
            result.append(("difference", difference,
                           difference_weight(profile, difference)))
    return result


def coverage(profile: Profile, point: tuple[int, int]) -> int:
    x, y = point
    return (axis_weight(profile, x) + axis_weight(profile, y)
            + sum_weight(profile, x + y)
            + difference_weight(profile, x - y))


def verify(profile: Profile) -> None:
    assert profile.parity in (0, 1)
    assert profile.n % 2 == 1
    assert all(weight >= 0 for weight in profile.axis + profile.diagonal)

    lines = expanded_line_weights(profile)
    computed_objective = 2 * sum(weight for _, _, weight in lines)
    assert computed_objective == profile.objective_numerator

    eligible = [(x, y) for x in range(profile.n) for y in range(profile.n)
                if (x + y) % 2 == profile.parity]
    slacks = [coverage(profile, point) - profile.denominator
              for point in eligible]
    assert min(slacks) >= 0

    value = Fraction(profile.objective_numerator, profile.denominator)
    if profile.n == 17:
        assert value < 27
        assert value.numerator // value.denominator == 26
    elif profile.parity == 0:
        assert profile.objective_numerator - 33 * profile.denominator == 1
        counts = Counter(slacks)
        assert counts[0] == 116 and counts[1] == 20
    else:
        assert profile.objective_numerator == 33 * profile.denominator
        assert Counter(slacks)[0] == 132

    print("PASS", f"n={profile.n}", f"parity={profile.parity}",
          f"lines={len(lines)}", f"points={len(eligible)}",
          f"objective={value}", f"minimum_slack={min(slacks)}")


def main() -> None:
    for profile in PROFILES:
        verify(profile)
    print("ALL EXPANDED DUAL PROFILES VERIFIED INDEPENDENTLY")


if __name__ == "__main__":
    main()
