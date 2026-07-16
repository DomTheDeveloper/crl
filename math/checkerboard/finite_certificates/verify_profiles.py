#!/usr/bin/env python3
"""Exact verification of the compact 17x17 and 21x21 line-cover profiles.

The script uses only Python's standard library and integer arithmetic. It
lifts each symmetry-reduced profile to the actual rows, columns, and slope
+/-1 diagonals, checks every eligible point-cover inequality, and checks the
exact dual objective. For n=21 it additionally regenerates the zero/one
slack candidate sets used by the finite upper-bound reduction.
"""
from __future__ import annotations

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


def points(n: int, parity: int) -> list[tuple[int, int]]:
    return [(x, y) for x in range(n) for y in range(n)
            if (x + y) % 2 == parity]


def coverage_numerator(profile: Profile, point: tuple[int, int]) -> int:
    """Lift a reduced profile to the four geometric lines through ``point``.

    ``diagonal`` contains the orbit weights for the two oblique line
    families; ``axis`` contains the row/column orbit weights. The formulas
    are the explicit inverse of the odd-fat and odd-thin orbit reductions.
    """
    n, parity = profile.n, profile.parity
    m = (n - 1) // 2
    x, y = point
    folded_x = min(x, n - 1 - x)
    folded_y = min(y, n - 1 - y)
    axis_cover = profile.axis[folded_x] + profile.axis[folded_y]
    total = x + y
    difference = abs(x - y)

    if parity == 0:
        if total % 2 or difference % 2:
            raise ValueError(f"{point} is not in the fat parity class")
        sum_index = min(total, 2 * n - 2 - total) // 2
        difference_index = m - difference // 2
    else:
        if total % 2 != 1 or difference % 2 != 1:
            raise ValueError(f"{point} is not in the thin parity class")
        sum_index = (min(total, 2 * n - 2 - total) - 1) // 2
        difference_index = m - (difference + 1) // 2

    return (axis_cover + profile.diagonal[sum_index]
            + profile.diagonal[difference_index])


def computed_objective_numerator(profile: Profile) -> int:
    """Twice the sum of all lifted line weights, over the common denominator."""
    n, parity = profile.n, profile.parity
    m = (n - 1) // 2
    if parity == 0:
        return (8 * sum(profile.diagonal[:m])
                + 4 * profile.diagonal[m]
                + 8 * sum(profile.axis[:m])
                + 4 * profile.axis[m])
    return (8 * sum(profile.diagonal)
            + 8 * sum(profile.axis[:m])
            + 4 * profile.axis[m])


def verify(profile: Profile) -> dict[str, int | str]:
    if profile.n % 2 != 1:
        raise AssertionError("these profiles are for odd side lengths")
    if any(weight < 0 for weight in profile.diagonal + profile.axis):
        raise AssertionError("dual weights must be nonnegative")
    expected_points = (profile.n * profile.n + (1 if profile.parity == 0 else -1)) // 2
    eligible = points(profile.n, profile.parity)
    assert len(eligible) == expected_points

    computed_objective = computed_objective_numerator(profile)
    assert computed_objective == profile.objective_numerator, (
        computed_objective, profile.objective_numerator)

    slacks = [coverage_numerator(profile, point) - profile.denominator
              for point in eligible]
    assert min(slacks) >= 0, f"negative cover slack: {min(slacks)}"

    value = Fraction(profile.objective_numerator, profile.denominator)
    result: dict[str, int | str] = {
        "n": profile.n,
        "parity": profile.parity,
        "point_count": len(eligible),
        "minimum_slack": min(slacks),
        "objective": str(value),
        "integer_upper_bound": value.numerator // value.denominator,
    }

    if profile.n == 17:
        assert value < 27
        assert result["integer_upper_bound"] == 26
    elif profile.n == 21 and profile.parity == 0:
        assert profile.objective_numerator - 33 * profile.denominator == 1
        zero = sum(slack == 0 for slack in slacks)
        one = sum(slack == 1 for slack in slacks)
        assert (zero, one) == (116, 20)
        result.update(zero_slack_points=zero, one_slack_points=one,
                      candidate_points=zero + one, slack_budget=1)
    elif profile.n == 21 and profile.parity == 1:
        assert profile.objective_numerator == 33 * profile.denominator
        zero = sum(slack == 0 for slack in slacks)
        assert zero == 132
        result.update(zero_slack_points=zero, candidate_points=zero,
                      slack_budget=0)
    return result


def main() -> None:
    for profile in PROFILES:
        result = verify(profile)
        print("PASS", " ".join(f"{key}={value}" for key, value in result.items()))
    print("ALL COMPACT LINE-COVER PROFILES VERIFIED EXACTLY")


if __name__ == "__main__":
    main()
