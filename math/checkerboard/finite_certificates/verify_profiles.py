#!/usr/bin/env python3
"""Exact verification of the compact 17x17 and 21x21 line-cover profiles.

The script uses only Python's standard library and integer arithmetic. It reads
the machine-readable certificate data in ``dual_profiles.json``, lifts each
symmetry-reduced profile to the actual rows, columns, and slope +/-1 diagonals,
checks every eligible point-cover inequality, and checks the exact dual
objective. For n=21 it additionally regenerates the zero/one slack candidate
sets used by the finite upper-bound reduction.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class Profile:
    n: int
    parity: int
    denominator: int
    diagonal: tuple[int, ...]
    axis: tuple[int, ...]
    objective_numerator: int


def load_profiles(path: Path | None = None) -> tuple[Profile, ...]:
    source = path or Path(__file__).with_name("dual_profiles.json")
    payload = json.loads(source.read_text(encoding="utf-8"))
    assert payload["format"] == "checkerboard-four-direction-dual-profiles-v1"
    profiles = tuple(Profile(
        n=int(entry["n"]),
        parity=int(entry["parity"]),
        denominator=int(entry["denominator"]),
        diagonal=tuple(map(int, entry["diagonal"])),
        axis=tuple(map(int, entry["axis"])),
        objective_numerator=int(entry["objective_numerator"]),
    ) for entry in payload["profiles"])
    assert [(profile.n, profile.parity) for profile in profiles] == [
        (17, 0), (17, 1), (21, 0), (21, 1)
    ]
    return profiles


PROFILES = load_profiles()


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
    if profile.parity not in (0, 1):
        raise AssertionError("parity must be zero or one")
    expected_orbits = (profile.n + 1) // 2
    assert len(profile.axis) == expected_orbits
    assert len(profile.diagonal) == expected_orbits - profile.parity
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
