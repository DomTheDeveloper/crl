#!/usr/bin/env python3
"""Deterministic exhaustive proof of the n=21 checkerboard upper bounds.

The checker uses only Python's standard library and exact integer arithmetic.
It reconstructs the exact rational dual reductions from ``dual_profiles.json``
and proves that no 33-point all-slope no-three-in-line set exists in either
parity class of the 21 by 21 board.

The proof search has no heuristic acceptance condition: every branch is an
exhaustive partition of the remaining assignments on an exact-cardinality
line. A branch closes only by an integer cardinality contradiction. Memoization
only reuses previously closed assignment states for the same constraint system.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

Point = tuple[int, int]


@dataclass(frozen=True)
class Profile:
    n: int
    parity: int
    denominator: int
    diagonal: tuple[int, ...]
    axis: tuple[int, ...]
    objective_numerator: int


@dataclass(frozen=True)
class ExactConstraint:
    name: str
    mask: int
    target: int


@dataclass(frozen=True)
class SearchResult:
    nodes: int
    closed_states: int
    elapsed_seconds: float


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def load_profiles(path: Path) -> dict[tuple[int, int], Profile]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    require(payload.get("format") == "checkerboard-four-direction-dual-profiles-v1",
            "unexpected dual profile format")
    result: dict[tuple[int, int], Profile] = {}
    for entry in payload["profiles"]:
        profile = Profile(
            n=int(entry["n"]),
            parity=int(entry["parity"]),
            denominator=int(entry["denominator"]),
            diagonal=tuple(map(int, entry["diagonal"])),
            axis=tuple(map(int, entry["axis"])),
            objective_numerator=int(entry["objective_numerator"]),
        )
        result[(profile.n, profile.parity)] = profile
    require((21, 0) in result and (21, 1) in result,
            "the n=21 profiles are missing")
    return result


def board_points(n: int, parity: int) -> list[Point]:
    return [(x, y) for x in range(n) for y in range(n)
            if (x + y) % 2 == parity]


def four_line_weights(profile: Profile, point: Point) -> tuple[int, int, int, int]:
    n, parity = profile.n, profile.parity
    middle = (n - 1) // 2
    x, y = point
    row = profile.axis[min(x, n - 1 - x)]
    column = profile.axis[min(y, n - 1 - y)]
    total = x + y
    difference = abs(x - y)
    if parity == 0:
        require(total % 2 == 0 and difference % 2 == 0,
                f"wrong parity point {point}")
        sum_index = min(total, 2 * n - 2 - total) // 2
        difference_index = middle - difference // 2
    else:
        require(total % 2 == 1 and difference % 2 == 1,
                f"wrong parity point {point}")
        sum_index = (min(total, 2 * n - 2 - total) - 1) // 2
        difference_index = middle - (difference + 1) // 2
    return row, column, profile.diagonal[sum_index], profile.diagonal[difference_index]


def coverage_numerator(profile: Profile, point: Point) -> int:
    return sum(four_line_weights(profile, point))


def mask_of(indices: Iterable[int]) -> int:
    result = 0
    for index in indices:
        result |= 1 << index
    return result


def normalized_line_key(left: Point, right: Point) -> tuple[int, int, int]:
    x1, y1 = left
    x2, y2 = right
    dx, dy = x2 - x1, y2 - y1
    divisor = math.gcd(abs(dx), abs(dy))
    require(divisor != 0, "distinct points are required")
    a, b = dy // divisor, -dx // divisor
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * x1 + b * y1


def maximal_line_masks(points: Sequence[Point]) -> tuple[int, ...]:
    groups: dict[tuple[int, int, int], set[int]] = {}
    for left, right in itertools.combinations(range(len(points)), 2):
        key = normalized_line_key(points[left], points[right])
        groups.setdefault(key, set()).update((left, right))
    masks = {mask_of(indices) for indices in groups.values() if len(indices) >= 3}
    return tuple(sorted(masks, key=lambda mask: (mask.bit_count(), mask)))


def positive_line_constraints(profile: Profile,
                              candidates: Sequence[Point]) -> tuple[ExactConstraint, ...]:
    n, parity = profile.n, profile.parity
    middle = (n - 1) // 2
    constraints: list[ExactConstraint] = []

    for x in range(n):
        weight = profile.axis[min(x, n - 1 - x)]
        if weight > 0:
            constraints.append(ExactConstraint(
                f"R{x}", mask_of(i for i, (xx, _) in enumerate(candidates) if xx == x), 2))
    for y in range(n):
        weight = profile.axis[min(y, n - 1 - y)]
        if weight > 0:
            constraints.append(ExactConstraint(
                f"C{y}", mask_of(i for i, (_, yy) in enumerate(candidates) if yy == y), 2))
    for total in range(2 * n - 1):
        if total % 2 != parity:
            continue
        if parity == 0:
            index = min(total, 2 * n - 2 - total) // 2
        else:
            index = (min(total, 2 * n - 2 - total) - 1) // 2
        if profile.diagonal[index] > 0:
            constraints.append(ExactConstraint(
                f"S{total}",
                mask_of(i for i, (x, y) in enumerate(candidates) if x + y == total), 2))
    for difference in range(-(n - 1), n):
        if difference % 2 != parity:
            continue
        distance = abs(difference)
        if parity == 0:
            index = middle - distance // 2
        else:
            index = middle - (distance + 1) // 2
        if profile.diagonal[index] > 0:
            constraints.append(ExactConstraint(
                f"D{difference}",
                mask_of(i for i, (x, y) in enumerate(candidates)
                        if x - y == difference), 2))
    require(all(constraint.mask.bit_count() >= constraint.target
                for constraint in constraints), "malformed exact line constraint")
    return tuple(constraints)


def transform(point: Point, element: int, n: int = 21) -> Point:
    require(0 <= element < 8, "D4 element must lie in 0..7")
    center = (n - 1) // 2
    x, y = point
    a, b = x - center, y - center
    images = (
        (a, b), (-b, a), (-a, -b), (b, -a),
        (-a, b), (a, -b), (b, a), (-b, -a),
    )
    u, v = images[element]
    return u + center, v + center


class ExhaustiveSolver:
    """Exact-cardinality propagation plus exhaustive line-choice branching."""

    def __init__(self, exact: Sequence[ExactConstraint], at_most_two: Sequence[int]):
        self.exact = tuple(exact)
        self.at_most_two = tuple(at_most_two)
        self.closed: set[tuple[int, int]] = set()
        self.nodes = 0

    def propagate(self, true_mask: int, false_mask: int) -> tuple[int, int] | None:
        while True:
            changed = False
            for constraint in self.exact:
                selected = (true_mask & constraint.mask).bit_count()
                undecided = constraint.mask & ~(true_mask | false_mask)
                undecided_count = undecided.bit_count()
                if selected > constraint.target or selected + undecided_count < constraint.target:
                    return None
                if undecided and selected == constraint.target:
                    false_mask |= undecided
                    changed = True
                elif undecided and selected + undecided_count == constraint.target:
                    true_mask |= undecided
                    changed = True
            for line_mask in self.at_most_two:
                selected = (true_mask & line_mask).bit_count()
                if selected > 2:
                    return None
                if selected == 2:
                    undecided = line_mask & ~(true_mask | false_mask)
                    if undecided:
                        false_mask |= undecided
                        changed = True
            if true_mask & false_mask:
                return None
            if not changed:
                return true_mask, false_mask

    def search(self, true_mask: int, false_mask: int) -> bool:
        """Return True exactly when a satisfying completion exists."""
        self.nodes += 1
        propagated = self.propagate(true_mask, false_mask)
        if propagated is None:
            return False
        true_mask, false_mask = propagated
        state = (true_mask, false_mask)
        if state in self.closed:
            return False

        best: tuple[int, int, int] | None = None
        for constraint in self.exact:
            selected = (true_mask & constraint.mask).bit_count()
            undecided = constraint.mask & ~(true_mask | false_mask)
            required = constraint.target - selected
            ways = math.comb(undecided.bit_count(), required)
            if ways > 1 and (best is None or ways < best[0]):
                best = ways, undecided, required

        if best is None:
            # Every exact constraint is satisfied and propagation has checked
            # every at-most-two line, so this is a genuine completion.
            return True

        _, undecided, required = best
        indices = tuple(i for i in range(undecided.bit_length())
                        if (undecided >> i) & 1)
        for chosen in itertools.combinations(indices, required):
            chosen_mask = mask_of(chosen)
            if self.search(true_mask | chosen_mask,
                           false_mask | (undecided ^ chosen_mask)):
                return True
        self.closed.add(state)
        return False

    def prove_unsat(self, true_mask: int, false_mask: int) -> SearchResult:
        started = time.perf_counter()
        satisfiable = self.search(true_mask, false_mask)
        elapsed = time.perf_counter() - started
        require(not satisfiable, "the exhaustive search found a completion")
        return SearchResult(self.nodes, len(self.closed), elapsed)


def candidate_data(profile: Profile) -> tuple[list[Point], list[int]]:
    all_points = board_points(profile.n, profile.parity)
    slacks = [coverage_numerator(profile, point) - profile.denominator
              for point in all_points]
    require(min(slacks) >= 0, "dual profile has negative point slack")
    gap = profile.objective_numerator - 33 * profile.denominator
    require(gap in (0, 1), "unexpected n=21 dual objective gap")
    chosen = [(point, slack) for point, slack in zip(all_points, slacks)
              if slack <= gap]
    return [point for point, _ in chosen], [slack for _, slack in chosen]


def point_orbits(points: Sequence[Point]) -> dict[Point, tuple[Point, ...]]:
    universe = set(points)
    result: dict[Point, list[Point]] = {}
    for point in points:
        images = {transform(point, element) for element in range(8)}
        require(images <= universe, "candidate subset is not D4-invariant")
        representative = min(images)
        result.setdefault(representative, []).append(point)
    return {representative: tuple(sorted(orbit))
            for representative, orbit in sorted(result.items())}


def canonical_special_pair(sum_point: Point, difference_point: Point,
                           zero_sum: set[Point], zero_difference: set[Point]) -> tuple[Point, Point]:
    images: list[tuple[Point, Point]] = []
    for element in range(8):
        left = transform(sum_point, element)
        right = transform(difference_point, element)
        if left in zero_sum and right in zero_difference:
            images.append((left, right))
        elif left in zero_difference and right in zero_sum:
            images.append((right, left))
        else:
            raise AssertionError("D4 did not preserve the two special-line classes")
    return min(images)


def prove_parity_one(profile: Profile) -> tuple[int, list[tuple[tuple[Point, Point], SearchResult]]]:
    candidates, slacks = candidate_data(profile)
    require(len(candidates) == 132 and set(slacks) == {0},
            "unexpected parity-one candidate reduction")
    exact = positive_line_constraints(profile, candidates)
    all_lines = maximal_line_masks(candidates)
    require(len(exact) == 56 and len(all_lines) == 508,
            "unexpected parity-one line census")

    weights = [four_line_weights(profile, point) for point in candidates]
    zero_sum_indices = [i for i, value in enumerate(weights) if value[2] == 0]
    zero_difference_indices = [i for i, value in enumerate(weights) if value[3] == 0]
    require(len(zero_sum_indices) == len(zero_difference_indices) == 8,
            "unexpected zero-diagonal candidate census")
    require(all(sum(weight == 0 for weight in value) <= 1 for value in weights),
            "a parity-one candidate lies on multiple zero-weight lines")

    zero_sum = {candidates[i] for i in zero_sum_indices}
    zero_difference = {candidates[i] for i in zero_difference_indices}
    pair_orbits: dict[tuple[Point, Point], list[tuple[Point, Point]]] = {}
    for sum_point in sorted(zero_sum):
        for difference_point in sorted(zero_difference):
            representative = canonical_special_pair(
                sum_point, difference_point, zero_sum, zero_difference)
            pair_orbits.setdefault(representative, []).append((sum_point, difference_point))
    require(len(pair_orbits) == 10 and sum(map(len, pair_orbits.values())) == 64,
            "unexpected D4 orbit census for the special point pair")

    index = {point: i for i, point in enumerate(candidates)}
    zero_sum_mask = mask_of(index[point] for point in zero_sum)
    zero_difference_mask = mask_of(index[point] for point in zero_difference)
    results: list[tuple[tuple[Point, Point], SearchResult]] = []
    total_nodes = 0
    for representative in sorted(pair_orbits):
        sum_point, difference_point = representative
        true_mask = (1 << index[sum_point]) | (1 << index[difference_point])
        false_mask = ((zero_sum_mask & ~(1 << index[sum_point])) |
                      (zero_difference_mask & ~(1 << index[difference_point])))
        solver = ExhaustiveSolver(exact, all_lines)
        result = solver.prove_unsat(true_mask, false_mask)
        total_nodes += result.nodes
        results.append((representative, result))
    require(total_nodes == 13239,
            f"parity-one search fingerprint changed: {total_nodes} nodes")
    return total_nodes, results


def transformed_mask(mask: int, candidates: Sequence[Point], element: int) -> int:
    index = {point: i for i, point in enumerate(candidates)}
    return mask_of(index[transform(candidates[i], element)]
                   for i in range(len(candidates)) if (mask >> i) & 1)


def prove_parity_zero(profile: Profile) -> tuple[int, list[tuple[str, SearchResult]]]:
    candidates, slacks = candidate_data(profile)
    require(len(candidates) == 136 and slacks.count(0) == 116 and slacks.count(1) == 20,
            "unexpected parity-zero candidate reduction")
    exact_two = positive_line_constraints(profile, candidates)
    all_lines = maximal_line_masks(candidates)
    require(len(exact_two) == 58 and len(all_lines) == 548,
            "unexpected parity-zero line census")

    one_slack_indices = [i for i, slack in enumerate(slacks) if slack == 1]
    one_slack_points = [candidates[i] for i in one_slack_indices]
    one_slack_mask = mask_of(one_slack_indices)
    orbits = point_orbits(one_slack_points)
    require([(representative, len(orbit)) for representative, orbit in orbits.items()] == [
        ((0, 8), 8), ((0, 10), 4), ((3, 9), 8)
    ], "unexpected D4 orbit census for one-slack points")

    index = {point: i for i, point in enumerate(candidates)}
    results: list[tuple[str, SearchResult]] = []
    total_nodes = 0

    # Case sigma=1: exactly one one-slack point is selected, and every
    # positive-weight line is saturated at two selected points.
    for representative in orbits:
        chosen = index[representative]
        solver = ExhaustiveSolver(exact_two, all_lines)
        result = solver.prove_unsat(
            1 << chosen, one_slack_mask & ~(1 << chosen))
        total_nodes += result.nodes
        results.append((f"slack-one representative {representative}", result))

    # Case sigma=0: no one-slack point is selected. The weighted capacity
    # deficit is one, so exactly one weight-one line has count one and every
    # other positive line has count two. The four weight-one lines form one D4
    # orbit, represented by R6.
    weight_one_names = {"R6", "R14", "C6", "C14"}
    exact_by_name = {constraint.name: constraint for constraint in exact_two}
    require({name for name in exact_by_name
             if (name.startswith("R") or name.startswith("C")) and
             profile.axis[min(int(name[1:]), profile.n - 1 - int(name[1:]))] == 1}
            == weight_one_names, "unexpected weight-one line set")
    representative_mask = exact_by_name["R6"].mask
    orbit_masks = {transformed_mask(representative_mask, candidates, element)
                   for element in range(8)}
    require(orbit_masks == {exact_by_name[name].mask for name in weight_one_names},
            "the four weight-one lines are not one D4 orbit")

    sigma_zero_exact = tuple(ExactConstraint(
        constraint.name, constraint.mask,
        1 if constraint.name == "R6" else 2)
        for constraint in exact_two)
    solver = ExhaustiveSolver(sigma_zero_exact, all_lines)
    result = solver.prove_unsat(0, one_slack_mask)
    total_nodes += result.nodes
    results.append(("zero slack, deficient line R6", result))

    require(total_nodes == 13560,
            f"parity-zero search fingerprint changed: {total_nodes} nodes")
    return total_nodes, results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profiles", type=Path,
        default=Path(__file__).with_name("dual_profiles.json"))
    args = parser.parse_args()
    profiles = load_profiles(args.profiles)

    started = time.perf_counter()
    zero_nodes, zero_results = prove_parity_zero(profiles[(21, 0)])
    one_nodes, one_results = prove_parity_one(profiles[(21, 1)])

    for label, result in zero_results:
        print("PASS", "parity=0", f"case={label!r}", f"nodes={result.nodes}",
              f"closed={result.closed_states}",
              f"seconds={result.elapsed_seconds:.6f}")
    for pair, result in one_results:
        print("PASS", "parity=1", f"pair={pair}", f"nodes={result.nodes}",
              f"closed={result.closed_states}",
              f"seconds={result.elapsed_seconds:.6f}")

    elapsed = time.perf_counter() - started
    print("VERIFIED D_mono(21,0) <= 32", f"nodes={zero_nodes}")
    print("VERIFIED D_mono(21,1) <= 32", f"nodes={one_nodes}")
    print("ALL N=21 EXHAUSTIVE UPPER BOUNDS VERIFIED",
          f"nodes={zero_nodes + one_nodes}", f"seconds={elapsed:.6f}")


if __name__ == "__main__":
    main()
