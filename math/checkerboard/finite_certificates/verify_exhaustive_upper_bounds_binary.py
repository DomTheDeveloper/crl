#!/usr/bin/env python3
"""Independent binary-branching replay of the n=21 exhaustive proof.

This checker shares only the exact geometric reduction helpers with
``verify_exhaustive_upper_bounds.py``. Its propagation, memoization, and branch
partition are separately implemented: each unresolved state branches on one
Boolean variable rather than enumerating a whole exact-line choice.
"""
from __future__ import annotations

import time
from pathlib import Path

from verify_exhaustive_upper_bounds import (
    ExactConstraint,
    candidate_data,
    canonical_special_pair,
    four_line_weights,
    load_profiles,
    mask_of,
    maximal_line_masks,
    point_orbits,
    positive_line_constraints,
    transformed_mask,
)


class BinarySearch:
    def __init__(self, exact: tuple[ExactConstraint, ...], lines: tuple[int, ...]):
        self.exact = exact
        self.lines = lines
        self.dead: set[tuple[int, int]] = set()
        self.nodes = 0

    def close(self, selected: int, rejected: int) -> tuple[int, int] | None:
        while True:
            changed = False
            for equation in self.exact:
                have = (selected & equation.mask).bit_count()
                open_mask = equation.mask & ~(selected | rejected)
                available = open_mask.bit_count()
                need = equation.target - have
                if need < 0 or need > available:
                    return None
                if open_mask and need == 0:
                    rejected |= open_mask
                    changed = True
                elif open_mask and need == available:
                    selected |= open_mask
                    changed = True
            for line in self.lines:
                have = (selected & line).bit_count()
                if have > 2:
                    return None
                if have == 2:
                    open_mask = line & ~(selected | rejected)
                    if open_mask:
                        rejected |= open_mask
                        changed = True
            if selected & rejected:
                return None
            if not changed:
                return selected, rejected

    def solve(self, selected: int, rejected: int) -> bool:
        self.nodes += 1
        state = self.close(selected, rejected)
        if state is None:
            return False
        selected, rejected = state
        if state in self.dead:
            return False

        tightest: tuple[int, int] | None = None
        for equation in self.exact:
            have = (selected & equation.mask).bit_count()
            open_mask = equation.mask & ~(selected | rejected)
            need = equation.target - have
            if 0 < need < open_mask.bit_count():
                choices = open_mask.bit_count()
                if tightest is None or choices < tightest[0]:
                    tightest = choices, open_mask
        if tightest is None:
            return True

        open_mask = tightest[1]
        bit = open_mask & -open_mask
        if self.solve(selected | bit, rejected):
            return True
        if self.solve(selected, rejected | bit):
            return True
        self.dead.add(state)
        return False

    def prove(self, selected: int, rejected: int) -> tuple[int, int, float]:
        started = time.perf_counter()
        if self.solve(selected, rejected):
            raise AssertionError("binary exhaustive replay found a completion")
        return self.nodes, len(self.dead), time.perf_counter() - started


def parity_one(profile):
    candidates, slacks = candidate_data(profile)
    if len(candidates) != 132 or set(slacks) != {0}:
        raise AssertionError("parity-one candidates")
    exact = positive_line_constraints(profile, candidates)
    lines = maximal_line_masks(candidates)
    weights = [four_line_weights(profile, point) for point in candidates]
    zero_sum = {candidates[i] for i, value in enumerate(weights) if value[2] == 0}
    zero_difference = {candidates[i] for i, value in enumerate(weights) if value[3] == 0}

    orbits = {}
    for left in zero_sum:
        for right in zero_difference:
            representative = canonical_special_pair(left, right, zero_sum, zero_difference)
            orbits.setdefault(representative, []).append((left, right))
    if len(orbits) != 10 or sum(map(len, orbits.values())) != 64:
        raise AssertionError("parity-one pair orbits")

    index = {point: i for i, point in enumerate(candidates)}
    sum_mask = mask_of(index[point] for point in zero_sum)
    difference_mask = mask_of(index[point] for point in zero_difference)
    total = 0
    results = []
    for representative in sorted(orbits):
        left, right = representative
        left_bit = 1 << index[left]
        right_bit = 1 << index[right]
        selected = left_bit | right_bit
        rejected = ((sum_mask & ~left_bit) | (difference_mask & ~right_bit))
        result = BinarySearch(exact, lines).prove(selected, rejected)
        total += result[0]
        results.append((representative, result))
    if total != 4890:
        raise AssertionError(f"binary parity-one fingerprint {total}")
    return total, results


def parity_zero(profile):
    candidates, slacks = candidate_data(profile)
    if len(candidates) != 136 or slacks.count(1) != 20:
        raise AssertionError("parity-zero candidates")
    exact = positive_line_constraints(profile, candidates)
    lines = maximal_line_masks(candidates)
    one_indices = [i for i, slack in enumerate(slacks) if slack == 1]
    one_mask = mask_of(one_indices)
    one_points = [candidates[i] for i in one_indices]
    orbits = point_orbits(one_points)
    if [(point, len(orbit)) for point, orbit in orbits.items()] != [
        ((0, 8), 8), ((0, 10), 4), ((3, 9), 8)
    ]:
        raise AssertionError("parity-zero point orbits")

    index = {point: i for i, point in enumerate(candidates)}
    total = 0
    results = []
    for representative in orbits:
        bit = 1 << index[representative]
        result = BinarySearch(exact, lines).prove(bit, one_mask & ~bit)
        total += result[0]
        results.append((f"slack-one {representative}", result))

    by_name = {equation.name: equation for equation in exact}
    weight_one = {"R6", "R14", "C6", "C14"}
    orbit = {transformed_mask(by_name["R6"].mask, candidates, element)
             for element in range(8)}
    if orbit != {by_name[name].mask for name in weight_one}:
        raise AssertionError("weight-one line orbit")
    zero_exact = tuple(ExactConstraint(
        equation.name, equation.mask, 1 if equation.name == "R6" else 2)
        for equation in exact)
    result = BinarySearch(zero_exact, lines).prove(0, one_mask)
    total += result[0]
    results.append(("zero slack, deficient R6", result))

    if total != 13160:
        raise AssertionError(f"binary parity-zero fingerprint {total}")
    return total, results


def main() -> None:
    profiles = load_profiles(Path(__file__).with_name("dual_profiles.json"))
    zero_nodes, zero_results = parity_zero(profiles[(21, 0)])
    one_nodes, one_results = parity_one(profiles[(21, 1)])
    for label, (nodes, closed, seconds) in zero_results:
        print("PASS", "binary", "parity=0", f"case={label!r}",
              f"nodes={nodes}", f"closed={closed}", f"seconds={seconds:.6f}")
    for pair, (nodes, closed, seconds) in one_results:
        print("PASS", "binary", "parity=1", f"pair={pair}",
              f"nodes={nodes}", f"closed={closed}", f"seconds={seconds:.6f}")
    print("BINARY VERIFIED D_mono(21,0) <= 32", f"nodes={zero_nodes}")
    print("BINARY VERIFIED D_mono(21,1) <= 32", f"nodes={one_nodes}")
    print("ALL BINARY EXHAUSTIVE UPPER BOUNDS VERIFIED",
          f"nodes={zero_nodes + one_nodes}")


if __name__ == "__main__":
    main()
