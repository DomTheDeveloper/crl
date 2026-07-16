#!/usr/bin/env python3
"""Independent D4-invariance audit for the n=21 exhaustive reductions."""
from __future__ import annotations

from pathlib import Path

from verify_exhaustive_upper_bounds import (
    candidate_data,
    load_profiles,
    maximal_line_masks,
    positive_line_constraints,
    transform,
    transformed_mask,
)


def check(parity: int) -> None:
    profiles = load_profiles(Path(__file__).with_name("dual_profiles.json"))
    candidates, _ = candidate_data(profiles[(21, parity)])
    exact = positive_line_constraints(profiles[(21, parity)], candidates)
    lines = maximal_line_masks(candidates)
    candidate_set = set(candidates)
    exact_set = {(constraint.mask, constraint.target) for constraint in exact}
    line_set = set(lines)

    for element in range(8):
        images = {transform(point, element) for point in candidates}
        if images != candidate_set:
            raise AssertionError((parity, element, "candidate set"))
        for constraint in exact:
            image = transformed_mask(constraint.mask, candidates, element)
            if (image, constraint.target) not in exact_set:
                raise AssertionError((parity, element, constraint.name))
        for line in lines:
            if transformed_mask(line, candidates, element) not in line_set:
                raise AssertionError((parity, element, "all-slope line"))

    print(f"PASS parity={parity} candidates={len(candidates)} "
          f"exact_lines={len(exact)} all_slope_lines={len(lines)}")


def main() -> None:
    check(0)
    check(1)
    print("ALL D4 SYMMETRY REDUCTIONS VERIFIED")


if __name__ == "__main__":
    main()
