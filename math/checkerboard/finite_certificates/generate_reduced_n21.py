#!/usr/bin/env python3
"""Generate the exact slack-reduced n=21 checkerboard UNSAT instances.

The candidate point sets are regenerated from the compact rational dual
profiles, not read from a stored matrix. Every maximal Euclidean line meeting
at least three candidates is regenerated from exact integer line keys.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

from generate_cnf import CnfBuilder, add_at_least
from verify_profiles import PROFILES, Profile, coverage_numerator, points, verify


def normalized_line_key(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int, int]:
    x1, y1 = p
    x2, y2 = q
    dx, dy = x2 - x1, y2 - y1
    divisor = math.gcd(abs(dx), abs(dy))
    if divisor == 0:
        raise ValueError("distinct points required")
    a, b = dy // divisor, -dx // divisor
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * x1 + b * y1


def maximal_candidate_lines(candidates: list[tuple[int, int]]) -> list[tuple[int, ...]]:
    groups: dict[tuple[int, int, int], set[int]] = {}
    for i, j in itertools.combinations(range(len(candidates)), 2):
        groups.setdefault(normalized_line_key(candidates[i], candidates[j]), set()).update((i, j))
    return sorted({tuple(sorted(indices)) for indices in groups.values()
                   if len(indices) >= 3}, key=lambda line: (len(line), line))


def profile_for(parity: int) -> Profile:
    return next(profile for profile in PROFILES
                if profile.n == 21 and profile.parity == parity)


def build(parity: int) -> tuple[list[tuple[int, int]], list[int], list[tuple[int, ...]], CnfBuilder, dict[str, object]]:
    profile = profile_for(parity)
    verify(profile)
    all_points = points(21, parity)
    all_slacks = [coverage_numerator(profile, point) - profile.denominator
                  for point in all_points]
    if parity == 0:
        selected = [(point, slack) for point, slack in zip(all_points, all_slacks)
                    if slack <= 1]
    else:
        selected = [(point, slack) for point, slack in zip(all_points, all_slacks)
                    if slack == 0]
    candidates = [point for point, _ in selected]
    slacks = [slack for _, slack in selected]
    expected_candidates = 136 if parity == 0 else 132
    assert len(candidates) == expected_candidates

    lines = maximal_candidate_lines(candidates)
    expected_lines = 548 if parity == 0 else 508
    assert len(lines) == expected_lines

    builder = CnfBuilder(len(candidates))
    triple_clause_count = 0
    for line in lines:
        for i, j, k in itertools.combinations(line, 3):
            builder.add(-(i + 1), -(j + 1), -(k + 1))
            triple_clause_count += 1

    # A feasible set of size >=33 contains a feasible subset of size exactly
    # 33. Encoding only >=33 therefore gives the smallest monotone decision
    # instance with the same satisfiability status.
    cardinality_auxiliaries = add_at_least(builder, list(range(1, len(candidates) + 1)), 33)

    slack_clause_count = 0
    if parity == 0:
        one_slack_variables = [index + 1 for index, slack in enumerate(slacks) if slack == 1]
        assert len(one_slack_variables) == 20
        for left, right in itertools.combinations(one_slack_variables, 2):
            builder.add(-left, -right)
            slack_clause_count += 1
    else:
        assert all(slack == 0 for slack in slacks)

    metadata: dict[str, object] = {
        "format": "checkerboard-n21-slack-reduced-cnf-v1",
        "n": 21,
        "parity": parity,
        "target": 33,
        "profile_denominator": profile.denominator,
        "profile_objective_numerator": profile.objective_numerator,
        "dual_slack_budget": 1 if parity == 0 else 0,
        "candidate_count": len(candidates),
        "maximal_line_count": len(lines),
        "collinear_triple_clause_count": triple_clause_count,
        "slack_clause_count": slack_clause_count,
        "cardinality_auxiliary_count": cardinality_auxiliaries,
        "variable_count": builder.variable_count,
        "clause_count": len(builder.clauses),
        "candidates": candidates,
        "candidate_slacks": slacks,
        "maximal_lines": lines,
    }
    return candidates, slacks, lines, builder, metadata


def write_dimacs(path: Path, builder: CnfBuilder) -> str:
    with path.open("w", encoding="ascii", newline="\n") as handle:
        handle.write(f"p cnf {builder.variable_count} {len(builder.clauses)}\n")
        for clause in builder.clauses:
            handle.write(" ".join(map(str, clause)))
            if clause:
                handle.write(" ")
            handle.write("0\n")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--parity", type=int, choices=(0, 1), required=True)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    args = parser.parse_args()
    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    _, _, _, builder, metadata = build(args.parity)
    metadata["cnf_sha256"] = write_dimacs(args.cnf, builder)
    args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    compact = {key: value for key, value in metadata.items()
               if key not in {"candidates", "candidate_slacks", "maximal_lines"}}
    print(json.dumps(compact, sort_keys=True))


if __name__ == "__main__":
    main()
