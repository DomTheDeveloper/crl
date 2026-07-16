#!/usr/bin/env python3
"""Independently verify generated checkerboard CNF instances.

This checker deliberately imports none of the generator modules. It rebuilds the
eligible point set, tests collinearity with exact determinants, reconstructs the
canonical dynamic-programming cardinality counter, and checks the CNF clause by
clause. For the reduced n=21 instances it also rechecks the exact rational dual
profile and derives the candidate/slack restriction from first principles.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

PROFILES = {
    (21, 0): {
        "denominator": 75,
        "diagonal": (0, 0, 0, 10, 18, 24, 30, 36, 41, 44, 45),
        "axis": (28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0),
        "objective_numerator": 2476,
    },
    (21, 1): {
        "denominator": 48,
        "diagonal": (0, 0, 6, 11, 15, 18, 22, 25, 27, 28),
        "axis": (15, 12, 8, 6, 3, 2, 0, 0, 0, 0, 0),
        "objective_numerator": 1584,
    },
}


def parse_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variable_count = None
    declared_clauses = None
    clauses: list[tuple[int, ...]] = []
    pending: list[int] = []
    for raw in path.read_text(encoding="ascii").splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            if variable_count is not None:
                raise AssertionError("multiple DIMACS headers")
            fields = line.split()
            assert fields[:2] == ["p", "cnf"] and len(fields) == 4
            variable_count, declared_clauses = map(int, fields[2:])
            continue
        assert variable_count is not None, "clause before DIMACS header"
        for token in map(int, line.split()):
            if token == 0:
                clauses.append(tuple(pending))
                pending.clear()
            else:
                assert abs(token) <= variable_count
                pending.append(token)
    assert variable_count is not None and declared_clauses is not None
    assert not pending, "unterminated DIMACS clause"
    assert len(clauses) == declared_clauses
    return variable_count, clauses


def points(n: int, parity: int) -> list[tuple[int, int]]:
    return [(x, y) for x in range(n) for y in range(n) if (x + y) % 2 == parity]


def determinant(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def collinear_clauses(candidate_points: list[tuple[int, int]]) -> list[tuple[int, int, int]]:
    result: list[tuple[int, int, int]] = []
    for i, j, k in itertools.combinations(range(len(candidate_points)), 3):
        if determinant(candidate_points[i], candidate_points[j], candidate_points[k]) == 0:
            result.append((-(i + 1), -(j + 1), -(k + 1)))
    return result


def counter_layout(primary_count: int, bound: int) -> tuple[dict[tuple[int, int], int], int]:
    states: dict[tuple[int, int], int] = {}
    next_variable = primary_count
    for i in range(1, primary_count + 1):
        for j in range(1, min(i, bound) + 1):
            next_variable += 1
            states[(i, j)] = next_variable
    return states, next_variable


def at_least_clauses(primary_count: int, bound: int) -> tuple[list[tuple[int, ...]], int]:
    if bound <= 0:
        return [], primary_count
    if bound > primary_count:
        return [()], primary_count
    states, last_variable = counter_layout(primary_count, bound)
    clauses: list[tuple[int, ...]] = []
    for i in range(1, primary_count + 1):
        x = i
        for j in range(1, min(i, bound) + 1):
            current = states[(i, j)]
            same = states.get((i - 1, j))
            less: int | bool = True if j == 1 else states.get((i - 1, j - 1), False)
            if same is None:
                if less is False:
                    clauses.append((-current,))
                elif less is True:
                    clauses.extend(((-current, x), (-x, current)))
                else:
                    clauses.extend(((-current, x), (-current, less), (-x, -less, current)))
            else:
                clauses.append((-same, current))
                if less is True:
                    clauses.extend(((-x, current), (-current, same, x)))
                elif less is False:
                    clauses.append((-current, same))
                else:
                    clauses.extend(((-x, -less, current), (-current, same, x),
                                    (-current, same, less)))
    clauses.append((states[(primary_count, bound)],))
    return clauses, last_variable


def coverage_numerator(parity: int, point: tuple[int, int]) -> int:
    profile = PROFILES[(21, parity)]
    x, y = point
    folded_x = min(x, 20 - x)
    folded_y = min(y, 20 - y)
    axis = profile["axis"][folded_x] + profile["axis"][folded_y]
    total = x + y
    difference = abs(x - y)
    if parity == 0:
        sum_index = min(total, 40 - total) // 2
        difference_index = 10 - difference // 2
    else:
        sum_index = (min(total, 40 - total) - 1) // 2
        difference_index = 10 - (difference + 1) // 2
    return axis + profile["diagonal"][sum_index] + profile["diagonal"][difference_index]


def reduced_n21(parity: int) -> tuple[list[tuple[int, int]], list[int], int]:
    profile = PROFILES[(21, parity)]
    all_points = points(21, parity)
    slacks = [coverage_numerator(parity, point) - profile["denominator"]
              for point in all_points]
    assert min(slacks) >= 0
    objective_gap = profile["objective_numerator"] - 33 * profile["denominator"]
    assert objective_gap == (1 if parity == 0 else 0)
    selected = [(point, slack) for point, slack in zip(all_points, slacks)
                if slack <= objective_gap]
    candidates = [point for point, _ in selected]
    candidate_slacks = [slack for _, slack in selected]
    assert len(candidates) == (136 if parity == 0 else 132)
    return candidates, candidate_slacks, objective_gap


def verify_full(metadata: dict[str, object]) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]], list[tuple[int, ...]], int]:
    n = int(metadata["n"])
    parity = int(metadata["parity"])
    bound = int(metadata["minimum_selected"])
    candidate_points = points(n, parity)
    geometric = collinear_clauses(candidate_points)
    counter, final_variable = at_least_clauses(len(candidate_points), bound)
    assert metadata["format"] == "checkerboard-ntil-cnf-v1"
    assert int(metadata["point_count"]) == len(candidate_points)
    assert int(metadata["collinear_triple_clause_count"]) == len(geometric)
    assert metadata["points"] == [list(point) for point in candidate_points]
    return geometric, counter, [], final_variable


def verify_reduced(metadata: dict[str, object]) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]], list[tuple[int, ...]], int]:
    parity = int(metadata["parity"])
    candidates, slacks, budget = reduced_n21(parity)
    geometric = collinear_clauses(candidates)
    counter, final_variable = at_least_clauses(len(candidates), 33)
    slack_clauses: list[tuple[int, ...]] = []
    if budget == 1:
        one_slack = [index + 1 for index, slack in enumerate(slacks) if slack == 1]
        slack_clauses = [(-left, -right) for left, right in itertools.combinations(one_slack, 2)]
    else:
        assert all(slack == 0 for slack in slacks)
    assert metadata["format"] == "checkerboard-n21-slack-reduced-cnf-v1"
    assert int(metadata["target"]) == 33
    assert int(metadata["dual_slack_budget"]) == budget
    assert int(metadata["candidate_count"]) == len(candidates)
    assert int(metadata["collinear_triple_clause_count"]) == len(geometric)
    assert int(metadata["slack_clause_count"]) == len(slack_clauses)
    assert metadata["candidates"] == [list(point) for point in candidates]
    assert metadata["candidate_slacks"] == slacks
    return geometric, counter, slack_clauses, final_variable


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    args = parser.parse_args()

    metadata = json.loads(args.metadata.read_text(encoding="utf-8"))
    digest = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    assert digest == metadata["cnf_sha256"]
    variable_count, clauses = parse_dimacs(args.cnf)
    if metadata["format"] == "checkerboard-ntil-cnf-v1":
        geometric, counter, slack, expected_variables = verify_full(metadata)
    elif metadata["format"] == "checkerboard-n21-slack-reduced-cnf-v1":
        geometric, counter, slack, expected_variables = verify_reduced(metadata)
    else:
        raise AssertionError(f"unknown metadata format: {metadata['format']!r}")

    expected = geometric + counter + slack
    assert variable_count == expected_variables == int(metadata["variable_count"])
    assert len(clauses) == len(expected) == int(metadata["clause_count"])
    geometric_end = len(geometric)
    counter_end = geometric_end + len(counter)
    assert Counter(clauses[:geometric_end]) == Counter(geometric), "geometric clauses differ"
    assert clauses[geometric_end:counter_end] == counter, "cardinality clauses differ"
    assert Counter(clauses[counter_end:]) == Counter(slack), "slack clauses differ"
    print(json.dumps({
        "status": "PASS",
        "format": metadata["format"],
        "n": int(metadata["n"]),
        "parity": int(metadata["parity"]),
        "variables": variable_count,
        "clauses": len(clauses),
        "sha256": digest,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
