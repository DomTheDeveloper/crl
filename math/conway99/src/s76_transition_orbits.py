#!/usr/bin/env python3
"""Deterministically regenerate all 701 completed ``s = 76`` transition orbits.

The short-transition deficit is an 8-edge subset of the allowed 14-by-7
row/column incidence cells.  Positive row and column degrees cannot be one.
The acting group is exactly ``Aut(7 K2) = C2 wr S7``; no automorphism of the
unknown Conway graph is assumed.

The quotient is performed in two independently auditable stages:

1. swap the two rows inside each of the seven fixed pairs, then quotient the
   resulting support matrices by the simultaneous S7 action on row-pairs and
   columns;
2. enumerate every deranged perfect-matching completion of each support and
   quotient by its exact support stabilizer.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path

DEFICIT = 8
PAIR_PERMUTATIONS = tuple(permutations(range(7)))


def encode_rows(rows: list[int]) -> int:
    code = 0
    shift = 0
    for group in range(7):
        left, right = rows[2 * group], rows[2 * group + 1]
        if left > right:
            left, right = right, left
        code |= left << shift
        shift += 7
        code |= right << shift
        shift += 7
    return code


def decode_rows(code: int) -> list[int]:
    rows = []
    for _ in range(14):
        rows.append(code & 127)
        code >>= 7
    return rows


def permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    while mask:
        least = mask & -mask
        column = least.bit_length() - 1
        result |= 1 << permutation[column]
        mask ^= least
    return result


def transform_support(code: int, permutation: tuple[int, ...]) -> int:
    source = decode_rows(code)
    target = [0] * 14
    for group in range(7):
        destination = permutation[group]
        target[2 * destination] = permute_mask(source[2 * group], permutation)
        target[2 * destination + 1] = permute_mask(
            source[2 * group + 1], permutation
        )
    return encode_rows(target)


def enumerate_row_swap_normal_forms() -> tuple[set[int], int]:
    codes: set[int] = set()
    raw_count = 0
    rows = [0] * 14
    column_degrees = [0] * 7

    row_options = []
    for row in range(14):
        columns = [column for column in range(7) if column != row // 2]
        options = []
        for degree in range(2, 7):
            for subset in combinations(columns, degree):
                mask = sum(1 << column for column in subset)
                options.append((degree, mask, subset))
        row_options.append(options)

    def visit(row: int, remaining: int) -> None:
        nonlocal raw_count
        if row == 14:
            if remaining == 0 and all(degree != 1 for degree in column_degrees):
                raw_count += 1
                codes.add(encode_rows(rows))
            return

        # Leave this row intact.
        rows[row] = 0
        visit(row + 1, remaining)

        for degree, mask, subset in row_options[row]:
            if degree > remaining:
                continue
            rows[row] = mask
            for column in subset:
                column_degrees[column] += 1
            visit(row + 1, remaining - degree)
            for column in subset:
                column_degrees[column] -= 1
        rows[row] = 0

    visit(0, DEFICIT)
    return codes, raw_count


def skeleton_orbits(codes: set[int]) -> tuple[list[int], Counter[int]]:
    remaining = set(codes)
    representatives = []
    orbit_sizes: Counter[int] = Counter()
    while remaining:
        representative = min(remaining)
        orbit = {
            transform_support(representative, permutation)
            for permutation in PAIR_PERMUTATIONS
        }
        remaining.difference_update(orbit)
        representatives.append(representative)
        orbit_sizes[len(orbit)] += 1
    return representatives, orbit_sizes


@lru_cache(maxsize=None)
def deranged_matchings(columns: tuple[int, ...]) -> tuple[tuple[tuple[int, int], ...], ...]:
    vertices = tuple(vertex for column in columns for vertex in (2 * column, 2 * column + 1))
    answers = set()

    def visit(remaining: tuple[int, ...], pairs: tuple[tuple[int, int], ...]) -> None:
        if not remaining:
            answers.add(tuple(sorted(pairs)))
            return
        first = remaining[0]
        for position in range(1, len(remaining)):
            second = remaining[position]
            if second == (first ^ 1):
                continue
            rest = remaining[1:position] + remaining[position + 1 :]
            visit(rest, pairs + ((min(first, second), max(first, second)),))

    visit(vertices, ())
    return tuple(sorted(answers))


def row_matching_options(row: int, defect_mask: int) -> tuple[tuple[tuple[int, int], ...], ...]:
    own_column = row // 2
    intact = tuple(
        (2 * column, 2 * column + 1)
        for column in range(7)
        if column != own_column and not ((defect_mask >> column) & 1)
    )
    defective_columns = tuple(
        column for column in range(7) if (defect_mask >> column) & 1
    )
    if not defective_columns:
        return (tuple(sorted(intact)),)
    return tuple(
        tuple(sorted(intact + replacement))
        for replacement in deranged_matchings(defective_columns)
    )


def support_stabilizer(code: int) -> list[tuple[tuple[int, ...], int]]:
    target = decode_rows(code)
    stabilizer = []
    for permutation in PAIR_PERMUTATIONS:
        allowed_flips: list[tuple[int, ...]] = []
        valid = True
        for group in range(7):
            destination = permutation[group]
            left = permute_mask(target[2 * group], permutation)
            right = permute_mask(target[2 * group + 1], permutation)
            target_left = target[2 * destination]
            target_right = target[2 * destination + 1]
            choices = []
            if left == target_left and right == target_right:
                choices.append(0)
            if left == target_right and right == target_left:
                choices.append(1)
            if not choices:
                valid = False
                break
            allowed_flips.append(tuple(choices))
        if not valid:
            continue
        for choices in product(*allowed_flips):
            flip_mask = sum(bit << group for group, bit in enumerate(choices))
            stabilizer.append((permutation, flip_mask))
    return stabilizer


def transform_state(
    state: tuple[tuple[tuple[int, int], ...], ...],
    permutation: tuple[int, ...],
    flips: int,
) -> tuple[tuple[tuple[int, int], ...], ...]:
    target: list[tuple[tuple[int, int], ...] | None] = [None] * 14

    def endpoint_map(vertex: int) -> int:
        group, bit = divmod(vertex, 2)
        return 2 * permutation[group] + (bit ^ ((flips >> group) & 1))

    for row, matching in enumerate(state):
        group, bit = divmod(row, 2)
        target_row = 2 * permutation[group] + (bit ^ ((flips >> group) & 1))
        target[target_row] = tuple(
            sorted(
                (
                    min(endpoint_map(left), endpoint_map(right)),
                    max(endpoint_map(left), endpoint_map(right)),
                )
                for left, right in matching
            )
        )
    assert all(matching is not None for matching in target)
    return tuple(target)  # type: ignore[arg-type]


def completed_transition_orbits(
    skeletons: list[int],
) -> tuple[list[tuple[tuple[int, tuple[tuple[int, int], ...]], ...]], list[dict[str, int]]]:
    representatives = []
    summaries = []

    for skeleton_index, code in enumerate(skeletons):
        rows = decode_rows(code)
        options = [row_matching_options(row, rows[row]) for row in range(14)]
        states = set(product(*options))
        stabilizer = support_stabilizer(code)
        remaining = set(states)
        local_representatives = []

        while remaining:
            state = min(remaining)
            orbit = {
                transform_state(state, permutation, flips)
                for permutation, flips in stabilizer
            }
            present = orbit & remaining
            representative = min(present)
            remaining.difference_update(present)
            local_representatives.append(
                tuple(
                    (row, representative[row])
                    for row in range(14)
                    if rows[row]
                )
            )

        local_representatives.sort()
        representatives.extend(local_representatives)
        summaries.append(
            {
                "skeleton": skeleton_index,
                "support_code": code,
                "raw_completions": len(states),
                "support_stabilizer": len(stabilizer),
                "transition_orbits": len(local_representatives),
            }
        )

    return representatives, summaries


def json_representatives(representatives):
    return [
        [
            [row, [[left, right] for left, right in matching]]
            for row, matching in state
        ]
        for state in representatives
    ]


def canonical_bytes(representatives) -> bytes:
    return (
        json.dumps(
            json_representatives(representatives),
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode()


def audit() -> dict[str, object]:
    row_normal_forms, raw_supports = enumerate_row_swap_normal_forms()
    skeletons, skeleton_orbit_sizes = skeleton_orbits(row_normal_forms)
    representatives, summaries = completed_transition_orbits(skeletons)
    payload = canonical_bytes(representatives)

    assert raw_supports == 1_447_530
    assert len(row_normal_forms) == 164_535
    assert len(skeletons) == 105
    assert sum(item["raw_completions"] for item in summaries) == 11_872
    assert len(representatives) == 701
    assert hashlib.sha256(payload).hexdigest() == "802dd82ae32a7e43549d742a176778fd1f2fd55b8001d5f102eaf30b8c9a692c"

    return {
        "PASS": True,
        "deficit": DEFICIT,
        "raw_supports": raw_supports,
        "row_swap_normal_forms": len(row_normal_forms),
        "skeleton_orbits": len(skeletons),
        "skeleton_orbit_size_histogram": {
            str(size): count for size, count in sorted(skeleton_orbit_sizes.items())
        },
        "raw_matching_completions": sum(item["raw_completions"] for item in summaries),
        "completed_transition_orbits": len(representatives),
        "representatives_sha256": hashlib.sha256(payload).hexdigest(),
        "representatives_bytes": len(payload),
        "representatives": representatives,
        "skeleton_summaries": summaries,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out")
    parser.add_argument("--summary")
    args = parser.parse_args()
    report = audit()

    if args.out:
        Path(args.out).write_bytes(canonical_bytes(report["representatives"]))
    public = {key: value for key, value in report.items() if key != "representatives"}
    if args.summary:
        Path(args.summary).write_text(json.dumps(public, indent=2, sort_keys=True) + "\n")
    print(json.dumps(public, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
