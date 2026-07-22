#!/usr/bin/env python3
"""Exact ``S3`` quotient reduction for the exceptional ``s = 76`` cores.

The curvature and six-path audits leave 51 supports in core profile 39 and 50
in profile 40.  After fixing a spanning-tree gauge, the ``C3`` coordinate of
an ``S3 = C3 semidirect C2`` edge connection is constrained by:

* zero ``C3`` holonomy on every even triangle;
* equality of the two odd based holonomies incident with a curved central edge.

For every one of the 101 supports this homogeneous system has nullity exactly
one.  Thus each support has precisely three gauge-fixed quotient connections.
"""
from __future__ import annotations

import json
from collections import Counter, deque
from itertools import combinations

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit
from s76_curvature_support_audit import (
    EDGE_TRIANGLES,
    TRIANGLES,
    class_assignment_exists,
    gf2_nullspace,
    support_space,
)
from s76_path_parity_audit import solve_linear


def rank_mod_3(rows: list[list[int]], columns: int) -> int:
    work = [row[:] for row in rows if any(value % 3 for value in row)]
    rank = 0
    for column in range(columns):
        pivot = next(
            (index for index in range(rank, len(work)) if work[index][column] % 3),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        scale = 1 if work[rank][column] % 3 == 1 else 2
        work[rank] = [(scale * value) % 3 for value in work[rank]]
        for index in range(len(work)):
            if index != rank and work[index][column] % 3:
                factor = work[index][column] % 3
                work[index] = [
                    (left - factor * right) % 3
                    for left, right in zip(work[index], work[rank])
                ]
        rank += 1
    return rank


def path_compatible_supports(profile: dict[str, int]):
    mask = int(profile["mask"])
    intact = {vertex for vertex in range(21) if (mask >> vertex) & 1}
    used_edges = [
        edge for edge in KG_EDGES if edge[0] in intact or edge[1] in intact
    ]
    edge_position = {edge: index for index, edge in enumerate(used_edges)}
    central_edges = [
        edge for edge in KG_EDGES if edge[0] in intact and edge[1] in intact
    ]
    relevant_triangles = sorted(
        {triangle for edge in central_edges for triangle in EDGE_TRIANGLES[edge]}
    )
    triangle_position = {
        triangle: index for index, triangle in enumerate(relevant_triangles)
    }
    triangle_forms = []
    for triangle in relevant_triangles:
        form = 0
        for edge in combinations(TRIANGLES[triangle], 2):
            form ^= 1 << edge_position[edge]
        triangle_forms.append(form)

    _, _, support_basis = support_space(profile)
    supports = []
    for mask_value in range(1 << len(support_basis)):
        support = 0
        for index, basis_vector in enumerate(support_basis):
            if (mask_value >> index) & 1:
                support ^= basis_vector
        if not class_assignment_exists(support, central_edges, triangle_position):
            continue
        edge_solution = solve_linear(triangle_forms, support, len(used_edges))
        valid = True
        for left, right in combinations(sorted(intact), 2):
            if not (set(FIBERS[left]) & set(FIBERS[right])):
                continue
            path_weight = 0
            for middle in range(21):
                if not (
                    set(FIBERS[middle]).isdisjoint(FIBERS[left])
                    and set(FIBERS[middle]).isdisjoint(FIBERS[right])
                ):
                    continue
                first = tuple(sorted((left, middle)))
                second = tuple(sorted((right, middle)))
                path_weight += (
                    ((edge_solution >> edge_position[first]) & 1)
                    ^ ((edge_solution >> edge_position[second]) & 1)
                )
            if path_weight in (1, 5):
                valid = False
                break
        if valid:
            supports.append(support)
    return intact, used_edges, central_edges, relevant_triangles, triangle_position, triangle_forms, supports


def audit_profile(profile_index: int, profile: dict[str, int]) -> dict[str, object]:
    (
        intact,
        used_edges,
        central_edges,
        relevant_triangles,
        triangle_position,
        triangle_forms,
        supports,
    ) = path_compatible_supports(profile)
    edge_position = {edge: index for index, edge in enumerate(used_edges)}

    adjacency = [[] for _ in range(21)]
    for left, right in used_edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    parent = [None] * 21
    parent[0] = -1
    queue = deque([0])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if parent[neighbor] is None:
                parent[neighbor] = vertex
                queue.append(neighbor)
    assert all(value is not None for value in parent)
    tree_edges = {
        tuple(sorted((vertex, parent[vertex]))) for vertex in range(1, 21)
    }
    non_tree_edges = [edge for edge in used_edges if edge not in tree_edges]
    non_tree_position = {edge: index for index, edge in enumerate(non_tree_edges)}
    assert len(non_tree_edges) == len(used_edges) - 20

    parity_rows = []
    for triangle in relevant_triangles:
        row = 0
        for edge in combinations(TRIANGLES[triangle], 2):
            if edge in non_tree_position:
                row ^= 1 << non_tree_position[edge]
        parity_rows.append(row)

    def oriented_form(source: int, target: int, edge_parity: int):
        edge = tuple(sorted((source, target)))
        parity = (edge_parity >> edge_position[edge]) & 1
        form = [0] * len(non_tree_edges)
        if edge in non_tree_position:
            coefficient = 1
            if source > target:
                coefficient = 1 if parity else -1
            form[non_tree_position[edge]] = coefficient % 3
        return form, parity

    def product(left, right):
        left_form, left_parity = left
        right_form, right_parity = right
        sign = -1 if left_parity else 1
        return (
            [
                (left_value + sign * right_value) % 3
                for left_value, right_value in zip(left_form, right_form)
            ],
            left_parity ^ right_parity,
        )

    def based_holonomy(left: int, right: int, third: int, edge_parity: int):
        return product(
            oriented_form(right, left, edge_parity),
            product(
                oriented_form(third, right, edge_parity),
                oriented_form(left, third, edge_parity),
            ),
        )

    signatures = Counter()
    for support in supports:
        non_tree_parity = solve_linear(parity_rows, support, len(non_tree_edges))
        edge_parity = 0
        for edge, position in non_tree_position.items():
            if (non_tree_parity >> position) & 1:
                edge_parity |= 1 << edge_position[edge]

        rows_mod_3 = []
        for triangle_index, triangle in enumerate(relevant_triangles):
            if (support >> triangle_index) & 1:
                continue
            left, middle, right = TRIANGLES[triangle]
            form, curved = based_holonomy(left, middle, right, edge_parity)
            assert not curved
            rows_mod_3.append(form)

        for edge in central_edges:
            left, right = edge
            curved_thirds = []
            for triangle in EDGE_TRIANGLES[edge]:
                position = triangle_position[triangle]
                if (support >> position) & 1:
                    curved_thirds.append(
                        next(vertex for vertex in TRIANGLES[triangle] if vertex not in edge)
                    )
            assert len(curved_thirds) in (0, 2)
            if len(curved_thirds) == 2:
                first, parity_one = based_holonomy(
                    left, right, curved_thirds[0], edge_parity
                )
                second, parity_two = based_holonomy(
                    left, right, curved_thirds[1], edge_parity
                )
                assert parity_one == parity_two == 1
                rows_mod_3.append(
                    [(left_value - right_value) % 3 for left_value, right_value in zip(first, second)]
                )

        rank = rank_mod_3(rows_mod_3, len(non_tree_edges))
        signatures[(len(rows_mod_3), rank, len(non_tree_edges) - rank)] += 1

    assert all(signature[2] == 1 for signature in signatures)
    return {
        "profile_index": profile_index,
        "branches": profile["branches"],
        "path_compatible_supports": len(supports),
        "used_edges": len(used_edges),
        "spanning_tree_edges_fixed": 20,
        "F3_variables": len(non_tree_edges),
        "F3_signature_histogram": {
            str(signature): count for signature, count in sorted(signatures.items())
        },
        "F3_nullity": 1,
        "gauge_fixed_quotient_connections": 3 * len(supports),
    }


def audit() -> dict[str, object]:
    profiles = core_profile_audit()["profiles"]
    reports = [audit_profile(index, profiles[index]) for index in (39, 40)]
    assert reports == [
        {
            "profile_index": 39,
            "branches": 3,
            "path_compatible_supports": 51,
            "used_edges": 104,
            "spanning_tree_edges_fixed": 20,
            "F3_variables": 84,
            "F3_signature_histogram": {
                "(106, 83, 1)": 6,
                "(109, 83, 1)": 24,
                "(110, 83, 1)": 6,
                "(112, 83, 1)": 6,
                "(113, 83, 1)": 6,
                "(118, 83, 1)": 3,
            },
            "F3_nullity": 1,
            "gauge_fixed_quotient_connections": 153,
        },
        {
            "profile_index": 40,
            "branches": 3,
            "path_compatible_supports": 50,
            "used_edges": 101,
            "spanning_tree_edges_fixed": 20,
            "F3_variables": 81,
            "F3_signature_histogram": {
                "(95, 80, 1)": 4,
                "(97, 80, 1)": 4,
                "(98, 80, 1)": 16,
                "(99, 80, 1)": 4,
                "(101, 80, 1)": 10,
                "(104, 80, 1)": 12,
            },
            "F3_nullity": 1,
            "gauge_fixed_quotient_connections": 150,
        },
    ]
    return {
        "PASS": True,
        "exceptional_profiles": reports,
        "path_compatible_supports": 101,
        "gauge_fixed_quotient_connections": 303,
        "exceptional_transition_orbits": 6,
        "consequence": (
            "The six exceptional s=76 transition orbits reduce to 303 gauge-fixed "
            "S3 quotient cases before restoring physical C4 axes and V4 translations."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
