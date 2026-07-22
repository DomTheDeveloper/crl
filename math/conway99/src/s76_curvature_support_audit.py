#!/usr/bin/env python3
"""Exact finite-field reduction of parity curvature in the 41 ``s = 76`` cores.

For a cross-fiber permutation retain its sign.  Triangle-holonomy signs are the
coboundary of those edge signs.  At every disjoint pair of intact fibers, the
three incident holonomy signs must have even weight.  We intersect this image
with the local cycle constraints and then apply the exact holonomy conjugacy-
class rules.

Thirty-nine core types admit the zero-curvature support.  Only two dense core
types require nonzero curvature; their complete support spaces have dimensions
12 and 13, and exhaustive class filtering leaves 99 and 176 supports.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import combinations

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit

TRIANGLES = [
    triangle
    for triangle in combinations(range(21), 3)
    if all(
        set(FIBERS[left]).isdisjoint(FIBERS[right])
        for left, right in combinations(triangle, 2)
    )
]
TRIANGLE_INDEX = {triangle: index for index, triangle in enumerate(TRIANGLES)}
EDGE_TRIANGLES = {
    edge: tuple(
        TRIANGLE_INDEX[tuple(sorted((*edge, third)))]
        for third in range(21)
        if third not in edge
        and set(FIBERS[third]).isdisjoint(FIBERS[edge[0]])
        and set(FIBERS[third]).isdisjoint(FIBERS[edge[1]])
    )
    for edge in KG_EDGES
}


class DSU:
    def __init__(self, size: int):
        self.parent = list(range(size))

    def find(self, value: int) -> int:
        while self.parent[value] != value:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left: int, right: int) -> None:
        left = self.find(left)
        right = self.find(right)
        if left != right:
            self.parent[right] = left


def gf2_nullspace(rows: list[int], columns: int) -> list[int]:
    work = [row for row in rows if row]
    pivots = []
    rank = 0
    for column in range(columns):
        pivot = next(
            (index for index in range(rank, len(work)) if (work[index] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for index in range(len(work)):
            if index != rank and ((work[index] >> column) & 1):
                work[index] ^= work[rank]
        pivots.append(column)
        rank += 1
        if rank == len(work):
            break

    pivot_set = set(pivots)
    basis = []
    for free in (column for column in range(columns) if column not in pivot_set):
        vector = 1 << free
        for row_index, pivot in enumerate(pivots):
            if (work[row_index] >> free) & 1:
                vector |= 1 << pivot
        assert all((row & vector).bit_count() % 2 == 0 for row in rows)
        basis.append(vector)
    return basis


def independent_basis(vectors: list[int]) -> list[int]:
    pivots: dict[int, int] = {}
    for vector in vectors:
        value = vector
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    return list(pivots.values())


def class_assignment_exists(
    support: int,
    central_edges: list[tuple[int, int]],
    triangle_position: dict[int, int],
) -> bool:
    dsu = DSU(len(triangle_position))
    for edge in central_edges:
        incident = [triangle_position[index] for index in EDGE_TRIANGLES[edge]]
        weight = sum((support >> index) & 1 for index in incident)
        if weight not in (0, 2):
            return False
        if weight == 2:
            dsu.union(incident[0], incident[1])
            dsu.union(incident[0], incident[2])

    roots = sorted({dsu.find(index) for index in range(len(triangle_position))})
    root_index = {root: index for index, root in enumerate(roots)}
    component = [root_index[dsu.find(index)] for index in range(len(triangle_position))]
    forced: dict[int, int] = {}
    exact_one_constraints = []

    for edge in central_edges:
        incident = [triangle_position[index] for index in EDGE_TRIANGLES[edge]]
        if sum((support >> index) & 1 for index in incident):
            continue
        multiplicity = Counter(component[index] for index in incident)
        if len(multiplicity) == 1:
            return False
        if len(multiplicity) == 2:
            repeated = next(variable for variable, count in multiplicity.items() if count == 2)
            singleton = next(variable for variable, count in multiplicity.items() if count == 1)
            for variable, value in ((repeated, 0), (singleton, 1)):
                if variable in forced and forced[variable] != value:
                    return False
                forced[variable] = value
        else:
            exact_one_constraints.append(tuple(multiplicity))

    assignment = [-1] * len(roots)
    for variable, value in forced.items():
        assignment[variable] = value

    def search(current: list[int]) -> bool:
        changed = True
        while changed:
            changed = False
            for constraint in exact_one_constraints:
                ones = sum(current[variable] == 1 for variable in constraint)
                unknown = [variable for variable in constraint if current[variable] < 0]
                if ones > 1 or (ones == 0 and not unknown):
                    return False
                if ones == 1:
                    for variable in unknown:
                        current[variable] = 0
                        changed = True
                elif len(unknown) == 1:
                    current[unknown[0]] = 1
                    changed = True
        unresolved = next(
            (
                variable
                for constraint in exact_one_constraints
                for variable in constraint
                if current[variable] < 0
            ),
            None,
        )
        if unresolved is None:
            return True
        for value in (0, 1):
            child = current.copy()
            child[unresolved] = value
            if search(child):
                return True
        return False

    return search(assignment)


def support_space(profile: dict[str, int]):
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
        row = 0
        for edge in combinations(TRIANGLES[triangle], 2):
            row ^= 1 << edge_position[edge]
        triangle_forms.append(row)

    local_rows = []
    for edge in central_edges:
        row = 0
        for triangle in EDGE_TRIANGLES[edge]:
            row ^= triangle_forms[triangle_position[triangle]]
        local_rows.append(row)

    edge_kernel = gf2_nullspace(local_rows, len(used_edges))
    support_generators = []
    for edge_vector in edge_kernel:
        support = 0
        for triangle, form in enumerate(triangle_forms):
            if (form & edge_vector).bit_count() & 1:
                support |= 1 << triangle
        support_generators.append(support)
    support_basis = independent_basis(support_generators)
    return central_edges, triangle_position, support_basis


def canonical_support_bytes(supports: list[int]) -> bytes:
    return (json.dumps(supports, separators=(",", ":")) + "\n").encode()


def audit() -> dict[str, object]:
    profile_report = core_profile_audit()
    profiles = profile_report["profiles"]
    zero_curvature_survivors = []
    exceptional = []

    for profile_index, profile in enumerate(profiles):
        central_edges, triangle_position, support_basis = support_space(profile)
        if class_assignment_exists(0, central_edges, triangle_position):
            zero_curvature_survivors.append(profile_index)
            continue

        surviving_supports = []
        for mask in range(1 << len(support_basis)):
            support = 0
            for index, basis_vector in enumerate(support_basis):
                if (mask >> index) & 1:
                    support ^= basis_vector
            if class_assignment_exists(support, central_edges, triangle_position):
                surviving_supports.append(support)
        payload = canonical_support_bytes(surviving_supports)
        exceptional.append(
            {
                "profile_index": profile_index,
                "branches": profile["branches"],
                "intact_fibers": profile["intact_fibers"],
                "used_curvature_dimension": len(support_basis),
                "supports_before_class_filter": 1 << len(support_basis),
                "supports_after_class_filter": len(surviving_supports),
                "support_weight_histogram": {
                    str(weight): count
                    for weight, count in sorted(
                        Counter(support.bit_count() for support in surviving_supports).items()
                    )
                },
                "surviving_supports_sha256": hashlib.sha256(payload).hexdigest(),
                "surviving_supports_bytes": len(payload),
            }
        )

    assert zero_curvature_survivors == list(range(39))
    assert exceptional == [
        {
            "profile_index": 39,
            "branches": 3,
            "intact_fibers": 18,
            "used_curvature_dimension": 12,
            "supports_before_class_filter": 4096,
            "supports_after_class_filter": 99,
            "support_weight_histogram": {
                "46": 6,
                "48": 27,
                "52": 6,
                "54": 24,
                "56": 18,
                "58": 6,
                "60": 12,
            },
            "surviving_supports_sha256": "19690d214ef0b424974b4aa81a90c6293855ace021af6ab0cbef31db4817b3b6",
            "surviving_supports_bytes": 3152,
        },
        {
            "profile_index": 40,
            "branches": 3,
            "intact_fibers": 17,
            "used_curvature_dimension": 13,
            "supports_before_class_filter": 8192,
            "supports_after_class_filter": 176,
            "support_weight_histogram": {
                "36": 2,
                "40": 8,
                "42": 4,
                "44": 12,
                "46": 28,
                "48": 20,
                "50": 56,
                "52": 14,
                "54": 28,
                "56": 4,
            },
            "surviving_supports_sha256": "429fe711e4566b19a80b6e7195434757a7da654a02002f51ce1b082d41a6c632",
            "surviving_supports_bytes": 5088,
        },
    ]

    return {
        "PASS": True,
        "canonical_core_types": len(profiles),
        "zero_curvature_class_survivors": len(zero_curvature_survivors),
        "zero_curvature_profile_indices": zero_curvature_survivors,
        "exceptional_profiles": exceptional,
        "exceptional_transition_orbits": sum(item["branches"] for item in exceptional),
        "consequence": (
            "Only six of the 701 completed transition orbits require nonzero parity "
            "curvature at the intact-core level; they lie in canonical profiles 39 and 40."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
