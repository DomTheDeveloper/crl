#!/usr/bin/env python3
"""Exact six-path parity reduction for the two exceptional ``s = 76`` cores.

Profiles 39 and 40 do not admit zero triangle curvature.  The companion
curvature audit reduces them to 99 and 176 class-compatible supports.  Here we
restore one edge-parity lift for each support and impose the parity projection
of every intersecting-fiber six-path equation.

The kernel of the triangle coboundary map has dimension 20 and is exactly the
vertex-gauge space on the connected 21-fiber used-edge graph.  Every two-edge
path parity is invariant under that kernel.  Consequently the path test depends
only on the curvature support, not on the selected edge-parity lift.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import combinations

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit
from s76_curvature_support_audit import (
    EDGE_TRIANGLES,
    TRIANGLES,
    class_assignment_exists,
    gf2_nullspace,
    support_space,
)


def solve_linear(rows: list[int], rhs_bits: int, columns: int) -> int:
    work = rows[:]
    rhs = [(rhs_bits >> index) & 1 for index in range(len(rows))]
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
        rhs[rank], rhs[pivot] = rhs[pivot], rhs[rank]
        for index in range(len(work)):
            if index != rank and ((work[index] >> column) & 1):
                work[index] ^= work[rank]
                rhs[index] ^= rhs[rank]
        pivots.append(column)
        rank += 1
    assert all(work[index] or not rhs[index] for index in range(rank, len(work)))
    solution = 0
    for row, pivot in enumerate(pivots):
        if rhs[row]:
            solution |= 1 << pivot
    assert all((row & solution).bit_count() % 2 == ((rhs_bits >> index) & 1) for index, row in enumerate(rows))
    return solution


def canonical_support_bytes(supports: list[int]) -> bytes:
    return (json.dumps(supports, separators=(",", ":")) + "\n").encode()


def audit_profile(profile_index: int, profile: dict[str, int]) -> dict[str, object]:
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
    class_supports = []
    for mask_value in range(1 << len(support_basis)):
        support = 0
        for index, basis_vector in enumerate(support_basis):
            if (mask_value >> index) & 1:
                support ^= basis_vector
        if class_assignment_exists(support, central_edges, triangle_position):
            class_supports.append(support)

    edge_kernel = gf2_nullspace(triangle_forms, len(used_edges))
    assert len(edge_kernel) == 20

    intersecting_pairs = [
        (left, right)
        for left, right in combinations(sorted(intact), 2)
        if set(FIBERS[left]) & set(FIBERS[right])
    ]
    path_forms = []
    for left, right in intersecting_pairs:
        forms = []
        for middle in range(21):
            if not (
                set(FIBERS[middle]).isdisjoint(FIBERS[left])
                and set(FIBERS[middle]).isdisjoint(FIBERS[right])
            ):
                continue
            first = tuple(sorted((left, middle)))
            second = tuple(sorted((right, middle)))
            forms.append((1 << edge_position[first]) ^ (1 << edge_position[second]))
        assert len(forms) == 6
        path_forms.append(tuple(forms))

    # Flat edge-parity changes are vertex gauges, and cancel on all two-edge
    # paths between fixed endpoints.
    assert all(
        (form & kernel_vector).bit_count() % 2 == 0
        for kernel_vector in edge_kernel
        for forms in path_forms
        for form in forms
    )

    path_supports = []
    path_weight_profiles = Counter()
    for support in class_supports:
        edge_solution = solve_linear(triangle_forms, support, len(used_edges))
        path_weights = tuple(
            sum((form & edge_solution).bit_count() % 2 for form in forms)
            for forms in path_forms
        )
        if any(weight in (1, 5) for weight in path_weights):
            continue
        path_supports.append(support)
        path_weight_profiles[path_weights] += 1

    payload = canonical_support_bytes(path_supports)
    return {
        "profile_index": profile_index,
        "branches": profile["branches"],
        "intact_fibers": profile["intact_fibers"],
        "used_edges": len(used_edges),
        "central_disjoint_edges": len(central_edges),
        "intact_intersecting_pairs": len(intersecting_pairs),
        "edge_gauge_dimension": len(edge_kernel),
        "curvature_dimension": len(support_basis),
        "class_compatible_supports": len(class_supports),
        "path_compatible_supports": len(path_supports),
        "path_support_weight_histogram": {
            str(weight): count
            for weight, count in sorted(Counter(value.bit_count() for value in path_supports).items())
        },
        "distinct_path_weight_profiles": len(path_weight_profiles),
        "path_compatible_supports_sha256": hashlib.sha256(payload).hexdigest(),
        "path_compatible_supports_bytes": len(payload),
    }


def audit() -> dict[str, object]:
    profile_report = core_profile_audit()
    profiles = profile_report["profiles"]
    reports = [
        audit_profile(profile_index, profiles[profile_index])
        for profile_index in (39, 40)
    ]
    assert reports == [
        {
            "profile_index": 39,
            "branches": 3,
            "intact_fibers": 18,
            "used_edges": 104,
            "central_disjoint_edges": 76,
            "intact_intersecting_pairs": 77,
            "edge_gauge_dimension": 20,
            "curvature_dimension": 12,
            "class_compatible_supports": 99,
            "path_compatible_supports": 51,
            "path_support_weight_histogram": {
                "46": 6,
                "48": 9,
                "54": 24,
                "56": 6,
                "60": 6,
            },
            "distinct_path_weight_profiles": reports[0]["distinct_path_weight_profiles"],
            "path_compatible_supports_sha256": "d93b64823b56761be114493426fb890f322003ca6bc6d2aec98eb32e9b055519",
            "path_compatible_supports_bytes": 1622,
        },
        {
            "profile_index": 40,
            "branches": 3,
            "intact_fibers": 17,
            "used_edges": 101,
            "central_disjoint_edges": 69,
            "intact_intersecting_pairs": 67,
            "edge_gauge_dimension": 20,
            "curvature_dimension": 13,
            "class_compatible_supports": 176,
            "path_compatible_supports": 50,
            "path_support_weight_histogram": {
                "40": 4,
                "44": 4,
                "46": 12,
                "48": 10,
                "50": 16,
                "52": 4,
            },
            "distinct_path_weight_profiles": reports[1]["distinct_path_weight_profiles"],
            "path_compatible_supports_sha256": "1959f5bf2ff142b38da74232c34bdb8545dcc994604597b798f14eb1ca3b5b62",
            "path_compatible_supports_bytes": 1436,
        },
    ]
    return {
        "PASS": True,
        "exceptional_profiles": reports,
        "class_compatible_supports": sum(item["class_compatible_supports"] for item in reports),
        "path_compatible_supports": sum(item["path_compatible_supports"] for item in reports),
        "exceptional_transition_orbits": sum(item["branches"] for item in reports),
        "consequence": (
            "The six transition orbits in core profiles 39 and 40 reduce to 101 "
            "parity-curvature supports before restoring S3 and V4 lift data."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
