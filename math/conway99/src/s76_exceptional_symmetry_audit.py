#!/usr/bin/env python3
"""Exact symmetry quotient of the exceptional ``s = 76`` lift cases.

The six transition orbits in canonical core profiles 39 and 40 reduce to 101
path-compatible parity-curvature supports.  We quotient those supports by the
full stabilizer of the intact-fiber mask inside the natural ``S7`` action on
base pairs.  This is inherited label symmetry, not an assumed automorphism of
the unknown graph.

The support spaces collapse to seven and nine orbits.  For each support the
``S3=C3 semidirect C2`` quotient layer has one free ``F3`` parameter.  Global
conjugation by a reflection fixes the parity coordinate and sends the ``C3``
coordinate ``x`` to ``-x``, so parameters one and two are equivalent.  Hence
only two parameter classes, zero and nonzero, need be lifted for each support
orbit: 32 canonical quotient-lift cases in total.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import combinations, permutations

from s76_core_profiles import FIBERS, FIBER_INDEX, audit as core_profile_audit
from s76_exceptional_quotient_audit import path_compatible_supports

TRIANGLES = [
    triangle
    for triangle in combinations(range(21), 3)
    if all(
        set(FIBERS[left]).isdisjoint(FIBERS[right])
        for left, right in combinations(triangle, 2)
    )
]
TRIANGLE_INDEX = {triangle: index for index, triangle in enumerate(TRIANGLES)}


def permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    image = 0
    for index, fiber in enumerate(FIBERS):
        if not ((mask >> index) & 1):
            continue
        target = tuple(sorted((permutation[fiber[0]], permutation[fiber[1]])))
        image |= 1 << FIBER_INDEX[target]
    return image


def canonical_bytes(values: list[int]) -> bytes:
    return (json.dumps(values, separators=(",", ":")) + "\n").encode()


def quotient_profile(profile_index: int, profile: dict[str, int]) -> dict[str, object]:
    (
        _,
        _,
        central_edges,
        relevant_triangles,
        _,
        _,
        supports,
    ) = path_compatible_supports(profile)
    mask = int(profile["mask"])
    relevant_position = {
        triangle: index for index, triangle in enumerate(relevant_triangles)
    }

    stabilizer = []
    action_maps = []
    for permutation in permutations(range(7)):
        if permute_mask(mask, permutation) != mask:
            continue
        fiber_map = [
            FIBER_INDEX[tuple(sorted((permutation[left], permutation[right])))]
            for left, right in FIBERS
        ]
        triangle_map = []
        for triangle in relevant_triangles:
            target = tuple(
                sorted(fiber_map[vertex] for vertex in TRIANGLES[triangle])
            )
            target_index = TRIANGLE_INDEX[target]
            assert target_index in relevant_position
            triangle_map.append(relevant_position[target_index])
        stabilizer.append(permutation)
        action_maps.append(tuple(triangle_map))

    support_set = set(supports)

    def act(support: int, mapping: tuple[int, ...]) -> int:
        image = 0
        value = support
        while value:
            bit = value & -value
            source = bit.bit_length() - 1
            image |= 1 << mapping[source]
            value ^= bit
        return image

    remaining = set(supports)
    orbits = []
    while remaining:
        representative = min(remaining)
        orbit = {act(representative, mapping) for mapping in action_maps}
        assert orbit <= support_set
        remaining.difference_update(orbit)
        orbits.append(orbit)

    representatives = sorted(min(orbit) for orbit in orbits)
    orbit_size_histogram = Counter(len(orbit) for orbit in orbits)
    representative_weight_histogram = Counter(
        representative.bit_count() for representative in representatives
    )
    representative_stabilizers = [
        sum(act(representative, mapping) == representative for mapping in action_maps)
        for representative in representatives
    ]
    payload = canonical_bytes(representatives)

    return {
        "profile_index": profile_index,
        "branches": profile["branches"],
        "intact_fibers": profile["intact_fibers"],
        "central_disjoint_edges": len(central_edges),
        "path_compatible_supports": len(supports),
        "core_mask_stabilizer_order": len(stabilizer),
        "support_orbits": len(orbits),
        "support_orbit_size_histogram": {
            str(size): count for size, count in sorted(orbit_size_histogram.items())
        },
        "representative_weight_histogram": {
            str(weight): count
            for weight, count in sorted(representative_weight_histogram.items())
        },
        "representative_support_stabilizer_histogram": {
            str(order): count
            for order, count in sorted(Counter(representative_stabilizers).items())
        },
        "representatives_sha256": hashlib.sha256(payload).hexdigest(),
        "representatives_bytes": len(payload),
        "representatives": representatives,
        "quotient_parameter_classes_per_support_orbit": 2,
        "canonical_quotient_lift_cases": 2 * len(orbits),
    }


def audit() -> dict[str, object]:
    profiles = core_profile_audit()["profiles"]
    reports = [quotient_profile(index, profiles[index]) for index in (39, 40)]

    assert reports[0] == {
        "profile_index": 39,
        "branches": 3,
        "intact_fibers": 18,
        "central_disjoint_edges": 76,
        "path_compatible_supports": 51,
        "core_mask_stabilizer_order": 12,
        "support_orbits": 7,
        "support_orbit_size_histogram": {"3": 1, "6": 4, "12": 2},
        "representative_weight_histogram": {"46": 1, "48": 2, "54": 2, "56": 1, "60": 1},
        "representative_support_stabilizer_histogram": {"1": 2, "2": 4, "4": 1},
        "representatives_sha256": "f1df94ac4cba2bf41c9c98b28cb0daaec715f4aad89c26fc4a165f316b8f4523",
        "representatives_bytes": 218,
        "representatives": reports[0]["representatives"],
        "quotient_parameter_classes_per_support_orbit": 2,
        "canonical_quotient_lift_cases": 14,
    }
    assert reports[1] == {
        "profile_index": 40,
        "branches": 3,
        "intact_fibers": 17,
        "central_disjoint_edges": 69,
        "path_compatible_supports": 50,
        "core_mask_stabilizer_order": 8,
        "support_orbits": 9,
        "support_orbit_size_histogram": {"2": 1, "4": 4, "8": 4},
        "representative_weight_histogram": {"40": 1, "44": 1, "46": 2, "48": 2, "50": 2, "52": 1},
        "representative_support_stabilizer_histogram": {"1": 4, "2": 4, "4": 1},
        "representatives_sha256": "ccc96ec9217cc067686c2d8db542ea9bad94b970820508282f4193ad0e5918a4",
        "representatives_bytes": 259,
        "representatives": reports[1]["representatives"],
        "quotient_parameter_classes_per_support_orbit": 2,
        "canonical_quotient_lift_cases": 18,
    }

    all_representatives = reports[0]["representatives"] + reports[1]["representatives"]
    assert hashlib.sha256(canonical_bytes(all_representatives)).hexdigest() == (
        "5f98c2ff345e5c607fa85af418447bc1ab3ebb316b5f378caaf481d6189d6fe5"
    )

    return {
        "PASS": True,
        "exceptional_profiles": reports,
        "path_compatible_supports": 101,
        "support_orbits": sum(report["support_orbits"] for report in reports),
        "F3_parameter_classes": [0, "nonzero"],
        "canonical_quotient_lift_cases": sum(
            report["canonical_quotient_lift_cases"] for report in reports
        ),
        "representatives_sha256": (
            "5f98c2ff345e5c607fa85af418447bc1ab3ebb316b5f378caaf481d6189d6fe5"
        ),
        "consequence": (
            "The six exceptional transition orbits reduce from 303 gauge-fixed "
            "quotient connections to 32 canonical support/parameter lift cases."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
