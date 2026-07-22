#!/usr/bin/env python3
"""Exact conjugacy-class symmetry quotient for exceptional ``s = 76`` cores.

The support-stabilizer audit leaves sixteen parity-curvature support orbits.
A support can admit more than one triangle conjugacy-class assignment, so this
file enumerates those assignments exactly and quotients them by the stabilizer
of the support.  The result is thirty support/class orbits.  Since global
reflection conjugacy identifies the two nonzero ``F3`` quotient parameters,
each support/class orbit has two parameter classes: zero and nonzero.  Thus the
fully class-resolved exceptional lift problem has 60 canonical cases.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import combinations, permutations

from s76_core_profiles import FIBERS, FIBER_INDEX, audit as core_profile_audit
from s76_exceptional_quotient_audit import path_compatible_supports
from s76_exceptional_symmetry_audit import (
    TRIANGLES,
    TRIANGLE_INDEX,
    permute_mask,
)


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


def class_assignments(
    support: int,
    central_edges: list[tuple[int, int]],
    relevant_triangles: list[int],
    triangle_position: dict[int, int],
    edge_triangles: dict[tuple[int, int], tuple[int, ...]],
) -> list[int]:
    dsu = DSU(len(relevant_triangles))
    for edge in central_edges:
        incident = [triangle_position[index] for index in edge_triangles[edge]]
        weight = sum((support >> index) & 1 for index in incident)
        assert weight in (0, 2)
        if weight == 2:
            dsu.union(incident[0], incident[1])
            dsu.union(incident[0], incident[2])

    roots = sorted({dsu.find(index) for index in range(len(relevant_triangles))})
    root_index = {root: index for index, root in enumerate(roots)}
    component = [root_index[dsu.find(index)] for index in range(len(relevant_triangles))]
    forced: dict[int, int] = {}
    constraints = []

    for edge in central_edges:
        incident = [triangle_position[index] for index in edge_triangles[edge]]
        if sum((support >> index) & 1 for index in incident):
            continue
        multiplicity = Counter(component[index] for index in incident)
        if len(multiplicity) == 1:
            return []
        if len(multiplicity) == 2:
            repeated = next(variable for variable, count in multiplicity.items() if count == 2)
            singleton = next(variable for variable, count in multiplicity.items() if count == 1)
            for variable, value in ((repeated, 0), (singleton, 1)):
                if variable in forced and forced[variable] != value:
                    return []
                forced[variable] = value
        else:
            constraints.append(tuple(multiplicity))

    initial = [-1] * len(roots)
    for variable, value in forced.items():
        initial[variable] = value
    answers = []

    def search(current: list[int]) -> None:
        changed = True
        while changed:
            changed = False
            for constraint in constraints:
                ones = sum(current[variable] == 1 for variable in constraint)
                unknown = [variable for variable in constraint if current[variable] < 0]
                if ones > 1 or (ones == 0 and not unknown):
                    return
                if ones == 1:
                    for variable in unknown:
                        current[variable] = 0
                        changed = True
                elif len(unknown) == 1:
                    current[unknown[0]] = 1
                    changed = True

        unresolved = next((index for index, value in enumerate(current) if value < 0), None)
        if unresolved is not None:
            for value in (0, 1):
                child = current.copy()
                child[unresolved] = value
                search(child)
            return

        assignment = 0
        for triangle in range(len(relevant_triangles)):
            if current[component[triangle]]:
                assignment |= 1 << triangle
        answers.append(assignment)

    search(initial)
    return sorted(set(answers))


def canonical_bytes(cases: list[list[int]]) -> bytes:
    return (json.dumps(cases, separators=(",", ":")) + "\n").encode()


def audit_profile(profile_index: int, profile: dict[str, int]) -> dict[str, object]:
    (
        _,
        _,
        central_edges,
        relevant_triangles,
        triangle_position,
        _,
        supports,
    ) = path_compatible_supports(profile)
    mask = int(profile["mask"])

    edge_triangles = {
        edge: tuple(
            triangle_position[index]
            for index in sorted(
                {
                    TRIANGLE_INDEX[tuple(sorted((*edge, third)))]
                    for third in range(21)
                    if third not in edge
                    and set(FIBERS[third]).isdisjoint(FIBERS[edge[0]])
                    and set(FIBERS[third]).isdisjoint(FIBERS[edge[1]])
                }
            )
        )
        for edge in central_edges
    }
    # class_assignments expects global triangle identifiers in edge_triangles;
    # convert the local positions back to the identifiers used by the support.
    edge_triangles = {
        edge: tuple(relevant_triangles[position] for position in positions)
        for edge, positions in edge_triangles.items()
    }

    stabilizer_actions = []
    for permutation in permutations(range(7)):
        if permute_mask(mask, permutation) != mask:
            continue
        fiber_map = [
            FIBER_INDEX[tuple(sorted((permutation[left], permutation[right])))]
            for left, right in FIBERS
        ]
        mapping = []
        for triangle in relevant_triangles:
            target = tuple(sorted(fiber_map[vertex] for vertex in TRIANGLES[triangle]))
            target_identifier = TRIANGLE_INDEX[target]
            assert target_identifier in triangle_position
            mapping.append(triangle_position[target_identifier])
        stabilizer_actions.append(tuple(mapping))

    def act(value: int, mapping: tuple[int, ...]) -> int:
        image = 0
        while value:
            bit = value & -value
            source = bit.bit_length() - 1
            image |= 1 << mapping[source]
            value ^= bit
        return image

    support_set = set(supports)
    remaining_supports = set(supports)
    support_representatives = []
    while remaining_supports:
        seed = min(remaining_supports)
        orbit = {act(seed, mapping) for mapping in stabilizer_actions}
        assert orbit <= support_set
        remaining_supports.difference_update(orbit)
        support_representatives.append(seed)

    raw_assignments = 0
    class_orbits = 0
    class_orbit_sizes = Counter()
    cases = []
    support_summaries = []

    for support in sorted(support_representatives):
        assignments = class_assignments(
            support,
            central_edges,
            relevant_triangles,
            triangle_position,
            edge_triangles,
        )
        raw_assignments += len(assignments)
        support_stabilizer = [
            mapping for mapping in stabilizer_actions if act(support, mapping) == support
        ]
        remaining = set(assignments)
        assignment_orbits = []
        while remaining:
            seed = min(remaining)
            orbit = {act(seed, mapping) for mapping in support_stabilizer}
            assert orbit <= set(assignments)
            remaining.difference_update(orbit)
            assignment_orbits.append(orbit)

        class_orbits += len(assignment_orbits)
        class_orbit_sizes.update(map(len, assignment_orbits))
        class_representatives = sorted(min(orbit) for orbit in assignment_orbits)
        for assignment in class_representatives:
            cases.append([profile_index, support, assignment])
        support_summaries.append(
            {
                "support": support,
                "support_weight": support.bit_count(),
                "support_stabilizer_order": len(support_stabilizer),
                "class_assignments": len(assignments),
                "class_assignment_orbits": len(assignment_orbits),
                "class_orbit_size_histogram": {
                    str(size): count
                    for size, count in sorted(Counter(map(len, assignment_orbits)).items())
                },
                "class_representatives": class_representatives,
            }
        )

    cases.sort()
    payload = canonical_bytes(cases)
    return {
        "profile_index": profile_index,
        "branches": profile["branches"],
        "support_orbits": len(support_representatives),
        "raw_class_assignments_on_support_representatives": raw_assignments,
        "support_class_orbits": class_orbits,
        "class_orbit_size_histogram": {
            str(size): count for size, count in sorted(class_orbit_sizes.items())
        },
        "support_summaries": support_summaries,
        "support_class_cases_sha256": hashlib.sha256(payload).hexdigest(),
        "support_class_cases_bytes": len(payload),
        "support_class_cases": cases,
        "F3_parameter_classes_per_support_class_orbit": 2,
        "canonical_full_quotient_cases": 2 * class_orbits,
    }


def audit() -> dict[str, object]:
    profiles = core_profile_audit()["profiles"]
    reports = [audit_profile(index, profiles[index]) for index in (39, 40)]

    assert reports[0]["support_orbits"] == 7
    assert reports[0]["raw_class_assignments_on_support_representatives"] == 23
    assert reports[0]["support_class_orbits"] == 19
    assert reports[0]["class_orbit_size_histogram"] == {"1": 15, "2": 4}
    assert reports[0]["support_class_cases_sha256"] == (
        "e74a3a0631dcbb2ff46af8847f0f62a9bbcc6c2de53a7407d5a089c607507a2e"
    )
    assert reports[0]["support_class_cases_bytes"] == 1260
    assert reports[0]["canonical_full_quotient_cases"] == 38

    assert reports[1]["support_orbits"] == 9
    assert reports[1]["raw_class_assignments_on_support_representatives"] == 11
    assert reports[1]["support_class_orbits"] == 11
    assert reports[1]["class_orbit_size_histogram"] == {"1": 11}
    assert reports[1]["support_class_cases_sha256"] == (
        "3e0ff2a51fb75b2d8b9b4205ce69f6886da65e6fee8a882b2e1971d874737894"
    )
    assert reports[1]["support_class_cases_bytes"] == 665
    assert reports[1]["canonical_full_quotient_cases"] == 22

    cases = reports[0]["support_class_cases"] + reports[1]["support_class_cases"]
    cases.sort()
    assert hashlib.sha256(canonical_bytes(cases)).hexdigest() == (
        "c1b660cdfdf7fa14b4b58e0a6b34c1c1d3710146cb8f08ceedab556110c3d271"
    )

    return {
        "PASS": True,
        "exceptional_profiles": reports,
        "support_orbits": 16,
        "raw_class_assignments_on_support_representatives": 34,
        "support_class_orbits": 30,
        "F3_parameter_classes": [0, "nonzero"],
        "canonical_full_quotient_cases": 60,
        "support_class_cases_sha256": (
            "c1b660cdfdf7fa14b4b58e0a6b34c1c1d3710146cb8f08ceedab556110c3d271"
        ),
        "consequence": (
            "The six exceptional transition orbits reduce to 60 canonical "
            "support/class/quotient cases before restoring physical C4 axes and V4 translations."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
