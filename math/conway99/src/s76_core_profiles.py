#!/usr/bin/env python3
"""Profile the intact permutation cores of all 701 ``s = 76`` branches."""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import combinations

from s76_transition_orbits import PAIR_PERMUTATIONS, audit as orbit_audit

LABELS = [
    (left, right)
    for left, right in combinations(range(14), 2)
    if right != (left ^ 1)
]
LABEL_INDEX = {label: index for index, label in enumerate(LABELS)}
FIBERS = sorted(
    {tuple(sorted((left // 2, right // 2))) for left, right in LABELS}
)
FIBER_INDEX = {fiber: index for index, fiber in enumerate(FIBERS)}
FIBER_MEMBERS = {
    fiber: [
        index
        for index, (left, right) in enumerate(LABELS)
        if tuple(sorted((left // 2, right // 2))) == fiber
    ]
    for fiber in FIBERS
}
KG_EDGES = [
    (left, right)
    for left, right in combinations(range(21), 2)
    if set(FIBERS[left]).isdisjoint(FIBERS[right])
]
KG_TRIANGLES = [
    triangle
    for triangle in combinations(range(21), 3)
    if all(
        set(FIBERS[left]).isdisjoint(FIBERS[right])
        for left, right in combinations(triangle, 2)
    )
]
COMMON_THIRDS = {
    edge: [
        vertex
        for vertex in range(21)
        if vertex not in edge
        and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[0]])
        and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[1]])
    ]
    for edge in KG_EDGES
}


def edge_key(left: int, right: int) -> tuple[int, int]:
    return (left, right) if left < right else (right, left)


def transition_edges(state) -> set[tuple[int, int]]:
    specified = dict(state)
    edges = set()
    for row in range(14):
        matching = specified.get(
            row,
            tuple(
                (2 * group, 2 * group + 1)
                for group in range(7)
                if group != row // 2
            ),
        )
        for left, right in matching:
            u = LABEL_INDEX[tuple(sorted((row, left)))]
            v = LABEL_INDEX[tuple(sorted((row, right)))]
            edges.add(edge_key(u, v))
    assert len(edges) == 84
    return edges


def intact_mask(state) -> int:
    selected = transition_edges(state)
    mask = 0
    for fiber_index, fiber in enumerate(FIBERS):
        members = FIBER_MEMBERS[fiber]
        degrees = {vertex: 0 for vertex in members}
        internal_edges = 0
        for left, right in combinations(members, 2):
            if edge_key(left, right) in selected:
                internal_edges += 1
                degrees[left] += 1
                degrees[right] += 1
        if internal_edges == 4 and all(degrees[vertex] == 2 for vertex in members):
            mask |= 1 << fiber_index
    return mask


def permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    for index, fiber in enumerate(FIBERS):
        if not ((mask >> index) & 1):
            continue
        image = tuple(sorted((permutation[fiber[0]], permutation[fiber[1]])))
        result |= 1 << FIBER_INDEX[image]
    return result


def canonical_mask(mask: int) -> int:
    return min(permute_mask(mask, permutation) for permutation in PAIR_PERMUTATIONS)


def profile(mask: int, branches: int) -> dict[str, int]:
    vertices = [vertex for vertex in range(21) if (mask >> vertex) & 1]
    vertex_set = set(vertices)
    edges = [
        edge for edge in KG_EDGES if edge[0] in vertex_set and edge[1] in vertex_set
    ]
    triangles = [
        triangle
        for triangle in KG_TRIANGLES
        if all(vertex in vertex_set for vertex in triangle)
    ]
    closed_edges = sum(
        all(vertex in vertex_set for vertex in COMMON_THIRDS[edge])
        for edge in edges
    )
    degrees = Counter()
    for left, right in edges:
        degrees[left] += 1
        degrees[right] += 1

    unseen = set(vertices)
    components = 0
    adjacency = {vertex: set() for vertex in vertices}
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            vertex = stack.pop()
            for neighbor in tuple(adjacency[vertex] & unseen):
                unseen.remove(neighbor)
                stack.append(neighbor)

    return {
        "mask": mask,
        "branches": branches,
        "intact_fibers": len(vertices),
        "induced_KG_edges": len(edges),
        "induced_KG_triangles": len(triangles),
        "closed_KG_edges": closed_edges,
        "minimum_degree": min(degrees[vertex] for vertex in vertices),
        "cycle_rank": len(edges) - len(vertices) + components,
        "components": components,
    }


def canonical_profile_bytes(profiles) -> bytes:
    return (
        json.dumps(profiles, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()


def canonical_mapping_bytes(mapping) -> bytes:
    return (json.dumps(mapping, separators=(",", ":")) + "\n").encode()


def audit() -> dict[str, object]:
    orbit_report = orbit_audit()
    representatives = orbit_report["representatives"]
    masks = [intact_mask(state) for state in representatives]
    canonical_masks = [canonical_mask(mask) for mask in masks]
    canonical_counts = Counter(canonical_masks)
    ordered_masks = sorted(canonical_counts)
    profile_index = {mask: index for index, mask in enumerate(ordered_masks)}
    branch_profile_indices = [profile_index[mask] for mask in canonical_masks]
    profiles = [
        profile(mask, canonical_counts[mask])
        for mask in ordered_masks
    ]
    payload = canonical_profile_bytes(profiles)
    mapping_payload = canonical_mapping_bytes(branch_profile_indices)

    branch_histogram = Counter(mask.bit_count() for mask in masks)
    profile_histogram = Counter(item["intact_fibers"] for item in profiles)
    mapped_counts = Counter(branch_profile_indices)

    assert len(masks) == 701
    assert len(set(masks)) == 64
    assert len(profiles) == 41
    assert len(branch_profile_indices) == 701
    assert set(branch_profile_indices) == set(range(41))
    assert all(mapped_counts[index] == profiles[index]["branches"] for index in range(41))
    assert branch_histogram == Counter({13: 163, 14: 190, 15: 164, 16: 111, 17: 59, 18: 14})
    assert profile_histogram == Counter({13: 9, 14: 11, 15: 11, 16: 2, 17: 6, 18: 2})
    assert sum(item["branches"] for item in profiles) == 701
    assert min(item["closed_KG_edges"] for item in profiles) == 0
    assert max(item["closed_KG_edges"] for item in profiles) == 43
    assert hashlib.sha256(payload).hexdigest() == "0bb5b5453b83ca49e27027b227d1ca271475021bc75ed15d1eee19cad54f0e96"

    return {
        "PASS": True,
        "completed_transition_orbits": len(masks),
        "labelled_intact_masks": len(set(masks)),
        "S7_intact_core_orbits": len(profiles),
        "branch_intact_fiber_histogram": {
            str(size): count for size, count in sorted(branch_histogram.items())
        },
        "core_orbit_intact_fiber_histogram": {
            str(size): count for size, count in sorted(profile_histogram.items())
        },
        "minimum_closed_KG_edges": min(item["closed_KG_edges"] for item in profiles),
        "maximum_closed_KG_edges": max(item["closed_KG_edges"] for item in profiles),
        "profiles_sha256": hashlib.sha256(payload).hexdigest(),
        "branch_profile_indices_sha256": hashlib.sha256(mapping_payload).hexdigest(),
        "branch_profile_indices": branch_profile_indices,
        "profiles": profiles,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
