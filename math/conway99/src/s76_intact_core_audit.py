#!/usr/bin/env python3
"""Worst-case audit for the intact four-fiber core in the s=76 branches.

A non-intact K7-edge fiber has lost at least one of its four short transition
edges. Therefore deficit 8 affects at most eight of the 21 fibers, leaving at
least thirteen intact Paley-9 fibers. This audit checks every choice of eight
removed fibers and records the weakest possible induced KG(7,2) core.
"""
from __future__ import annotations

import json
from itertools import combinations


def audit() -> dict[str, object]:
    fibers = list(combinations(range(7), 2))
    n = len(fibers)
    edges = [
        (i, j)
        for i, j in combinations(range(n), 2)
        if set(fibers[i]).isdisjoint(fibers[j])
    ]
    triangles = [
        (i, j, k)
        for i, j, k in combinations(range(n), 3)
        if all(set(fibers[a]).isdisjoint(fibers[b]) for a, b in combinations((i, j, k), 2))
    ]
    adjacency = [0] * n
    for i, j in edges:
        adjacency[i] |= 1 << j
        adjacency[j] |= 1 << i
    edge_masks = [(1 << i) | (1 << j) for i, j in edges]
    triangle_masks = [sum(1 << x for x in triangle) for triangle in triangles]
    full = (1 << n) - 1

    minima = {
        "induced_KG_edges": 10**9,
        "induced_KG_triangles": 10**9,
        "minimum_degree": 10**9,
        "cycle_rank": 10**9,
    }
    maximum_components = 0
    subset_count = 0

    for removed_tuple in combinations(range(n), 8):
        subset_count += 1
        removed = sum(1 << x for x in removed_tuple)
        intact = full ^ removed
        vertices = [i for i in range(n) if (intact >> i) & 1]
        edge_count = sum((mask & intact) == mask for mask in edge_masks)
        triangle_count = sum((mask & intact) == mask for mask in triangle_masks)
        degrees = [(adjacency[i] & intact).bit_count() for i in vertices]

        unseen = set(vertices)
        components = 0
        while unseen:
            components += 1
            stack = [unseen.pop()]
            while stack:
                u = stack.pop()
                neighbors = [v for v in tuple(unseen) if (adjacency[u] >> v) & 1]
                for v in neighbors:
                    unseen.remove(v)
                    stack.append(v)

        cycle_rank = edge_count - len(vertices) + components
        minima["induced_KG_edges"] = min(minima["induced_KG_edges"], edge_count)
        minima["induced_KG_triangles"] = min(minima["induced_KG_triangles"], triangle_count)
        minima["minimum_degree"] = min(minima["minimum_degree"], min(degrees))
        minima["cycle_rank"] = min(minima["cycle_rank"], cycle_rank)
        maximum_components = max(maximum_components, components)

    assert subset_count == 203490
    assert minima == {
        "induced_KG_edges": 33,
        "induced_KG_triangles": 9,
        "minimum_degree": 2,
        "cycle_rank": 21,
    }
    assert maximum_components == 1

    return {
        "PASS": True,
        "deficit": 8,
        "maximum_affected_fibers": 8,
        "minimum_intact_fibers": 13,
        "removed_fiber_subsets_checked": subset_count,
        **minima,
        "maximum_connected_components": maximum_components,
        "consequence": (
            "Every s=76 branch retains a connected permutation-block core on at least "
            "13 fibers, with at least 33 KG edges and 9 KG triangles."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
