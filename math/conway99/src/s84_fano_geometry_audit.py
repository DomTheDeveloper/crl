#!/usr/bin/env python3
"""Identify the surviving ``s = 84`` support with the Fano geometry."""
from __future__ import annotations

import json
from itertools import combinations, permutations

from s84_conjugacy_filter_audit import solve_class_csp, topology
from s84_survivor_geometry_audit import unique_assignment


def audit():
    supports, edge_triangles = topology()
    survivors = [
        support
        for support in supports
        if solve_class_csp(support, edge_triangles)[0]
    ]
    assert len(survivors) == 30

    fibers = list(combinations(range(7), 2))
    fiber_index = {fiber: index for index, fiber in enumerate(fibers)}
    triangles = [
        triangle
        for triangle in combinations(range(21), 3)
        if all(
            set(fibers[a]).isdisjoint(fibers[b])
            for a, b in combinations(triangle, 2)
        )
    ]
    triangle_index = {triangle: index for index, triangle in enumerate(triangles)}

    support = survivors[0]

    # Generate the complete S7 orbit directly and compare it with the exact
    # survivor set.  This makes the coverage step independent of orbit-size
    # inference from the stabilizer order.
    orbit = set()
    support_triangles = [
        triangle for triangle in range(105) if (support >> triangle) & 1
    ]
    for permutation in permutations(range(7)):
        fiber_map = []
        for left, right in fibers:
            image = tuple(sorted((permutation[left], permutation[right])))
            fiber_map.append(fiber_index[image])
        image = 0
        for source in support_triangles:
            target = tuple(sorted(fiber_map[vertex] for vertex in triangles[source]))
            image |= 1 << triangle_index[target]
        orbit.add(image)
    assert len(orbit) == 30
    assert orbit == set(survivors)

    class_bits = unique_assignment(support, edge_triangles)
    identity_triangles = [
        triangle
        for triangle in range(105)
        if not ((support >> triangle) & 1) and class_bits[triangle]
    ]
    assert len(identity_triangles) == 7

    # Add a zero element.  Base label i represents the nonzero group element i+1.
    addition = [[None] * 8 for _ in range(8)]
    for x in range(8):
        addition[0][x] = x
        addition[x][0] = x
    for x in range(1, 8):
        addition[x][x] = 0

    for triangle in identity_triangles:
        k7_edges = [fibers[vertex] for vertex in triangles[triangle]]
        covered = set().union(*(set(edge) for edge in k7_edges))
        omitted = next(iter(set(range(7)) - covered)) + 1
        for a, b in k7_edges:
            addition[a + 1][b + 1] = omitted
            addition[b + 1][a + 1] = omitted

    assert all(entry is not None for row in addition for entry in row)
    assert all(
        addition[addition[x][y]][z] == addition[x][addition[y][z]]
        for x in range(8)
        for y in range(8)
        for z in range(8)
    )
    assert all(addition[x][x] == 0 for x in range(8))
    assert all(
        addition[x][y] == addition[y][x]
        for x in range(8)
        for y in range(8)
    )

    identity_matchings = {
        frozenset(fibers[vertex] for vertex in triangles[triangle])
        for triangle in identity_triangles
    }
    stabilizer = []
    for permutation in permutations(range(7)):
        image = {
            frozenset(
                tuple(sorted((permutation[a], permutation[b])))
                for a, b in matching
            )
            for matching in identity_matchings
        }
        if image == identity_matchings:
            stabilizer.append(permutation)
    assert len(stabilizer) == 168
    assert 5040 // len(stabilizer) == len(orbit)

    # Every stabilizer element extends by zero to an automorphism of the group.
    for permutation in stabilizer:
        extended = (0,) + tuple(permutation[i] + 1 for i in range(7))
        assert all(
            extended[addition[x][y]] == addition[extended[x]][extended[y]]
            for x in range(8)
            for y in range(8)
        )

    return {
        "PASS": True,
        "surviving_support_orbit_size": len(orbit),
        "survivor_set_equals_generated_S7_orbit": True,
        "base_permutations_checked": 5040,
        "stabilizer_order": len(stabilizer),
        "group_order": 8,
        "group_exponent": 2,
        "associativity_checks": 8**3,
        "interpretation": (
            "The seven identity triangles are the matchings {y,y+x} on "
            "F2^3 minus zero; their stabilizer is GL(3,2)."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
