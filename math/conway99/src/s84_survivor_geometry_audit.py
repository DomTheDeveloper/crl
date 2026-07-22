#!/usr/bin/env python3
"""Classify the geometry of the thirty surviving ``s = 84`` supports."""
from __future__ import annotations

import json
from collections import Counter
from itertools import combinations

from s84_conjugacy_filter_audit import DSU, solve_class_csp, topology


def unique_assignment(support, edge_triangles):
    dsu = DSU(105)
    for incident in edge_triangles:
        if sum((support >> triangle) & 1 for triangle in incident) == 2:
            dsu.union(incident[0], incident[1])
            dsu.union(incident[0], incident[2])

    roots = sorted({dsu.find(i) for i in range(105)})
    root_index = {root: i for i, root in enumerate(roots)}
    component = [root_index[dsu.find(i)] for i in range(105)]
    forced = {}
    constraints = []

    for incident in edge_triangles:
        if any((support >> triangle) & 1 for triangle in incident):
            continue
        multiplicity = Counter(component[triangle] for triangle in incident)
        if len(multiplicity) == 2:
            repeated = next(v for v, n in multiplicity.items() if n == 2)
            singleton = next(v for v, n in multiplicity.items() if n == 1)
            for variable, value in ((repeated, 0), (singleton, 1)):
                assert variable not in forced or forced[variable] == value
                forced[variable] = value
        elif len(multiplicity) == 3:
            constraints.append(tuple(multiplicity))
        else:
            return None

    assert not constraints
    assert len(forced) == len(roots) == 8
    return [forced[component[triangle]] for triangle in range(105)]


def audit():
    supports, edge_triangles = topology()
    fibers = list(combinations(range(7), 2))
    triangles = [
        triangle
        for triangle in combinations(range(21), 3)
        if all(
            set(fibers[a]).isdisjoint(fibers[b])
            for a, b in combinations(triangle, 2)
        )
    ]

    survivors = [
        support
        for support in supports
        if solve_class_csp(support, edge_triangles)[0]
    ]
    assert len(survivors) == 30

    signatures = Counter()
    for support in survivors:
        class_bits = unique_assignment(support, edge_triangles)
        signatures[
            tuple(
                sorted(
                    Counter(
                        ((support >> triangle) & 1, class_bits[triangle])
                        for triangle in range(105)
                    ).items()
                )
            )
        ] += 1

        identity_triangles = [
            triangle
            for triangle in range(105)
            if not ((support >> triangle) & 1) and class_bits[triangle]
        ]
        assert len(identity_triangles) == 7

        fiber_use = Counter(
            vertex
            for triangle in identity_triangles
            for vertex in triangles[triangle]
        )
        assert fiber_use == Counter({vertex: 1 for vertex in range(21)})

        omitted_points = []
        used_k7_edges = []
        for triangle in identity_triangles:
            k7_edges = [fibers[vertex] for vertex in triangles[triangle]]
            used_k7_edges.extend(k7_edges)
            covered = set().union(*(set(edge) for edge in k7_edges))
            assert len(covered) == 6
            omitted_points.append(next(iter(set(range(7)) - covered)))

        assert sorted(omitted_points) == list(range(7))
        assert Counter(used_k7_edges) == Counter({edge: 1 for edge in fibers})

    expected_signature = tuple(
        sorted({(1, 0): 56, (0, 0): 42, (0, 1): 7}.items())
    )
    assert signatures == Counter({expected_signature: 30})

    return {
        "PASS": True,
        "surviving_supports": 30,
        "identity_holonomies_per_support": 7,
        "double_transposition_holonomies_per_support": 42,
        "transposition_holonomies_per_support": 56,
        "four_cycle_holonomies_per_support": 0,
        "geometry": (
            "The seven identity triangles partition the 21 K7-edge fibers and form "
            "a near-one-factorization of K7, with one omitted base point per triangle."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
