#!/usr/bin/env python3
"""Reusable exact connection data for the surviving ``s = 84`` support."""
from __future__ import annotations

import json
from collections import Counter, deque
from itertools import combinations

from s84_conjugacy_filter_audit import solve_class_csp, topology
from s84_survivor_geometry_audit import unique_assignment


def compose3(p, q):
    return tuple(p[q[i]] for i in range(3))


def power3(p, n):
    out = (0, 1, 2)
    for _ in range(n):
        out = compose3(p, out)
    return out


R3 = (1, 2, 0)
S3 = (0, 2, 1)


def s3_permutation(x, parity):
    return compose3(power3(R3, x % 3), S3 if parity else (0, 1, 2))


def nullspace_mod3(rows, ncols):
    work = [row[:] for row in rows]
    pivots = []
    rank = 0
    for col in range(ncols):
        pivot = next(
            (i for i in range(rank, len(work)) if work[i][col] % 3),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        inverse = 1 if work[rank][col] % 3 == 1 else 2
        work[rank] = [(inverse * x) % 3 for x in work[rank]]
        for i in range(len(work)):
            if i != rank and work[i][col] % 3:
                factor = work[i][col] % 3
                work[i] = [
                    (x - factor * y) % 3
                    for x, y in zip(work[i], work[rank])
                ]
        pivots.append(col)
        rank += 1

    pivot_set = set(pivots)
    basis = []
    for free in (c for c in range(ncols) if c not in pivot_set):
        vector = [0] * ncols
        vector[free] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = (-work[i][free]) % 3
        assert all(
            sum(a * b for a, b in zip(row, vector)) % 3 == 0
            for row in rows
        )
        basis.append(vector)
    return basis


def build():
    supports, topological_edge_triangles = topology()
    survivors = [
        support
        for support in supports
        if solve_class_csp(support, topological_edge_triangles)[0]
    ]
    support = min(survivors)
    class_bits = unique_assignment(support, topological_edge_triangles)

    fibers = list(combinations(range(7), 2))
    edges = [
        (i, j)
        for i, j in combinations(range(21), 2)
        if set(fibers[i]).isdisjoint(fibers[j])
    ]
    edge_index = {edge: i for i, edge in enumerate(edges)}
    triangles = [
        triangle
        for triangle in combinations(range(21), 3)
        if all(
            set(fibers[a]).isdisjoint(fibers[b])
            for a, b in combinations(triangle, 2)
        )
    ]
    edge_triangles = [[] for _ in edges]
    for triangle_index, triangle in enumerate(triangles):
        for edge in combinations(triangle, 2):
            edge_triangles[edge_index[edge]].append(triangle_index)

    adjacency = [[] for _ in range(21)]
    for a, b in edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    parent = [None] * 21
    parent[0] = -1
    queue = deque([0])
    while queue:
        a = queue.popleft()
        for b in adjacency[a]:
            if parent[b] is None:
                parent[b] = a
                queue.append(b)

    tree_edges = {
        edge_index[tuple(sorted((vertex, parent[vertex])))]
        for vertex in range(1, 21)
    }
    non_tree = [edge for edge in range(105) if edge not in tree_edges]
    position = {edge: i for i, edge in enumerate(non_tree)}
    assert len(non_tree) == 85

    # Unique tree-gauged edge parity with the chosen curvature support.
    equations = []
    for triangle_index, (a, b, c) in enumerate(triangles):
        mask = 0
        for edge in ((a, b), (b, c), (a, c)):
            edge_id = edge_index[edge]
            if edge_id in position:
                mask ^= 1 << position[edge_id]
        equations.append([mask, (support >> triangle_index) & 1])

    row = 0
    pivots = {}
    for col in range(85):
        pivot = next(
            (
                i
                for i in range(row, len(equations))
                if (equations[i][0] >> col) & 1
            ),
            None,
        )
        if pivot is None:
            continue
        equations[row], equations[pivot] = equations[pivot], equations[row]
        pivot_mask, pivot_rhs = equations[row]
        for i in range(len(equations)):
            if i != row and ((equations[i][0] >> col) & 1):
                equations[i][0] ^= pivot_mask
                equations[i][1] ^= pivot_rhs
        pivots[col] = row
        row += 1

    assert len(pivots) == 85
    assert all(mask or not rhs for mask, rhs in equations)
    solution = 0
    for col, equation in pivots.items():
        if equations[equation][1]:
            solution |= 1 << col

    edge_parity = 0
    for edge, col in position.items():
        if (solution >> col) & 1:
            edge_parity |= 1 << edge

    def oriented_form(u, v):
        edge = edge_index[(min(u, v), max(u, v))]
        bit = (edge_parity >> edge) & 1
        form = [0] * 85
        if edge in position:
            coefficient = 1
            if u > v:
                coefficient = 1 if bit else -1
            form[position[edge]] = coefficient % 3
        return form, bit

    def product(left, right):
        left_form, left_parity = left
        right_form, right_parity = right
        sign = -1 if left_parity else 1
        return (
            [
                (a + sign * b) % 3
                for a, b in zip(left_form, right_form)
            ],
            left_parity ^ right_parity,
        )

    def based_holonomy(e, f, g):
        return product(
            oriented_form(f, e),
            product(oriented_form(g, f), oriented_form(e, g)),
        )

    rows_mod_3 = []
    for triangle_index, (a, b, c) in enumerate(triangles):
        form, curved = based_holonomy(a, b, c)
        assert curved == ((support >> triangle_index) & 1)
        if not curved:
            rows_mod_3.append(form)

    for edge_id, (e, f) in enumerate(edges):
        thirds = []
        for triangle_index in edge_triangles[edge_id]:
            if (support >> triangle_index) & 1:
                thirds.append(
                    next(
                        vertex
                        for vertex in triangles[triangle_index]
                        if vertex not in (e, f)
                    )
                )
        if len(thirds) == 2:
            first, p1 = based_holonomy(e, f, thirds[0])
            second, p2 = based_holonomy(e, f, thirds[1])
            assert p1 == p2 == 1
            rows_mod_3.append(
                [(a - b) % 3 for a, b in zip(first, second)]
            )

    basis = nullspace_mod3(rows_mod_3, 85)
    assert len(basis) == 1

    return {
        "support": support,
        "class_bits": class_bits,
        "fibers": fibers,
        "edges": edges,
        "edge_index": edge_index,
        "triangles": triangles,
        "edge_triangles": edge_triangles,
        "tree_edges": tree_edges,
        "non_tree": non_tree,
        "position": position,
        "edge_parity": edge_parity,
        "f3_basis": basis[0],
    }


def edge_elements(data, parameter):
    elements = []
    for edge in range(105):
        coordinate = (
            0
            if edge not in data["position"]
            else parameter * data["f3_basis"][data["position"][edge]] % 3
        )
        elements.append((coordinate, (data["edge_parity"] >> edge) & 1))
    return elements


def audit():
    data = build()
    summaries = []
    for parameter in range(3):
        elements = edge_elements(data, parameter)
        summaries.append(
            {
                "parameter": parameter,
                "odd_edges": sum(parity for _, parity in elements),
                "nonzero_C3_edges": sum(coordinate != 0 for coordinate, _ in elements),
            }
        )

    assert data["support"].bit_count() == 56
    assert Counter(
        ((data["support"] >> triangle) & 1, data["class_bits"][triangle])
        for triangle in range(105)
    ) == Counter({(1, 0): 56, (0, 0): 42, (0, 1): 7})

    return {
        "PASS": True,
        "support_weight": 56,
        "support_orbit_size": 30,
        "edge_parity_weight": data["edge_parity"].bit_count(),
        "F3_nullity": 1,
        "connections": summaries,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
