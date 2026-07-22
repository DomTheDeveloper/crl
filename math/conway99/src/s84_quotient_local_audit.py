#!/usr/bin/env python3
"""Exact local S3-quotient audit for every s=84 parity-curvature support."""
from __future__ import annotations

import json
from collections import Counter, deque

from s84_holonomy_audit import gf2_nullspace, matching_complex


def audit() -> dict[str, object]:
    edges, triangles, boundary = matching_complex()
    edge_index = {edge: i for i, edge in enumerate(edges)}
    edge_triangles = [[] for _ in edges]
    for t, triangle in enumerate(triangles):
        for i in range(3):
            for j in range(i + 1, 3):
                edge = (triangle[i], triangle[j])
                edge_triangles[edge_index[edge]].append(t)
    assert all(len(ts) == 3 for ts in edge_triangles)

    kernel = gf2_nullspace(boundary, 105)
    gram_rows = []
    for k in kernel:
        row = 0
        for j, other in enumerate(kernel):
            if (k & other).bit_count() & 1:
                row |= 1 << j
        gram_rows.append(row)
    coefficient_kernel = gf2_nullspace(gram_rows, len(kernel))
    support_basis = []
    for coeffs in coefficient_kernel:
        support = 0
        for i, vector in enumerate(kernel):
            if (coeffs >> i) & 1:
                support ^= vector
        support_basis.append(support)
    supports = []
    for mask in range(1 << len(support_basis)):
        support = 0
        for i, vector in enumerate(support_basis):
            if (mask >> i) & 1:
                support ^= vector
        supports.append(support)
    assert len(set(supports)) == 256

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
    tree_ids = {edge_index[tuple(sorted((v, parent[v])))] for v in range(1, 21)}
    non_tree = [edge for edge in range(105) if edge not in tree_ids]
    position = {edge: i for i, edge in enumerate(non_tree)}
    assert len(non_tree) == 85

    triangle_edges = [
        (
            edge_index[(a, b)],
            edge_index[(b, c)],
            edge_index[(a, c)],
        )
        for a, b, c in triangles
    ]

    def solve_parity(support: int) -> int:
        equations = []
        for t, edge_ids in enumerate(triangle_edges):
            mask = 0
            for edge in edge_ids:
                if edge in position:
                    mask ^= 1 << position[edge]
            equations.append([mask, (support >> t) & 1])
        row = 0
        pivots = {}
        for col in range(85):
            pivot = next((i for i in range(row, len(equations)) if (equations[i][0] >> col) & 1), None)
            if pivot is None:
                continue
            equations[row], equations[pivot] = equations[pivot], equations[row]
            pmask, prhs = equations[row]
            for i in range(len(equations)):
                if i != row and ((equations[i][0] >> col) & 1):
                    equations[i][0] ^= pmask
                    equations[i][1] ^= prhs
            pivots[col] = row
            row += 1
        assert len(pivots) == 85
        assert all(mask or not rhs for mask, rhs in equations)
        solution = 0
        for col, equation in pivots.items():
            if equations[equation][1]:
                solution |= 1 << col
        parity = 0
        for edge, col in position.items():
            if (solution >> col) & 1:
                parity |= 1 << edge
        return parity

    def oriented_form(u: int, v: int, parity: int) -> tuple[list[int], int]:
        edge = edge_index[(min(u, v), max(u, v))]
        bit = (parity >> edge) & 1
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
            [(a + sign * b) % 3 for a, b in zip(left_form, right_form)],
            left_parity ^ right_parity,
        )

    def based_holonomy(e: int, f: int, g: int, parity: int):
        # Transport e -> g -> f -> e, so all three edge-local holonomies are
        # compared in the same frame at e.
        return product(
            oriented_form(f, e, parity),
            product(oriented_form(g, f, parity), oriented_form(e, g, parity)),
        )

    def rank_mod_3(rows: list[list[int]]) -> int:
        work = [row[:] for row in rows if any(x % 3 for x in row)]
        rank = 0
        for col in range(85):
            pivot = next((i for i in range(rank, len(work)) if work[i][col] % 3), None)
            if pivot is None:
                continue
            work[rank], work[pivot] = work[pivot], work[rank]
            scale = 1 if work[rank][col] % 3 == 1 else 2
            work[rank] = [(scale * x) % 3 for x in work[rank]]
            for i in range(len(work)):
                if i != rank and work[i][col] % 3:
                    factor = work[i][col] % 3
                    work[i] = [(x - factor * y) % 3 for x, y in zip(work[i], work[rank])]
            rank += 1
        return rank

    signatures = Counter()
    for support in supports:
        parity = solve_parity(support)
        rows_mod_3 = []

        for t, (a, b, c) in enumerate(triangles):
            form, curved = based_holonomy(a, b, c, parity)
            assert curved == ((support >> t) & 1)
            if not curved:
                rows_mod_3.append(form)

        curved_edge_count = 0
        for edge, (e, f) in enumerate(edges):
            curved_thirds = []
            for t in edge_triangles[edge]:
                if (support >> t) & 1:
                    triangle = triangles[t]
                    curved_thirds.append(next(x for x in triangle if x not in (e, f)))
            assert len(curved_thirds) in (0, 2)
            if len(curved_thirds) == 2:
                curved_edge_count += 1
                first, p1 = based_holonomy(e, f, curved_thirds[0], parity)
                second, p2 = based_holonomy(e, f, curved_thirds[1], parity)
                assert p1 == p2 == 1
                rows_mod_3.append([(x - y) % 3 for x, y in zip(first, second)])

        rank = rank_mod_3(rows_mod_3)
        signatures[(support.bit_count(), curved_edge_count, len(rows_mod_3), rank, 85 - rank)] += 1

    expected = Counter({
        (0, 0, 105, 84, 1): 1,
        (48, 72, 129, 84, 1): 105,
        (56, 84, 133, 84, 1): 150,
    })
    assert signatures == expected

    return {
        "PASS": True,
        "supports_checked": 256,
        "signature_counts": {
            str(signature): count for signature, count in sorted(signatures.items())
        },
        "consequence": (
            "After spanning-tree gauge fixing, every allowed parity support has exactly "
            "one free F3 parameter in the S3 quotient. Thus each support has exactly "
            "three gauge-fixed quotient connections before restoring the 21 fiber C4 colors."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
