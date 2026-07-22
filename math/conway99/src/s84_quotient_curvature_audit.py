#!/usr/bin/env python3
"""Exact S7-orbit and F3-linear reduction of s=84 holonomy curvature."""
from __future__ import annotations

import json
from collections import deque
from itertools import combinations

from s84_holonomy_audit import gf2_nullspace, matching_complex


def audit() -> dict[str, object]:
    """Reduce all parity-curvature supports to four S7 orbit types.

    Write S3 as C3 semidirect C2. Once the parity support z is fixed, the
    edge-parity cochain is unique after spanning-tree gauge fixing because
    H^1(M_7; F2)=0. On every uncurved triangle, the C3 coordinate of the
    holonomy must vanish, giving a homogeneous linear system over F3.
    """
    fibers = list(combinations(range(7), 2))
    fiber_index = {fiber: i for i, fiber in enumerate(fibers)}
    edges, triangles, boundary = matching_complex()
    edge_index = {edge: i for i, edge in enumerate(edges)}
    triangle_index = {triangle: i for i, triangle in enumerate(triangles)}

    kernel = gf2_nullspace(boundary, 105)
    gram_rows = []
    for k in kernel:
        row = 0
        for j, other in enumerate(kernel):
            if (k & other).bit_count() & 1:
                row |= 1 << j
        gram_rows.append(row)
    coefficient_kernel = gf2_nullspace(gram_rows, len(kernel))
    intersection_basis = []
    for coeffs in coefficient_kernel:
        z = 0
        for i, vector in enumerate(kernel):
            if (coeffs >> i) & 1:
                z ^= vector
        intersection_basis.append(z)
    supports = set()
    for mask in range(1 << len(intersection_basis)):
        z = 0
        for i, vector in enumerate(intersection_basis):
            if (mask >> i) & 1:
                z ^= vector
        supports.add(z)
    assert len(supports) == 256

    generator_maps = []
    for swap in range(6):
        base_permutation = list(range(7))
        base_permutation[swap], base_permutation[swap + 1] = (
            base_permutation[swap + 1], base_permutation[swap]
        )
        fiber_map = []
        for a, b in fibers:
            image = tuple(sorted((base_permutation[a], base_permutation[b])))
            fiber_map.append(fiber_index[image])
        triangle_map = []
        for triangle in triangles:
            image = tuple(sorted(fiber_map[x] for x in triangle))
            triangle_map.append(triangle_index[image])
        generator_maps.append(triangle_map)

    def act(support: int, mapping: list[int]) -> int:
        image = 0
        while support:
            bit = support & -support
            i = bit.bit_length() - 1
            image |= 1 << mapping[i]
            support ^= bit
        return image

    orbits = []
    remaining = set(supports)
    while remaining:
        seed = remaining.pop()
        orbit = {seed}
        stack = [seed]
        while stack:
            current = stack.pop()
            for mapping in generator_maps:
                image = act(current, mapping)
                if image not in orbit:
                    orbit.add(image)
                    remaining.discard(image)
                    stack.append(image)
        orbits.append(orbit)
    orbit_signature = sorted((next(iter(orbit)).bit_count(), len(orbit)) for orbit in orbits)
    assert orbit_signature == [(0, 1), (48, 105), (56, 30), (56, 120)]

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
    tree_edge_ids = {edge_index[tuple(sorted((v, parent[v])))] for v in range(1, 21)}
    non_tree = [i for i in range(105) if i not in tree_edge_ids]
    non_tree_position = {edge: i for i, edge in enumerate(non_tree)}
    assert len(non_tree) == 85

    def solve_edge_parity(support: int) -> int:
        equations = []
        for t, (a, b, c) in enumerate(triangles):
            mask = 0
            for edge in ((a, b), (b, c), (a, c)):
                edge_id = edge_index[edge]
                if edge_id in non_tree_position:
                    mask ^= 1 << non_tree_position[edge_id]
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
        edge_parity = 0
        for edge_id, position in non_tree_position.items():
            if (solution >> position) & 1:
                edge_parity |= 1 << edge_id
        return edge_parity

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

    summaries = []
    for orbit in sorted(orbits, key=lambda o: (next(iter(o)).bit_count(), len(o))):
        ranks = set()
        for support in orbit:
            edge_parity = solve_edge_parity(support)
            equations_mod_3 = []
            for t, (a, b, c) in enumerate(triangles):
                if (support >> t) & 1:
                    continue
                eab = edge_index[(a, b)]
                ebc = edge_index[(b, c)]
                eac = edge_index[(a, c)]
                eb = (edge_parity >> ebc) & 1
                ec = (edge_parity >> eac) & 1
                coefficients = [0] * 85
                signed_terms = (
                    (eab, -1 if (ec + eb) & 1 else 1),
                    (ebc, -1 if ec else 1),
                    (eac, 1 if ec else -1),
                )
                for edge_id, coefficient in signed_terms:
                    if edge_id in non_tree_position:
                        position = non_tree_position[edge_id]
                        coefficients[position] = (coefficients[position] + coefficient) % 3
                equations_mod_3.append(coefficients)
            rank = rank_mod_3(equations_mod_3)
            ranks.add((len(equations_mod_3), rank, 85 - rank))
        assert len(ranks) == 1
        equation_count, rank, nullity = ranks.pop()
        summaries.append({
            "support_weight": next(iter(orbit)).bit_count(),
            "S7_orbit_size": len(orbit),
            "uncurved_triangle_equations": equation_count,
            "rank_over_F3": rank,
            "gauge_fixed_F3_nullity": nullity,
        })

    assert summaries == [
        {"support_weight": 0, "S7_orbit_size": 1, "uncurved_triangle_equations": 105, "rank_over_F3": 84, "gauge_fixed_F3_nullity": 1},
        {"support_weight": 48, "S7_orbit_size": 105, "uncurved_triangle_equations": 57, "rank_over_F3": 57, "gauge_fixed_F3_nullity": 28},
        {"support_weight": 56, "S7_orbit_size": 30, "uncurved_triangle_equations": 49, "rank_over_F3": 49, "gauge_fixed_F3_nullity": 36},
        {"support_weight": 56, "S7_orbit_size": 120, "uncurved_triangle_equations": 49, "rank_over_F3": 49, "gauge_fixed_F3_nullity": 36},
    ]
    return {
        "PASS": True,
        "parity_support_S7_orbits": summaries,
        "consequence": (
            "The 256 parity supports reduce to four base-symmetry types; after parity gauge fixing, "
            "their S3 quotient layers are linear systems over F3 of nullity 1, 28, or 36."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
