#!/usr/bin/env python3
"""Exact finite audit for the permutation/holonomy reduction of the s=84 branch.

The 21 four-vertex fibers are the vertices of KG(7,2). Every edge of KG(7,2)
carries a permutation of the four points. The reduced common-neighbor equations
become small matrix identities for the holonomies around the 105 triangles of
the matching complex M_7.

This file uses only exact integer and GF(2) arithmetic.
"""
from __future__ import annotations

import json
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations, permutations

POINTS = ((0, 0), (0, 1), (1, 0), (1, 1))
PERMS = tuple(permutations(range(4)))
IDENTITY4 = PERMS.index((0, 1, 2, 3))


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Return p after q."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def permutation_matrix(p: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    # Source rows, destination columns.
    return tuple(tuple(int(p[i] == j) for j in range(4)) for i in range(4))


PMATS = tuple(permutation_matrix(p) for p in PERMS)
PMAT_INDEX = {m: i for i, m in enumerate(PMATS)}
I4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
J4 = tuple((1, 1, 1, 1) for _ in range(4))
A4 = tuple(
    tuple(int(sum(a != b for a, b in zip(POINTS[i], POINTS[j])) == 1) for j in range(4))
    for i in range(4)
)


def conjugated_cycle(p: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(A4[p[i]][p[j]] for j in range(4)) for i in range(4))


def cycle_type(p: tuple[int, ...]) -> tuple[int, ...]:
    seen = [False] * len(p)
    lengths = []
    for i in range(len(p)):
        if seen[i]:
            continue
        j = i
        length = 0
        while not seen[j]:
            seen[j] = True
            length += 1
            j = p[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def parity(p: tuple[int, ...]) -> int:
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) & 1


def residual_matrix(target, left, right):
    return tuple(
        tuple(target[i][j] - left[i][j] - right[i][j] for j in range(4))
        for i in range(4)
    )


def disjoint_edge_holonomy_audit() -> dict[str, object]:
    """Classify the three triangle holonomies incident with one KG edge.

    If P is the cross-fiber permutation, the exact common-neighbor equations are

        I + A + P A P^T + T_1 + T_2 + T_3 = 2 J,

    where the T_i are the three triangle-holonomy permutation matrices.
    """
    automorphism_counts = Counter()
    pattern_counts = {"cycle_preserving": Counter(), "cycle_changing": Counter()}
    odd_incidence_counts = Counter()

    for p in PERMS:
        pap = conjugated_cycle(p)
        target = tuple(
            tuple(2 - I4[i][j] - A4[i][j] - pap[i][j] for j in range(4))
            for i in range(4)
        )
        triples = []
        for a, ma in enumerate(PMATS):
            for b, mb in enumerate(PMATS):
                needed = residual_matrix(target, ma, mb)
                c = PMAT_INDEX.get(needed)
                if c is not None:
                    triples.append((a, b, c))

        preserving = pap == A4
        expected = 9 if preserving else 24
        assert len(triples) == expected
        key = "cycle_preserving" if preserving else "cycle_changing"
        automorphism_counts[key] += 1

        for triple in triples:
            types = tuple(sorted(cycle_type(PERMS[x]) for x in triple))
            pattern_counts[key][str(types)] += 1
            odd = sum(parity(PERMS[x]) for x in triple)
            assert odd in (0, 2)
            odd_incidence_counts[odd] += 1

    assert automorphism_counts == Counter({"cycle_preserving": 8, "cycle_changing": 16})
    allowed_preserving = {
        str(((1, 1, 1, 1), (2, 2), (2, 2))),
        str(((2, 1, 1), (2, 1, 1), (2, 2))),
    }
    allowed_changing = allowed_preserving | {str(((1, 1, 1, 1), (4,), (4,)))}
    assert set(pattern_counts["cycle_preserving"]) == allowed_preserving
    assert set(pattern_counts["cycle_changing"]) == allowed_changing

    return {
        "cross_permutations_preserving_C4": automorphism_counts["cycle_preserving"],
        "cross_permutations_changing_C4": automorphism_counts["cycle_changing"],
        "ordered_holonomy_triples_per_preserving_edge": 9,
        "ordered_holonomy_triples_per_changing_edge": 24,
        "allowed_cycle_type_multisets": {
            key: sorted(counter) for key, counter in pattern_counts.items()
        },
        "odd_triangle_holonomies_incident_to_each_edge": [0, 2],
    }


def intersecting_pair_holonomy_audit() -> dict[str, int]:
    """Audit the six holonomies attached to two fibers sharing one K7 point."""
    same_sign = tuple(
        tuple(int(POINTS[u][0] == POINTS[v][0]) for v in range(4))
        for u in range(4)
    )
    target = tuple(tuple(2 - same_sign[i][j] for j in range(4)) for i in range(4))
    flat_target = tuple(x for row in target for x in row)
    flat_pmats = tuple(tuple(x for row in m for x in row) for m in PMATS)

    @lru_cache(maxsize=None)
    def ordered_count(remaining: int, residual: tuple[int, ...]) -> int:
        if remaining == 0:
            return int(not any(residual))
        total = 0
        for m in flat_pmats:
            nxt = tuple(a - b for a, b in zip(residual, m))
            if min(nxt) >= 0:
                total += ordered_count(remaining - 1, nxt)
        return total

    multiset_count = 0

    def enumerate_multisets(start: int, remaining: int, residual: tuple[int, ...]) -> None:
        nonlocal multiset_count
        if remaining == 0:
            multiset_count += int(not any(residual))
            return
        for i in range(start, len(flat_pmats)):
            nxt = tuple(a - b for a, b in zip(residual, flat_pmats[i]))
            if min(nxt) >= 0:
                enumerate_multisets(i, remaining - 1, nxt)

    ordered = ordered_count(6, flat_target)
    enumerate_multisets(0, 6, flat_target)
    assert ordered == 35280
    assert multiset_count == 58
    return {
        "ordered_six_holonomy_decompositions": ordered,
        "unordered_multisets": multiset_count,
    }


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for row in rows:
        x = row
        while x:
            pivot = x.bit_length() - 1
            if pivot in basis:
                x ^= basis[pivot]
            else:
                basis[pivot] = x
                break
    return len(basis)


def gf2_nullspace(rows: list[int], ncols: int) -> list[int]:
    work = [row for row in rows if row]
    pivots: list[int] = []
    r = 0
    for col in range(ncols):
        pivot = next((i for i in range(r, len(work)) if (work[i] >> col) & 1), None)
        if pivot is None:
            continue
        work[r], work[pivot] = work[pivot], work[r]
        for i in range(len(work)):
            if i != r and ((work[i] >> col) & 1):
                work[i] ^= work[r]
        pivots.append(col)
        r += 1
        if r == len(work):
            break
    free = [c for c in range(ncols) if c not in set(pivots)]
    basis = []
    for f in free:
        vector = 1 << f
        for row_index, pivot in enumerate(pivots):
            if (work[row_index] >> f) & 1:
                vector |= 1 << pivot
        assert all((row & vector).bit_count() % 2 == 0 for row in rows)
        basis.append(vector)
    return basis


def matching_complex() -> tuple[list[tuple[int, int]], list[tuple[int, int, int]], list[int]]:
    fibers = list(combinations(range(7), 2))
    edges = [
        (i, j)
        for i, j in combinations(range(21), 2)
        if set(fibers[i]).isdisjoint(fibers[j])
    ]
    edge_index = {edge: i for i, edge in enumerate(edges)}
    triangles = [
        (a, b, c)
        for a, b, c in combinations(range(21), 3)
        if (a, b) in edge_index and (a, c) in edge_index and (b, c) in edge_index
    ]
    boundary_rows = [0] * len(edges)
    for t, triangle in enumerate(triangles):
        for a, b in combinations(triangle, 2):
            boundary_rows[edge_index[(min(a, b), max(a, b))]] |= 1 << t
    assert len(fibers) == 21 and len(edges) == 105 and len(triangles) == 105
    return edges, triangles, boundary_rows


def parity_curvature_audit() -> dict[str, object]:
    """Classify every possible support of odd triangle holonomy.

    Local holonomy classification says every KG edge is incident with 0 or 2 odd
    triangle holonomies, so z lies in ker(B). Since permutation parity is a group
    homomorphism, z is also the coboundary of the edge-parity cochain, hence lies
    in row(B). The intersection is only eight-dimensional.
    """
    _, _, boundary = matching_complex()
    rank = gf2_rank(boundary)
    kernel = gf2_nullspace(boundary, 105)
    assert rank == 85 and len(kernel) == 20

    # z = sum a_i kernel_i is in row(B) iff it is orthogonal to ker(B).
    gram_rows = []
    for k in kernel:
        row = 0
        for j, other in enumerate(kernel):
            if (k & other).bit_count() & 1:
                row |= 1 << j
        gram_rows.append(row)
    coefficient_kernel = gf2_nullspace(gram_rows, len(kernel))
    assert len(coefficient_kernel) == 8

    intersection_basis = []
    for coeffs in coefficient_kernel:
        z = 0
        for i, vector in enumerate(kernel):
            if (coeffs >> i) & 1:
                z ^= vector
        intersection_basis.append(z)

    weights = Counter()
    for mask in range(1 << len(intersection_basis)):
        z = 0
        for i, vector in enumerate(intersection_basis):
            if (mask >> i) & 1:
                z ^= vector
        weights[z.bit_count()] += 1
    assert weights == Counter({56: 150, 48: 105, 0: 1})

    return {
        "matching_complex_vertices": 21,
        "matching_complex_edges": 105,
        "matching_complex_triangles": 105,
        "boundary_rank_mod_2": rank,
        "two_cycle_dimension": len(kernel),
        "cycle_coboundary_intersection_dimension": len(intersection_basis),
        "odd_holonomy_support_weight_enumerator": {
            str(weight): count for weight, count in sorted(weights.items())
        },
        "consequence": "odd holonomy support is empty, or has exactly 48 or 56 triangles",
    }


def flat_s3_connection_audit() -> dict[str, object]:
    """Enumerate gauge-fixed flat S3 connections on the matching complex."""
    edges, triangles, _ = matching_complex()
    edge_index = {edge: i for i, edge in enumerate(edges)}

    # A spanning tree fixes the vertex-frame gauge.
    adjacency = [[] for _ in range(21)]
    for a, b in edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    parent = [None] * 21
    parent[0] = -1
    queue = deque([0])
    order = [0]
    while queue:
        a = queue.popleft()
        for b in adjacency[a]:
            if parent[b] is None:
                parent[b] = a
                queue.append(b)
                order.append(b)
    assert len(order) == 21
    tree_edges = {tuple(sorted((v, parent[v]))) for v in range(1, 21)}

    s3 = tuple(permutations(range(3)))
    identity = s3.index((0, 1, 2))
    multiplication = tuple(
        tuple(s3.index(compose(p, q)) for q in s3)
        for p in s3
    )

    constraints = []
    incidence = [[] for _ in edges]
    allowed = tuple((x, y, multiplication[y][x]) for x in range(6) for y in range(6))
    for triangle in triangles:
        a, b, c = triangle
        variables = (edge_index[(a, b)], edge_index[(b, c)], edge_index[(a, c)])
        ci = len(constraints)
        constraints.append(variables)
        for variable in variables:
            incidence[variable].append(ci)

    all_values = (1 << 6) - 1
    domains = [all_values] * len(edges)
    for edge in tree_edges:
        domains[edge_index[edge]] = 1 << identity

    def propagate(current: list[int]) -> bool:
        pending = list(range(len(constraints)))
        in_pending = set(pending)
        while pending:
            ci = pending.pop()
            in_pending.discard(ci)
            a, b, c = constraints[ci]
            da, db, dc = current[a], current[b], current[c]
            sa = sb = sc = 0
            for x, y, z in allowed:
                if ((da >> x) & 1) and ((db >> y) & 1) and ((dc >> z) & 1):
                    sa |= 1 << x
                    sb |= 1 << y
                    sc |= 1 << z
            if not sa or not sb or not sc:
                return False
            for variable, reduced in ((a, sa), (b, sb), (c, sc)):
                if reduced != current[variable]:
                    current[variable] = reduced
                    for cj in incidence[variable]:
                        if cj not in in_pending:
                            pending.append(cj)
                            in_pending.add(cj)
        return True

    solutions: list[tuple[int, ...]] = []
    nodes = 0

    def search(current: list[int]) -> None:
        nonlocal nodes
        nodes += 1
        if not propagate(current):
            return
        unresolved = [(mask.bit_count(), i) for i, mask in enumerate(current) if mask.bit_count() > 1]
        if not unresolved:
            solutions.append(tuple(mask.bit_length() - 1 for mask in current))
            return
        _, variable = min(unresolved)
        mask = current[variable]
        for value in range(6):
            if (mask >> value) & 1:
                child = current.copy()
                child[variable] = 1 << value
                search(child)

    search(domains)
    assert len(solutions) == 3
    distributions = []
    for solution in solutions:
        distributions.append(Counter(cycle_type(s3[x]) for x in solution))
    assert distributions[0] == Counter({(1, 1, 1): 105})
    assert all(
        distribution == Counter({(1, 1, 1): 57, (3,): 48})
        for distribution in distributions[1:]
    )

    return {
        "spanning_tree_edges_fixed": len(tree_edges),
        "search_nodes": nodes,
        "gauge_fixed_flat_connections": len(solutions),
        "classes": [
            {str(cycle): count for cycle, count in sorted(distribution.items())}
            for distribution in distributions
        ],
        "interpretation": "one trivial class and an inverse pair of C3-valued classes",
    }


def audit() -> dict[str, object]:
    return {
        "PASS": True,
        "disjoint_edge_holonomy": disjoint_edge_holonomy_audit(),
        "intersecting_pair_holonomy": intersecting_pair_holonomy_audit(),
        "parity_curvature": parity_curvature_audit(),
        "flat_S3_quotient": flat_s3_connection_audit(),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
