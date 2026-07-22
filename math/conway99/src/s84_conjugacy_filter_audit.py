#!/usr/bin/env python3
"""Exact conjugacy-class filter for the ``s = 84`` holonomy reduction.

Every triangle holonomy is a permutation of four points.  Its image in
``S4 / V4 = S3`` determines whether the triangle is parity-curved.  The exact
edge-local common-neighbor equation then forces a tiny Boolean rule on the
conjugacy class of the three incident holonomies.  Combining those local rules
with the 256 topologically allowed parity supports leaves only one 30-element
``S7`` orbit.

The audit uses only exhaustive finite enumeration and GF(2) elimination.
"""
from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, permutations

POINTS = ((0, 0), (0, 1), (1, 0), (1, 1))
PERMS = tuple(permutations(range(4)))


def permutation_matrix(p):
    return tuple(tuple(int(p[i] == j) for j in range(4)) for i in range(4))


PMATS = tuple(permutation_matrix(p) for p in PERMS)
PMAT_INDEX = {matrix: i for i, matrix in enumerate(PMATS)}
I4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
A4 = tuple(
    tuple(
        int(sum(a != b for a, b in zip(POINTS[i], POINTS[j])) == 1)
        for j in range(4)
    )
    for i in range(4)
)


def conjugated_cycle(p):
    return tuple(tuple(A4[p[i]][p[j]] for j in range(4)) for i in range(4))


def parity(p):
    return sum(p[i] > p[j] for i in range(4) for j in range(i + 1, 4)) & 1


def cycle_type(p):
    seen = [False] * 4
    lengths = []
    for i in range(4):
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


def residual(target, left, right):
    return tuple(
        tuple(target[i][j] - left[i][j] - right[i][j] for j in range(4))
        for i in range(4)
    )


def holonomy_class_bit(p):
    """Encode the two possible full-S4 classes over a fixed quotient class.

    Even quotient:
      1 = identity, 0 = double transposition.
    Odd quotient:
      1 = four-cycle, 0 = transposition.
    """
    kind = cycle_type(p)
    if parity(p) == 0:
        assert kind in ((1, 1, 1, 1), (2, 2))
        return int(kind == (1, 1, 1, 1))
    assert kind in ((2, 1, 1), (4,))
    return int(kind == (4,))


def local_rule_audit():
    signatures = Counter()
    triple_count = 0
    for edge_permutation in PERMS:
        conjugate = conjugated_cycle(edge_permutation)
        target = tuple(
            tuple(2 - I4[i][j] - A4[i][j] - conjugate[i][j] for j in range(4))
            for i in range(4)
        )
        for ia, ma in enumerate(PMATS):
            for ib, mb in enumerate(PMATS):
                ic = PMAT_INDEX.get(residual(target, ma, mb))
                if ic is None:
                    continue
                triple_count += 1
                holonomies = (PERMS[ia], PERMS[ib], PERMS[ic])
                odd = sum(parity(h) for h in holonomies)
                bits = tuple(holonomy_class_bit(h) for h in holonomies)
                if odd == 0:
                    assert sum(bits) == 1
                    signatures[("flat", bits)] += 1
                else:
                    assert odd == 2
                    assert bits[0] == bits[1] == bits[2]
                    signatures[("curved", bits)] += 1

    assert triple_count == 456
    assert sum(v for (kind, _), v in signatures.items() if kind == "flat") == 120
    assert sum(v for (kind, _), v in signatures.items() if kind == "curved") == 336
    return {
        "allowed_ordered_local_triples": triple_count,
        "flat_rule": "exactly one identity holonomy among the three even holonomies",
        "curved_rule": (
            "the uncurved holonomy is identity iff both curved holonomies are four-cycles"
        ),
    }


def gf2_nullspace(rows, ncols):
    work = [row for row in rows if row]
    pivots = []
    rank = 0
    for col in range(ncols):
        pivot = next(
            (i for i in range(rank, len(work)) if (work[i] >> col) & 1),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for i in range(len(work)):
            if i != rank and ((work[i] >> col) & 1):
                work[i] ^= work[rank]
        pivots.append(col)
        rank += 1
        if rank == len(work):
            break

    pivot_set = set(pivots)
    basis = []
    for free in (c for c in range(ncols) if c not in pivot_set):
        vector = 1 << free
        for row_index, pivot in enumerate(pivots):
            if (work[row_index] >> free) & 1:
                vector |= 1 << pivot
        assert all((row & vector).bit_count() % 2 == 0 for row in rows)
        basis.append(vector)
    return basis


def topology():
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
    boundary = [0] * len(edges)
    for triangle_index, triangle in enumerate(triangles):
        for a, b in combinations(triangle, 2):
            edge = edge_index[(a, b)]
            edge_triangles[edge].append(triangle_index)
            boundary[edge] |= 1 << triangle_index
    assert len(edges) == len(triangles) == 105
    assert all(len(incident) == 3 for incident in edge_triangles)

    kernel = gf2_nullspace(boundary, 105)
    gram_rows = []
    for vector in kernel:
        row = 0
        for j, other in enumerate(kernel):
            if (vector & other).bit_count() & 1:
                row |= 1 << j
        gram_rows.append(row)
    coefficient_kernel = gf2_nullspace(gram_rows, len(kernel))

    support_basis = []
    for coefficients in coefficient_kernel:
        support = 0
        for i, vector in enumerate(kernel):
            if (coefficients >> i) & 1:
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
    return supports, edge_triangles


class DSU:
    def __init__(self, n):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        a = self.find(a)
        b = self.find(b)
        if a == b:
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]


def solve_class_csp(support, edge_triangles):
    """Solve the Boolean conjugacy-class CSP exactly.

    A curved edge equates the three incident class bits.  A flat edge requires
    exactly one of its three bits to be one.
    """
    dsu = DSU(105)
    for incident in edge_triangles:
        curved = sum((support >> triangle) & 1 for triangle in incident)
        assert curved in (0, 2)
        if curved == 2:
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
        if len(multiplicity) == 1:
            return False, len(roots), len(forced), len(constraints), 0
        if len(multiplicity) == 2:
            repeated = next(v for v, n in multiplicity.items() if n == 2)
            singleton = next(v for v, n in multiplicity.items() if n == 1)
            for variable, value in ((repeated, 0), (singleton, 1)):
                if variable in forced and forced[variable] != value:
                    return False, len(roots), len(forced), len(constraints), 0
                forced[variable] = value
        else:
            constraints.append(tuple(multiplicity))

    assignment = [-1] * len(roots)
    for variable, value in forced.items():
        assignment[variable] = value
    solution_count = 0

    def search(current):
        nonlocal solution_count
        changed = True
        while changed:
            changed = False
            for constraint in constraints:
                ones = sum(current[v] == 1 for v in constraint)
                unknown = [v for v in constraint if current[v] < 0]
                if ones > 1 or (ones == 0 and not unknown):
                    return
                if ones == 1:
                    for variable in unknown:
                        current[variable] = 0
                        changed = True
                elif len(unknown) == 1:
                    current[unknown[0]] = 1
                    changed = True

        unresolved = sorted(
            {v for constraint in constraints for v in constraint if current[v] < 0}
        )
        if not unresolved:
            solution_count += 1
            return
        variable = unresolved[0]
        for value in (0, 1):
            child = current.copy()
            child[variable] = value
            search(child)
            if solution_count > 1:
                return

    search(assignment)
    return (
        solution_count > 0,
        len(roots),
        len(forced),
        len(constraints),
        solution_count,
    )


def audit():
    supports, edge_triangles = topology()
    signatures = Counter()
    for support in supports:
        sat, components, forced, constraints, solutions = solve_class_csp(
            support, edge_triangles
        )
        signatures[
            (support.bit_count(), sat, components, forced, constraints, solutions)
        ] += 1

    expected = Counter(
        {
            (0, False, 105, 0, 105, 0): 1,
            (48, False, 14, 13, 3, 0): 105,
            (56, False, 1, 0, 0, 0): 120,
            (56, True, 8, 8, 0, 1): 30,
        }
    )
    assert signatures == expected

    return {
        "PASS": True,
        "local_conjugacy_rules": local_rule_audit(),
        "support_filter": {
            str(signature): count
            for signature, count in sorted(signatures.items(), key=lambda item: str(item[0]))
        },
        "surviving_supports": 30,
        "surviving_support_weight": 56,
        "surviving_class_assignment_is_unique": True,
        "consequence": (
            "Only the size-30 S7 orbit of weight-56 parity supports survives; "
            "its triangle conjugacy classes are uniquely forced."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
