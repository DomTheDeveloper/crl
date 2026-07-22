#!/usr/bin/env python3
"""Exact obstruction to the flat-curvature sector of the ``s = 84`` branch.

The four points in every intact fiber form the affine plane ``F_2^2``.  The
quotient of its affine permutation group by translations is
``GL(2,2) = S_3``.  Earlier audits show that a flat triangle-curvature support
has exactly three gauge-fixed ``S_3`` connections: the trivial one and an
inverse pair of ``C_3``-valued connections.

This audit restores the physical endpoint directions of every K7-edge fiber
and projects the exact intersecting-fiber common-neighbor equation to the
``S_3`` quotient.  It proves:

* the two nontrivial flat connections are locally impossible at every pair of
  intersecting fibers;
* the trivial connection would induce a proper three-coloring of K7, which is
  impossible.

Consequently the odd triangle-holonomy support in a putative ``s = 84`` graph
cannot be empty.  It must have weight 48 or 56.
"""
from __future__ import annotations

import json
from collections import Counter, deque
from itertools import combinations, permutations, product

from s84_holonomy_audit import compose, matching_complex

POINTS = range(4)
FULL_PERMS = tuple(permutations(POINTS))
S3 = tuple(permutations(range(3)))
S3_INDEX = {p: i for i, p in enumerate(S3)}


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def permutation_matrix(p: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(int(p[i] == j) for j in POINTS) for i in POINTS)


FULL_PMATS = tuple(permutation_matrix(p) for p in FULL_PERMS)
FLAT_PMATS = tuple(tuple(x for row in m for x in row) for m in FULL_PMATS)


def linear_quotient(p: tuple[int, ...]) -> tuple[int, ...]:
    """Action of an affine four-point permutation on the three nonzero vectors."""
    images = []
    for difference in (1, 2, 3):
        values = {p[x] ^ p[x ^ difference] for x in POINTS}
        assert len(values) == 1
        images.append(values.pop() - 1)
    return tuple(images)


FULL_QUOTIENT = tuple(S3_INDEX[linear_quotient(p)] for p in FULL_PERMS)
S3_MUL = tuple(
    tuple(S3_INDEX[compose(left, right)] for right in S3)
    for left in S3
)
S3_INV = tuple(S3_INDEX[inverse(p)] for p in S3)
IDENTITY = S3_INDEX[(0, 1, 2)]


def flat_connections() -> list[tuple[int, ...]]:
    """Enumerate the three spanning-tree-gauge-fixed flat S3 connections."""
    edges, triangles, _ = matching_complex()
    edge_index = {edge: i for i, edge in enumerate(edges)}
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
    tree_ids = {
        edge_index[tuple(sorted((v, parent[v])))]
        for v in range(1, 21)
    }

    constraints = []
    incidence = [[] for _ in edges]
    allowed = tuple(
        (x, y, S3_MUL[y][x])
        for x in range(6)
        for y in range(6)
    )
    for a, b, c in triangles:
        variables = (
            edge_index[(a, b)],
            edge_index[(b, c)],
            edge_index[(a, c)],
        )
        ci = len(constraints)
        constraints.append(variables)
        for variable in variables:
            incidence[variable].append(ci)

    domains = [(1 << 6) - 1] * len(edges)
    for edge in tree_ids:
        domains[edge] = 1 << IDENTITY

    def propagate(current: list[int]) -> bool:
        pending = list(range(len(constraints)))
        queued = set(pending)
        while pending:
            ci = pending.pop()
            queued.discard(ci)
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
                        if cj not in queued:
                            pending.append(cj)
                            queued.add(cj)
        return True

    solutions = []

    def search(current: list[int]) -> None:
        if not propagate(current):
            return
        unresolved = [
            (mask.bit_count(), variable)
            for variable, mask in enumerate(current)
            if mask.bit_count() > 1
        ]
        if not unresolved:
            solutions.append(tuple(mask.bit_length() - 1 for mask in current))
            return
        _, variable = min(unresolved)
        for value in range(6):
            if (current[variable] >> value) & 1:
                child = current.copy()
                child[variable] = 1 << value
                search(child)

    search(domains)
    assert len(solutions) == 3
    return solutions


def oriented_value(
    u: int,
    v: int,
    connection: tuple[int, ...],
    edge_index: dict[tuple[int, int], int],
) -> int:
    edge = edge_index[(min(u, v), max(u, v))]
    value = connection[edge]
    return value if u < v else S3_INV[value]


def transport_signature(
    u: int,
    v: int,
    connection: tuple[int, ...],
    fibers: list[tuple[int, int]],
    edge_index: dict[tuple[int, int], int],
) -> tuple[int, ...]:
    """Six quotient transports u -> w -> v for an intersecting fiber pair."""
    thirds = [
        w
        for w in range(21)
        if set(fibers[w]).isdisjoint(fibers[u])
        and set(fibers[w]).isdisjoint(fibers[v])
    ]
    assert len(thirds) == 6
    values = []
    for w in thirds:
        u_to_w = oriented_value(u, w, connection, edge_index)
        v_to_w = oriented_value(v, w, connection, edge_index)
        values.append(S3_MUL[S3_INV[v_to_w]][u_to_w])
    return tuple(sorted(values))


def linear_class(kernel: int, point: int) -> int:
    """The nonzero F2-linear functional whose kernel is {0, kernel}."""
    covector = next(
        a
        for a in (1, 2, 3)
        if ((a & kernel).bit_count() & 1) == 0
    )
    return (covector & point).bit_count() & 1


def target_matrix(kernel_u: int, kernel_v: int, offset: int) -> tuple[int, ...]:
    relation = tuple(
        tuple(
            int((linear_class(kernel_u, x) ^ linear_class(kernel_v, y)) == offset)
            for y in POINTS
        )
        for x in POINTS
    )
    return tuple(2 - relation[i][j] for i in POINTS for j in POINTS)


def allowed_kernel_pairs(signature: tuple[int, ...]) -> set[tuple[int, int]]:
    """Project the exact six-permutation equation to endpoint kernel directions."""
    allowed = set()
    for kernel_u, kernel_v, offset in product((1, 2, 3), (1, 2, 3), (0, 1)):
        target = target_matrix(kernel_u, kernel_v, offset)
        found = False

        def enumerate_multisets(
            start: int,
            remaining: int,
            residual: tuple[int, ...],
            quotient_values: tuple[int, ...],
        ) -> None:
            nonlocal found
            if found:
                return
            if remaining == 0:
                if not any(residual) and tuple(sorted(quotient_values)) == signature:
                    found = True
                return
            for index in range(start, len(FLAT_PMATS)):
                nxt = tuple(a - b for a, b in zip(residual, FLAT_PMATS[index]))
                if min(nxt) >= 0:
                    enumerate_multisets(
                        index,
                        remaining - 1,
                        nxt,
                        quotient_values + (FULL_QUOTIENT[index],),
                    )

        enumerate_multisets(0, 6, target, ())
        if found:
            allowed.add((kernel_u, kernel_v))
    return allowed


def audit() -> dict[str, object]:
    fibers = list(combinations(range(7), 2))
    edges, _, _ = matching_complex()
    edge_index = {edge: i for i, edge in enumerate(edges)}
    intersecting_pairs = [
        (u, v)
        for u, v in combinations(range(21), 2)
        if set(fibers[u]) & set(fibers[v])
    ]
    assert len(intersecting_pairs) == 105

    connections = flat_connections()
    signatures = []
    for connection in connections:
        counter = Counter(
            transport_signature(u, v, connection, fibers, edge_index)
            for u, v in intersecting_pairs
        )
        assert sum(counter.values()) == 105
        assert len(counter) == 1
        signature, multiplicity = next(iter(counter.items()))
        assert multiplicity == 105
        signatures.append(signature)

    trivial_signature = (IDENTITY,) * 6
    rotation = S3_INDEX[(1, 2, 0)]
    inverse_rotation = S3_INV[rotation]
    nontrivial_signature = tuple(sorted(
        (IDENTITY, IDENTITY, rotation, rotation, inverse_rotation, inverse_rotation)
    ))
    assert Counter(signatures) == Counter({trivial_signature: 1, nontrivial_signature: 2})

    trivial_allowed = allowed_kernel_pairs(trivial_signature)
    nontrivial_allowed = allowed_kernel_pairs(nontrivial_signature)
    assert trivial_allowed == {(1, 1), (2, 2), (3, 3)}
    assert nontrivial_allowed == set()

    # In the trivial connection, every two fibers sharing base point a must use
    # the same shared-sign kernel direction.  Call it color(a).  On a fiber
    # {a,b}, the two endpoint kernel directions are distinct because a physical
    # frame permutes the three nonzero vectors.  Thus color(a) != color(b) for
    # every edge of K7: a proper three-coloring of K7, which does not exist.
    proper_three_colorings = sum(
        all(colors[a] != colors[b] for a, b in combinations(range(7), 2))
        for colors in product(range(3), repeat=7)
    )
    assert proper_three_colorings == 0

    return {
        "PASS": True,
        "flat_gauge_fixed_S3_connections": 3,
        "connection_classes": {
            "trivial": 1,
            "nontrivial_C3_inverse_pair": 2,
        },
        "intersecting_pairs_checked_per_connection": 105,
        "trivial_transport_signature": {
            "identity": 6,
            "allowed_endpoint_kernel_pairs": sorted(trivial_allowed),
            "induced_problem": "proper 3-coloring of K7",
            "proper_3_colorings": proper_three_colorings,
        },
        "nontrivial_transport_signature": {
            "identity": 2,
            "C3_rotation": 2,
            "inverse_C3_rotation": 2,
            "allowed_endpoint_kernel_pairs": [],
        },
        "consequence": (
            "The flat odd-holonomy support is impossible. In the s=84 branch, "
            "odd triangle holonomy must occur on exactly 48 or 56 triangles."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
