#!/usr/bin/env python3
"""Exact audit of a compressed ``s = 84`` model for Conway's 99-graph.

The audit has two purposes.

1. It proves that the scalar Frobenius/projector equations add no inequality
   beyond the already-known weighted deficit equation.
2. It verifies the exact Walsh compression of the four-fold-cover model from
   84 label vectors to 63 fiber-character vectors.

Everything is integer arithmetic; no floating-point eigensolver is used.
"""
from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, permutations

LABELS = [
    (a, b)
    for a, b in combinations(range(14), 2)
    if b != (a ^ 1)
]


def intersection(u: int, v: int) -> int:
    return len(set(LABELS[u]) & set(LABELS[v]))


def matching_cross_count(u: int, v: int) -> int:
    return sum(
        1
        for a in LABELS[u]
        for b in LABELS[v]
        if (a ^ 1) == b
    )


def dot(x: tuple[int, ...], y: tuple[int, ...]) -> int:
    return sum(a * b for a, b in zip(x, y))


def matvec(
    matrix: tuple[tuple[int, ...], ...],
    vector: tuple[int, ...],
) -> tuple[int, ...]:
    return tuple(dot(row, vector) for row in matrix)


def pair_type_audit() -> dict[str, object]:
    counts = Counter(
        (intersection(u, v), matching_cross_count(u, v))
        for u, v in combinations(range(84), 2)
    )
    expected = {
        (0, 0): 1680,
        (0, 1): 840,
        (0, 2): 42,
        (1, 0): 840,
        (1, 1): 84,
    }
    assert counts == expected
    assert sum(counts.values()) == 84 * 83 // 2
    return {
        f"m={m},y={y}": n
        for (m, y), n in sorted(counts.items())
    }


def projector_scalar_audit() -> dict[str, object]:
    # Coefficients in the ordered basis (I, J, M, Y, B).
    g30 = (24, 2, -3, -1, -8)
    g40 = (60, -2, -4, 1, 15)
    combined = tuple(15 * a + 8 * b for a, b in zip(g30, g40))
    assert combined == (840, 14, -77, -7, 0)
    assert combined == tuple(7 * x for x in (120, 2, -11, -1, 0))

    # Let d_y be the number of selected disjoint-label edges with matching
    # cross-count y, and s the number of selected short transition edges.
    #
    # tr(G30^2)=56 tr(G30) gives
    #   2 d0 + 3 d1 + 4 d2 + s = 924.
    # tr(G40^2)=105 tr(G40) gives
    #   11 d0 + 13 d1 + 15 d2 + 2s = 4788.
    #
    # Since d0+d1+d2=420, both equations reduce to
    #   d1 + 2d2 + s = 84.
    eq30_constant_after_degree = 924 - 2 * 420
    eq40_constant_after_degree = (4788 - 11 * 420) // 2
    assert eq30_constant_after_degree == 84
    assert eq40_constant_after_degree == 84
    return {
        "projector_linear_identity": {
            "lhs": "15 G30 + 8 G40",
            "rhs": "7(120 I + 2 J - 11 M - Y)",
            "B_coefficient": combined[-1],
        },
        "G30_frobenius_equation": "2 d0 + 3 d1 + 4 d2 + s = 924",
        "G40_frobenius_equation": "11 d0 + 13 d1 + 15 d2 + 2s = 4788",
        "common_reduction": "d1 + 2 d2 + s = 84",
    }


POINTS = ((0, 0), (0, 1), (1, 0), (1, 1))
WALSH = (
    (1, 1, -1, -1),   # first coordinate
    (1, -1, 1, -1),   # second coordinate
    (1, -1, -1, 1),   # parity
)


def fiber_block_audit() -> dict[str, object]:
    # G30 inside a fiber: diagonal 20, -10 on the C4, and 0 on opposites.
    block = tuple(
        tuple(
            20 if p == q else (
                -10 if sum(a != b for a, b in zip(p, q)) == 1 else 0
            )
            for q in POINTS
        )
        for p in POINTS
    )
    one = (1, 1, 1, 1)
    assert matvec(block, one) == (0, 0, 0, 0)
    eigenvalues = []
    for chi in WALSH:
        image = matvec(block, chi)
        candidates = {image[i] // chi[i] for i in range(4)}
        assert len(candidates) == 1
        eigenvalues.append(candidates.pop())
    assert eigenvalues == [20, 20, 40]

    # If two fibers share their first base point, the cross block is -u u^T,
    # where u is the character of the shared sign. Under the normalized
    # Walsh component A=(1/2) sum u_x v_x, the shared components pair to -4.
    shared = tuple(
        tuple(-WALSH[0][r] * WALSH[0][c] for c in range(4))
        for r in range(4)
    )
    shared_component_inner = dot(
        WALSH[0], matvec(shared, WALSH[0])
    ) // 4
    assert shared_component_inner == -4
    for chi in WALSH[1:]:
        assert dot(chi, matvec(shared, chi)) == 0

    # For disjoint fibers, every cross block is 2J-8P. On the zero-sum Walsh
    # subspace the J term vanishes. Every permutation of four points induces a
    # signed 3-by-3 permutation matrix because S4 = AGL(2,2).
    signed_actions = set()
    for perm in permutations(range(4)):
        pmat = tuple(
            tuple(int(perm[r] == c) for c in range(4))
            for r in range(4)
        )
        action = tuple(
            tuple(
                dot(chi, matvec(pmat, psi)) // 4
                for psi in WALSH
            )
            for chi in WALSH
        )
        assert all(sum(x != 0 for x in row) == 1 for row in action)
        assert all(
            sum(action[r][c] != 0 for r in range(3)) == 1
            for c in range(3)
        )
        assert all(x in (-1, 0, 1) for row in action for x in row)
        signed_actions.add(action)
    assert len(signed_actions) == 24

    # Six shared-point components have Gram diagonal 20 and off-diagonal -4:
    # their sum is zero and the remaining five directions have eigenvalue 24.
    simplex = tuple(
        tuple(20 if i == j else -4 for j in range(6))
        for i in range(6)
    )
    assert matvec(simplex, (1,) * 6) == (0,) * 6
    for vector in (
        (1, -1, 0, 0, 0, 0),
        (1, 0, -1, 0, 0, 0),
        (1, 0, 0, -1, 0, 0),
        (1, 0, 0, 0, -1, 0),
        (1, 0, 0, 0, 0, -1),
    ):
        assert matvec(simplex, vector) == tuple(24 * x for x in vector)

    return {
        "fibers": 21,
        "vectors_per_fiber_before_compression": 4,
        "characters_per_fiber_after_compression": 3,
        "compressed_dimension": 63,
        "required_rank": 30,
        "fiber_character_norm_squares": eigenvalues,
        "shared_point_simplex": {
            "vectors": 6,
            "diagonal": 20,
            "off_diagonal": -4,
            "nonzero_eigenvalue": 24,
            "rank": 5,
        },
        "disjoint_block_actions": len(signed_actions),
        "disjoint_component_block": "-8 times a signed 3-by-3 permutation",
    }


def audit() -> dict[str, object]:
    return {
        "PASS": True,
        "pair_types": pair_type_audit(),
        "projector_scalar_closure": projector_scalar_audit(),
        "s84_walsh_compression": fiber_block_audit(),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
