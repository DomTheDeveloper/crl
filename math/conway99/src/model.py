#!/usr/bin/env python3
"""Exact root-reduced model for SRG(v,k,1,2), especially k=14, v=99.

Fix a root r. Its k neighbors induce a perfect matching. Every non-neighbor
is uniquely indexed by a non-edge of that matching. The unknown part is a
Boolean graph B on those labels.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable

@dataclass(frozen=True)
class RootModel:
    k: int
    labels: tuple[tuple[int, int], ...]
    label_index: dict[tuple[int, int], int]
    matching: tuple[int, ...]
    incidence: tuple[tuple[int, ...], ...]

    @property
    def m(self) -> int:
        return len(self.labels)

    @property
    def v(self) -> int:
        return 1 + self.k + self.m

    def intersection(self, u: int, v: int) -> int:
        a, b = self.labels[u]
        c, d = self.labels[v]
        return int(a == c or a == d) + int(b == c or b == d)

    def rhs_incidence(self, u: int, i: int) -> int:
        a, b = self.labels[u]
        return 2 - int(i == a or i == b) - int(self.matching[i] == a or self.matching[i] == b)

    def full_adjacency(self, b_edges: Iterable[tuple[int, int]]) -> list[list[int]]:
        n = self.v
        A = [[0] * n for _ in range(n)]
        root, n0, m0 = 0, 1, 1 + self.k
        for i in range(self.k):
            A[root][n0 + i] = A[n0 + i][root] = 1
        for i in range(0, self.k, 2):
            A[n0 + i][n0 + i + 1] = A[n0 + i + 1][n0 + i] = 1
        for u, (a, b) in enumerate(self.labels):
            for i in (a, b):
                A[m0 + u][n0 + i] = A[n0 + i][m0 + u] = 1
        for u, v in b_edges:
            A[m0 + u][m0 + v] = A[m0 + v][m0 + u] = 1
        return A

def make_root_model(k: int) -> RootModel:
    if k <= 0 or k % 2:
        raise ValueError("k must be positive and even")
    matching = tuple(i ^ 1 for i in range(k))
    labels = tuple((a, b) for a, b in combinations(range(k), 2) if matching[a] != b)
    idx = {e: i for i, e in enumerate(labels)}
    incidence = tuple(tuple(u for u, e in enumerate(labels) if i in e) for i in range(k))
    return RootModel(k, labels, idx, matching, incidence)

CONWAY = make_root_model(14)
PALEY9 = make_root_model(4)

# Exact full-stabilizer orbit representatives for the two distinguished
# neighbors of seed label (0,2). Old branch B1 is equivalent to A2.
SEED_BRANCHES = {
    "A1": ((0, 3), (1, 2)),
    "A2": ((0, 3), (2, 4)),
    "B2": ((0, 4), (2, 4)),
    "B3": ((0, 4), (2, 5)),
    "B4": ((0, 4), (2, 6)),
}
