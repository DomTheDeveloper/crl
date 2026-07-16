#!/usr/bin/env python3
"""Combinatorial exact verifier for full and root-reduced witnesses."""
from __future__ import annotations
import argparse, json
from pathlib import Path
from model import RootModel, make_root_model

def verify_full(A: list[list[int]], k: int, lam: int = 1, mu: int = 2) -> None:
    n = len(A)
    assert all(len(row) == n for row in A)
    for i in range(n):
        assert A[i][i] == 0
        for j in range(n):
            assert A[i][j] in (0, 1)
            assert A[i][j] == A[j][i]
        assert sum(A[i]) == k, (i, sum(A[i]), k)
    for i in range(n):
        for j in range(i + 1, n):
            common = sum(A[i][w] & A[j][w] for w in range(n))
            want = lam if A[i][j] else mu
            assert common == want, (i, j, A[i][j], common, want)

def verify_reduced(model: RootModel, edges: list[tuple[int, int]]) -> None:
    m = model.m
    B = [[0] * m for _ in range(m)]
    for u, v in edges:
        assert 0 <= u < v < m
        assert B[u][v] == 0
        B[u][v] = B[v][u] = 1
    for u in range(m):
        for i in range(model.k):
            got = sum(B[u][q] for q in model.incidence[i])
            want = model.rhs_incidence(u, i)
            assert got == want, ("incidence", u, i, got, want)
    for u in range(m):
        assert sum(B[u]) == model.k - 2, ("degree", u, sum(B[u]))
        for v in range(u + 1, m):
            common = sum(B[u][w] & B[v][w] for w in range(m))
            want = 2 - model.intersection(u, v) - B[u][v]
            assert common == want, ("pair", u, v, common, want)
    verify_full(model.full_adjacency(edges), model.k)

def read_edge_json(path: Path):
    data = json.loads(path.read_text())
    return int(data["k"]), [tuple(map(int, e)) for e in data["edges"]]

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("witness")
    args = ap.parse_args()
    k, edges = read_edge_json(Path(args.witness))
    model = make_root_model(k)
    verify_reduced(model, edges)
    print(json.dumps({"verified": True, "method": "combinatorial", "k": k,
                      "v": model.v, "reduced_vertices": model.m, "edges": len(edges)}))

if __name__ == "__main__":
    main()
