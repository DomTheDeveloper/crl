#!/usr/bin/env python3
"""Independent integer-matrix verifier.

This does not call the common-neighbor verifier. It checks the two reduced
matrix identities and then the full adjacency identity

    A^2 + A = (k-2) I + 2 J.

For k=14 this is exactly A^2 + A = 12 I + 2 J.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
from model import make_root_model

def matmul(A, B):
    rows, mid, cols = len(A), len(B), len(B[0])
    assert len(A[0]) == mid
    C = [[0] * cols for _ in range(rows)]
    for i in range(rows):
        for t, a in enumerate(A[i]):
            if a:
                bt = B[t]
                for j, b in enumerate(bt):
                    C[i][j] += a * b
    return C

def verify_matrix(k: int, edges: list[tuple[int, int]]) -> None:
    rm = make_root_model(k)
    m = rm.m
    B = [[0] * m for _ in range(m)]
    for u, v in edges:
        assert 0 <= u < v < m and not B[u][v]
        B[u][v] = B[v][u] = 1
    assert all(B[i][i] == 0 for i in range(m))
    assert all(B[i][j] == B[j][i] for i in range(m) for j in range(m))

    X = [[int(i in rm.labels[u]) for u in range(m)] for i in range(k)]
    XB = matmul(X, B)
    for i in range(k):
        for u in range(m):
            px = int(rm.matching[i] in rm.labels[u])
            rhs = 2 - X[i][u] - px
            assert XB[i][u] == rhs, ("XB", i, u, XB[i][u], rhs)

    B2 = matmul(B, B)
    for u in range(m):
        for v in range(m):
            xtx = rm.intersection(u, v) if u != v else 2
            lhs = B2[u][v] + B[u][v] + xtx
            rhs = (k - 2 if u == v else 0) + 2
            assert lhs == rhs, ("reduced polynomial", u, v, lhs, rhs)

    A = rm.full_adjacency(edges)
    A2 = matmul(A, A)
    n = len(A)
    for i in range(n):
        for j in range(n):
            lhs = A2[i][j] + A[i][j]
            rhs = (k - 2 if i == j else 0) + 2
            assert lhs == rhs, ("full polynomial", i, j, lhs, rhs)

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("witness")
    args = ap.parse_args()
    d = json.loads(Path(args.witness).read_text())
    k = int(d["k"])
    edges = [tuple(map(int, e)) for e in d["edges"]]
    verify_matrix(k, edges)
    print(json.dumps({"verified": True, "method": "integer-matrix", "k": k,
                      "v": make_root_model(k).v, "edges": len(edges)}))

if __name__ == "__main__":
    main()
