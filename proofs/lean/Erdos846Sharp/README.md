# Erdős 846 sharpness bridge

This project imports the exact AlphaProof Nexus construction and formalizes both sides of
the sharpness mechanism:

1. For an `IsGoodMap`, a finite point image is non-trilinear iff its underlying valid
   edge set contains no `FormsTriangle` triple.
2. Every triangle-free graph on `n` vertices satisfies the exact Mantel bound
   `4 * |E(G)| ≤ n²`, with equality attained by the bipartite Turán graph.

Together these are the formal geometry-to-extremal-graph bridge showing why the `1/2`
guarantee in the Erdős 846 construction is asymptotically sharp within that construction.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The final theorems print their axiom footprints, and CI rejects placeholders and custom axioms.
