# Erdős 846 sharpness ingredient

This project kernel-checks the exact Mantel/Turán bound used to prove that the
`1/2` guarantee in the Erdős 846 edge-to-point construction is asymptotically sharp:

```text
G.CliqueFree 3  →  4 * |E(G)| ≤ n²
```

It also proves that the bound is attained by the complete bipartite Turán graph.
Combined with the upstream `IsGoodMap` equivalence between collinear triples and graph
triangles, this supplies the exact extremal upper half of the sharpness argument.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The final theorems print their axiom footprints, and CI rejects placeholders and custom axioms.
