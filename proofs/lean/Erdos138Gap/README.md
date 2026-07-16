# Formalized Erdős 138 consecutive-gap refinement

This project imports the AlphaProof Nexus proof at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and formalizes the endpoint refinement

```text
W(k + 1) - W(k) ≥ k + 1   for k > 0.
```

The April 10, 2026 Erdős Problems discussion already records the stronger informal
`r`-color statement `W_r(k+1)-W_r(k) ≥ k+r-1`; this project therefore claims formalization,
not mathematical novelty.

The proof allows the greedy extension index `i = k`, which the original intersection
argument supports.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The result remains unverified until the kernel build passes.
