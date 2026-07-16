# Erdős 741 finite-partition strengthening

This project imports the exact AlphaProof Nexus proof of Erdős Problem 741(ii) at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and proves the following corollary:

> There exists an additive basis `A` of order two such that every finite partition of
> `A` into at least two pairwise-disjoint cells has a cell whose self-sumset is not syndetic.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The source contains no `sorry`, `admit`, `native_decide`, or custom axioms and prints the
axiom footprint of the final theorem.
