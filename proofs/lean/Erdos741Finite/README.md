# Erdős 741 arbitrary-partition strengthening

This project imports the exact AlphaProof Nexus proof of Erdős Problem 741(ii) at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and proves the following strengthening:

> There exists an additive basis `A` of order two such that every partition of `A`
> indexed by any nontrivial type has a cell whose self-sumset is not syndetic.

The index type need not be finite or countable.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The source contains no `sorry`, `admit`, `native_decide`, or custom axioms and prints the
axiom footprint of the final theorem.
