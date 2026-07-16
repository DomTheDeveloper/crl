# Erdős 741 partition strengthening

This project imports the exact AlphaProof Nexus proof of Erdős Problem 741(ii) at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and proves the following strengthening:

> There exists an additive basis `A` of order two such that in every partition of `A`
> indexed by any type, at most one cell has a syndetic self-sumset.

Consequently, every partition indexed by a nontrivial type has a cell whose self-sumset
is not syndetic. The index type need not be finite or countable.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The source contains no `sorry`, `admit`, `native_decide`, or custom axioms and prints the
axiom footprint of the final theorem.
