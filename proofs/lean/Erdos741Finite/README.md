# Erdős 741 strong partition theorem

This project imports the exact AlphaProof Nexus proof of Erdős Problem 741(ii) at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and proves the following strengthening:

> There exists an additive basis `A` of order two such that, in every partition of `A`,
> if one cell has a syndetic self-sumset, then every other cell's self-sumset has
> arbitrarily long gaps.

In particular, at most one cell has a syndetic self-sumset, and every partition indexed
by a nontrivial type has a non-syndetic cell. The index type may be finite, countable,
or uncountable.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The source contains no `sorry`, `admit`, `native_decide`, or custom axioms and prints the
axiom footprint of the final theorem.
