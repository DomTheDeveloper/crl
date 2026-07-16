# Erdős Problem 865 — exact Formal Conjectures wrapper

This directory kernel-checks the exact statement currently found in
`FormalConjectures/ErdosProblems/865.lean`.

The underlying combinatorial proof is **not an original result of this repository**. It is the
Lean formalization by Jay Yang (`Jayyhk/erdos-lean`, commit
`32434b3a0859bb1e485fa7e530f38eee73a3debf`), based on the Cipollini / GPT-5.5 Pro solution.
That proof establishes the explicit bound

```text
5 * N + 53 < 8 * |A|  ⇒  A contains the required pairwise-sum triple.
```

`FormalConjecturesExact.lean` proves that this implies the precise Formal Conjectures theorem:
choose the real constant `C = 7`; then `|A| ≥ (5/8)N + 7` gives
`8|A| ≥ 5N + 56 > 5N + 53`.

The workflow pins the source proof commit and rejects `sorryAx` and any axiom outside the standard
Mathlib footprint `propext`, `Classical.choice`, and `Quot.sound`.
