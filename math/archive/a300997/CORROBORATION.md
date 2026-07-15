# A300997 — independent computational corroboration

**Attribution.** The *proof* of A300997's finite-difference lemma is by **Google
DeepMind AlphaProof**, not by this project. Their machine-checked Lean proof is
`DeepMind_AlphaProof_a300997.lean` in this folder (Apache-2.0, © 2026 Google LLC),
mirrored from
`google-deepmind/alphaproof-nexus-results` →
`APNOutputs/OEIS/oeis_a300997_finite_difference_is_one_or_two.lean`.

Their top-level theorem:

```lean
theorem target_theorem_0 :
    ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2
```

where `a n` is the stabilization time of the mass-splitting cellular automaton.

**Our contribution is only a finite computational corroboration** (not a proof):
an independent re-implementation of the CA (`math/assets/js/numtools.js`,
`tests/a300997.mjs`) reproduces the sequence and checks the gap lemma
`a(n+1) − a(n) ∈ {1,2}` for `n = 1..600` — **0 violations**.

```
a(1..16) = 0, 1, 3, 4, 6, 8, 10, 11, 13, 15, 17, 19, 21, 23, 24, 26
```

This is finite evidence consistent with DeepMind's proof; it does not replace it.
