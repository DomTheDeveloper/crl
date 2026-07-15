# Issue to open first (github.com/google-deepmind/formal-conjectures → New issue)

**Title:** A317940 nonnegativity (`A317940_f_nonnegative`) has a formal Lean 4 proof — mark solved?

**Body:**

The OEIS A317940 conjecture currently staged at
`FormalConjectures/OEIS/Auto/317940_cd729cdd.lean` (branch `auto_oeis`) is stated
with `sorry`:

```lean
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by sorry
```

I have a complete Lean 4 proof of **the exact statement**, using your exact
definitions of `A005187`, `A046644`, and `A317940_f` (byte-identical after
comment stripping). Per the >25–50 line guidance, the 659-line proof stays in my
repository and would be linked via `@[formal_proof using lean4 at "…"]`.

**Evidence**
- Proof (Lean 4, no `sorry`/`admit`/custom axiom): <PROOF_URL_PLACEHOLDER>
- Kernel-verified against Mathlib in CI; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`):
  <CI_RUN_URL_PLACEHOLDER>
- Faithfulness: your upstream file sha256
  `4658ee6927738e3b54f54e64fed146124558797b161bc3ec280f8b64280ef020`; the
  definition code matches byte-for-byte.
- Prior-art check (no pre-existing formal proof found; conjecture still open
  upstream): <PRIOR_ART_URL_PLACEHOLDER>
- Human-readable proof / paper: <PROJECT_URL_PLACEHOLDER>

**Question on process.** A317940 lives on the `auto_oeis` branch and carries no
`@[category]` tags yet (unlike the curated files). What's your preferred path?
1. Add `@[category research solved, AMS 11, formal_proof using lean4 at "…"]` to
   the theorem in the auto file, or
2. Curate A317940 into a `main` location (I'm happy to add the appropriate
   category tags to the accompanying value-check statements too).

I've signed the CLA and can open a PR against whichever target you prefer.

*(Replace the placeholder URLs before posting; see SUBMISSION_GUIDE.md.)*
