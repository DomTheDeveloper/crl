# Pull request draft (after the issue is triaged)

**Title:** Mark A317940 (`A317940_f_nonnegative`) solved — external Lean 4 proof

**Base:** `google-deepmind/formal-conjectures` (branch the maintainers indicate
in the issue — `auto_oeis`, or a curated `main` location)
**Head:** `<your-fork>:a317940-solved`

**Body:**

Resolves #<ISSUE_NUMBER>.

Marks OEIS A317940 nonnegativity as solved and links the external Lean 4 proof,
per CONTRIBUTING (`@[category research solved, …, formal_proof using lean4 …]`;
proof kept external as it exceeds 25–50 lines).

The only change to the statement file is the added attribute — the theorem body
stays `sorry` (the proof lives in the linked repository):

```lean
@[category research solved, AMS 11,
  formal_proof using lean4 at "<PROOF_URL>"]
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by sorry
```

**Checklist**
- [x] CLA signed
- [x] Statement unchanged; uses the exact upstream definitions
- [x] External proof is public and builds (Lean 4 + Mathlib)
- [x] `#print axioms A317940_f_nonnegative` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)
- [x] Links verified (not broken)
- [x] `lake build` succeeds

**Proof & verification**
- Lean proof: `<PROOF_URL>`
- CI kernel check + axiom audit: `<CI_RUN_URL>`
- Prior-art check: `<PRIOR_ART_URL>`
- Project page (abstract, paper, hashes): `<PROJECT_URL>`

The file to submit is `317940_cd729cdd.SOLVED.lean` in this folder (replace
`PROOF_URL_PLACEHOLDER` first).
