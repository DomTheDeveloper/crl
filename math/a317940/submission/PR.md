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
  formal_proof using lean4 at "https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean"]
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
- Lean proof: `https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean`
- CI kernel check + axiom audit: `https://github.com/DomTheDeveloper/crl/actions/runs/29378868663`
- Prior-art check: `https://domthedeveloper.github.io/crl/math/a317940/prior-art.html`
- Project page (abstract, paper, hashes): `https://domthedeveloper.github.io/crl/math/a317940/`

The file to submit is `317940_cd729cdd.SOLVED.lean` in this folder — its
`formal_proof` URL is already set to the public gh-pages URL
(`https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean`).
