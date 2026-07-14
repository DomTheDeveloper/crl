# A317940 verification report

Date: July 14, 2026

## Exact theorem

```lean
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) :
    A317940_f n ≥ 0
```

The proof internally establishes the stronger statement `0 < A317940_f n` for `n > 0`.

## Specification integrity

The definitions of `A005187`, `A046644`, `A317940_f`, and the exact theorem signature were compared token-by-token against the Google DeepMind Formal Conjectures `auto_oeis` source. All comparisons matched.

## Strict verifier

AXLE, Lean 4.27.0:

- `okay`: `true`
- failed declarations: none
- Lean errors: none
- Lean warnings: none
- tool errors: none
- candidate occurrences of `sorry`, `admit`, or custom `axiom`: none

## Official repository integration

The complete proof was installed into an actual checkout of `google-deepmind/formal-conjectures` at the exact path

`FormalConjectures/OEIS/Auto/317940_cd729cdd.lean`

and compiled under

```lean
import FormalConjectures.Util.ProblemImports
```

with warnings treated as errors for the exact target file. The compile succeeded and produced an empty compiler log, as expected for a warning-free successful Lean invocation.

## Axiom audit

The command

```lean
#print axioms A317940_f_nonnegative
```

reported:

```text
'A317940_f_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms used broadly by Lean/mathlib; no theorem-specific axiom was introduced.

## Repository-wide build

The initial corpus-wide command used `lake --wfail build`. It compiled 9,192 of 9,193 build steps and emitted no Lean error. It returned failure only because `--wfail` turns existing warnings into a nonzero exit status. The log contains 484 warning-marked generated OEIS modules, principally pre-existing style warnings such as missing namespace, AMS, or category attributes.

The repository's normal full-build criterion is `lake build`; a corrected run was launched. This distinction does not affect the exact target proof, which already passed its own warning-free compile and axiom audit.

## Solved-status metadata

A minimal Formal Conjectures patch was tested using the repository's long-proof convention:

```lean
@[category research solved,
  formal_proof using lean4 at "<fixed proof URL>",
  AMS 11]
```

The metadata-patched upstream file compiled successfully under the repository's normal warning policy.

## Parameterized generalization

`DigitalEulerPositivity.lean` proves for rational `0 < q ≤ 1` and `α > 0` that the coefficients of the canonical formal solution

```text
F' = α D_q F,   F(0)=1
```

are strictly positive. It also proves the logarithmic-derivative lower bound and the defining formal differential equation.

Strict AXLE result:

- `okay`: `true`
- failed declarations: none
- errors: none
- warnings: none

The mathematical identification of this canonical series with

`∏_{r≥0} (1 + q z^(2^r))^α`

follows by formal logarithmic differentiation and uniqueness. The reusable arbitrary-parameter product-notation API remains a separate formalization task.

## Independent exact-rational generalization check

A separate Python implementation used exact `fractions.Fraction` arithmetic to compare:

1. direct degree-truncated expansion of `prod_r (1 + q z^(2^r))^alpha`; and
2. the logarithmic-derivative coefficient recurrence formalized in Lean.

It tested 30 rational parameter pairs with `q` in `{1/7, 1/3, 1/2, 3/4, 1}` and `alpha` in `{1/5, 1/3, 1/2, 1, 5/3, 2}` through degree 160. Every comparison agreed exactly; every tested coefficient was positive; and the formal lower bound for the logarithmic-derivative coefficients held.

## Manuscript

The package includes a six-page research draft, rendered and visually inspected on pages 1, 3, and 6. No clipping, overlap, broken glyphs, or malformed formulas were observed.

## Scholarly status

The exact formal conjecture is solved and kernel-checked. Public scholarly recognition remains pending:

- independent human review;
- maintainer acceptance or solved-status update in Formal Conjectures;
- OEIS update;
- priority/literature review;
- journal or preprint submission.
