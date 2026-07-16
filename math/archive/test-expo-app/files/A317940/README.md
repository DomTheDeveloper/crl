# OEIS A317940: strict positivity

This directory hosts a complete Lean 4 proof of the Google DeepMind Formal Conjectures theorem

```lean
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) :
    A317940_f n ≥ 0
```

and proves the stronger internal result `A317940_f n > 0` for every positive `n`.

## Files

- [`A317940.lean`](./A317940.lean): complete Lean proof of the exact benchmark theorem.
- [`DigitalEulerPositivity.lean`](./DigitalEulerPositivity.lean): verified parameterized positivity core for rational `0 < q ≤ 1`, `α > 0`.
- [`HUMAN_PROOF.md`](./HUMAN_PROOF.md): readable mathematical proof.
- [`SHORT_NOTE.tex`](./SHORT_NOTE.tex): short-paper draft.
- [`GENERALIZATION.md`](./GENERALIZATION.md): broader digital Euler-product theorem and research program.
- [`PRIOR_ART.md`](./PRIOR_ART.md): current prior-art boundary and responsible novelty language.
- [`FORMAL_CONJECTURES_PATCH.diff`](./FORMAL_CONJECTURES_PATCH.diff): minimal solved-status/link patch for DeepMind.
- [`DEEPMIND_ISSUE.md`](./DEEPMIND_ISSUE.md): maintainer-submission draft.
- [`OEIS_SUBMISSION.txt`](./OEIS_SUBMISSION.txt): OEIS update draft.

## Verification

The exact A317940 proof has passed:

1. strict AXLE verification under Lean 4.27.0;
2. token-level matching against DeepMind's `auto_oeis` definitions and theorem signature;
3. compilation under `FormalConjectures.Util.ProblemImports` in an actual checkout of `google-deepmind/formal-conjectures`, with warnings treated as errors for the exact target;
4. a `#print axioms A317940_f_nonnegative` audit, reporting only `[propext, Classical.choice, Quot.sound]`;
5. checks rejecting `sorry`, `admit`, and custom `axiom` declarations.

The parameterized file `DigitalEulerPositivity.lean` separately passed strict AXLE verification with no errors, warnings, or failed declarations.

The first corpus-wide experiment used `lake --wfail build`; it failed only because hundreds of unrelated auto-generated OEIS files already emit style warnings. A second run uses the repository's normal `lake build` criterion.

The official target audit and repository build are linked in the proof-host pull request.

## Disclosure

The mathematical strategy, formalization, and proof engineering were developed with substantial assistance from OpenAI's ChatGPT. The final proof terms are independently checked by the Lean kernel. Independent human review remains welcome.
