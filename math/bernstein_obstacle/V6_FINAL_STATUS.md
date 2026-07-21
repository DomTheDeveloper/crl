# Bernstein V6 final status

## Completed internally

1. Assembled Bernstein coefficient inner cones and positive Mosco recovery.
2. Corrected regular-interface clipping theorem with
   `h^r+h_Gamma^(3/2)` recovery and `O(h_Gamma^3)` multiplier residual.
3. Strongly monotone operator-transfer theorem, without symmetry or an energy
   functional.
4. Translated-cone theorem for exact or conformingly majorized nonzero
   obstacles.
5. Same-cone operator/data perturbation estimate.
6. Concrete nonlinear nonsymmetric convection--reaction--`tanh` corollary.
7. Reproducible coefficientwise nonlinear complementarity benchmark.
8. Lean source for the operator-VI algebra and a pinned terminal axiom audit.
9. Deep prior-art audit with material narrowing of the novelty claim.
10. Dedicated external audit protocol.

## Current honest classification

- **Mathematical derivation:** internally complete under the written
  hypotheses.
- **Numerical benchmark:** executed successfully; archived JSON and workflow
  included.
- **Lean V6 bridge:** source complete; verification requires a successful
  pinned workflow and inspected axiom transcript.
- **Physical Sobolev/free-boundary theorem:** analytical, not fully formalized.
- **Independent expert review:** pending.
- **Novelty:** plausible only for the complete Bernstein
  coefficient-cone/clipping/interface-rate synthesis; not established.

## Release gates

The package may be called **internally complete and audit-ready** after the
pinned workflows pass. It may be called **independently confirmed** only after:

1. a qualified numerical analyst signs off on the physical recovery and rate;
2. a qualified prior-art review confirms the corrected novelty boundary;
3. a clean-room numerical reproduction verifies the implementation claims.

## Canonical assets

- branch: `integration/bernstein-v6-final`
- base: `formalization/bernstein-v5-hilbert-consolidation`
- final PR: `#148`
- independent audit issue: `#123`
- superseded PRs: `#119`, `#146`

## Recommended next work

1. Inspect the pinned Lean workflow and fix only concrete checker errors.
2. Obtain Panel E external review.
3. Add a two-dimensional nonlinear benchmark with a manufactured or
   independently characterized interface.
4. Integrate the corrected V8 framing into the venue manuscript.
5. Do not broaden claims beyond `V6_PRIOR_ART_AND_CLAIM_CORRECTION.md`.
