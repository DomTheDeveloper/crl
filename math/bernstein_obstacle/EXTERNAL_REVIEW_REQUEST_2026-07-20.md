# External review request: Bernstein–Bézier certified inner cones

Date: 2026-07-20

Canonical review target: PR #133, branch `formal/bernstein-bezier-grand-canonical`

## Requested review panels

We request independent reports from four specialties. A reviewer may address one
panel only.

### Panel A — numerical analysis and Mosco convergence

Please verify:

1. the `C`-valued cutoff/mollification density construction in
   `W_0^{1,p}`;
2. conformity and boundary preservation of fixed-degree positive Bernstein
   sampling;
3. the diagonal recovery argument for the coefficient inner cones;
4. the distinction from general pointwise convex-constraint Mosco results.

### Panel B — free-boundary and contact estimates

Please verify:

1. coefficient-distance localization near the active interface;
2. local quasi-uniform patch scaling;
3. multiplier pairing and sign;
4. the exponent
   \[
   \gamma=\min\{\beta-1+\kappa/q,(\beta+\kappa+\sigma)/q\};
   \]
5. the restricted sharpness claim for the phase-locked clipping family.

### Panel C — formal methods

Please verify:

1. correspondence between the mathematical statements and Lean declarations;
2. whether any physical assertion is hidden in an unconstrained structure
   field;
3. the exact-head build and `#print axioms` transcript;
4. absence of `sorryAx` in all advertised terminal endpoints.

### Panel D — novelty and attribution

Please search for prior work combining:

1. fixed-degree Bernstein coefficient inner cones on conforming simplicial FEM;
2. constructive Mosco recovery for those practical cones;
3. globally assembled coefficient projection localized at a free boundary;
4. the defect-order/codimension/duality rate law;
5. the balanced `3/2` quadratic-contact specialization;
6. a formal proof bridge covering the finite certificate and abstract endgame.

General Bernstein convex-hull theory, bounds-constrained approximation and
finite-element Mosco convergence are acknowledged prior art and are not claimed
as new individually.

## Required report format

Please return:

- reviewer name and affiliation;
- panel addressed;
- exact commit reviewed;
- verdict: `PASS`, `PASS AFTER CORRECTION`, or `FAIL`;
- numbered findings with theorem/file/line references;
- any missing citation or collision;
- permission or refusal to publish the report.

## Principal files

- `GRAND_THEOREM_FINAL_REVIEWED_2026-07-20.md`;
- `BERNSTEIN_BEZIER_GRAND_BARRIER_THEOREM.md`;
- `CORRECTED_THEOREM_AND_CONSTANT_LEDGER.md`;
- `GRAND_FORMALIZATION_MAP.md`;
- `audit_packets/AI_RED_TEAM_PANEL_2026-07-20.md`;
- `lean/GrandCanonicalAudit.lean`;
- `lean/BernsteinObstacle/ConvexConstraint.lean`;
- `reproduction/README.md`.

## Trust statement

The project currently presents a candidate grand theorem and a substantial
formal reduction. It does not claim independent confirmation until signed
external reports are received.