# Manuscript update V8 - constant ledger, robust mechanics, expanded formal stack

## Analytical presentation

- Added an explicit localization threshold

  ```text
  kappa >= 1 + sqrt(C_coeff / c0).
  ```

- Added a ledger of every permitted dependence of the final sharp-rate
  constant and explicitly stated that it is independent of `h`, `h_Gamma`, the
  mesh index, interface-element count, and mesh phase.
- Added the unified corrected theorem and constant ledger to the repository.

## Phase-robust Hertz comparison

The manuscript no longer relies on the selected-mesh approximately `48.9x`
width observation as the meaningful improvement claim.

Relative to the matched-size P1 run with 20,513 displacement unknowns, across
five neighboring curved P2 meshes:

- median bracketed contact-width error is approximately `2.13x` lower;
- median pressure `L2` error is approximately `3.32x` lower;
- even the largest P2 pressure error in the sweep is approximately `2.34x`
  lower;
- every run has minimum gap coefficient zero and reaction error below
  `1.7e-11`.

A new figure presents this matched-size pressure comparison.

## Expanded machine-checked statement

The manuscript now accurately states that the pinned Lean stack includes:

- arbitrary-simplex certificates and all-degree unisolvence;
- oriented shared-face conformity;
- clipping projection/KKT theory;
- assembled obstacle energies and abstract Mosco/minimizer interfaces;
- local-distance localization;
- physical-boundary linear-growth domination;
- codimension-one strip scaling;
- broken bulk and multiplier cubic bookkeeping;
- the terminal corrected sharp-rate algebraic implication.

It still explicitly excludes the concrete physical Sobolev interpolation,
moving-mesh realization, and free-boundary geometry from the claim of complete
formalization.

## Build

- 21 pages;
- 229-word abstract;
- two clean `pdflatex` passes;
- no undefined references or citations;
- no overfull boxes;
- PDF preflight passed;
- full rendered-page inspection passed.
