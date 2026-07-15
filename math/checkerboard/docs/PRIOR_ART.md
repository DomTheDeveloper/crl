# Prior-art and novelty boundary

## Source problem

The checkerboard-restricted no-three-in-line problem studied here was introduced by Thomas Prellberg in:

- T. Prellberg, *No-three-in-line sets on the checkerboard grid*, arXiv:2605.09215 (2026).

That paper defines the monochromatic checkerboard problem, the three parity-sensitive four-direction linear programs, the continuum obstacle problem, and the algebraic constant

\[
\alpha=1.576823396873808\ldots.
\]

It supplies an exact continuum dual certificate and presents the relevant discrete limiting equalities as conjectures.

## Results inherited from Prellberg

The following are not claimed as new here:

- the checkerboard problem and notation;
- the row, column and slope-`±1` relaxations;
- the reduced odd-fat, odd-thin and even linear programs;
- the continuum dual obstacle problem;
- the exact dual functions and the cubic defining `α`;
- all finite values already reported in the source paper.

## Results that appear new in this package

Subject to expert review and a full literature check, the package appears to add:

1. the defect-moment identity and its weighted Cauchy consequence;
2. the finite theorem `Dmono(n) ≤ 2n-4` for `n ≥ 6`;
3. the explicit finite moment bound involving `ceil(2^(2/3)n)`;
4. an exact continuum-to-finite upper sampling lemma;
5. an exact continuum primal certificate matching Prellberg's dual value `α`;
6. the matching lower transfer for the three finite four-direction LPs;
7. an integral four-direction rounding argument using bounded-rank small-codegree hypergraph edge coloring;
8. rigidity and complementary-slackness consequences;
9. selected exact finite certificates showing other slopes are fractionally redundant.

## What is not claimed

The package does not claim to solve:

- the classical unrestricted no-three-in-line problem;
- the all-slope checkerboard lower limit;
- the exact finite value of `Dmono(n)` for arbitrary `n`;
- any DeepMind Formal Conjectures theorem currently present in the repository.

Google DeepMind's Formal Conjectures repository contains a classical no-three-in-line entry, but not the checkerboard-specific Prellberg conjectures as of 15 July 2026.

## Verification versus novelty

Exact computation or Lean compilation verifies that a stated formal artifact follows from its definitions. It does not establish that the mathematical result is historically new. Novelty and priority require review by Prellberg and independent specialists, followed by normal peer review.
