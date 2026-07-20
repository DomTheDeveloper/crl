# Bernstein–Bézier Obstacle Novelty Audit

## Search scope

The audit searched exact and neighboring phrases across web-indexed journal
pages, arXiv, Springer, ScienceDirect, Wiley, Cambridge, GitHub/mathlib, and
formal-conjectures. Query families included:

- "Bernstein coefficients" + obstacle / variational inequality / contact;
- "Bernstein–Bézier" + obstacle finite element;
- Mosco convergence + Bernstein finite element cone;
- coefficient clipping + free boundary;
- pointwise-feasible high-order FEM;
- GLL, proximal DG, mixed multiplier, Signorini barriers, and isogeometric
  contact as adjacent competitors;
- Lean, mathlib, Coq, formal verification, and de Casteljau.

This is a strong accessible-index audit, not a logical proof that no obscure or
unindexed publication exists.

## Main conclusion

The literature contains each major ingredient separately:

1. Bernstein coefficient bounds as sufficient global polynomial certificates.
2. High-order variational-inequality and obstacle discretizations.
3. Mosco convergence for many finite-dimensional convex sets.
4. Free-boundary and contact error estimates.
5. Formal Bernstein/de Casteljau theory in Coq.
6. Bernstein infrastructure in mathlib.

The audit did not locate one source combining:

- the Bernstein coefficient obstacle cone;
- a Mosco recovery theorem for that cone;
- strong obstacle-minimizer convergence;
- localization and clipping of negative coefficients near a regular free
  boundary;
- an H1 estimate of `h^r + h_Gamma^(3/2)`;
- pointwise-feasible adaptive contact computation;
- a Lean no-penetration bridge.

## Most important collision risk

Kirby–Shapero (arXiv:2311.05880) is the closest theoretical predecessor. It
proves high-order approximation for the full pointwise bounds-constrained
polynomial set but expressly does not prove the same high accuracy for the
smaller Bernstein coefficient-constrained subset. The current theorem should
be positioned as closing that narrower gap for an obstacle/free-boundary
setting, not as inventing bounds-constrained FEM.

## Formalization boundary

The 2011 Coq paper by Bertot, Guilhot and Mahboubi prevents a claim of being
the first formal study of Bernstein coefficients. The defensible formal claim
is a Lean/mathlib obstacle-facing certificate and clipping interface, followed
by finite no-penetration theorems. Full PDE/FEM formalization remains a larger
library-development program.
