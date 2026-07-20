# Lean formalization plan and valuation

## Recommended pricing

- Isolated reusable Bernstein/no-penetration bridge: **$3,500–$8,500**.
- Complete algebraic and simplicial Bernstein library: **$25,000–$60,000**.
- General Mosco/minimizer theorem through fixed-degree FEM: **$75,000–$150,000**.
- Full scoped free-boundary theorem through the
  `h^r + h_Gamma^(3/2)` estimate: **$175,000–$350,000**.
- Paper-complete, no-`sorry`, axiom-audited formalization with independent
  statement-faithfulness review: **$250,000–$500,000 professional replacement
  value**.

The staged public-bounty schedule below totals **$248,500**.

These numbers are project estimates based on scope, missing library
infrastructure, expected review burden, and the distinction between compilation
and faithful formalization. They are not claims of an established universal
market price.

## Staged public bounties

| Stage | Deliverable | Proposed bounty |
|---|---|---:|
| 0 | Faithful paper-to-Lean statement specification | $5,000 |
| 1 | One-dimensional Bernstein certificate bridge | $5,000 |
| 2 | Clipping and downstream no-penetration theorem | $3,500 |
| 3 | Simplicial Bernstein–Bézier and face/subdivision infrastructure | $20,000 |
| 4 | Abstract convex/Mosco/variational-inequality layer | $30,000 |
| 5 | General finite-element Mosco and strong-minimizer theorem | $45,000 |
| 6 | Coefficient localization and conformity-preserving clipping repair | $60,000 |
| 7 | Sharp `H1` rate plus multiplier/energy/Falk proofs | $60,000 |
| 8 | Reproducibility, axiom audit, and independent faithfulness review | $20,000 |

## Why the full price is high

The algebraic certificate is small. The expensive components are absent or
specialized infrastructure:

1. simplicial Bernstein bases and shared-face coefficient APIs;
2. shape-regular meshes and affine element scaling;
3. finite-element interpolation and Sobolev estimates;
4. Mosco convergence of moving convex sets;
5. regular free-boundary tubular geometry and strip-volume estimates;
6. multiplier support and Falk/energy estimates;
7. a faithful paper-to-Lean correspondence audit.

## Acceptance gates

Payment should be milestone-based and require:

- a pinned Lean/mathlib revision;
- no `sorry`, no project axioms, and explicit `#print axioms`;
- a natural-language theorem-correspondence document;
- deterministic build instructions;
- independent review of theorem faithfulness;
- upstream-quality names and reusable lemmas where practical.

## Current formal status

The one-dimensional coefficient certificate, convex-hull/range bounds,
clipping, and no-penetration theorem have been written in Lean and are going
through a pinned checker. The higher analytic theorem package remains informal
mathematics plus numerical verification; it must not be advertised as fully
Lean-formalized yet.
