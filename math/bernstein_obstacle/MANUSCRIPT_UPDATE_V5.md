# Manuscript update V5

The venue manuscript has been rebuilt as a 19-page V5 submission package.

## Added mechanics result

The plane-strain Hertz--Signorini section now includes a genuinely curved
quadratic isoparametric Bernstein--Bézier contact discretization.

On each contact edge, geometry and vertical displacement use the same quadratic
Bernstein basis, so

\[
g(t)=\sum_{i=0}^2(Y_i+U_i)B_i^2(t).
\]

Nonnegative gap coefficients certify nonpenetration at every point of the
curved edge.

Finest curved result:

- 20,193 displacement unknowns;
- maximum circular-radius error `1.78e-11`;
- positive isoparametric Jacobians;
- PDAS KKT residual `5.12e-13`;
- bracketed Hertz half-width error `1.01e-4`;
- pressure `L2` error `8.82e-2`;
- half-load error `1.02e-11`;
- minimum gap coefficient `0`.

At the same algebraic size, the polygonal P2 pressure `L2` error was `2.05e-1`,
so curved geometry lowers this diagnostic by approximately 57 percent.

An independently initialized L-BFGS-B solve on the coarse curved system agrees
with PDAS within `9.56e-12` in objective value and retains zero minimum gap.

## Verification

- two successful `pdflatex` passes;
- 19 pages;
- no undefined references or citations;
- no overfull boxes;
- PDF preflight passed;
- all pages rendered and visually inspected;
- source, reproducibility, and full-submission bundles checksumed.
