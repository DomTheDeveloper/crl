# Curved isoparametric P2 Bernstein–Bézier Hertz/Signorini benchmark

## Purpose

This benchmark removes the polygonal contact-geometry approximation from the
quadratic Hertz/Signorini test. Geometry and displacement are represented by
the same quadratic triangular Bernstein–Bézier basis.

On every curved contact edge,

\[
y(t)=\sum_{i=0}^2Y_i B_i^2(t),\qquad
u_y(t)=\sum_{i=0}^2U_i B_i^2(t),
\]

so the gap is

\[
g(t)=y(t)+u_y(t)=\sum_{i=0}^2(Y_i+U_i)B_i^2(t).
\]

Consequently, the three linear inequalities

\[
Y_i+U_i\ge0,\qquad i=0,1,2,
\]

certify nonpenetration at every point of the curved edge.

## Curved geometry

For circular-arc endpoints `P0`, `P2` and exact arc midpoint `M`, the quadratic
Bézier control point is

\[
C=2M-\frac{P_0+P_2}{2}.
\]

This forces the curve to interpolate the exact arc midpoint. The finest test
has maximum circular-radius error

\[
1.78\times10^{-11}.
\]

All isoparametric Jacobians remained positive.

## Finest result

For 20,193 displacement unknowns:

- PDAS iterations: 13;
- KKT residual: `5.12e-13`;
- bracketed Hertz contact-half-width error: `1.01e-4`;
- pressure-fitted half-width error: `9.42e-4`;
- pressure `L2` error: `8.82e-2`;
- half-load error: `1.02e-11`;
- minimum gap coefficient: exactly `0`;
- maximum circular-boundary radius error: `1.78e-11`.

The polygonal P2 run at the same unknown count had pressure `L2` error about
`2.05e-1`; curved geometry reduces it by approximately 57% while retaining the
same pointwise Bernstein gap certificate.

## Independent optimizer check

On the coarsest curved P2 system, an independently initialized L-BFGS-B solve
agreed with PDAS to:

- objective difference `9.56e-12`;
- displacement `L∞` difference `5.66e-7`;
- minimum gap coefficient `0`.

## Reproduction

Run `hertz_signorini_p2_curved_bernstein.py` beside
`hertz_signorini_p2_bernstein.py`. The script emits the CSV table, independent
cross-check JSON, pressure profile, convergence plot, and geometry-error plot.
