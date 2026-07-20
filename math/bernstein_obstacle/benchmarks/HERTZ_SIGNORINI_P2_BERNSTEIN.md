# Quadratic Bernstein–Bézier Hertz/Signorini contact benchmark

## Why this benchmark matters

The earlier vector-elastic benchmark used linear triangles. This version uses
continuous quadratic triangular Bernstein–Bézier displacement fields, so the
contact certificate now exercises the same high-order control-coefficient
principle as the obstacle method.

Each element uses the six degree-two Bernstein basis functions

\[
\lambda_0^2,\ \lambda_1^2,\ \lambda_2^2,
\ 2\lambda_0\lambda_1,\ 2\lambda_0\lambda_2,
\ 2\lambda_1\lambda_2.
\]

Vertex and edge control coefficients are shared globally.

## Pointwise contact certificate

On a polygonal contact edge, the geometric gap is affine. After degree
elevation to degree two, its three Bernstein coefficients are the two endpoint
heights and their average. These are added to the quadratic vertical
 displacement control coefficients.

The three resulting gap coefficients are constrained to be nonnegative.
Because the edge Bernstein basis is nonnegative and sums to one,

\[
\text{nonnegative edge gap coefficients}
\Longrightarrow
u_y(x)+g(x)\ge0
\]

for every point of the entire contact edge.

Thus the method does not merely enforce contact at vertices or quadrature
points.

## Mechanical model

The plane-strain model and Hertz analytical reference are identical to the
linear benchmark:

\[
R=1,\quad E=200,\quad \nu=0.3,\quad p=0.5,
\]

\[
b=2\sqrt{\frac{2R^2p(1-\nu^2)}{E\pi}}
  =0.0761133360755\ldots,
\]

\[
p_H(x)=\frac{4Rp}{\pi b^2}\sqrt{b^2-x^2}.
\]

The finite-dimensional contact problem is solved by PDAS.

## Results

| Radial x angular intervals | Displacement unknowns | PDAS iterations | Half-width error | Pressure L2 error | Half-reaction error | Minimum gap coefficient |
|---:|---:|---:|---:|---:|---:|---:|
| 4 x 40 | 1,209 | 13 | 7.454e-3 | 6.847e-1 | 4.37e-14 | 0 |
| 6 x 60 | 2,773 | 13 | 4.185e-3 | 4.771e-1 | 3.39e-13 | 0 |
| 8 x 80 | 4,977 | 14 | 2.551e-3 | 3.831e-1 | 7.06e-13 | 0 |
| 12 x 120 | 11,305 | 14 | 9.182e-4 | 2.586e-1 | 2.75e-12 | 0 |
| 16 x 160 | 20,193 | 15 | **1.019e-4** | 2.049e-1 | 1.04e-11 | 0 |

At comparable displacement counts, the quadratic Bernstein representation
resolves the contact half-width substantially more accurately than the linear
boundary representation. On the finest P2 test,

\[
|b_h-b|\approx1.02\times10^{-4}.
\]

The applied half-load is recovered to approximately eleven or more digits,
and every computed gap control coefficient is nonnegative.

## Independent optimization check

The coarse 4 x 40 system was also solved by L-BFGS-B from zero displacement.

- convergence: successful;
- iterations: 1,288;
- objective difference from PDAS: `3.85e-11`;
- displacement L-infinity difference: `1.79e-6`;
- minimum gap coefficient: `0`.

## Limitations

The geometry remains polygonal and the pressure is reconstructed from discrete
contact multipliers with projected Bernstein-control weights. Pressure error
near the contact edge remains limited by the Hertz square-root singularity and
by multiplier reconstruction. A curved isoparametric geometry and an explicit
mixed pressure space are the next upgrades.
