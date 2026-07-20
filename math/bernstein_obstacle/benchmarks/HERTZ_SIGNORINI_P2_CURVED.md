# Curved isoparametric P2 Bernstein–Bézier Hertz/Signorini benchmark

## Purpose

This benchmark removes the polygonal contact-geometry approximation from the quadratic Hertz/Signorini test. Geometry and displacement are represented by the same quadratic triangular Bernstein–Bézier basis.

On every curved contact edge,
\[
y(t)=\sum_{i=0}^2Y_iB_i^2(t),\qquad
u_y(t)=\sum_{i=0}^2U_iB_i^2(t),
\]
so
\[
g(t)=y(t)+u_y(t)=\sum_{i=0}^2(Y_i+U_i)B_i^2(t).
\]
Consequently,
\[
Y_i+U_i\ge0\quad(i=0,1,2)
\]
certifies nonpenetration at every point of the curved edge.

## Curved geometry

For circular-arc endpoints `P0`, `P2` and exact arc midpoint `M`, the quadratic Bézier control point is
\[
C=2M-\frac{P_0+P_2}{2}.
\]
The finest test has maximum circular-radius error `1.78e-11`, and all isoparametric Jacobians remained positive.

## Selected finest result

For 20,193 displacement unknowns:

- PDAS iterations: 13;
- KKT residual: `5.12e-13`;
- bracketed Hertz contact-half-width error: `1.01e-4`;
- pressure-fitted half-width error: `9.42e-4`;
- pressure `L2` error: `8.82e-2`;
- half-load error: `1.02e-11`;
- minimum gap coefficient: exactly `0`;
- maximum circular-boundary radius error: `1.78e-11`.

The polygonal P2 run at the same unknown count had pressure `L2` error about `2.05e-1`; curved geometry reduces that diagnostic by approximately 57% while retaining the same pointwise Bernstein gap certificate.

## Mesh-phase sensitivity correction

The selected 160-interval mesh has an unusually small bracketed contact-width error because its last active edge lands close to the exact Hertz radius. Neighboring curved meshes give:

| Angular intervals | Unknowns | Bracketed-width error | Pressure-fitted error | Pressure `L2` error |
|---:|---:|---:|---:|---:|
| 145 | 15,979 | `3.055e-3` | `3.544e-4` | `1.305e-1` |
| 155 | 19,563 | `2.346e-3` | `8.385e-4` | `9.735e-2` |
| 160 | 20,193 | `1.011e-4` | `9.419e-4` | `8.818e-2` |
| 165 | 20,823 | `2.400e-3` | `2.712e-5` | `9.074e-2` |
| 170 | 22,815 | `4.289e-5` | `1.551e-3` | `1.256e-1` |

Therefore the previously quoted approximately `48.9×` comparison is only a selected-mesh observation, not a uniform accuracy factor. The robust validation metrics are:

- exact coefficientwise feasibility;
- KKT residual and complementarity;
- total reaction balance;
- positive curved-element Jacobians;
- pressure-profile error across a mesh sequence;
- agreement with a second FEM assembly framework.

## Optimizer and framework checks

On the coarsest curved P2 system, an independently initialized L-BFGS-B solve agreed with PDAS to:

- objective difference `9.56e-12`;
- displacement `L∞` difference `5.66e-7`;
- minimum gap coefficient `0`.

A separate scikit-fem implementation independently assembles the elasticity operator and constraint matrix. It is a second FEM assembly framework developed within this project, not an external clean-room reproduction.

## Reproduction

Run `hertz_signorini_p2_curved_bernstein.py` beside `hertz_signorini_p2_bernstein.py`. The script emits the CSV table, optimizer cross-check JSON, pressure profile, convergence plot, and geometry-error plot. The neighboring-mesh phase-sensitivity data must also be reported whenever contact-width improvement factors are discussed.