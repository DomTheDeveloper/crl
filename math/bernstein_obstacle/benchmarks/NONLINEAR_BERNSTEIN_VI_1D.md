# Nonlinear nonsymmetric Bernstein obstacle benchmark

## Problem

This benchmark tests the V6 operator theorem on a problem not covered by the
old symmetric metric-projection argument:

\[
A(u)=-u''+0.7u'+u+0.5\tanh(u),
\qquad u\ge0
\]

on `(0,1)` with homogeneous Dirichlet data.

The manufactured exact solution is

\[
u(x)=(x-a)_+^2(1-x),
\qquad
a=\frac{\sqrt5-1}{4}.
\]

The multiplier is one on the contact interval `x<a` and zero on the positive
phase. The load is defined by `f=A(u)-lambda`.

The irrational interface location deliberately changes its position relative
to the mesh under dyadic refinement. This exposes the same interface-phase
sensitivity seen in the curved Hertz contact-width diagnostic.

## Discretization

Each interval uses the quadratic Bernstein basis

\[
(1-t)^2,\qquad2t(1-t),\qquad t^2.
\]

Endpoint coefficients are shared globally and the interior coefficient is
local to the element. Every free assembled Bernstein coefficient is constrained
to be nonnegative, which certifies

\[
u_h(x)\ge0
\]

at every point, not only at nodes.

The nonlinear discrete variational inequality is solved through the
Fischer--Burmeister system

\[
\Phi_i(z,R)=\sqrt{z_i^2+R_i^2}-z_i-R_i=0.
\]

A consistent analytic Jacobian is assembled, including the convection and
`sech^2(u_h)` reaction derivative.

## Reproduction

```bash
python benchmarks/nonlinear_bernstein_vi_1d.py \
  --levels 32,64,128,256 \
  --output results/nonlinear_bernstein_vi_1d_results.json
```

Dependencies are NumPy and SciPy.

## Results

| elements | H1 error | L2 error | FB residual | min coefficient | complementarity |
|---:|---:|---:|---:|---:|---:|
| 32 | 2.441e-4 | 4.116e-6 | 1.593e-15 | -3.15e-18 | 2.03e-17 |
| 64 | 1.697e-4 | 4.043e-6 | 7.633e-16 | 0 | 3.63e-17 |
| 128 | 9.367e-5 | 3.085e-7 | 5.536e-12 | -1.60e-19 | 8.83e-17 |
| 256 | 1.564e-5 | 2.153e-7 | 2.147e-14 | -7.81e-20 | 1.68e-16 |

All apparent negative coefficients and dual residuals are roundoff-scale. The
complementarity products remain below `2e-16`.

## Interpretation

The calculation validates three claims:

1. the Bernstein cone remains exactly pointwise feasible for a nonlinear,
   nonsymmetric operator;
2. the operator VI can be solved directly without symmetrizing it or inventing
   a quadratic energy;
3. the error decreases under refinement while displaying the expected
   interface-phase oscillation.

The individual two-level rates are not advertised as an asymptotic constant:

\[
0.525,\qquad0.857,\qquad2.583.
\]

The phase-dependent oscillation is expected because the irrational free
boundary samples different positions inside the cut element. Across levels
32--256, the normalized quantity

\[
\|u-u_h\|_{H^1}/h^{3/2}
\]

remains between approximately `0.044` and `0.136`. This is consistent with,
but does not prove, the predicted `O(h^{3/2})` interface bound.

## Trust boundary

This is a manufactured one-dimensional validation. It does not independently
prove the multidimensional free-boundary theorem or establish the sharpness of
the exponent. Its role is to demonstrate that the V6 operator extension has a
working nonlinear nonsymmetric instance with complete coefficient feasibility,
dual feasibility, and complementarity diagnostics.
