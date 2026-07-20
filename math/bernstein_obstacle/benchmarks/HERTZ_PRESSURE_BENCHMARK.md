# Certified Hertz line-contact pressure benchmark

## Purpose

This benchmark tests whether a Bernstein representation can approximate the
classical Hertz line-contact pressure while preserving three physical
constraints exactly:

1. nonnegative pressure throughout the contact interval;
2. zero pressure at both contact edges;
3. exact resultant normal force.

It validates the pressure representation and certificate. It is not yet a
full vector-elastic finite-element solution of the half-cylinder contact
boundary-value problem.

## Analytical reference

On the contact interval `|x| <= a`, the normalized Hertz pressure is

\[
p(x)=p_{\max}\sqrt{1-(x/a)^2}.
\]

Its resultant force per unit out-of-plane length is

\[
F=\int_{-a}^{a}p(x)\,dx=\frac{\pi a p_{\max}}{2}.
\]

The square-root pressure profile is the standard reference used in modern
Hertz contact validation studies. Examples include recent Computational
Mechanics papers comparing finite-element contact pressure against the
analytical law.

## Bernstein problem

After mapping the contact interval to `t in [0,1]`, fit

\[
p_n(t)=\sum_{k=0}^{n}c_kB_{k,n}(t)
\]

by weighted least squares subject to

\[
c_k\ge0,\qquad c_0=c_n=0,
\qquad \sum_{k=0}^{n}c_k=\frac{(n+1)F}{2a}.
\]

The final equality is exact because

\[
\int_0^1B_{k,n}(t)\,dt=\frac1{n+1}.
\]

Coefficient nonnegativity certifies `p_n(t) >= 0` for every point, not only at
quadrature nodes.

## Independent optimization check

The same convex quadratic program is solved by:

- SciPy SLSQP;
- a custom primal active-set method using equality-constrained KKT systems.

At degree 24:

- exact force error: `0`;
- minimum pressure on 40,001 points: `0`;
- both endpoint pressures: `0`;
- active-set KKT residual: `3.55e-15`;
- optimizer pressure `L-infinity` difference: `3.13e-5`;
- objective difference: `1.53e-10`.

The coefficient vectors differ more than the represented pressure because the
high-degree Bernstein least-squares system is ill-conditioned; the represented
fields and objectives agree closely.

## Convergence summary

| Degree | L2 pressure error | L-infinity pressure error | Force error |
|---:|---:|---:|---:|
| 4 | 7.343e-2 | 1.321e-1 | 0 |
| 8 | 3.293e-2 | 9.075e-2 | 2.22e-16 |
| 12 | 2.032e-2 | 7.199e-2 | 2.22e-16 |
| 16 | 1.473e-2 | 6.140e-2 | 2.22e-16 |
| 20 | 1.149e-2 | 5.424e-2 | 0 |
| 24 | 9.442e-3 | 4.916e-2 | 0 |

The slower edge convergence is expected because the analytical pressure has a
square-root derivative singularity at the contact boundary.

## Next mechanics gate

The next benchmark must solve the plane-strain elastic semicylinder/rigid-plane
Signorini problem and compare:

- contact half-width;
- pressure profile;
- resultant force;
- displacement and stress fields;
- penetration and negative-pressure diagnostics;
- runtime and active-set convergence.
