# Plane-strain Hertz/Signorini elasticity benchmark

## Model

A deformable half-cylinder of radius `R=1` rests above a rigid plane. By
symmetry, the computation uses the lower-right quarter disk

\[
\Omega=\{(x,y):x\ge0,\ y\le R,\ x^2+(y-R)^2\le R^2\}.
\]

The top diameter carries a uniform downward pressure `p=0.5`. Plane-strain
linear elasticity uses

\[
E=200,\qquad \nu=0.3.
\]

The curved boundary has initial rigid-plane gap `g=y` and satisfies the
Signorini conditions

\[
u_y+g\ge0,\qquad \lambda\ge0,
\qquad \lambda(u_y+g)=0.
\]

Symmetry imposes `u_x=0` on `x=0`.

## Hertz reference

The analytical contact half-width is

\[
b=2\sqrt{\frac{2R^2p(1-\nu^2)}{E\pi}}
  =0.0761133360755\ldots,
\]

and the pressure on the half-contact interval is

\[
p_H(x)=\frac{4Rp}{\pi b^2}\sqrt{b^2-x^2},
\qquad 0\le x\le b.
\]

This is the standard pressure law used in contemporary numerical contact
benchmarks.

## Discretization

- conforming P1 triangular plane-strain elasticity;
- polar quarter-disk meshes;
- consistent top-edge traction;
- nodal curved-boundary contact inequalities;
- primal-dual active-set solution;
- lumped projected-length reconstruction of contact pressure.

Because the gap is piecewise linear on each contact edge, nonnegative nodal
gaps certify nonpenetration along the full polygonal boundary edge, not only at
nodes.

## Results

| Radial x angular intervals | Unknowns | PDAS iterations | Contact half-width error | Pressure L2 error | Half-reaction error | Minimum gap |
|---:|---:|---:|---:|---:|---:|---:|
| 8 x 80 | 1,289 | 17 | 7.448e-3 | 6.070e-1 | 4.73e-13 | 0 |
| 12 x 120 | 2,893 | 18 | 1.724e-2 | 5.849e-1 | 4.73e-14 | 0 |
| 16 x 160 | 5,137 | 19 | 1.234e-2 | 4.661e-1 | 6.32e-14 | 0 |
| 24 x 240 | 11,545 | 18 | 7.445e-3 | 3.663e-1 | 1.46e-11 | 0 |
| 32 x 320 | 20,513 | 18 | 4.997e-3 | 3.230e-1 | 1.95e-11 | 0 |

The contact-half-width sequence is not monotone on the coarsest meshes because
the contact boundary is represented polygonally and the endpoint lies between
nodes. The fine-mesh sequence approaches the analytical half-width.

The half-domain reaction equals the applied half-load `pR=0.5` to near machine
precision on every mesh.

## Independent optimizer check

On the 8 x 80 mesh, the same bound-constrained vector-elastic problem was also
solved by L-BFGS-B from the zero displacement rather than from the PDAS state.

- convergence: successful;
- iterations: 2,766;
- objective difference from PDAS: `2.28e-11`;
- displacement L-infinity difference: `5.74e-7`;
- minimum contact gap: `0`.

## Interpretation

This is now a recognized Hertz/Signorini mechanics benchmark rather than only
a manufactured scalar obstacle test. It confirms:

1. exact discrete nonpenetration on the polygonal contact boundary;
2. global force balance;
3. stable active-set iteration counts under refinement;
4. convergence of contact extent and pressure toward the Hertz reference;
5. agreement between two independent optimization algorithms.

The pressure comparison remains intentionally conservative. Linear triangles,
polygonal geometry, and lumped nodal multiplier recovery are known to be weak
near the square-root contact edge. The next mechanics stage is a quadratic
Bernstein–Bézier or mixed multiplier implementation with curved geometry and a
consistent pressure-space projection.
