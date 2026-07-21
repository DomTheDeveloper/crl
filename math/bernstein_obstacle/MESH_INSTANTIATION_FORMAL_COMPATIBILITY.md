# Formal compatibility note for curved-interface mesh instantiations

The current certified prism theorem uses one fixed affine fiber direction on each
retained element and one fixed hinge amplitude and phase on the corresponding local
model.  A curved regular free boundary must therefore be reduced element-by-element
to a flat constant-coefficient model rather than inserted directly as a family of
varying normal directions.

For a retained element centered at a regular free-boundary point `x_T`, choose:

```text
nu_T = normal at x_T,
a_T  = quadratic-contact coefficient at x_T.
```

Use parallel affine fibers in direction `nu_T`.  In tangent-normal coordinates based
at `x_T`, write the actual local profile as

```text
u - psi = a_T (t_+)^2 + R_T.
```

The remainder `R_T` absorbs all of the following:

1. variation of the contact coefficient `a(s)-a_T`;
2. curvature of the free boundary relative to its tangent line;
3. variation of the normal direction;
4. higher-order PDE terms already present in the regular expansion.

If the free boundary is `C^{1,kappa}` and the amplitude is `C^{0,kappa}`, then on an
`O(h)` patch these perturbations contribute a gradient remainder of order
`O(h^(1+kappa))` (or better).  The existing remainder element and patch theorems then
produce an `O(h^(3/2+kappa))` global remainder, which is absorbed by the certified
leading `h^(3/2)` obstruction.

For a `C^2` arc, the tangent-line graph height is `O(K h^2)`, so replacing the curved
hinge `(t-g(s))_+^2` by the flat hinge `(t_+)^2` changes the normal derivative by
`O(Kh^2)` away from an `O(Kh^2)` transition set.  This is higher order than the
leading `O(h)` derivative mismatch responsible for saturation.

Consequently both the designed tubular mesh and the generic translated-core argument
fit the current Lean API without changing the certified prism theorem:

- each retained element uses a fixed center normal;
- the model phase is `1/2` on a centered flat prism;
- curvature and coefficient variation are sent to the existing remainder channel.
