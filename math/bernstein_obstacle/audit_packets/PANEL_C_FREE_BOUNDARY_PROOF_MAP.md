# Panel C proof map: clipping repair and the three-halves rate

## Exact scoped claim

For the zero-obstacle problem, assume:

1. the interior free boundary `Gamma` is compact and regular;
2. `u in C^{1,1}` and `u = grad u = 0` on `Gamma`;
3. on the positive side,
   \[
   c_0 d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
   \]
4. a mesh-independent one-sided `H^{r+1}` extension exists near `Gamma`;
5. the multiplier is a bounded nonnegative density supported on contact;
6. interface elements are locally quasi-uniform with scale `h_Gamma`;
7. the physical boundary is separated from the free boundary or satisfies the
   stated compatible linear-growth condition;
8. the obstacle is represented exactly after shifting to a zero-gap problem.

Then the coefficient-feasible minimizer satisfies

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]

## Dependency map

### C1. Coefficient-to-value estimate

For barycentric-lattice interpolation, inversion of the fixed reference
collocation matrix and exact reproduction of affine functions give

\[
|b_{T,\alpha}(I_T^r v)-v(x_{T,\alpha})|
\le C_{r,\mathrm{shape}} h_T^2\operatorname{Lip}(\nabla v).
\]

The all-degree interpolation unisolvence proof is recorded in
`UNISOLVENCE_PROOF.md`; exact rational constants through degree six are checked
by `verify_bernstein_coefficient_constants.py`.

**Failure criterion:** find a degree, dimension, or shape-regular simplex for
which the affine moment cancellation or `h_T^2` scaling fails.

### C2. Localization

If an element lies more than `kappa h_T` inside the positive phase, quadratic
nondegeneracy gives a lattice value of order `h_T^2` with a coefficient larger
than the coefficient error. Contact-interior elements interpolate the zero
function. Thus negative coefficients occur only in an `O(h_Gamma)` interface
patch.

**Failure criterion:** construct a negative coefficient outside every fixed
multiple of the free-boundary strip while all assumptions hold.

### C3. Two-sided risky coefficient amplitude

On an interface element, the quadratic upper growth and `C^{1,1}` regularity
give `|u(x_j)| <= C h_Gamma^2` at every interpolation node. Fixed-degree
collocation inversion then gives

\[
|b_{T,\alpha}(I_h^r u)|\le C h_\Gamma^2.
\]

This two-sided estimate is essential for both repair size and multiplier
consistency.

**Failure criterion:** show the inverse-collocation constant is not uniform on
the stated shape-regular family or that nodal values need not be `O(h^2)`.

### C4. Global clipping repair

Identify shared global Bernstein degrees of freedom and set

\[
\widetilde b_i=\max\{b_i,0\}.
\]

Clipping is performed once per global degree of freedom, so shared face traces
remain identical. Zero boundary coefficients remain zero. Pointwise
nonnegativity follows from the Bernstein convex-hull property.

This algebraic statement is Lean formalized in `GlobalMesh.lean`,
`Projection.lean`, and `ProjectionVI.lean`.

**Failure criterion:** give an orientation/shared-index configuration in which
global clipping breaks conformity or boundary values.

### C5. Three-halves repair scaling

The correction coefficients are `O(h_Gamma^2)` on a patch of thickness
`O(h_Gamma)`. On one `d`-simplex,

\[
\|\nabla d_h\|_{L^2(T)}^2=O(h_\Gamma^{d+2}).
\]

A codimension-one strip contains `O(h_Gamma^{-(d-1)})` locally quasi-uniform
elements. Therefore

\[
\|\nabla d_h\|_{L^2}^2=O(h_\Gamma^3),
\qquad
\|d_h\|_{H^1}=O(h_\Gamma^{3/2}),
\]

independently of ambient dimension. The deterministic stress test recovers a
fitted exponent `1.5001806` and a terminal slope `1.500000003`.

**Failure criterion:** identify an incorrect element count, support-volume
bound, inverse estimate, or hidden anisotropy dependence.

### C6. Bulk and strip interpolation

Away from the free boundary, the one-sided extension gives the standard
`O(h^r)` energy estimate. On the interface strip, `C^{1,1}` regularity gives an
`O(h_Gamma^{3/2})` contribution after the same strip-volume count.

**Failure criterion:** show the stated extension hypothesis does not provide a
uniform bulk interpolation constant as the interface is approached.

### C7. Multiplier consistency

On the contact portion of the interface strip, `u=0` and the repaired feasible
field is `O(h_Gamma^2)`. Since the multiplier density is bounded and the strip
has measure `O(h_Gamma)`,

\[
\langle\lambda,v_h^B-u\rangle=O(h_\Gamma^3).
\]

**Failure criterion:** challenge multiplier sign, support, absolute continuity,
or the pointwise amplitude of the repair on contact.

### C8. Transfer to the minimizer

The exact energy identity and discrete minimality imply

\[
\alpha\|u_h^B-u\|_{H^1}^2
\lesssim
\|v_h^B-u\|_{H^1}^2+
\langle\lambda,v_h^B-u\rangle.
\]

A separate Falk variational-inequality derivation yields the same estimate.
The finite-dimensional energy algebra is formalized in `Energy.lean` and
`FiniteObstacle.lean`.

**Failure criterion:** locate a sign error, an invalid test function, or a
missing coercivity/continuity assumption in either transfer proof.

## Required reviewer verdict

Return PASS/PASS AFTER CORRECTION/FAIL for C1--C8, and separately state:

- whether the exponent `3/2` is valid in dimensions two and three;
- whether the physical-boundary assumption is sufficient;
- whether singular or degenerate free-boundary points must remain excluded;
- the strongest theorem that survives if any assumption is weakened.
