# Panel C proof map: corrected clipping repair and three-halves rate

## Exact scoped claim

The intended mechanics theorem is stated in spatial dimension `d = 2` or
`d = 3` and fixed polynomial degree `r >= 1`. More generally, the same proof
applies in a fixed finite dimension when the pointwise interpolation used below
is well defined, for example under `r + 1 > d/2` together with the stated local
`C^{1,1}` assumptions.

For the zero-obstacle problem, assume:

1. the interior free boundary `Gamma` is compact and regular;
2. `u in C^{1,1}` and `u = grad u = 0` on `Gamma`;
3. on the positive side,
   \[
   c_0d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
   \]
4. a mesh-independent one-sided `H^{r+1}` extension exists near `Gamma`;
5. outside the risky patch,
   \[
   \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg}
   \]
   uniformly over the mesh family;
6. the multiplier is a bounded nonnegative density supported on contact;
7. the risky set is defined using local element size,
   \[
   \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
   \]
8. on its fixed one-ring enlargement `omega_h`,
   \[
   c_mh_\Gamma\le h_T\le C_mh_\Gamma,
   \qquad |\omega_h|\le C_\Gamma h_\Gamma;
   \]
9. the physical boundary is separated from the free boundary or positive
   boundary elements lie in a collar with a uniform `C^{1,1}` bound and the
   stated compatible inward linear-growth condition;
10. the obstacle is represented exactly after shifting to a zero-gap problem.

Then
\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]

The local-distance hypothesis is deliberate. Shape regularity alone does not
allow a strip defined only by a single `h_Gamma` to control larger transition
elements.

## Dependency map

### C1. Coefficient-to-value estimate

For barycentric-lattice interpolation,
\[
|b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})|
\le C_{r,\mathrm{shape}}h_T^2\operatorname{Lip}(\nabla v).
\]
The fixed reference collocation inverse and exact affine reproduction cancel
the constant and linear Taylor terms. All-degree unisolvence is recorded in
`UNISOLVENCE_PROOF.md`; exact constants through degree six are verification
examples.

**Failure criterion:** find a fixed degree, dimension, or shape-regular simplex
for which affine cancellation or `h_T^2` scaling fails.

### C2. Local-size localization

For a positive element outside `R_h`, every barycentric node is at distance at
least `c kappa h_T` from `Gamma`. Quadratic nondegeneracy gives a positive node
value of order `h_T^2`, which dominates the `O(h_T^2)` coefficient error when
`kappa` is chosen sufficiently large. Contact-interior elements interpolate
zero. Positive interior elements outside the quadratic-growth neighborhood are
handled separately by compactness and local uniform continuity: there `u` has
a strictly positive minimum and the fixed inverse-collocation map approaches
the locally constant value vector.

The one-ring assumptions convert the locally defined risky set into an
`O(h_Gamma)` patch with volume `O(h_Gamma)`.

**Failure criterion:** construct a negative coefficient outside `R_h`, or a
mesh satisfying the stated one-ring assumptions whose risky patch has volume
larger than `C h_Gamma`.

### C3. Physical-boundary split

On a positive boundary element, Bernstein coefficients attached to the boundary
face are exactly zero. Every off-face lattice point lies a distance comparable
to `h_T` inside the domain. The uniform boundary-collar `C^{1,1}` bound gives an
`O(h_T^2)` coefficient discrepancy, while the inward linear lower bound is
`O(h_T)`; therefore the off-face coefficients are nonnegative for small `h_T`.

**Failure criterion:** find an off-face lattice point whose inward distance is
not comparable to `h_T` on a uniformly shape-regular simplex, show that
boundary-face coefficients need not vanish, or show that the stated boundary
collar hypotheses do not provide a uniform `O(h_T^2)` discrepancy.

### C4. Two-sided risky coefficient amplitude

On `omega_h`, local quasi-uniformity gives `h_T comparable to h_Gamma`.
Quadratic upper growth and contact-side vanishing give
`|u(x_j)| <= C h_Gamma^2` at every interpolation node. Fixed-degree collocation
inversion yields
\[
|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2.
\]

**Failure criterion:** show the inverse-collocation constant is not uniform on
the stated shape-regular family or that the nodal values need not be
`O(h_Gamma^2)`.

### C5. Global clipping repair

Clip once per shared global degree of freedom:
\[
\widetilde b_i=\max\{b_i,0\}.
\]
Common-face traces remain identical, boundary zeros remain zero, and the
Bernstein convex-hull property gives pointwise feasibility. The algebraic
statement is Lean formalized in `GlobalMesh.lean`, `FaceTrace.lean`,
`Projection.lean`, and `ProjectionVI.lean`.

**Failure criterion:** give a concrete orientation/indexing configuration in
which global clipping breaks conformity or boundary values.

### C6. Three-halves repair scaling

The correction coefficients are `O(h_Gamma^2)` on a patch of volume
`O(h_Gamma)`. On one `d`-simplex,
\[
\|\nabla d_h\|_{L^2(T)}^2=O(h_\Gamma^{d+2}).
\]
The patch contains `O(h_Gamma^{-(d-1)})` locally quasi-uniform elements, so
\[
\|\nabla d_h\|_{L^2}^2=O(h_\Gamma^3),
\qquad
\|d_h\|_{H^1}=O(h_\Gamma^{3/2}).
\]
The exponent is independent of ambient dimension once the nodal interpolation
and local regularity assumptions are valid, because the support is codimension
one.

**Failure criterion:** identify an incorrect support-volume bound, element
count, inverse estimate, or hidden anisotropy dependence.

### C7. Bulk and strip interpolation

In `d = 2,3`, fixed `r >= 1` gives `H^{r+1}` enough pointwise regularity for the
standard nodal interpolation used in this theorem. More generally, assume the
interpolation is well defined, for example `r + 1 > d/2`. The one-sided
extension and uniform broken regularity bound give
\[
\|u-I_h^ru\|_{H^1(\Omega\setminus\omega_h)}\le Ch^r.
\]
On `omega_h`, `C^{1,1}` regularity and `|omega_h|=O(h_Gamma)` give the
`O(h_Gamma^{3/2})` gradient contribution.

**Failure criterion:** show that the stated dimension/regularity conditions do
not define the nodal interpolant or that the broken bound does not imply a
mesh-uniform bulk interpolation constant.

### C8. Multiplier consistency and minimizer transfer

On contact inside `omega_h`, `u=0` and the repaired field is
`O(h_Gamma^2)`. Bounded multiplier density and patch volume `O(h_Gamma)` give
\[
\langle\lambda,v_h^B-u\rangle=O(h_\Gamma^3).
\]
The exact energy identity and discrete minimality yield
\[
\alpha\|u_h^B-u\|_{H^1}^2
\lesssim
\|v_h^B-u\|_{H^1}^2+
\langle\lambda,v_h^B-u\rangle.
\]
A separate Falk derivation gives the same rate.

**Failure criterion:** locate a sign error, invalid test function, unsupported
multiplier regularity, or missing coercivity/continuity assumption.

## AI-audit result incorporated

The internal AI audit returned `PASS AFTER CORRECTION`:

- the general Mosco theorem passed in every fixed finite dimension;
- the `3/2` scaling mechanism passed conditionally;
- the sharp nodal-interpolation theorem is now explicitly scoped to `d = 2,3`
  or to dimensions/regularity for which pointwise interpolation is valid;
- the physical-boundary case now explicitly assumes a uniform `C^{1,1}` collar
  bound in addition to inward linear growth;
- the old global-`h_Gamma` localization wording was replaced by C2;
- the uniform broken regularity requirement was added in C7;
- the boundary-face/off-face proof was added in C3.

## Required independent verdict

Return `PASS`, `PASS AFTER STATED CORRECTION`, or `FAIL` for C1--C8. Separately
state:

- whether the local grading assumptions are sufficient and reasonably standard;
- whether the exponent `3/2` is valid in dimensions two and three;
- whether the dimension/pointwise-interpolation scope is complete;
- whether the physical-boundary collar assumptions are sufficient;
- whether singular or degenerate free-boundary points must remain excluded;
- the strongest theorem surviving if any assumption is weakened.
