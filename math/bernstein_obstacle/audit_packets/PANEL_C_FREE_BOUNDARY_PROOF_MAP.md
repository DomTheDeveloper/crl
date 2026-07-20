# Panel C proof map: corrected clipping repair and three-halves rate

## Exact scoped claim

For the zero-obstacle problem, assume:

1. the interior free boundary `Gamma` is compact, regular, and separated from the physical boundary;
2. `u in C^{1,1}` and `u = grad u = 0` on `Gamma`;
3. in a fixed tubular neighborhood on the positive side,
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
9. all physical-boundary lattice points carry the homogeneous value zero, and every positive boundary element away from `Gamma` satisfies a uniform inward linear lower bound at lattice points lying off the union of all its physical-boundary faces;
10. the obstacle is represented exactly after shifting to a zero-gap problem.

Then
\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]

The local-distance hypothesis is deliberate. Shape regularity alone does not allow a strip defined only by a single `h_Gamma` to control larger transition elements.

## Dependency map

### C1. Coefficient-to-value estimate

For barycentric-lattice interpolation,
\[
|b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})|
\le C_{r,d,\sigma}h_T^2\operatorname{Lip}(\nabla v).
\]
The fixed reference collocation inverse and exact affine reproduction cancel the constant and linear Taylor terms. All-degree unisolvence is recorded in `UNISOLVENCE_PROOF.md`; exact constants through degree six are verification examples.

**Failure criterion:** find a fixed degree, dimension, or shape-regular simplex for which affine cancellation or `h_T^2` scaling fails.

### C2. Phase classification and local-size localization

A simplex outside `R_h` does not meet `Gamma`. Since a simplex is connected, it is either contained in the contact interior or in the positive phase.

- Contact-interior elements interpolate zero.
- Positive elements in the tubular neighborhood have every lattice point at distance at least `kappa h_T` from `Gamma`; quadratic nondegeneracy gives a value of order `kappa^2 h_T^2`, which dominates the `O(h_T^2)` coefficient error for sufficiently large fixed `kappa`.
- Positive elements separated from `Gamma` and from the physical boundary have a mesh-independent positive lower bound, which dominates the coefficient error for sufficiently small `h`.

The one-ring assumptions convert the locally defined risky set into an `O(h_Gamma)` patch with volume `O(h_Gamma)`.

**Failure criterion:** construct a negative coefficient outside `R_h`, or a mesh satisfying the stated one-ring assumptions whose risky patch has volume larger than `C h_Gamma`.

### C3. Multi-face physical-boundary split

On a positive boundary element, classify lattice points into:

1. points lying on the union of all physical-boundary faces of the simplex;
2. points lying off that union.

Coefficients in the first class are exactly zero because the trace is homogeneous. For fixed degree, every point in the second class has a positive barycentric layer relative to every physical-boundary face. Uniform shape regularity therefore gives
\[
\operatorname{dist}(x_{T,\alpha},\partial\Omega)\ge c_{r,\sigma}h_T.
\]
The inward linear lower bound is `O(h_T)` and dominates the `O(h_T^2)` coefficient discrepancy for sufficiently small `h_T`. This covers corner simplices having more than one physical-boundary face.

**Failure criterion:** find an off-boundary lattice point whose inward distance is not comparable to `h_T`, or show that a coefficient attached to a physical-boundary lattice point need not vanish.

### C4. Two-sided one-ring coefficient amplitude

Clipping a coefficient attached to a shared face changes every incident element, so the support of the repair is the one-ring `omega_h` rather than `R_h` alone.

Every point of `omega_h` is within `C h_Gamma` of `Gamma`: start from a risky element, use the local distance bound there, and cross only a fixed number of neighboring shape-regular elements of size comparable to `h_Gamma`. Quadratic upper growth and contact-side vanishing give `|u(x_j)| <= C h_Gamma^2` at every interpolation node. Fixed-degree collocation inversion yields
\[
|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2,
\qquad T\subset\omega_h.
\]

**Failure criterion:** show the inverse-collocation constant is not uniform on the stated shape-regular family, that the one-ring need not lie in a `C h_Gamma` tubular neighborhood, or that the nodal values need not be `O(h_Gamma^2)`.

### C5. Global clipping repair

Clip once per shared global Bernstein degree of freedom:
\[
\widetilde b_i=\max\{b_i,0\}.
\]
Common-face traces remain identical under all face permutations, every physical-boundary coefficient remains zero, and the Bernstein convex-hull property gives pointwise feasibility. The algebraic statement is Lean formalized in `GlobalMesh.lean`, `FaceTrace.lean`, `ConcreteFaceConformity.lean`, `Projection.lean`, and `ProjectionVI.lean`.

**Failure criterion:** give a concrete orientation/indexing configuration in which global clipping breaks conformity or boundary values.

### C6. Three-halves repair scaling

The correction coefficients are `O(h_Gamma^2)` on a patch of volume `O(h_Gamma)`. On one `d`-simplex,
\[
\|\nabla d_h\|_{L^2(T)}^2=O(h_\Gamma^{d+2}).
\]
The patch contains `O(h_Gamma^{-(d-1)})` locally quasi-uniform elements, so
\[
\|\nabla d_h\|_{L^2}^2=O(h_\Gamma^3),
\qquad
\|d_h\|_{H^1}=O(h_\Gamma^{3/2}).
\]
The exponent is independent of ambient dimension because the support is codimension one.

**Failure criterion:** identify an incorrect support-volume bound, element count, inverse estimate, or hidden anisotropy dependence.

### C7. Bulk and strip interpolation

The one-sided extension and uniform broken regularity bound give
\[
\|u-I_h^ru\|_{H^1(\Omega\setminus\omega_h)}\le Ch^r.
\]
On `omega_h`, fixed-degree interpolation of a `C^{1,1}` function gives a pointwise gradient error `O(h_Gamma)`. Since `|omega_h|=O(h_Gamma)`, the strip contribution is `O(h_Gamma^{3/2})`.

**Failure criterion:** show that the stated broken bound does not imply a mesh-uniform bulk interpolation constant, or that the strip estimate requires regularity stronger than `C^{1,1}`.

### C8. Multiplier consistency and minimizer transfer

Use the multiplier convention
\[
\langle\lambda,v-u\rangle=a(u,v-u)-\ell(v-u)\ge0
\]
for every feasible `v`. The exact identity is
\[
J(v)-J(u)=\tfrac12a(v-u,v-u)+\langle\lambda,v-u\rangle.
\]
On contact inside `omega_h`, `u=0` and the repaired field is between zero and `C h_Gamma^2`. Bounded multiplier density and patch volume `O(h_Gamma)` give
\[
\langle\lambda,v_h^B-u\rangle=O(h_\Gamma^3).
\]
Discrete minimality, continuity, and coercivity yield
\[
\alpha\|u_h^B-u\|_{H^1}^2
\lesssim
\|v_h^B-u\|_{H^1}^2+
\langle\lambda,v_h^B-u\rangle.
\]
A separate Falk derivation gives the same rate.

**Failure criterion:** locate a sign error, invalid test function, unsupported multiplier regularity, or missing coercivity/continuity assumption.

## AI-audit result incorporated

The internal AI audit returned `PASS AFTER CORRECTION`:

- the general Mosco theorem passed;
- the `3/2` scaling mechanism passed conditionally;
- the old global-`h_Gamma` localization wording was replaced by C2;
- the uniform broken regularity requirement was added in C7;
- the physical-boundary proof was expanded to the multi-face formulation in C3;
- the support enlargement from `R_h` to `omega_h` was made explicit in C4.

## Required independent verdict

Return `PASS`, `PASS AFTER STATED CORRECTION`, or `FAIL` for C1--C8. Separately state:

- whether the local grading assumptions are sufficient and reasonably standard;
- whether the exponent `3/2` is valid in dimensions two and three;
- whether the multi-face physical-boundary split is complete;
- whether singular or degenerate free-boundary points must remain excluded;
- the strongest theorem surviving if any assumption is weakened.