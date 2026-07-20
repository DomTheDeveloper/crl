# Panel C proof map: corrected clipping repair and three-halves rate

## Exact scoped claim

Let `(T_n)` be a conforming uniformly shape-regular simplicial mesh sequence,
let `h_n=max_T h_T -> 0`, and fix `r >= 1`. For the zero-obstacle problem,
assume:

1. the interior free boundary `Gamma` is compact and regular;
2. `u in C^{1,1}` and `u = grad u = 0` on `Gamma`;
3. on the positive side,
   \[
   c_0d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
   \]
4. a mesh-independent one-sided `H^{r+1}` extension exists near `Gamma`;
5. outside the risky patch,
   \[
   \sum_{T\not\subset\omega_n}|u|_{H^{r+1}(T)}^2\le C_{\rm reg}
   \]
   uniformly over the mesh family;
6. the multiplier is a bounded nonnegative density supported on contact;
7. the risky set is defined using local element size,
   \[
   \mathcal R_n=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
   \]
8. on its fixed one-ring enlargement `omega_n`, there is a scale
   `h_{Gamma,n} -> 0` such that
   \[
   c_mh_{\Gamma,n}\le h_T\le C_mh_{\Gamma,n},
   \qquad |\omega_n|\le C_\Gamma h_{\Gamma,n};
   \]
9. the physical boundary is separated from the free-boundary analysis or
   positive boundary elements satisfy the stated compatible inward
   linear-growth condition;
10. the obstacle is represented exactly after shifting to a zero-gap problem.

Then

\[
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
\]

The full sequence-indexed derivation and constant ledger are in
`math/bernstein_obstacle/SOBOLEV_FEM_CLOSURE.md`.

The local-distance hypothesis is deliberate. Shape regularity alone does not
allow a strip defined only by a single `h_Gamma` to control larger transition
elements.

## Dependency map

### C1. Coefficient-to-value estimate

For barycentric-lattice interpolation,

\[
|b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})|
\le C_{r,d,\mathrm{shape}}h_T^2\operatorname{Lip}(\nabla v;T).
\]

The fixed reference collocation inverse and exact affine reproduction cancel
the constant and linear Taylor terms. All-degree unisolvence is recorded in
`UNISOLVENCE_PROOF.md`; exact constants through degree six are verification
examples, not the existence proof.

**Failure criterion:** find a fixed degree, dimension, or shape-regular
simplex for which affine cancellation or `h_T^2` scaling fails.

### C2. Local-size localization

If a positive element lies outside `R_n`, then every barycentric lattice point
satisfies

\[
\operatorname{dist}(x_{T,\alpha},\Gamma)>\kappa h_T.
\]

Quadratic nondegeneracy gives

\[
u(x_{T,\alpha})\ge c_0\kappa^2h_T^2,
\]

which dominates the coefficient discrepancy once `kappa` is chosen so that
`c_0 kappa^2` exceeds the uniform collocation/Taylor constant. An element on
the contact side and outside `R_n` is contained in the contact interior and
interpolates zero.

The one-ring assumptions convert the locally defined risky set into an
`O(h_{Gamma,n})` patch with volume `O(h_{Gamma,n})`.

**Failure criterion:** construct a negative coefficient outside `R_n`, or a
mesh satisfying the stated one-ring assumptions whose risky patch violates the
volume bound.

### C3. Physical-boundary split

On a positive boundary element, Bernstein coefficients attached to the
boundary face are exactly zero because the degree-`r` interpolated trace has
zero values at all face lattice nodes. Every off-face lattice point has
opposite barycentric coordinate at least `1/r`. Uniform shape regularity
therefore places it at inward distance at least
`c_face(r,shape) h_T`. The inward linear lower bound is `Omega(h_T)` and
dominates the `O(h_T^2)` coefficient discrepancy for sufficiently small
`h_T`.

**Failure criterion:** find an off-face lattice point whose inward distance is
not comparable to `h_T` on a uniformly shape-regular simplex, or show that the
boundary-face coefficients need not vanish.

### C4. Two-sided risky coefficient amplitude

Every interpolation node in `omega_n` is at distance
`O(h_{Gamma,n})` from `Gamma`. Quadratic upper growth on the positive side,
contact-side vanishing, and fixed-degree collocation inversion yield

\[
|b_{T,\alpha}(I_n^ru)|\le Ch_{\Gamma,n}^2
\qquad(T\subset\omega_n).
\]

**Failure criterion:** show the inverse-collocation constant is not uniform on
the stated shape-regular family, the one-ring does not retain the distance
bound, or the nodal values need not be `O(h_{Gamma,n}^2)`.

### C5. Global clipping repair

Clip once per assembled shared degree of freedom:

\[
\widetilde b_i=\max\{b_i,0\}.
\]

Common-face traces remain identical, boundary zeros remain zero, and the
Bernstein convex-hull property gives pointwise feasibility. The algebraic
statement is Lean formalized in `GlobalMesh.lean`, `FaceTrace.lean`,
`Projection.lean`, and `ProjectionVI.lean`.

The correction is supported in the fixed one-ring patch because an assembled
coefficient changed on a risky element can affect only elements sharing that
coefficient.

**Failure criterion:** give a concrete orientation/indexing configuration in
which global clipping breaks conformity, changes a prescribed boundary zero,
or propagates beyond the fixed patch.

### C6. Three-halves repair scaling by patch volume

Correction coefficients are `O(h_{Gamma,n}^2)`. Fixed-degree norm equivalence
and affine scaling give on every affected element

\[
\|d_n\|_{L^2(T)}^2
\le C|T|h_{\Gamma,n}^4,
\]

\[
\|\nabla d_n\|_{L^2(T)}^2
\le C|T|h_T^{-2}h_{\Gamma,n}^4
\le C|T|h_{\Gamma,n}^2.
\]

Summing directly by patch volume avoids an informal dimension-dependent
element count:

\[
\|d_n\|_{L^2}^2
\le Ch_{\Gamma,n}^4|\omega_n|
\le Ch_{\Gamma,n}^5,
\]

\[
\|\nabla d_n\|_{L^2}^2
\le Ch_{\Gamma,n}^2|\omega_n|
\le Ch_{\Gamma,n}^3.
\]

Therefore

\[
\|d_n\|_{H^1}\le Ch_{\Gamma,n}^{3/2}.
\]

The exponent is independent of ambient dimension because the entire dimension
dependence has already been absorbed into the physical patch-volume bound.

**Failure criterion:** identify an incorrect support-volume bound, affine
scaling factor, hidden anisotropy dependence, or failure of local size
comparability.

### C7. Bulk and strip interpolation

The one-sided extension and uniform broken regularity bound give

\[
\|u-I_n^ru\|_{H^1(\Omega\setminus\omega_n)}\le Ch_n^r.
\]

On `omega_n`, fixed-degree affine reproduction and `C^{1,1}` regularity give a
pointwise gradient error `O(h_{Gamma,n})`. Since
`|omega_n|^{1/2}=O(h_{Gamma,n}^{1/2})`,

\[
\|u-I_n^ru\|_{H^1(\omega_n)}
\le Ch_{\Gamma,n}^{3/2}.
\]

Combining interpolation and clipping produces a feasible field `v_n^B` with

\[
\|u-v_n^B\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2}).
\]

**Failure criterion:** show that the stated broken bound does not imply a
mesh-uniform bulk interpolation constant or that `C^{1,1}` does not give the
stated strip estimate.

### C8. Multiplier consistency and direct minimizer transfer

Define

\[
\langle\lambda,z\rangle=a(u,z)-F(z).
\]

On contact outside `omega_n`, the repaired field is zero. On contact inside
`omega_n`, coefficient stability and the Bernstein convex-hull bound give

\[
0\le v_n^B\le Ch_{\Gamma,n}^2.
\]

A bounded multiplier density supported on contact therefore satisfies

\[
0\le\langle\lambda,v_n^B-u\rangle
\le C\|\lambda\|_\infty h_{\Gamma,n}^2|\omega_n|
\le Ch_{\Gamma,n}^3.
\]

For every feasible `z`,

\[
J(z)-J(u)
=\tfrac12a(z-u,z-u)+\langle\lambda,z-u\rangle.
\]

Since `K_n^B subset K`, discrete minimality gives the direct estimate

\[
\tfrac12\alpha\|u_n^B-u\|_{H^1}^2
\le J(u_n^B)-J(u)
\le J(v_n^B)-J(u)
\le C(h_n^{2r}+h_{\Gamma,n}^3).
\]

Taking square roots proves the claimed rate. A separate Falk derivation gives
the same estimate.

**Failure criterion:** locate a sign error, unsupported multiplier regularity,
missing support statement, invalid bound on the repaired field over contact,
or missing coercivity/symmetry assumption.

## Constant ledger

The final constant is mesh-index independent. It may depend on fixed degree,
dimension, shape regularity, bilinear-form continuity/coercivity, free-boundary
quadratic-growth constants, tubular geometry, `C^{1,1}` and one-sided
extension bounds, broken `H^{r+1}` regularity, local grading constants, the
fixed ring depth, physical-boundary constants, and `||lambda||_infty`.

## AI-audit result incorporated

The internal AI audit returned `PASS AFTER CORRECTION`:

- the general Mosco theorem passed;
- the `3/2` scaling mechanism passed conditionally;
- the old global-`h_Gamma` localization wording was replaced by C2;
- the uniform broken regularity requirement was added in C7;
- the boundary-face/off-face proof was added in C3;
- the scaling proof is now summed directly by patch volume;
- the minimizer transfer is now given by a direct inner-cone energy estimate.

## Required independent verdict

Return `PASS`, `PASS AFTER STATED CORRECTION`, or `FAIL` for C1--C8. Separately
state:

- whether the local grading assumptions are sufficient and reasonably
  standard;
- whether the exponent `3/2` is valid in dimensions two and three;
- whether the physical-boundary split is complete;
- whether singular or degenerate free-boundary points must remain excluded;
- the strongest theorem surviving if any assumption is weakened.
