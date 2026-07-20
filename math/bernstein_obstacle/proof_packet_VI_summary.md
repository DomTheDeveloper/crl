# Bernstein–Bézier Obstacle Proof Packet XII

## Exact scope

This packet records the strongest theorem currently supported by the repository:

1. Mosco convergence of fixed-degree conforming simplicial Bernstein coefficient cones to the homogeneous obstacle cone.
2. Strong convergence of the corresponding symmetric coercive energy minimizers.
3. Under the corrected regular-interface assumptions below,
   \[
   \|u-u_h^B\|_{H^1(\Omega)}\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
   \]
4. Nestedness and strict-positivity completeness of uniformly shape-regular subdivision-refined Bernstein cones.
5. The limitation that subdivision alone need not certify a nonnegative polynomial having zeros.

The internal adversarial audit returned **PASS AFTER CORRECTION**. The corrections are part of the theorem statement here, not merely editorial notes.

---

## 1. General Bernstein cones

Let
\[
V=H_0^1(\Omega),\qquad K=\{v\in V:v\ge0\text{ a.e.}\},
\]
and on a conforming uniformly shape-regular simplicial mesh let
\[
K_h^B=\{v_h\in V_h^r:b_{T,\alpha}(v_h)\ge0\ \forall T,\alpha\}.
\]
The nonnegative Bernstein partition of unity gives `K_h^B ⊂ K`.

For smooth `w ≥ 0`, define
\[
\mathcal B_T^rw=\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]
The sampled face data agree from both adjacent elements, so the operator is conforming. If `w` has compact support in the interior, then for all sufficiently fine meshes every boundary lattice value vanishes, hence the assembled recovery has homogeneous trace.

On the fixed reference simplex, the operator reproduces affine functions. Taylor expansion and affine scaling therefore give
\[
\|w-\mathcal B_T^rw\|_{L^2(T)}
 \le C h_T^2 |T|^{1/2}\|D^2w\|_{L^\infty(T)},
\]
\[
\|\nabla(w-\mathcal B_T^rw)\|_{L^2(T)}
 \le C h_T |T|^{1/2}\|D^2w\|_{L^\infty(T)}.
\]
The constant depends only on fixed degree, dimension, and shape regularity.

Nonnegative `C_c^∞(Ω)` functions are dense in the positive cone of `H_0^1`: approximate in `H_0^1`, apply the continuous positive-part map, and mollify with a nonnegative kernel inside the positive distance of the compact support from the boundary. A monotone diagonal sequence then gives, for every `v in K`, a sequence `v_h in K_h^B` converging strongly to `v`.

The weak Mosco condition follows from `K_h^B ⊂ K` and weak closedness of the norm-closed convex cone `K`. Hence
\[
K_h^B\xrightarrow{M}K.
\]
For a symmetric continuous coercive quadratic energy, recovery, weak lower semicontinuity, uniqueness, and convergence of the energy norm imply strong convergence of minimizers.

---

## 2. Exact coefficient-to-value estimate

For barycentric-lattice interpolation `I_T^r`, let `A_r` be the inverse Bernstein collocation matrix on the reference simplex. Then
\[
b_\alpha(I_T^rv)=\sum_j(A_r)_{\alpha j}v(x_j).
\]
Affine reproduction gives
\[
\sum_j(A_r)_{\alpha j}=1,
\qquad
\sum_j(A_r)_{\alpha j}x_j=x_\alpha.
\]
Taylor expansion therefore cancels the constant and linear terms and yields
\[
|b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})|
\le C_{r,d,\sigma}h_T^2\operatorname{Lip}(\nabla v),
\]
where `σ` is the shape-regularity bound. The general barycentric-lattice unisolvence theorem is proved separately; finite exact inversions through degree six are verification examples rather than the existence proof.

---

## 3. Corrected regular-free-boundary theorem

Assume:

- `Γ = ∂{u>0} ∩ Ω` is compact and `C^1` and has positive distance from the physical boundary;
- `u ∈ C^{1,1}` and `u = ∇u = 0` on `Γ`;
- in a fixed tubular neighborhood on the positive side,
  \[
  c_0d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
  \]
- a mesh-independent one-sided `H^{r+1}` extension exists near `Γ`;
- outside the risky patch the broken regularity is uniformly bounded:
  \[
  \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg};
  \]
- the multiplier is a nonnegative `L^∞` density supported on the contact set;
- the local risky set is
  \[
  \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
  \]
- on its fixed one-ring enlargement `ω_h`,
  \[
  c_mh_\Gamma\le h_T\le C_mh_\Gamma,
  \qquad |\omega_h|\le C_\Gamma h_\Gamma;
  \]
- every physical-boundary lattice point carries the homogeneous value zero, while positive boundary elements away from `Γ` satisfy a uniform inward linear lower bound at lattice points lying off the union of all physical-boundary faces;
- the obstacle is represented exactly after shifting to a zero-gap problem.

The local-distance definition is essential. A strip defined only with one global `h_Γ` does not control larger transition elements under shape regularity alone.

### Localization

A non-risky element does not meet `Γ`, hence, by connectedness, is either contained in the contact interior or in the positive phase.

- Contact-interior elements interpolate zero.
- Positive elements in the tubular neighborhood have nodal values at least `c κ^2 h_T^2`; for sufficiently large fixed `κ`, this dominates the coefficient discrepancy `C h_T^2`.
- Positive elements separated from both `Γ` and the physical boundary have a mesh-independent positive lower bound, which dominates `C h_T^2` for sufficiently small `h`.
- On a positive physical-boundary element, coefficients whose lattice points lie on any physical-boundary face vanish exactly. Every other fixed-degree lattice point lies a distance comparable to `h_T` inside the domain, so the inward linear lower bound is `O(h_T)` and dominates the `O(h_T^2)` coefficient discrepancy.

Thus all negative coefficients occur in `R_h`.

### One-ring amplitude bound

Clipping a face coefficient changes every incident element, so the repair is supported on the one-ring patch `ω_h`, not merely on `R_h`. Every point of `ω_h` lies within `C h_Γ` of `Γ`. Quadratic upper growth on the positive side and vanishing on contact give
\[
|u(x_j)|\le Ch_\Gamma^2
\]
at every interpolation node in the patch. Fixed-degree collocation stability gives
\[
|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2,
\qquad T\subset\omega_h.
\]

### Conforming clipping repair

Clip each shared global coefficient once:
\[
\widetilde b_i=\max\{b_i,0\}.
\]
Common-face traces remain identical, all physical-boundary coefficients remain zero, and the resulting function is pointwise feasible.

The correction has coefficient amplitude `O(h_Γ^2)` on a codimension-one patch of volume `O(h_Γ)`. Reference-element norm equivalence and affine scaling give
\[
\|d_h\|_{L^2}\le Ch_\Gamma^{5/2},
\qquad
\|\nabla d_h\|_{L^2}\le Ch_\Gamma^{3/2}.
\]
The exponent is independent of ambient dimension because the patch has codimension one.

The uniform broken regularity bound gives the bulk `O(h^r)` term. On `ω_h`, `C^{1,1}` interpolation gives an `O(h_Γ)` pointwise gradient error over volume `O(h_Γ)`, hence an `O(h_Γ^{3/2})` contribution. Therefore a feasible recovery satisfies
\[
\|u-v_h^B\|_{H^1}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]
A positive piecewise-linear cutoff lift provides a second repair with the same rate.

---

## 4. Transfer to the minimizer

For feasible `v`, with multiplier convention
\[
\langle\lambda,v-u\rangle=a(u,v-u)-\ell(v-u)\ge0,
\]
the exact energy identity is
\[
J(v)-J(u)=\tfrac12a(v-u,v-u)+\langle\lambda,v-u\rangle.
\]
On the contact part of the risky patch, `u=0` and `0 ≤ v_h^B ≤ Ch_Γ^2`; bounded multiplier density and patch measure `O(h_Γ)` give
\[
\langle\lambda,v_h^B-u\rangle\le C\|\lambda\|_\infty h_\Gamma^3.
\]
Discrete minimality, continuity, and coercivity yield
\[
\|u-u_h^B\|_{H^1}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]
A separate Falk derivation gives the same estimate.

---

## 5. Numerical-claim correction

One matched-size Hertz mesh pair produced an approximately `48.9×` smaller bracketed active-set contact-width error. Neighboring meshes show that this scalar estimator is phase sensitive because the last active edge can land unusually close to the exact Hertz radius. It is not a uniform convergence-factor claim.

The robust conclusions are:

- coefficientwise nonpenetration over each complete curved edge;
- small KKT residuals and accurate total reaction;
- positive curved-element Jacobians;
- lower pressure-profile error for curved quadratic geometry on the reported benchmark sequence;
- close agreement with a second FEM assembly framework developed within the project.

That second implementation is not described as an external clean-room replication.

---

## 6. Deliberate exclusions and trust boundary

The sharp theorem excludes singular or degenerate free-boundary points, free boundaries meeting the physical boundary, anisotropic meshes without a separate audit, inexact arbitrary obstacles, measure-valued multipliers, nonsymmetric operators, and optimal adaptive-complexity claims.

The finite coefficient, simplex, clipping, projection/KKT, assembly, energy, Mosco-infrastructure, diagonal-recovery, Sobolev/FEM recovery-interface, strip-scaling, and Hilbert-space VI layers are machine checked under pinned Lean/mathlib toolchains. The moving Sobolev finite-element realization, local free-boundary geometry, coefficient localization on actual meshes, and complete sharp rate remain analytical and require independent expert review.