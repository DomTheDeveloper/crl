# Bernstein–Bézier Obstacle Proof Packet XI

## Exact scope

This packet records:

1. Mosco convergence of the coefficient-feasible Bernstein finite-element cones to the homogeneous obstacle cone.
2. Strong convergence of the corresponding symmetric coercive energy minimizers.
3. Under the corrected regular-interface assumptions below,
   \[
   \|u-u_h^B\|_{H^1(\Omega)}\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
   \]
4. Nestedness and strict-positivity completeness of shape-regular subdivision-refined Bernstein cones.
5. The limitation that subdivision alone need not certify a nonnegative polynomial having zeros.

The full internal AI red-team audit returned **PASS AFTER CORRECTION**. The corrections are part of the theorem statement here, not merely editorial notes.

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
The sampled face data agree from both adjacent elements, so the operator is conforming; compact support gives zero boundary traces on sufficiently fine meshes. Fixed-degree affine reproduction and scaling give strong `H^1` approximation for each smooth `w`.

Nonnegative `C_c^∞(Ω)` functions are dense in the positive cone of `H_0^1`: approximate, take positive parts, then mollify with a nonnegative kernel inside the domain. A diagonal sequence proves Mosco recovery. The weak-limit condition follows from closed convexity of `K`. Hence
\[
K_h^B\xrightarrow{M}K.
\]
For a symmetric continuous coercive quadratic energy, recovery, weak lower semicontinuity, uniqueness, and convergence of the energy norm imply strong convergence of minimizers.

---

## 2. Exact coefficient-to-value estimate

For barycentric-lattice interpolation `I_T^r`, let `A_r` be the inverse Bernstein collocation matrix. Then
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
\le C_{r,\mathrm{shape}}h_T^2\operatorname{Lip}(\nabla v).
\]
The general barycentric-lattice unisolvence theorem is proved separately; finite exact inversions through degree six are verification examples rather than the existence proof.

---

## 3. Corrected regular-free-boundary theorem

Assume:

- `Γ = ∂{u>0} ∩ Ω` is compact and `C^1`;
- `u ∈ C^{1,1}` and `u = ∇u = 0` on `Γ`;
- on the positive side near `Γ`,
  \[
  c_0d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
  \]
- a mesh-independent one-sided `H^{r+1}` extension exists near `Γ`;
- outside the risky patch the broken regularity is uniformly bounded:
  \[
  \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg};
  \]
- the multiplier is a nonnegative `L^∞` density supported on contact;
- the local risky set is
  \[
  \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
  \]
- on its fixed one-ring enlargement `ω_h`,
  \[
  c_mh_\Gamma\le h_T\le C_mh_\Gamma,
  \qquad |\omega_h|\le C_\Gamma h_\Gamma;
  \]
- either a contact collar separates the physical boundary, or positive boundary elements satisfy a uniform inward linear lower bound.

The local-distance definition is essential. A strip defined only with a single `h_Γ` does not control larger transition elements under shape regularity alone.

### Localization

For a positive element outside `R_h`, every barycentric node is at distance at least `cκh_T` from `Γ`. Quadratic nondegeneracy gives a positive value of order `h_T^2`, while the coefficient discrepancy is at most `Ch_T^2`; choosing `κ` large gives nonnegative coefficients. Contact-interior elements interpolate zero.

For a positive boundary element, coefficients on the boundary face are exactly zero. Off-face lattice points are a distance comparable to `h_T` inside the domain, so the inward linear lower bound is `O(h_T)` and dominates the `O(h_T^2)` discrepancy.

Thus all negative coefficients occur in `R_h`. On its one-ring patch, quadratic upper growth and fixed-degree collocation stability give
\[
|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2.
\]

### Conforming clipping repair

Clip each shared global coefficient once:
\[
\widetilde b_i=\max\{b_i,0\}.
\]
Shared traces remain identical, homogeneous boundary coefficients remain zero, and the resulting function is pointwise feasible.

The correction has coefficient amplitude `O(h_Γ^2)` on a codimension-one patch of volume `O(h_Γ)`. Reference-element norm equivalence and affine scaling give
\[
\|d_h\|_{L^2}\le Ch_\Gamma^{5/2},
\qquad
\|\nabla d_h\|_{L^2}\le Ch_\Gamma^{3/2}.
\]
The uniform broken regularity bound gives the bulk `O(h^r)` term; `C^{1,1}` interpolation gives the same `h_Γ^{3/2}` strip scale. Hence a feasible recovery satisfies
\[
\|u-v_h^B\|_{H^1}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]
A positive piecewise-linear cutoff lift provides a second repair with the same rate.

---

## 4. Transfer to the minimizer

For feasible `v`,
\[
J(v)-J(u)=\tfrac12a(v-u,v-u)+\langle\lambda,v-u\rangle.
\]
On the contact part of the risky strip, `0 ≤ v_h^B ≤ Ch_Γ^2`; bounded multiplier density and strip measure `O(h_Γ)` give
\[
\langle\lambda,v_h^B-u\rangle\le C\|\lambda\|_\infty h_\Gamma^3.
\]
Discrete minimality and coercivity yield
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
- lower pressure-profile error for curved quadratic geometry;
- close agreement with a second FEM assembly framework developed within the project.

That second implementation is not described as an external clean-room replication.

---

## 6. Deliberate exclusions and trust boundary

The sharp theorem excludes singular or degenerate free-boundary points, free boundaries meeting the physical boundary, anisotropic meshes without a separate audit, inexact arbitrary obstacles, measure-valued multipliers, nonsymmetric operators, and optimal adaptive-complexity claims.

The finite coefficient, simplex, clipping, projection/KKT, assembly, energy, Mosco-infrastructure, and Hilbert-space VI layers are machine checked under pinned Lean/mathlib toolchains. The moving Sobolev finite-element recovery, local free-boundary geometry, coefficient localization, and complete sharp rate remain analytical and require independent expert review.