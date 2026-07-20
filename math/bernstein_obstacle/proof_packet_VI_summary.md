# Bernstein–Bézier Obstacle Proof Packet VI

## Exact scope

This file closes the following theorems under explicit hypotheses:

1. Mosco convergence of pointwise-feasible Bernstein finite-element cones to the homogeneous obstacle cone, without free-boundary regularity assumptions.
2. Strong convergence of the corresponding obstacle minimizers.
3. A regular-free-boundary recovery and minimizer estimate
   \[
   \|u-u_h^B\|_{H^1(\Omega)}\le C\bigl(h^r+h_\Gamma^{3/2}\bigr),
   \]
   under quadratic gap growth, bounded multiplier, local mesh regularity, and boundary compatibility.
4. Nestedness and strict-positivity completeness of subdivision-refined Bernstein cones.
5. A correction to the previous subdivision claim: subdivision does not certify every nonnegative polynomial with zeros.

The full line-by-line proof packet and verification bundle are archived separately; this repository file records the theorem structure and audit conclusions.

---

## 1. General Bernstein cones

Let

\[
V=H_0^1(\Omega),\qquad K=\{v\in V:v\ge0\text{ a.e.}\}.
\]

On a shape-regular conforming simplicial mesh, let \(V_h^r\) be the continuous piecewise-\(\mathbb P_r\) space with zero trace. Define

\[
K_h^B=\{v_h\in V_h^r:b_{T,\alpha}(v_h)\ge0\text{ for every }T,\alpha\}.
\]

Since the Bernstein basis is nonnegative and sums to one, \(K_h^B\subset K\).

For a continuous function \(w\), define the local positive Bernstein operator

\[
\mathcal B_T^rw=\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]

It is positive, globally conforming, and preserves zero boundary traces. It reproduces affine functions, so for smooth \(w\),

\[
\|w-\mathcal B_h^rw\|_{H^1}\to0.
\]

Nonnegative smooth compactly supported functions are dense in \(K\): approximate in \(H_0^1\), take positive parts, and mollify with nonnegative kernels inside the domain. A diagonal sequence of positive Bernstein approximants therefore proves the Mosco recovery condition. The weak-limit condition follows because \(K\) is closed and convex, hence weakly closed.

Thus

\[
K_h^B\xrightarrow{M}K.
\]

For a symmetric continuous coercive quadratic energy

\[
J(v)=\tfrac12a(v,v)-F(v),
\]

Mosco convergence and strict convexity imply strong convergence of minimizers. Equivalently, if \(z\) solves \(a(z,w)=F(w)\), then the minimizers are the energy-metric projections

\[
u=P_K^az,\qquad u_h=P_{K_h^B}^az,
\]

and Mosco convergence implies convergence of projections.

---

## 2. Exact coefficient-to-value estimate

Let \(I_T^r\) be barycentric-lattice Lagrange interpolation. Let \(E_r\) be the Bernstein collocation matrix and \(A_r=E_r^{-1}\). Then

\[
b_\alpha(I_T^rv)=\sum_j(A_r)_{\alpha j}v(x_j).
\]

Affine reproduction gives the exact moment identities

\[
\sum_j(A_r)_{\alpha j}=1,
\qquad
\sum_j(A_r)_{\alpha j}x_j=x_\alpha.
\]

Taylor expansion at \(x_\alpha\) cancels the constant and linear terms and yields

\[
|b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})|
\le C_{r,\mathrm{shape}}h_T^2\operatorname{Lip}(\nabla v).
\]

A second proof follows because the same functional annihilates \(\mathbb P_1\), so reference-element Bramble–Hilbert gives the identical scaling.

Exact rational inversion on the standard triangle gives maximal reference constants

\[
C_1=0,\quad C_2=\tfrac14,\quad C_3=\tfrac59,
\quad C_4=\tfrac98,\quad C_5=\tfrac{2852}{1125},
\quad C_6=\tfrac{1304}{225}.
\]

---

## 3. Regular-free-boundary theorem

Assume:

- \(\Gamma=\partial\{u>0\}\cap\Omega\) is compact and \(C^1\);
- \(u\in C^{1,1}\), with piecewise \(H^{r+1}\) regularity away from \(\Gamma\);
- on the positive side near \(\Gamma\),
  \[
  c_0d(x,\Gamma)^2\le u(x)\le C_0d(x,\Gamma)^2;
  \]
- the multiplier \(\lambda=Au-F\) has a nonnegative \(L^\infty\) density supported on the contact set;
- free-boundary elements are locally quasi-uniform of size \(h_\Gamma\);
- the physical boundary is compatible: either there is a contact collar, or positive boundary elements satisfy a uniform linear lower bound in the inward distance. Without this condition an additional boundary-strip term is required.

The coefficient estimate and quadratic nondegeneracy imply that every negative coefficient of \(I_h^ru\) is confined to an \(O(h_\Gamma)\)-thick free-boundary patch and has magnitude at most \(Ch_\Gamma^2\).

### Preferred repair: coefficient clipping

Identify the global Bernstein face/control coefficients of the continuous finite-element function and set

\[
c_i=\max\{b_i,0\}.
\]

Face coefficients agree across adjacent elements, so clipping preserves conformity. Boundary coefficients remain zero. The clipped function is globally pointwise feasible.

The correction has coefficients \(O(h_\Gamma^2)\) on a patch of measure \(O(h_\Gamma)\). Finite-dimensional scaling gives

\[
\|d_h\|_{L^2}\le Ch_\Gamma^{5/2},
\qquad
\|\nabla d_h\|_{L^2}\le Ch_\Gamma^{3/2}.
\]

Together with standard bulk interpolation and \(C^{1,1}\) strip interpolation,

\[
\|u-v_h^B\|_{H^1}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]

### Independent repair: positive cutoff lift

A nonnegative piecewise-linear cutoff equal to one on risky elements has nonnegative degree-elevated Bernstein coefficients. Adding \(Mh_\Gamma^2\eta_h\) gives the same recovery rate. This independently checks the clipping proof.

---

## 4. Two independent minimizer proofs

For every feasible \(v\), the exact energy identity is

\[
J(v)-J(u)
=\tfrac12a(v-u,v-u)+\langle\lambda,v-u\rangle.
\]

Discrete minimality against the recovery function gives

\[
\tfrac\alpha2\|u_h^B-u\|_{H^1}^2
\le
C\|v_h^B-u\|_{H^1}^2
+\langle\lambda,v_h^B-u\rangle.
\]

On the contact part of the risky strip, \(0\le v_h^B\le Ch_\Gamma^2\); the strip has measure \(O(h_\Gamma)\). Hence

\[
\langle\lambda,v_h^B-u\rangle\le C\|\lambda\|_\infty h_\Gamma^3.
\]

This proves

\[
\|u-u_h^B\|_{H^1}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\]

A separate Falk derivation starts from coercivity, uses the continuous and discrete variational inequalities, and yields

\[
\|u-u_h^B\|_{H^1}^2
\le C\|u-v_h\|_{H^1}^2
+C\langle\lambda,v_h-u\rangle.
\]

Substitution of the same recovery produces the identical result.

---

## 5. Subdivision theorem and required correction

De Casteljau subdivision expresses child coefficients as convex combinations of parent coefficients. Therefore subdivision-refined feasible cones are nested.

If a polynomial is strictly positive on a simplex, sufficiently fine subdivision gives positive Bernstein coefficients because coefficient errors relative to barycentric-grid values are \(O(h_S^2)\).

However, exact certification of every nonnegative polynomial is false. A published simplicial counterexample has an isolated zero and retains a negative Bernstein coefficient in a simplex of every triangulation. The correct conclusion is:

- strict positivity is eventually certified;
- every nonnegative polynomial is locally approximated by certified polynomials \(p+\varepsilon\);
- subdivision alone cannot replace free-boundary clipping/repair where the gap vanishes.

This correction is now incorporated into the theorem scope.

---

## 6. Verification

The exact symbolic verification script checks the affine moment identities over \(\mathbb Q\) and computes the constants above.

A phase-locked one-dimensional contact test uses meshes \(n=3\cdot2^k+1\), keeping each free boundary in the same relative position in its cut element. For degrees \(2,3,4,5\), coefficient clipping produces observed \(H^1\) rate

\[
1.500000\ldots
\]

at every refinement step, matching the proved strip scaling.

---

## Deliberate exclusions

The theorem does not claim coverage of singular/degenerate free-boundary points, boundary-touching free boundaries, inexact arbitrary obstacles, measure-valued multipliers without additional work, nonsymmetric operators, or optimal adaptive complexity without a specified refinement-closure theorem.