# Grand Positive-Basis Constraint Theorem — Unified V3

## Executive statement

A conforming finite-element basis that is nonnegative and forms a partition of
unity converts finitely many coefficient inequalities into exact pointwise
constraints over complete elements.  For Bernstein–Bézier elements this
certificate is compatible with shared-face conformity, clipping, moving
obstacles, and arbitrary-dimensional simplices.

The resulting theory has four layers:

1. **qualitative positive-basis convergence** by Mosco recovery;
2. **topology-robust quantitative convergence** controlled by a gradient
   modulus and contact measures;
3. **geometry-sensitive high-order convergence** controlled by vanishing order
   and Minkowski codimension;
4. **exact interval/box constraints** obtained by coefficient boxes after an
   affine normalization.

The classical Bernstein obstacle estimate

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2})
\]

is one regular-interface corollary, not the full theorem.

---

## I. Positive-basis Mosco principle

Let `V` be a Hilbert energy space and let `V_h subset V` be conforming
finite-dimensional spaces.  Suppose each local basis is nonnegative and forms
a partition of unity, and shared trace coefficients are identified globally.
Let `K_h^+` be the cone obtained by requiring every gap coefficient to be
nonnegative.

If every nonnegative smooth gap has a conforming positive recovery converging
strongly in `V`, then

\[
K_h^+\xrightarrow{M}K,
\qquad
K=\{v\in V:v\ge0\}.
\]

For symmetric continuous coercive energies, minimizers converge strongly.
For continuous coercive operators that need not be symmetric, the same
recovery framework combines with the standard strongly-monotone
variational-inequality argument.

For moving obstacles `psi_h -> psi`, translated-cone Mosco convergence follows
from the exact identity

\[
K_{h,\psi_h}=\psi_h+K_h^+.
\]

The repository formalizes the translated Mosco and moving-obstacle endgames;
the concrete Sobolev recovery estimates remain analytical inputs.

---

## II. Universal arbitrary-contact rate

After essential-boundary lifting, let

\[
V=H_0^1(\Omega),
\qquad
K_\psi=\{v\in V:v\ge\psi\},
\]

with a possibly nonpolynomial obstacle `psi in V`.  Define the exact affine
discrete cone

\[
K_{h,\psi}^B
=
\{\psi+z_h:z_h\in V_h^r,
\ b_{T,\alpha}(z_h)\ge0\}.
\]

Write `u=psi+g`, with `g>=0`.  Assume:

- `g in C^1(bar Omega) cap H_0^1(Omega)`;
- `grad g` is uniformly continuous;
- the residual multiplier lies in the variational dual, extends to a finite
  nonnegative Radon measure on the open domain `Omega`, and is supported on
  the interior contact set `C={x in Omega:g(x)=0}`;
- the bilinear form is continuous and coercive, but may be nonsymmetric.

For each simplex set

\[
\omega_T(\rho)
=
\sup_{x,y\in\overline T,\ |x-y|\le\rho}
|\nabla g(x)-\nabla g(y)|,
\]

\[
\eta_h^2=\sum_T|T|\omega_T(h_T)^2,
\]

\[
q_h(x)=\max_{x\in\overline T}h_T\omega_T(h_T),
\qquad
\mu_h=\int_Cq_h\,d\lambda.
\]

Then the positive Bernstein sampling recovery yields

\[
\boxed{
\|u-u_h\|_{H^1}^2
\le C(\eta_h^2+\mu_h),
}
\]

and hence

\[
\boxed{
\|u-u_h\|_{H^1}
\le C(\eta_h+\sqrt{\mu_h}).
}
\]

No smoothness, manifold structure, or nondegeneracy of the boundary of the
contact set is used.  The closure of the active set may reach the physical
boundary; the theorem contains no boundary multiplier.

### Global modulus corollary

If

\[
|\nabla g(x)-\nabla g(y)|\le\omega(|x-y|),
\]

then

\[
\boxed{
\|u-u_h\|_{H^1}
\le C\left[
|\Omega|^{1/2}\omega(h)
+
\sqrt{h\omega(h)\lambda(\Omega)}
\right].
}
\]

Thus

\[
g\in C^{1,\beta}(\bar\Omega),\quad0<\beta\le1
\quad\Longrightarrow\quad
\boxed{\|u-u_h\|_{H^1}=O(h^\beta)}.
\]

In particular, `C^{1,1}` gaps give a universal `O(h)` rate for arbitrary
interior contact topology and finite measure multipliers.

### Minimal refinement principle

Global refinement is sufficient but not necessary.  Convergence follows from

\[
\eta_h\to0,
\qquad
\mu_h\to0.
\]

This is a solution-dependent convergence criterion; a computable estimator
requires separate reconstruction of the modulus and multiplier.

---

## III. Minkowski repair law

Suppose near an active interface `Sigma` the gap satisfies

\[
c\,\operatorname{dist}(x,\Sigma)^q
\le g(x)\le
C\,\operatorname{dist}(x,\Sigma)^q,
\]

coefficient consistency is `O(h^m)`, and the tubular neighborhood obeys

\[
|\{x:\operatorname{dist}(x,\Sigma)\le\delta\}|
\le C\delta^s.
\]

Set

\[
a=\min\{m,q\},
\qquad
\delta_h\simeq h^{a/q}.
\]

The clipping correction has amplitude `O(h^a)` on a patch of thickness
`delta_h`.  Therefore

\[
\|d_h\|_{H^1}
\lesssim
h^{a-1}\delta_h^{s/2},
\]

with repair exponent

\[
\boxed{
\rho_{\rm repair}
=a-1+\frac{sa}{2q}.
}
\]

For a bounded multiplier density, the variational-inequality exponent is

\[
\boxed{
\rho_{\rm VI}
=\frac{sa}{2q}
+
\min\left\{a-1,\frac a2\right\}.
}
\]

When `a>=2`,

\[
\boxed{
\rho_{\rm VI}
=\frac a2\left(1+\frac s q\right).
}
\]

This separates three independent mechanisms:

- coefficient consistency `m`;
- physical vanishing order `q`;
- geometric Minkowski codimension `s`.

For stratified interfaces, compute the exponent on every stratum and take the
minimum.

---

## IV. Quadratic-contact saturation and sharpness

For regular quadratic contact,

\[
m=2,
\qquad q=2,
\qquad s=1,
\]

so

\[
\rho_{\rm repair}=\rho_{\rm VI}=\frac32.
\]

More generally, if `q=2` and `m>=2`, then `a=2`; raising degree or improving
coefficient consistency alone does not improve the unfitted coefficientwise
clipping exponent:

\[
\boxed{\rho_{\rm VI}=\frac32}.
\]

A phase-locked cut-cell model gives a clipping correction whose `H^1` seminorm
is exactly a positive constant times `h^(3/2)`.  Hence the barrier is sharp for
the stated unfitted clipping class.

To beat `3/2`, a method must change geometry fitting, repair support,
contact orthogonality, or the coefficientwise repair mechanism.

This is not an impossibility result for every high-order obstacle method.

---

## V. Exact bilateral and box constraints

Let lower and upper obstacles satisfy `phi-psi=w>=w_0>0`, and normalize

\[
\theta=\frac{u-\psi}{w}.
\]

Then `psi<=u<=phi` is equivalent to `0<=theta<=1`.  Define

\[
K_h^{\rm box}
=
\{\psi+w\theta_h:
\ 0\le b_{T,\alpha}(\theta_h)\le1\}.
\]

The Bernstein convex-hull property certifies

\[
\boxed{\psi\le u_h\le\phi}
\]

pointwise on every complete element, even for nonpolynomial obstacles.

If the residual decomposes into lower and upper nonnegative contact measures,
the universal rate becomes

\[
\boxed{
\|u-u_h\|_{H^1}^2
\le
C_w(\eta_h^2+\mu_h^-+\mu_h^+).
}
\]

For `theta in C^{1,beta}`, this gives `O(h^beta)` without regularity of either
active-set boundary.

The Lean layer proves both one-dimensional and arbitrary-dimensional
simplicial coefficient-box certificates.  The bilateral Sobolev rate remains
analytical.

---

## VI. Combined decision law

The same method may satisfy both the topology-robust and geometry-sensitive
bounds.  In that case

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le
\min\left\{
C_1(\eta_h+\sqrt{\mu_h}),
C_2\left(h^r+h^{\rho_{\rm VI}}\right)
\right\}.
}
\]

For ordinary regular quadratic contact this reduces to

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le
\min\left\{
C_1(\eta_h+\sqrt{\mu_h}),
C_2(h^r+h_\Gamma^{3/2})
\right\}.
}
\]

The first branch survives rough topology and measure multipliers.  The second
uses detailed growth and geometry to recover higher-order bulk accuracy and a
sharp interface exponent.

---

## VII. Formal status

The repository formalizes or packages:

- Bernstein positivity, partition of unity, range, and exact box certificates;
- shared-face conformity and clipping;
- translated Mosco convergence and moving-obstacle endgames;
- scheduled threshold recovery;
- Minkowski repair exponents and quadratic saturation algebra;
- two-scale coercive rate transfer;
- exact one-dimensional and simplicial affine box certificates.

Still analytical:

- the concrete Sobolev gradient-modulus estimate on moving meshes;
- identification of the multiplier with a finite measure in a given PDE;
- the universal contact-measure estimate in the full function-space model;
- verification of growth and Minkowski hypotheses for singular PDE interfaces;
- the bilateral multiplier decomposition and full box-rate theorem.

---

## VIII. Trust and novelty boundary

This unified theorem is an internal derivation, not yet an independently
confirmed theorem or novelty verdict.  Classical variational-inequality error
estimates, nonsymmetric and hp-adaptive obstacle FEM, proximal Galerkin methods,
bounds-constrained Bernstein approximation, and recent GLL-constrained
hp/spectral analysis must be compared carefully.

The candidate contribution is the combined framework:

- exact whole-element positive-basis certificates;
- moving and nonpolynomial obstacles by affine translation;
- gradient-modulus/contact-measure rates without interface regularity;
- Minkowski/vanishing-order classification of clipping rates;
- a sharp quadratic-contact `3/2` saturation law;
- exact bilateral coefficient boxes;
- a substantial Lean-checked finite and abstract bridge.

Independent mathematical and prior-art audits remain mandatory.
