# Grand theorem candidate: universal Bernstein obstacle rates

## 1. Two tiers, not one fragile theorem

The regular-interface analysis gives the refined estimate

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr)
\]

when the free boundary is regular and the mesh, multiplier, obstacle, and
one-sided regularity satisfy the stated sharp-rate hypotheses.

A more robust theorem lies underneath it.  The positive Bernstein sampling
operator is already a feasible comparison function.  It gives a quantitative
rate without assuming:

- that the free boundary is a manifold;
- nondegeneracy of the gap;
- separation of the active-set closure from the physical boundary;
- a tubular strip or strip-volume estimate;
- local interface quasi-uniformity;
- an `L^infinity` multiplier density;
- symmetry of the coercive operator;
- polynomial representation of the obstacle.

The resulting theory has two complementary tiers:

1. a universal gradient-modulus/contact-measure rate for arbitrary interior
   contact topology;
2. the higher-order `h^r+h_Gamma^(3/2)` rate when regular-interface geometry
   permits localization and clipping repair.

The word “boundary-touching” below means that the closure of the active set may
reach `partial Omega`.  The multiplier is a Radon measure on the open domain
`Omega`; no boundary measure is included in the theorem.

---

## 2. Exact affine obstacle shift

Perform the standard essential-boundary lifting first.  Set

\[
V=H_0^1(\Omega)
\]

and assume that the lifted obstacle `psi` belongs to `V` and has a pointwise
representative.  Define

\[
K_\psi=\{v\in V:v\ge\psi\text{ a.e.}\}.
\]

For a conforming fixed-degree simplicial space `V_h^r subset V`, define the
affine Bernstein cone

\[
K_{h,\psi}^B
=
\left\{
\psi+z_h:
 z_h\in V_h^r,
\ b_{T,\alpha}(z_h)\ge0
\text{ for every }T,\alpha
\right\}.
\]

This is a finite-dimensional closed convex affine subset of `V`; it need not be
a subset of `V_h^r` when `psi` is nonpolynomial.  Nevertheless, every member
satisfies

\[
\psi+z_h\ge\psi
\]

pointwise on each complete element.  Thus the physical obstacle is represented
exactly rather than interpolated.

Write the exact solution as

\[
u=\psi+g,
\qquad g\ge0,
\qquad g\in H_0^1(\Omega).
\]

---

## 3. Local gradient and contact scales

For every closed simplex `bar T`, define

\[
\omega_T(\rho)
=
\sup\left\{
|\nabla g(x)-\nabla g(y)|:
 x,y\in\overline T,
\ |x-y|\le\rho
\right\}.
\]

Let

\[
\eta_h^2
=
\sum_{T\in\mathcal T_h}|T|\,\omega_T(h_T)^2.
\]

The interior contact set is

\[
C=\{x\in\Omega:g(x)=0\}.
\]

For `x in C`, define

\[
q_h(x)
=
\max_{x\in\overline T}h_T\omega_T(h_T),
\qquad
\mu_h=\int_C q_h\,d\lambda.
\]

Using the maximum over incident elements makes `q_h` unambiguous when the
measure charges an interior mesh face or lower-dimensional skeleton.

---

## 4. Universal arbitrary-contact theorem

### Theorem U

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`.  Let
`{mathcal T_h}` be conforming uniformly shape-regular simplicial meshes and fix
`r>=1`.  Let `V_h^r subset H_0^1(Omega)` be the conforming piecewise-`P_r`
spaces.

Let

\[
a:V\times V\to\mathbb R
\]

be continuous and coercive, but not necessarily symmetric:

\[
|a(v,w)|\le M\|v\|_V\|w\|_V,
\qquad
a(v,v)\ge\alpha\|v\|_V^2.
\]

Assume:

1. `g in C^1(bar Omega) cap H_0^1(Omega)`, `g>=0`, and `grad g` is uniformly
   continuous;
2. the residual
   \[
   \lambda(\varphi)=a(u,\varphi)-\ell(\varphi)
   \]
   lies in `V*`, extends to a finite nonnegative Radon measure on the open
   domain `Omega`, and is supported on `C`;
3. the positive Bernstein sampling recovery uses one fixed degree across every
   shared face.

Then the variational inequality over `K_{h,psi}^B` has a unique solution `u_h`
and

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}^2
\le C\bigl(\eta_h^2+\mu_h\bigr).
}
\]

Consequently,

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}
\le C\left(\eta_h+\sqrt{\mu_h}\right).
}
\]

The constant depends only on `M`, `alpha`, dimension, fixed degree, the
Poincare constant, and mesh shape regularity.  It does not depend on a
parametrization, smoothness, or nondegeneracy of the boundary of `C`.

---

## 5. Proof

### U1. Positive conforming recovery

On each simplex define

\[
(\mathcal B_{T,r}g)(x)
=
\sum_{|\alpha|=r}g(x_{T,\alpha})B_{T,\alpha}(x).
\]

Because `g>=0`, all coefficients are nonnegative, hence
`mathcal B_{T,r}g>=0` throughout `T`.  Shared-face samples are intrinsic to the
face, so the local traces agree under the face permutation.  Since the
continuous representative of `g` vanishes on the physical boundary, every
boundary-face sample is zero.  Therefore the assembled function

\[
g_h^+=\mathcal B_h^r g
\]

belongs to `V_h^r`, has nonnegative Bernstein coefficients, and has homogeneous
trace.  Thus

\[
v_h=\psi+g_h^+\in K_{h,\psi}^B.
\]

### U2. Gradient-modulus approximation

Fix an affine Taylor polynomial `p_T` on `T`.  Affine reproduction gives

\[
g-\mathcal B_{T,r}g
=(g-p_T)-\mathcal B_{T,r}(g-p_T).
\]

The first-order remainder obeys

\[
\|g-p_T\|_{L^\infty(T)}
\le Ch_T\omega_T(h_T),
\qquad
\|\nabla(g-p_T)\|_{L^\infty(T)}
\le C\omega_T(h_T).
\]

Fixed-degree reference-element norm equivalence and affine scaling yield

\[
\|\nabla(g-\mathcal B_{T,r}g)\|_{L^2(T)}
\le C|T|^{1/2}\omega_T(h_T).
\]

Because `g-g_h^+ in H_0^1(Omega)`, Poincare's inequality controls the full
`H^1` norm.  Summing gives

\[
\|u-v_h\|_{H^1}^2
=
\|g-g_h^+\|_{H^1}^2
\le C\eta_h^2.
\]

### U3. Contact-measure consistency without interface geometry

Take `x in C`.  Since `x` is an interior point of `Omega`, `g>=0`, `g(x)=0`,
and `g` is differentiable, `x` is an unconstrained local minimum and

\[
\nabla g(x)=0.
\]

For every lattice point in an incident simplex, integration along the segment
inside that simplex gives

\[
0\le g(x_{T,\alpha})
\le
|x_{T,\alpha}-x|\,\omega_T(h_T)
\le h_T\omega_T(h_T).
\]

The nonnegative Bernstein partition of unity therefore gives

\[
0\le g_h^+(x)\le Cq_h(x).
\]

Since `lambda` is supported on `C`,

\[
0\le
\lambda(v_h-u)
=
\int_C g_h^+\,d\lambda
\le C\mu_h.
\]

No free-boundary parametrization, quadratic lower growth, strip estimate, or
multiplier density is used.

### U4. Nonsymmetric Falk transfer

Let `e=u-u_h`.  Coercivity and the feasible comparison `v_h` give

\[
\alpha\|e\|_V^2
\le a(e,e)
=a(e,u-v_h)+a(e,v_h-u_h).
\]

The discrete variational inequality implies

\[
a(e,v_h-u_h)\le\lambda(v_h-u_h).
\]

The continuous variational inequality with test `u_h` gives

\[
\lambda(u_h-u)\ge0,
\]

hence

\[
\lambda(v_h-u_h)
=
\lambda(v_h-u)-\lambda(u_h-u)
\le\lambda(v_h-u).
\]

Continuity and Young's inequality now give

\[
\|e\|_V^2
\le
\frac{M^2}{\alpha^2}\|u-v_h\|_V^2
+
\frac{2}{\alpha}\lambda(v_h-u).
\]

Insert U2 and U3 to prove Theorem U.

---

## 6. Global modulus and Holder corollaries

Suppose

\[
|\nabla g(x)-\nabla g(y)|
\le\omega(|x-y|)
\]

on `bar Omega`, and let `h=max_T h_T`.  Then

\[
\eta_h\le |\Omega|^{1/2}\omega(h),
\qquad
\mu_h\le h\omega(h)\lambda(\Omega).
\]

Therefore

\[
\boxed{
\|u-u_h\|_{H^1}
\le
C\left[
|\Omega|^{1/2}\omega(h)
+
\sqrt{h\omega(h)\lambda(\Omega)}
\right].
}
\]

If `g in C^{1,beta}(bar Omega)` for `0<beta<=1`, then

\[
\omega(h)\le Lh^\beta
\]

and

\[
\|u-u_h\|_{H^1}
\le C\left(h^\beta+h^{(1+\beta)/2}\right)
=O(h^\beta).
\]

The last equality uses `0<h<=1` and `beta<=1`.  In particular,

\[
g\in C^{1,1}
\quad\Longrightarrow\quad
\boxed{\|u-u_h\|_{H^1}=O(h)}.
\]

---

## 7. Minimal refinement principle

Global refinement is sufficient but not necessary.  The theorem only requires

\[
\eta_h\to0,
\qquad
\mu_h\to0.
\]

An element may remain coarse if the exact gap is locally affine and no contact
measure is present there.  This is a solution-dependent convergence criterion,
not yet a computable a posteriori estimator; computability requires separate
reconstruction or upper bounds for the unknown modulus and multiplier.

---

## 8. Two-tier grand theorem

Under the universal assumptions,

\[
\|u-u_h^B\|_{H^1}
\le C_1(\eta_h+\sqrt{\mu_h}).
\]

Under the regular-interface assumptions,

\[
\|u-u_h^B\|_{H^1}
\le C_2(h^r+h_\Gamma^{3/2}).
\]

When both estimates apply to the same shifted Bernstein method,

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

The first branch is topologically robust; the second captures higher-order
accuracy from regular free-boundary geometry.

---

## 9. Trust and novelty boundary

This is a complete internal proof candidate, not yet an independent theorem or
novelty verdict.  Classical first-order obstacle estimates, nonsymmetric and
hp-adaptive obstacle FEM, proximal Galerkin methods, bounds-constrained
Bernstein approximation, and a 2026 GLL-constrained `O(h/p)` hp/spectral result
must all be compared carefully.

The candidate contribution requiring independent audit is the combination of:

- exact whole-element Bernstein feasibility;
- exact affine shifting by a nonpolynomial obstacle;
- a local gradient-modulus/contact-measure estimate;
- arbitrary interior contact topology whose closure may meet the boundary;
- finite Radon measure multipliers;
- nonsymmetric continuous coercive operators;
- a Lean-checked finite and abstract convergence/rate bridge.

Audit panel E is issue #122.  A counterexample, missing hypothesis, narrower
valid theorem, or prior-art collision counts as a successful audit outcome.
