# Grand theorem candidate: universal Bernstein obstacle rate

## 1. The enlargement

The regular-interface theorem proves

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr)
\]

under a regular interior free boundary, quadratic nondegeneracy, local interface
quasi-uniformity, bounded multiplier density, and additional one-sided
regularity.

There is a broader theorem underneath it. The positive Bernstein sampling
operator is already a feasible recovery. It gives a quantitative rate without:

- any manifold, smoothness, or nondegeneracy assumption on the free boundary;
- separation of the free boundary from the physical boundary;
- a strip-volume estimate;
- local interface quasi-uniformity;
- an `L^infinity` multiplier density;
- symmetry of the elliptic operator;
- polynomial representation of the obstacle.

The multiplier may be a finite nonnegative Radon measure. The contact set may be
singular, disconnected, degenerate, or boundary-touching. The gradient of the
exact gap needs only a modulus of continuity.

The final theory is therefore two-tiered:

1. a universal modulus-of-continuity rate for arbitrary contact topology;
2. the sharper `h^r+h_Gamma^(3/2)` theorem when regular-interface geometry
   permits localization and high-order clipping repair.

---

## 2. Exact shifted obstacle cone

After the usual boundary lifting, let

\[
V=H_0^1(\Omega),
\qquad
K_\psi=\{\psi+z:z\in V,\ z\ge0\text{ a.e.}\}.
\]

The obstacle `psi` need not be a finite-element polynomial. Define

\[
K_{h,\psi}^B
=
\{\psi+z_h:z_h\in V_h^r,
\ b_{T,\alpha}(z_h)\ge0\text{ for all }T,\alpha\}.
\]

Every member of this affine finite-dimensional set satisfies

\[
\psi+z_h\ge\psi
\]

pointwise on every complete element. The finite unknown is the shifted gap
`z_h`; `psi` remains a fixed known function.

Write

\[
u=\psi+g,
\qquad g\ge0,
\]

and assume that `g` has homogeneous trace after boundary lifting.

---

## 3. Local gradient modulus

For each simplex `T`, define the local gradient modulus

\[
\omega_T(\rho)
=
\sup\left\{
|\nabla g(x)-\nabla g(y)|:
 x,y\in T,\ |x-y|\le\rho
\right\}.
\]

Set

\[
\eta_h^2
=
\sum_{T\in\mathcal T_h}|T|\,\omega_T(h_T)^2,
\]

and, on the contact set `C={g=0}`,

\[
q_h(x)
=
\max_{T\ni x}h_T\omega_T(h_T),
\qquad
\mu_h=\int_C q_h(x)\,d\lambda(x).
\]

The maximum over incident elements makes the definition unambiguous when the
multiplier charges a mesh face or lower-dimensional skeleton.

---

## 4. Universal theorem

### Theorem U: arbitrary contact, measure multiplier, nonsymmetric operator

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`. Let
`{T_h}` be conforming uniformly shape-regular simplicial meshes. Fix a degree
`r>=1`, and let `V_h^r` be the conforming piecewise-`P_r` gap space with
homogeneous trace.

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

1. `g in C^1(closure Omega) cap H_0^1(Omega)`, `g>=0`, and `grad g` is
   uniformly continuous;
2. the multiplier
   \[
   \lambda(\varphi)=a(u,\varphi)-\ell(\varphi)
   \]
   belongs to `V*`, extends to a finite nonnegative Radon measure on `Omega`,
   and is supported on `C={g=0}`;
3. the positive Bernstein sampling operator uses the same fixed degree on both
   sides of every face.

Then the coefficient-feasible discrete variational inequality has a unique
solution and

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}^2
\le C\bigl(\eta_h^2+\mu_h\bigr).
}
\]

Equivalently,

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}
\le C\left(\eta_h+\sqrt{\mu_h}\right).
}
\]

The constant depends only on coercivity, continuity, dimension, fixed degree,
Poincare's constant, and mesh shape regularity.

No regularity of the contact-set boundary is used.

---

## 5. Global modulus corollary

Suppose

\[
|\nabla g(x)-\nabla g(y)|\le\omega(|x-y|)
\]

throughout `Omega`, where `omega` is a modulus of continuity. With

\[
h=\max_T h_T,
\]

the local theorem gives

\[
\boxed{
\|u-u_h\|_{H^1}
\le
C\left[
|\Omega|^{1/2}\omega(h)
+
\sqrt{h\,\omega(h)\,\lambda(\Omega)}
\right].
}
\]

### Holder-gradient corollary

If `g in C^{1,beta}` for `0<beta<=1`, then

\[
\omega(h)\le Lh^\beta.
\]

Therefore

\[
\|u-u_h\|_{H^1}
\le
C\left(h^\beta+h^{(1+\beta)/2}\right).
\]

For `0<h<=1` and `beta<=1`, the first term dominates, so

\[
\boxed{
\|u-u_h\|_{H^1}=O(h^\beta).
}
\]

In particular, `C^{1,1}` regularity gives the universal first-order result

\[
\boxed{
\|u-u_h\|_{H^1}=O(h).
}
\]

This first-order estimate permits an arbitrary contact topology and a finite
measure multiplier.

---

## 6. Proof

### U1. Positive conforming recovery

For each simplex `T`, set

\[
(\mathcal B_{T,r}g)(x)
=
\sum_{|\alpha|=r}g(x_{T,\alpha})B_{T,\alpha}(x).
\]

Every coefficient is nonnegative, so the polynomial is nonnegative on the
entire simplex. Shared-face lattice values are intrinsic to the face, hence the
assembled traces agree after orientation permutations. Boundary-face samples
vanish because `g` has zero trace. Thus

\[
g_h^+=\mathcal B_h^r g
\]

is conforming, has homogeneous trace, and belongs to the coefficient cone. The
shifted comparison field

\[
v_h=\psi+g_h^+
\]

belongs to `K_{h,psi}^B`.

### U2. Approximation from the gradient modulus

Fix an affine Taylor function `p_T` on `T`. Since the Bernstein operator
reproduces affine functions,

\[
g-\mathcal B_{T,r}g
=
(g-p_T)-\mathcal B_{T,r}(g-p_T).
\]

The first-order Taylor remainder satisfies

\[
\|g-p_T\|_{L^\infty(T)}
\le Ch_T\omega_T(h_T),
\]

\[
\|\nabla(g-p_T)\|_{L^\infty(T)}
\le C\omega_T(h_T).
\]

Fixed-degree reference-element norm equivalence and affine scaling therefore
give

\[
\|\nabla(g-\mathcal B_{T,r}g)\|_{L^2(T)}
\le C|T|^{1/2}\omega_T(h_T).
\]

Because both `g` and `g_h^+` have homogeneous trace, their difference lies in
`H_0^1(Omega)`. Poincare's inequality absorbs the global `L^2` contribution,
so

\[
\|u-v_h\|_{H^1}^2
=
\|g-g_h^+\|_{H^1}^2
\le C\eta_h^2.
\]

### U3. Contact estimate without interface geometry

Let `x in C cap T`. Since `g>=0`, `g(x)=0`, and `g` is differentiable,

\[
\nabla g(x)=0.
\]

For every Bernstein lattice point `x_{T,alpha}`, integrate the gradient along
the segment inside `T`:

\[
0\le g(x_{T,\alpha})
\le
|x_{T,\alpha}-x|\,\omega_T(h_T)
\le
h_T\omega_T(h_T).
\]

The Bernstein basis is a nonnegative partition of unity, hence

\[
0\le g_h^+(x)\le Cq_h(x)
\quad\text{for }x\in C.
\]

Since the multiplier is supported on contact,

\[
0\le
\lambda(v_h-u)
=
\int_C g_h^+\,d\lambda
\le C\mu_h.
\]

This step uses no free-boundary parametrization, nondegeneracy lower bound,
strip measure, or multiplier density.

### U4. Nonsymmetric Falk transfer

Let `e=u-u_h`. Coercivity gives

\[
\alpha\|e\|_V^2\le a(e,e).
\]

Using the feasible comparison `v_h`,

\[
a(e,e)=a(e,u-v_h)+a(e,v_h-u_h).
\]

The discrete variational inequality implies

\[
a(e,v_h-u_h)\le\lambda(v_h-u_h).
\]

The continuous variational inequality with test `u_h` gives

\[
\lambda(u_h-u)\ge0,
\]

so

\[
\lambda(v_h-u_h)
=
\lambda(v_h-u)-\lambda(u_h-u)
\le
\lambda(v_h-u).
\]

Therefore

\[
\alpha\|e\|_V^2
\le
M\|e\|_V\|u-v_h\|_V+\lambda(v_h-u).
\]

Young's inequality yields

\[
\|e\|_V^2
\le
\frac{M^2}{\alpha^2}\|u-v_h\|_V^2
+
\frac{2}{\alpha}\lambda(v_h-u).
\]

Insert U2 and U3 to obtain

\[
\|u-u_h\|_{H^1}^2\le C(\eta_h^2+\mu_h).
\]

---

## 7. Minimal adaptive refinement principle

Global refinement `max_T h_T -> 0` is sufficient but not necessary. The theorem
only requires

\[
\eta_h\to0,
\qquad
\mu_h\to0.
\]

Thus an element may remain coarse when the gap is locally affine and no contact
measure is present. Refinement is mathematically required only where the gap's
gradient varies or where the multiplier is supported.

This is a solution-dependent convergence criterion, not yet a computable a
posteriori estimator. A separate estimator theorem would require reconstructing
or bounding the unknown curvature and multiplier terms.

---

## 8. Two-tier grand theorem

When only the universal assumptions hold,

\[
\|u-u_h^B\|_{H^1}
\le C(\eta_h+\sqrt{\mu_h}).
\]

When the regular-interface assumptions also hold,

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

When both estimates apply to the same shifted coefficient-cone method,

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

The first branch is topologically robust and permits measure multipliers and
nonsymmetric operators. The second branch captures high-order accuracy from
regular free-boundary geometry.

---

## 9. Novelty boundary

This is an internal theorem candidate, not an external novelty verdict.
Classical obstacle FEM already has first-order estimates. Higher-order mixed,
proximal Galerkin, and hp-adaptive obstacle methods are established. A 2026
hp/spectral paper proves an `O(h/p)` estimate using constraints at transformed
GLL points.

The candidate new combination requiring an adversarial prior-art audit is:

- exact whole-element feasibility from nonnegative Bernstein coefficients;
- exact affine shifting by a nonpolynomial obstacle;
- a gradient-modulus rate for arbitrary contact topology;
- finite Radon measure multipliers;
- nonsymmetric continuous coercive operators;
- the local curvature/contact-measure convergence criterion;
- a Lean-checked finite and abstract convergence bridge.

## 10. Required comparisons

- Falk, variational-inequality approximation estimates, 1974.
- Brezzi--Hager--Raviart, primal FEM estimates, 1977.
- Nochetto--Otarola--Salgado, obstacle convergence rates, 2015.
- Banz and collaborators, higher-order and hp-adaptive obstacle FEM.
- Keith--Surowiec and Papadopoulos, proximal and hierarchical hp Galerkin
  methods with pointwise inequality constraints.
- Allen--Kirby, bounds-constrained Bernstein approximation.
- Bekhouche--Benchettah, hp/spectral obstacle/free-boundary methods with an
  `O(h/p)` estimate and GLL constraints, 2026.
