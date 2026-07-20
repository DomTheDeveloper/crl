# Grand theorem candidate: universal Bernstein obstacle rate

## 1. Why this is a genuine enlargement

The regular-interface theorem proves the refined estimate

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr)
\]

under a regular interior free boundary, quadratic nondegeneracy, local interface
quasi-uniformity, bounded multiplier density, and additional one-sided
regularity.

There is a broader theorem underneath it.  The positive Bernstein sampling
operator is itself a feasible recovery.  It gives a first-order estimate with
none of the following assumptions:

- regularity, smoothness, or even manifold structure of the free boundary;
- separation of the free boundary from the physical boundary;
- a strip-volume estimate;
- local interface quasi-uniformity;
- an `L^infinity` multiplier density;
- symmetry of the elliptic operator.

The multiplier may instead be a finite nonnegative Radon measure, and the
operator may be any continuous coercive bilinear form.

The refined `h^r+h_Gamma^(3/2)` result should therefore be presented as the
second tier of a two-tier theorem:

1. a universal adaptive first-order theorem for arbitrary contact topology;
2. a higher-order regular-interface theorem when the geometry permits
   localization and clipping.

---

## 2. Shifted obstacle formulation

After a boundary lifting, let

\[
V=H_0^1(\Omega),
\qquad
K_\psi=\{\psi+z:z\in V,\ z\ge0\text{ a.e.}\}.
\]

The obstacle `psi` need not be a finite-element polynomial.  The discrete
method uses the exact affine shift

\[
K_{h,\psi}^B
=
\{\psi+z_h:z_h\in V_h^r,
\ b_{T,\alpha}(z_h)\ge0\text{ for every }T,\alpha\}.
\]

Thus every discrete field satisfies the physical obstacle exactly:

\[
\psi+z_h\ge\psi
\quad\text{pointwise on every complete element}.
\]

This removes the need to represent the obstacle by a polynomial.  The finite
unknown remains `z_h`; `psi` is a fixed known affine shift.

Let `u=psi+g`, where `g>=0` is the exact gap.  Let `u_h=psi+g_h` be the discrete
solution.

---

## 3. Universal theorem

### Theorem U: arbitrary contact, measure multiplier, nonsymmetric operator

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`.  Let
`{T_h}` be conforming uniformly shape-regular simplicial meshes and let the
polynomial degree `r>=1` be fixed.  Let `V_h^r` be the conforming piecewise
`P_r` space with homogeneous trace for the shifted gap.

Let

\[
a:V\times V\to\mathbb R
\]

be continuous and coercive, not necessarily symmetric:

\[
|a(v,w)|\le M\|v\|_V\|w\|_V,
\qquad
a(v,v)\ge\alpha\|v\|_V^2.
\]

Let `u=psi+g` solve the obstacle variational inequality and assume:

1. `g in C^{1,1}(closure Omega) cap H_0^1(Omega)` and `g>=0`;
2. the multiplier
   \[
   \lambda(\varphi)=a(u,\varphi)-\ell(\varphi)
   \]
   belongs to `V*`, extends to a finite nonnegative Radon measure on `Omega`,
   and is supported on the contact set
   \[
   C=\{x:g(x)=0\};
   \]
3. the local positive Bernstein sampling operator is assembled using the same
   fixed degree on both sides of every face.

Then the coefficient-feasible discrete variational inequality has a unique
solution and

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}^2
\le
C\left[
\sum_{T\in\mathcal T_h}
 h_T^2 |T|\operatorname{Lip}(\nabla g;T)^2
+
\int_C q_h(x)\,d\lambda(x)
\right],
}
\]

where

\[
q_h(x)=
\max_{T\ni x}
 h_T^2\operatorname{Lip}(\nabla g;T).
\]

The constant depends only on coercivity, continuity, dimension, fixed degree,
and mesh shape regularity.

In particular, with

\[
h=\max_T h_T,
\qquad L=\operatorname{Lip}(\nabla g;\Omega),
\]

one obtains

\[
\boxed{
\|u-u_h\|_{H^1(\Omega)}
\le
C h
\left(
L^2|\Omega|+L\lambda(\Omega)
\right)^{1/2}.
}
\]

This estimate requires no regular free boundary and allows measure-valued
multipliers and nonsymmetric coercive operators.

---

## 4. Proof

### Step U1: positive conforming recovery

For each simplex `T`, define

\[
(\mathcal B_{T,r}g)(x)
=
\sum_{|\alpha|=r}
 g(x_{T,\alpha})B_{T,\alpha}(x).
\]

Because `g>=0`, every Bernstein coefficient is nonnegative.  Hence

\[
\mathcal B_{T,r}g\ge0
\]

on the complete simplex.

The lattice values on a shared face are intrinsic to that face, so the two
local traces agree after the face permutation.  Since `g=0` on the physical
boundary, every boundary-face lattice value is zero.  Therefore the assembled
function

\[
g_h^+=\mathcal B_h^r g
\]

belongs to the coefficient cone and has homogeneous trace.  The shifted field

\[
v_h=\psi+g_h^+
\]

belongs to `K_{h,psi}^B` and is an admissible comparison function.

### Step U2: local approximation

Affine reproduction and reference-simplex scaling give

\[
\|g-\mathcal B_{T,r}g\|_{L^2(T)}
\le
C h_T^2|T|^{1/2}\operatorname{Lip}(\nabla g;T),
\]

\[
\|\nabla(g-\mathcal B_{T,r}g)\|_{L^2(T)}
\le
C h_T|T|^{1/2}\operatorname{Lip}(\nabla g;T).
\]

Consequently,

\[
\|u-v_h\|_{H^1(\Omega)}^2
=
\|g-g_h^+\|_{H^1(\Omega)}^2
\le
C\sum_T h_T^2|T|\operatorname{Lip}(\nabla g;T)^2.
\]

### Step U3: quadratic contact estimate without a regular interface

Let `x in C cap T`.  Since `g>=0`, `g(x)=0`, and `g` is differentiable,
`x` is a local minimum and

\[
\nabla g(x)=0.
\]

For every Bernstein lattice point `x_{T,alpha}`, the `C^{1,1}` Taylor estimate
along the segment inside `T` gives

\[
0\le g(x_{T,\alpha})
\le
\frac12\operatorname{Lip}(\nabla g;T)
|x_{T,\alpha}-x|^2
\le
C h_T^2\operatorname{Lip}(\nabla g;T).
\]

The Bernstein basis is a nonnegative partition of unity, so

\[
0\le g_h^+(x)
\le q_h(x)
\quad\text{for }x\in C,
\]

up to a fixed degree/shape constant.  Therefore

\[
0\le
\langle\lambda,v_h-u\rangle
=
\int_C g_h^+\,d\lambda
\le
C\int_C q_h\,d\lambda.
\]

No interface parametrization, nondegeneracy lower bound, strip measure, or
multiplier density is used.

### Step U4: nonsymmetric Falk inequality

Let `e=u-u_h`.  Coercivity gives

\[
\alpha\|e\|_V^2\le a(e,e).
\]

Decompose with the feasible comparison `v_h`:

\[
a(e,e)
=
a(e,u-v_h)+a(e,v_h-u_h).
\]

The discrete variational inequality gives

\[
a(e,v_h-u_h)
\le
\lambda(v_h-u_h).
\]

Since `u_h` is feasible in the continuous problem,

\[
\lambda(u_h-u)\ge0,
\]

and hence

\[
\lambda(v_h-u_h)
=
\lambda(v_h-u)-\lambda(u_h-u)
\le
\lambda(v_h-u).
\]

Thus

\[
\alpha\|e\|_V^2
\le
M\|e\|_V\|u-v_h\|_V
+
\lambda(v_h-u).
\]

Young's inequality yields

\[
\|e\|_V^2
\le
\frac{M^2}{\alpha^2}\|u-v_h\|_V^2
+
\frac{2}{\alpha}\lambda(v_h-u).
\]

Substituting Steps U2 and U3 proves the theorem.

---

## 5. Adaptive convergence corollary

Define

\[
\eta_h^2
=
\sum_T h_T^2|T|\operatorname{Lip}(\nabla g;T)^2,
\]

\[
\mu_h
=
\int_C q_h\,d\lambda.
\]

Then

\[
\|u-u_h\|_{H^1}^2\le C(\eta_h^2+\mu_h).
\]

Therefore global refinement `max h_T -> 0` is sufficient but not necessary.
It is enough that

\[
\eta_h\to0,
\qquad
\mu_h\to0.
\]

This gives a solution-dependent adaptive convergence principle: coarse
simplices may remain where the gap is affine, while refinement is required
where curvature or contact measure is present.

---

## 6. Relation to the regular-interface theorem

The universal theorem gives `O(h)` under global `C^{1,1}` regularity and a
finite measure multiplier, regardless of contact topology.

Under the stronger regular-interface assumptions, interpolation plus localized
coefficient repair recovers

\[
O(h^r+h_\Gamma^{3/2}),
\]

which may be much sharper for `r>=2` away from the interface.  The combined
statement is:

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le
\min\left\{
C_1 h,
C_2(h^r+h_\Gamma^{3/2})
\right\}
}
\]

whenever the assumptions of both tiers hold.

The first branch is robust; the second branch is high order.

---

## 7. Novelty boundary

This document establishes an internal theorem candidate, not an external
novelty verdict.  Classical obstacle FEM already has first-order estimates, and
recent hp/spectral work proves `O(h/p)`-type estimates with constraints imposed
at transformed GLL points.  Higher-order mixed, proximal Galerkin, and
hp-adaptive obstacle methods are also established.

The candidate new combination to audit is:

- exact whole-element feasibility from nonnegative Bernstein coefficients;
- an exact nonpolynomial obstacle shift;
- arbitrary contact topology;
- a finite Radon measure multiplier rather than an `L^infinity` density;
- nonsymmetric coercive operators;
- the local curvature/contact-measure estimate;
- a Lean-checked finite and abstract convergence bridge.

A literature panel must determine which components, individually or jointly,
are genuinely new.

## 8. References requiring comparison

- Falk, error estimates for variational inequalities, 1974.
- Brezzi--Hager--Raviart, primal finite-element error estimates, 1977.
- Nochetto--Otárola--Salgado, convergence rates for obstacle problems, 2015.
- Banz and collaborators, higher-order and hp-adaptive mixed obstacle FEM.
- Keith--Surowiec and Papadopoulos, proximal and hierarchical hp Galerkin
  methods with pointwise inequality constraints.
- Allen--Kirby, bounds-constrained Bernstein approximation.
- Bekhouche--Benchettah, hp/spectral obstacle and free-boundary methods,
  `O(h/p)` estimate with GLL constraints, 2026.
