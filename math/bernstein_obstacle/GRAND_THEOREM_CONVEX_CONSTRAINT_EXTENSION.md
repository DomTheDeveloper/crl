# Bernstein–Bézier Convex-Constraint Grand Theorem

Date: 2026-07-20

Status: **complete human-level theorem under the hypotheses stated below; physical instantiation and Lean realization remain separate obligations**.

This note extracts the largest defensible principle behind the scalar obstacle result. The essential fact is not merely that nonnegative Bernstein coefficients certify a nonnegative polynomial. It is that Bernstein basis values are convex weights. Consequently, membership of every coefficient in a closed convex target set certifies pointwise membership of the complete polynomial field in that target set.

---

## 1. Exact convex-hull certificate

Let `T` be a simplex, `r >= 1`, and let `C` be a nonempty convex subset of a finite-dimensional real vector space `Y`. If

\[
p(x)=\sum_{|\alpha|=r} c_\alpha B_{T,\alpha}(x),
\qquad c_\alpha\in C,
\]

then

\[
p(x)\in C\qquad\text{for every }x\in T.
\]

Indeed, `B_{T,alpha}(x) >= 0` and their sum is one, so `p(x)` is a convex combination of the coefficient vectors.

This single certificate includes:

- scalar nonnegativity and bilateral boxes;
- componentwise vector inequalities;
- simplex-valued or probability-valued fields;
- second-order cone constraints;
- positive-semidefinite matrix fields;
- any fixed closed convex constitutive or admissibility set.

For conformity, shared face coefficients must be globally assembled and projected only once. If homogeneous boundary coefficients are fixed at zero and `0 in C`, coefficient projection preserves the boundary condition.

---

## 2. Convex-constraint Mosco theorem

Let `Omega` be a bounded polyhedral Lipschitz domain, `1 < p < infinity`, and

\[
X=W_0^{1,p}(\Omega;\mathbb R^m).
\]

Let `C subset R^m` be nonempty, closed and convex, with `0 in C`, and define

\[
K_C=\{v\in X:v(x)\in C\text{ for a.e. }x\in\Omega\}.
\]

Let `{T_h}` be a shape-regular conforming simplicial mesh family and let `V_h^r` be a fixed-degree conforming vector finite-element space represented in the Bernstein basis. Define

\[
K_{h,C}^B=
\{v_h\in V_h^r:
 b_{T,\alpha}(v_h)\in C
 \text{ for every element and coefficient}\}.
\]

Assume the standard fixed-degree positive Bernstein sampling estimate for every smooth compactly supported field `w`:

\[
\|\mathcal B_h^r w-w\|_{W^{1,p}(\Omega)}\to0.
\]

Then

\[
\boxed{K_{h,C}^B\xrightarrow{M}K_C
\quad\text{in }W_0^{1,p}(\Omega;\mathbb R^m).}
\]

### Proof

**Inner inclusion.** The exact convex-hull certificate gives `K_{h,C}^B subset K_C`.

**Weak-limit condition.** `K_C` is convex. It is strongly closed: strong `W^{1,p}` convergence implies strong `L^p` convergence, hence an almost-everywhere convergent subsequence; closedness of `C` passes the constraint to the limit. A strongly closed convex subset of a Banach space is weakly closed. Thus every weak limit of coefficient-feasible fields lies in `K_C`.

**C-valued smooth density.** Extend `v in K_C` by zero. Because `v in W_0^{1,p}` and `0 in C`, this is a `C`-valued `W^{1,p}` field on `R^d`. Convolution with a nonnegative mollifier preserves `C`, since every mollified value is a barycentric average of points in `C`. Multiplication by a cutoff `chi in [0,1]` preserves `C`, since `chi y=(1-chi)0+chi y`. The standard cutoff-mollification construction therefore produces `w_j in C_c^infty(Omega;R^m)` with `w_j(x) in C` and `w_j -> v` in `W^{1,p}`.

**Positive recovery.** For fixed `j`, the Bernstein sampling coefficients of `B_h^r w_j` are the values `w_j(x_{T,alpha})`, hence belong to `C`. Shared physical face samples give conformity, and compact support gives the homogeneous trace. Therefore `B_h^r w_j in K_{h,C}^B` and `B_h^r w_j -> w_j`. A diagonal choice proves Mosco recovery.

For an affine boundary value or a target set not containing zero, the same theorem applies after translation by a fixed compatible `C`-valued lifting.

---

## 3. Hilbert minimizer consequence

In the quadratic case `p=2`, let `a` be symmetric, continuous and coercive on `X`, and let

\[
J(v)=\tfrac12 a(v,v)-F(v).
\]

Let `u` and `u_h^B` be the unique minimizers over `K_C` and `K_{h,C}^B`. Mosco convergence and coercivity imply

\[
\boxed{u_h^B\to u\quad\text{strongly in }H_0^1.}
\]

The proof is the usual limsup/liminf argument, or equivalently convergence of metric projections in the energy inner product.

For nonsymmetric or nonlinear problems, the existing Inner-Cone Falk theorem transfers recovery estimates under explicit strong-monotonicity, Lipschitz, and residual hypotheses. No claim is made here for merely monotone operators without those hypotheses.

---

## 4. Coefficientwise metric projection repair

Let `P_C` denote Euclidean metric projection onto `C`. Project each globally assembled Bernstein coefficient once:

\[
b_i\mapsto P_C(b_i).
\]

Metric projection onto a nonempty closed convex set is nonexpansive and satisfies

\[
\|b_i-P_C(b_i)\|=\operatorname{dist}(b_i,C).
\]

Assume all violating coefficients lie in a patch `omega_h` and satisfy

\[
\operatorname{dist}(b_i,C)\le A h_\Gamma^\beta,
\qquad
|\omega_h|\le M h_\Gamma^\kappa.
\]

Assume local quasi-uniformity and fixed-degree reference-element norm equivalence. For a `W^{1,q}` error metric, `1<q<infinity`, the projected correction `d_h` satisfies

\[
\boxed{
\|d_h\|_{L^q}\lesssim h_\Gamma^{\beta+\kappa/q},
\qquad
\|\nabla d_h\|_{L^q}\lesssim
h_\Gamma^{\beta-1+\kappa/q}.}
\]

Thus the geometric repair exponent is

\[
\rho_{\rm repair}=\beta-1+\frac{\kappa}{q}.
\]

Here `beta` is the effective coefficient-defect order and `kappa` is the patch-volume or Minkowski-codimension exponent. If the physical gap vanishes to order `m` but coefficient consistency is only order `ell`, then

\[
\beta=\min\{m,\ell\},
\]

which is the consistency-saturation principle.

---

## 5. Universal defect-geometry-duality rate

Assume a variational inequality or energy has `q`-growth in the error norm, and that a feasible recovery `v_h` satisfies

\[
\|v_h-u\|_X
\lesssim h^s+h^r+h_\Gamma^{\beta-1+\kappa/q}.
\]

Assume the multiplier or normal residual has density vanishing to order `sigma` on the affected patch, so that

\[
0\le\langle\lambda,v_h-u\rangle
\lesssim h_\Gamma^{\beta+\kappa+\sigma}.
\]

Assume the standard Falk/Bregman transfer inequality

\[
c\|u_h-u\|_X^q
\le C\|v_h-u\|_X^q+
\langle\lambda,v_h-u\rangle.
\]

Then

\[
\boxed{
\|u_h-u\|_X
\lesssim
h^s+h^r+h_\Gamma^\gamma,
}
\]

where

\[
\boxed{
\gamma=
\min\left\{
\beta-1+\frac{\kappa}{q},
\frac{\beta+\kappa+\sigma}{q}
\right\}.}
\]

This is the **Bernstein–Bézier defect-geometry-duality law**.

The repair and multiplier mechanisms balance exactly when

\[
\beta-1+\frac{\kappa}{q}
=
\frac{\beta+\kappa+\sigma}{q},
\]

or equivalently

\[
\boxed{
\beta_*(q,\sigma)=\frac{q+\sigma}{q-1}.}
\]

The patch exponent cancels. For a nonvanishing multiplier density (`sigma=0`), this becomes the conjugate exponent `q/(q-1)`.

---

## 6. Classical quadratic contact specialization

For a quadratic energy and a regular codimension-one quadratic contact interface,

\[
q=2,
\qquad
\beta=2,
\qquad
\kappa=1,
\qquad
\sigma=0.
\]

Therefore

\[
\rho_{\rm repair}=2-1+\frac12=\frac32,
\qquad
\rho_{\rm multiplier}=\frac{2+1}{2}=\frac32,
\]

and

\[
\boxed{
\|u-u_h^B\|_{H^1}
\lesssim h^s+h^r+h_\Gamma^{3/2}.}
\]

For an exactly represented obstacle, `h^s` vanishes. The phase-locked quadratic clipping model in the canonical Lean package proves an exact correction energy proportional to `h_Gamma^3`, and hence a correction norm proportional to `h_Gamma^(3/2)`. This is matching sharpness for that clipping family, not a universal lower bound for every possible discretization or for every discrete minimizer.

---

## 7. What is newly unified

The grand theorem identifies one mechanism behind several previously separate statements:

1. **convex weights** give exact whole-element feasibility;
2. **positive sampling** gives Mosco recovery;
3. **global metric projection** repairs arbitrary closed convex coefficient constraints;
4. **defect order plus patch codimension** determines the recovery cost;
5. **multiplier vanishing** determines the dual consistency cost;
6. **energy growth** converts both costs into a solution rate;
7. the classical `3/2` law is the balanced quadratic codimension-one case.

---

## 8. Trust boundary

This note completes the human proof architecture under its explicit hypotheses. It does **not** by itself establish:

- a full Lean formalization of `C`-valued Sobolev density and positive sampling;
- the physical mesh and trace realization in arbitrary `W^{1,p}` spaces;
- the general real-power Bregman transfer theorem in Lean;
- noninteger Minkowski-codimension patch geometry;
- operator-specific nonlinear contact regularity;
- curved changing-normal or frictional contact;
- independent novelty confirmation or independent expert proof validation.

The fixed scalar obstacle theorem, abstract Mosco and Hilbert endgames, integer codimension algebra, consistency saturation, quadratic rate transfer, and exact phase-locked lower model remain the canonical formally developed core. This convex-constraint theorem is the next analytical layer to formalize and externally audit.
