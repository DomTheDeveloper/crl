# Bernstein–Bézier Certified Inner-Cone Grand Theorem

Date: 2026-07-20

Status: **reviewed theorem architecture under explicit hypotheses; finite convex-target Lean source added; exact-head audit and external expert review still required**

## 1. Positioning

The classical convex-hull property of Bernstein–Bézier representations, bounds-constrained Bernstein approximation, and general finite-element Mosco convergence for convex constraints are established prior art. The candidate contribution of this project is the following narrower combination:

1. a fixed-degree conforming Bernstein **coefficient inner cone**;
2. a constructive recovery theorem for that practical inner cone;
3. globally assembled coefficient projection localized near an active interface;
4. an explicit defect-order/codimension/duality rate law;
5. the balanced quadratic codimension-one `3/2` contact specialization;
6. a Lean bridge from finite coefficient certificates through abstract Mosco, variational-inequality and rate endgames.

No claim is made that convex-target Mosco convergence or Bernstein range certification is new by itself.

---

## 2. Exact finite convex-target certificate

Let `T` be a simplex, let `r >= 1`, and let `C` be a convex subset of a finite-dimensional real vector space. If

\[
p(x)=\sum_{|\alpha|=r}c_\alpha B_{T,\alpha}(x),
\qquad c_\alpha\in C,
\]

then

\[
\boxed{p(x)\in C\quad\text{for every }x\in T.}
\]

This follows because the Bernstein basis is nonnegative and sums to one.

For a conforming finite-element field, shared face coefficients must be globally identified. A coefficientwise repair must project each assembled coefficient exactly once. Homogeneous boundary coefficients remain zero when `0 in C`.

Lean source:

- `simplexVectorFieldNat_mem_convex`;
- `simplexVectorFieldNat_pointwise_feasible`;
- `convex_convexCoefficientSet`;
- `repaired_simplexVectorFieldNat_pointwise_feasible`;
- `smul_mem_convex_of_zero_mem`.

These endpoints remain audit-pending until the exact integrated workflow passes.

---

## 3. Fixed-degree coefficient-inner-cone Mosco theorem

Let

\[
X=W_0^{1,p}(\Omega;\mathbb R^m),
\qquad 1<p<\infty,
\]

where `Omega` is a bounded polyhedral Lipschitz domain. Let `C subset R^m` be nonempty, closed and convex, with `0 in C`, and define

\[
K_C=\{v\in X:v(x)\in C\text{ a.e.}\}.
\]

Let `{T_h}` be a uniformly shape-regular conforming simplicial mesh family. For a fixed degree `r >= 1`, define

\[
K_{h,C}^{B}
=
\{v_h\in V_h^r:
 b_{T,\alpha}(v_h)\in C
 \text{ for every complete element coefficient}\}.
\]

Assume:

1. shared face Bernstein coefficients are assembled consistently;
2. boundary face coefficients are fixed compatibly with the homogeneous trace;
3. for every `w in C_c^infty(Omega;R^m)`, the positive Bernstein sampling operator is globally conforming and satisfies
   \[
   \|\mathcal B_h^r w-w\|_{W^{1,p}}\to0;
   \]
4. all constants are uniform over the mesh family.

Then

\[
\boxed{K_{h,C}^{B}\xrightarrow{M}K_C
\quad\text{in }W_0^{1,p}(\Omega;\mathbb R^m).}
\]

### Proof map

**Inner inclusion.** The finite convex-target certificate gives
`K_{h,C}^B subset K_C`.

**Weak condition.** `K_C` is convex and norm closed. Strong `W^{1,p}` convergence implies strong `L^p` convergence and an almost-everywhere convergent subsequence, so closedness of `C` passes feasibility to the limit. Norm-closed convex sets are weakly closed.

**Recovery condition.** For `v in K_C`, extend by zero. Choose a standard coupled cutoff/mollification sequence producing

\[
w_j\in C_c^\infty(\Omega;\mathbb R^m),
\qquad w_j(x)\in C,
\qquad w_j\to v\text{ in }W^{1,p}.
\]

Convexity preserves `C` under nonnegative mollifier averages. Since `0 in C`, multiplication by a cutoff in `[0,1]` also preserves `C`. Positive Bernstein sampling gives coefficients `w_j(x_{T,alpha}) in C`. Fixed-`j` convergence followed by a diagonal schedule gives strong recovery.

For nonzero boundary data or `0 notin C`, a compatible `C`-valued lifting and a translated formulation are required.

---

## 4. Minimizer and variational-inequality transfer

In the Hilbert case, let

\[
J(v)=\frac12a(v,v)-F(v)
\]

with `a` symmetric, continuous and coercive. Let `u` and `u_h^B` be the minimizers over `K_C` and `K_{h,C}^B`. Mosco convergence implies

\[
\boxed{u_h^B\to u\quad\text{strongly in }H_0^1.}
\]

For a strongly monotone Lipschitz operator, the existing Inner-Cone Falk theorem gives the corresponding strong estimate from a feasible recovery and an explicitly controlled residual. Merely monotone, noncoercive or operator-specific nonlinear cases require separate arguments.

---

## 5. Globally assembled coefficient projection

Let `P_C` be Euclidean metric projection onto the nonempty closed convex set `C`. For each globally assembled Bernstein coefficient, set

\[
b_i^+=P_C(b_i).
\]

Let `d_h` be the resulting correction. Assume:

1. violating coefficients are supported in a patch `omega_h`;
2. the patch is locally quasi-uniform with representative scale `h_Gamma`;
3. coefficient distances satisfy
   \[
   \operatorname{dist}(b_i,C)\le A h_\Gamma^\beta;
   \]
4. the patch measure satisfies
   \[
   |\omega_h|\le M h_\Gamma^\kappa;
   \]
5. fixed-degree reference-element norm equivalence and affine scaling hold uniformly.

Then, for `1<q<infinity`,

\[
\boxed{
\|d_h\|_{L^q}
\lesssim h_\Gamma^{\beta+\kappa/q},
\qquad
\|\nabla d_h\|_{L^q}
\lesssim h_\Gamma^{\beta-1+\kappa/q}.}
\]

Thus

\[
\rho_{\rm repair}=\beta-1+\frac{\kappa}{q}.
\]

For anisotropic meshes, this statement must be replaced by an anisotropic scaling theorem.

---

## 6. Defect–geometry–duality theorem

Assume a feasible recovery satisfies

\[
\|v_h-u\|_X
\lesssim
h^s+h^r+h_\Gamma^{\beta-1+\kappa/q}.
\]

Assume the multiplier or normal residual has an appropriate local density and pairing satisfying

\[
0\le\langle\lambda,v_h-u\rangle
\lesssim h_\Gamma^{\beta+\kappa+\sigma}.
\]

Assume a genuine `q`-growth Falk/Bregman inequality

\[
c\|u_h-u\|_X^q
\le
C\|v_h-u\|_X^q+
\langle\lambda,v_h-u\rangle.
\]

Then

\[
\boxed{
\|u_h-u\|_X
\lesssim
h^s+h^r+h_\Gamma^\gamma,}
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

This is the **Bernstein–Bézier defect–geometry–duality law**.

If physical contact order is `m` and coefficient consistency order is `ell`, set

\[
\beta=\min\{m,\ell\}.
\]

The repair and dual mechanisms balance at

\[
\boxed{
\beta_*(q,\sigma)=\frac{q+\sigma}{q-1}.}
\]

The multiplier statement is not automatic for measure-valued, boundary or derivative-acting multipliers; each such application needs a separate pairing lemma.

---

## 7. Quadratic codimension-one specialization

For

\[
q=2,
\qquad
\beta=2,
\qquad
\kappa=1,
\qquad
\sigma=0,
\]

both mechanisms give `3/2`, and therefore

\[
\boxed{
\|u-u_h^B\|_{H^1}
\lesssim
h^s+h^r+h_\Gamma^{3/2}.}
\]

The exact phase-locked model in the Lean stack has correction energy proportional to `h_Gamma^3`, hence correction norm proportional to `h_Gamma^(3/2)`. This proves matching sharpness for that coefficient-clipping family only. It is not a universal lower bound for every feasible discretization or every discrete minimizer.

---

## 8. Evidence and trust boundary

### Formally developed or abstractly reduced

- finite scalar and simplicial Bernstein certificates;
- finite vector convex-target certificate source;
- shared-face and boundary-coefficient infrastructure;
- abstract Mosco and moving-obstacle recovery;
- Hilbert and strongly monotone VI endgames;
- integer codimension and consistency-saturation algebra;
- quadratic-contact rate transfer;
- exact phase-locked lower model.

### Still analytical

- complete physical `W_0^{1,p}` implementation;
- Bochner convolution and convex-target smooth density in Lean;
- physical positive-sampling estimate on moving meshes;
- metric projection existence/nonexpansiveness instantiated in the coefficient space;
- free-boundary patch geometry and multiplier pairing;
- real-power Bregman transfer;
- noninteger Minkowski codimension;
- curved changing-normal and frictional contact.

### Still external

- independent numerical-analysis review;
- independent free-boundary review;
- independent formal statement-faithfulness review;
- independent novelty search;
- third-party clean-room reproduction.

The internal adversarial review is recorded in
`audit_packets/AI_RED_TEAM_PANEL_2026-07-20.md`; it is not a substitute for those external reports.

---

## 9. Prior-art boundary

The manuscript must cite and distinguish at least:

1. Allen–Kirby, bounds-constrained Bernstein polynomial approximation;
2. Kirby–Shapero, high-order bounds-satisfying finite-element variational inequalities and the stated gap for the practical Bernstein coefficient subset;
3. Hintermüller–Rautenberg–Rösel, density and Mosco convergence for finite-element convex constraints;
4. Menaldi–Rautenberg, moving-set and Mosco-convergence context;
5. Diening–Kreuzer–Schwarzacher, vector-valued finite-element convex-hull principles in the low-order setting.

The safe candidate novelty sentence is:

> We analyze the practical fixed-degree Bernstein coefficient inner constraint itself, establish a constructive recovery mechanism under explicit conforming positive-sampling hypotheses, and derive a localized coefficient-projection rate law coupling defect order, active-set codimension, multiplier behavior and energy growth.
