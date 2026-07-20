# Explicit V6 operator corollaries

## Purpose

This note instantiates the abstract grand theorem with concrete PDE operators.
It demonstrates that V6 is not merely a relabeling of the symmetric Laplacian
theorem.

Let

\[
V=H_0^1(\Omega),
\qquad
\|v\|_V=\|\nabla v\|_{L^2(\Omega)},
\]

and let `C_P` satisfy

\[
\|v\|_{L^2}\le C_P\|v\|_V.
\]

Write `D_s=(D+D^T)/2`.

---

## 1. Nonsymmetric convection-diffusion obstacle operator

Define

\[
\langle A(u),v\rangle
=
\int_\Omega D\nabla u\cdot\nabla v
+
\int_\Omega(\beta\cdot\nabla u)v
+
\int_\Omega c u v.
\]

Assume:

- `D in L^infinity(Omega;R^{dxd})`;
- `beta in W^{1,infinity}(Omega;R^d)`;
- `c in L^infinity(Omega)`;
- for some `d_0>0`,
  \[
  \xi^TD_s(x)\xi\ge d_0|\xi|^2
  \quad\text{a.e.};
  \]
- and
  \[
  c-\tfrac12\operatorname{div}\beta\ge0
  \quad\text{a.e.}
  \]

The operator is generally nonsymmetric when `beta` is nonzero or `D` has a
skew-symmetric part.

### Strong monotonicity

For `e=u-w`, the zero trace and `beta in W^{1,infinity}` give the standard
identity

\[
\int_\Omega(\beta\cdot\nabla e)e
=-\frac12\int_\Omega(\operatorname{div}\beta)e^2.
\]

The skew part of `D` vanishes in the quadratic expression. Therefore

\[
\begin{aligned}
\langle A(u)-A(w),u-w\rangle
&=
\int_\Omega\nabla e^TD_s\nabla e
+
\int_\Omega
\left(c-\tfrac12\operatorname{div}\beta\right)e^2\\
&\ge d_0\|e\|_V^2.
\end{aligned}
\]

Thus `A` is strongly monotone with `alpha=d_0`.

### Lipschitz bound

For `e=u-w`,

\[
\begin{aligned}
|\langle A(u)-A(w),v\rangle|
&\le
\|D\|_\infty\|e\|_V\|v\|_V\\
&\quad+
\|\beta\|_\infty\|e\|_V\|v\|_{L^2}\\
&\quad+
\|c\|_\infty\|e\|_{L^2}\|v\|_{L^2}\\
&\le
L_{\rm cd}\|e\|_V\|v\|_V,
\end{aligned}
\]

where

\[
L_{\rm cd}
=
\|D\|_\infty
+C_P\|\beta\|_\infty
+C_P^2\|c\|_\infty.
\]

### Corollary 1.1

The Bernstein coefficient-constrained solutions converge strongly for this
nonsymmetric operator. Under the corrected regular-interface and bounded
multiplier hypotheses,

\[
\boxed{
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

No symmetrization of the discrete operator is required.

---

## 2. Nonlinear nonsymmetric reaction-convection operator

Let `g:R->R` be monotone and globally Lipschitz:

\[
(g(s)-g(t))(s-t)\ge0,
\]

\[
|g(s)-g(t)|\le L_g|s-t|.
\]

Define

\[
\langle A_g(u),v\rangle
=
\int_\Omega D\nabla u\cdot\nabla v
+
\int_\Omega(\beta\cdot\nabla u)v
+
\int_\Omega c u v
+
\int_\Omega g(u)v.
\]

The monotone reaction contributes

\[
\int_\Omega(g(u)-g(w))(u-w)\ge0,
\]

so

\[
\langle A_g(u)-A_g(w),u-w\rangle
\ge d_0\|u-w\|_V^2.
\]

Moreover,

\[
\left|
\int_\Omega(g(u)-g(w))v
\right|
\le
L_gC_P^2\|u-w\|_V\|v\|_V.
\]

Thus `A_g` is strongly monotone and Lipschitz, with one admissible Lipschitz
constant

\[
L=L_{\rm cd}+L_gC_P^2.
\]

### Corollary 2.1

The complete V6 Bernstein convergence and sharp-rate theory applies to
`A_g`. Exact pointwise feasibility and the interface rate survive for a
genuinely nonlinear and nonsymmetric operator.

---

## 3. Flagship concrete example

Take

\[
D=I,
\qquad
c\ge\tfrac12\operatorname{div}\beta,
\qquad
g(s)=\gamma\tanh(s),
\quad\gamma\ge0,
\]

with `beta in W^{1,infinity}` and bounded `c`. Since `tanh` is monotone and
1-Lipschitz, the operator

\[
A(u)
=
-\Delta u
+\beta\cdot\nabla u
+c u
+\gamma\tanh(u)
\]

is strongly monotone and Lipschitz from `H_0^1` to `H^{-1}`. It is nonlinear
when `gamma>0` and nonsymmetric when `beta` is nonzero.

For

\[
u\ge0,
\]

\[
\langle A(u)-f,v-u\rangle\ge0
\qquad(v\ge0),
\]

the Bernstein solutions satisfy

\[
u_n^B\to u
\quad\text{strongly in }H_0^1.
\]

If the solution has the corrected regular free-boundary structure and

\[
\lambda=A(u)-f\in L^\infty
\]

is nonnegative and supported on contact, then

\[
\boxed{
\|u-u_n^B\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2}).
}
\]

This application is not covered by the old symmetric metric-projection proof.

---

## 4. Further nonlinear reactions and a deliberate exclusion

The same argument applies to any monotone globally Lipschitz reaction, such as

\[
g(s)=\gamma\tanh(s)
\quad\text{or}\quad
g(s)=\gamma\arctan(s).
\]

A reaction such as `g(s)=s^3` is monotone but not globally Lipschitz on
`H_0^1`. It requires either an a priori `L^infinity` bound and a bounded-set
Lipschitz theorem, or a different monotone-operator stability proof. It is not
included in the current headline result.

---

## 5. What remains problem specific

The operator theorem supplies the universal VI endgame. The sharp rate still
requires:

1. the corrected regular free-boundary geometry;
2. the one-sided and broken regularity assumptions;
3. local interface mesh grading;
4. a bounded multiplier density supported on contact.

For a concrete nonlinear PDE, those are regularity hypotheses to verify or
cite. Strong monotonicity alone does not create the required free-boundary
regularity.

---

## 6. Audit questions

1. Is the sign condition
   `c-(1/2) div beta >= 0` sufficient and correctly oriented?
2. Are the `W^{1,infinity}` assumptions on `beta` sufficient for the weak
   integration-by-parts identity?
3. Is `A_g:H_0^1->H^{-1}` globally Lipschitz under the listed assumptions?
4. Is the multiplier convention `lambda=A(u)-f` consistent with
   nonnegativity on contact?
5. Which nonlinear obstacle regularity results provide `C^{1,1}` and quadratic
   growth for the flagship example?
