# Explicit V6 operator corollaries

## Purpose

This note instantiates the abstract grand theorem with concrete PDE operators.
It demonstrates that the V6 result is not merely a relabeling of the symmetric
Laplacian theorem.

Throughout, let

\[
V=H_0^1(\Omega),
\qquad
\|v\|_V=\|\nabla v\|_{L^2(\Omega)},
\]

and let `C_P` be a Poincaré constant:

\[
\|v\|_{L^2}\le C_P\|v\|_V.
\]

Let `D_s=(D+D^T)/2` denote the symmetric part of a matrix field.

---

## 1. Nonsymmetric convection-diffusion obstacle problem

Define

\[
\langle A(u),v\rangle
=
\int_\Omega D\nabla u\cdot\nabla v
+
\int_\Omega (\beta\cdot\nabla u)v
+
\int_\Omega c u v.
\]

Assume

\[
\xi^TD_s(x)\xi\ge d_0|\xi|^2
\qquad\text{a.e.},
\]

for `d_0>0`, and

\[
c-\tfrac12\operatorname{div}\beta\ge0
\qquad\text{a.e.}
\]

with

\[
D,\beta,c,\operatorname{div}\beta\in L^\infty.
\]

The form is generally nonsymmetric when `beta` is nonzero or `D` has a
skew-symmetric part.

### Strong monotonicity

For `e=u-w`, integration by parts and the zero trace give

\[
\int_\Omega(\beta\cdot\nabla e)e
=-\frac12\int_\Omega(\operatorname{div}\beta)e^2.
\]

The skew part of `D` vanishes in the quadratic expression. Therefore

\[
\begin{aligned}
\langle A(u)-A(w),u-w\rangle
&=
\int_\Omega \nabla e^TD_s\nabla e
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

where one may take

\[
L_{\rm cd}
=
\|D\|_\infty
+C_P\|\beta\|_\infty
+C_P^2\|c\|_\infty.
\]

Hence `A:V->V*` is Lipschitz.

### Corollary 1.1

The Bernstein coefficient-constrained solutions converge strongly for this
nonsymmetric operator. Under the corrected regular-interface and bounded
multiplier hypotheses,

\[
\boxed{
\|u-u_n^B\|_{H^1(\Omega)}
\le
C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

No symmetrization of the discrete problem is needed.

---

## 2. Nonlinear nonsymmetric reaction-convection obstacle problem

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

Assume the same diffusion, convection, and reaction hypotheses as in Section
1.

### Strong monotonicity

For `e=u-w`, monotonicity of `g` gives

\[
\int_\Omega(g(u)-g(w))(u-w)\ge0.
\]

Consequently,

\[
\langle A_g(u)-A_g(w),u-w\rangle
\ge d_0\|u-w\|_V^2.
\]

### Lipschitz bound

The nonlinear term satisfies

\[
\left|
\int_\Omega(g(u)-g(w))v
\right|
\le
L_gC_P^2\|u-w\|_V\|v\|_V.
\]

Thus one may take

\[
L=L_{\rm cd}+L_gC_P^2.
\]

### Corollary 2.1

The complete V6 Bernstein convergence and rate theory applies to `A_g`.
In particular, the method retains exact pointwise feasibility and the sharp
regular-interface estimate for a genuinely nonlinear, nonsymmetric operator.

---

## 3. Flagship concrete example

Take

\[
D=I,
\qquad
c\ge\tfrac12\operatorname{div}\beta,
\qquad
g(s)=\gamma\tanh(s),
\quad\gamma\ge0.
\]

Then `g` is monotone and `gamma`-Lipschitz. The operator

\[
A(u)
=
-\Delta u
+\beta\cdot\nabla u
+c u
+\gamma\tanh(u)
\]

is strongly monotone and Lipschitz from `H_0^1` to `H^{-1}` under the stated
boundedness assumptions. It is nonlinear when `gamma>0` and nonsymmetric when
`beta` is nonzero.

For the unilateral problem

\[
u\ge0,
\]

\[
\langle A(u)-f,v-u\rangle\ge0
\qquad(v\ge0),
\]

the Bernstein finite-element solutions satisfy

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

This is a direct new application of the V6 operator theorem and is not covered
by the old symmetric metric-projection proof.

---

## 4. Variable nonlinear reaction examples

The same conclusion applies to any monotone globally Lipschitz reaction, for
example

\[
g(s)=\gamma\tanh(s),
\]

\[
g(s)=\gamma\arctan(s),
\]

or a monotone globally Lipschitz saturation law.

A polynomial reaction such as `g(s)=s^3` is monotone but not globally
Lipschitz on `H_0^1`. It requires either:

- a priori `L^infinity` bounds and a bounded-set Lipschitz version of the grand
  theorem; or
- a different monotone-operator convergence argument.

It is intentionally not included in the current headline theorem.

---

## 5. What remains problem specific

The operator theorem supplies the VI stability endgame. The sharp rate still
requires the physical solution to satisfy:

1. the corrected regular free-boundary geometry;
2. the one-sided and broken regularity assumptions;
3. local interface mesh grading;
4. a bounded multiplier density supported on contact.

For a particular nonlinear PDE, these are regularity assumptions to verify or
cite. The V6 theorem does not manufacture free-boundary regularity from strong
monotonicity alone.

---

## 6. Audit questions

1. Are the coercivity hypotheses for the convection term stated with the
   correct sign?
2. Does the integration-by-parts identity require any boundary assumption
   beyond `e in H_0^1` and the stated regularity of `beta`?
3. Is `A_g:H_0^1->H^{-1}` globally Lipschitz under the listed assumptions?
4. Is the multiplier convention `lambda=A(u)-f` consistent with
   nonnegativity on contact?
5. Which nonlinear obstacle regularity theorem supplies the required
   `C^{1,1}` and quadratic-growth hypotheses for the flagship example?
