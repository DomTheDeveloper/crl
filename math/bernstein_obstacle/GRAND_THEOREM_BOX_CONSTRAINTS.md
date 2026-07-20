# Grand theorem extension: exact Bernstein box constraints

## 1. Exact double-obstacle certification

Let `psi` and `phi` be lower and upper obstacles after essential-boundary
lifting.  Set

\[
w=\phi-\psi
\]

and assume

\[
w\in W^{1,\infty}(\Omega),
\qquad
w\ge w_0>0.
\]

Normalize the exact solution by

\[
\theta=\frac{u-\psi}{w}.
\]

Then

\[
\psi\le u\le\phi
\quad\Longleftrightarrow\quad
0\le\theta\le1.
\]

For a conforming fixed-degree Bernstein field `theta_h`, impose

\[
0\le b_{T,\alpha}(\theta_h)\le1
\quad\text{for every }T,\alpha.
\]

The Bernstein convex-hull property yields

\[
0\le\theta_h(x)\le1
\]

throughout every complete element.  Therefore

\[
u_h=\psi+w\theta_h
\]

satisfies the exact physical box constraint

\[
\boxed{\psi\le u_h\le\phi}
\]

pointwise, even when neither obstacle is a finite-element polynomial.

The set

\[
K_h^{\rm box}
=
\{\psi+w\theta_h:
 \theta_h\in V_h^r,
\ 0\le b_{T,\alpha}(\theta_h)\le1\}
\]

is the image of a finite-dimensional closed convex coefficient box under an
affine continuous map.  Hence it is a finite-dimensional closed convex trial
set in `H^1`.

For the clean homogeneous theorem, assume the lifted boundary data equal the
lower obstacle, so `theta,theta_h in H_0^1(Omega)`.  General boundary values
require a normalized conforming boundary lift whose trace is represented
exactly.

---

## 2. Interior contact measures

Define the interior lower and upper active sets

\[
C_- =\{x\in\Omega:u(x)=\psi(x)\}=\{\theta=0\},
\]

\[
C_+ =\{x\in\Omega:u(x)=\phi(x)\}=\{\theta=1\}.
\]

Their closures may meet the physical boundary.  The theorem does not include
boundary multipliers.

Assume the residual decomposes as

\[
\Lambda=a(u,\cdot)-\ell
=\lambda_- - \lambda_+,
\]

where `lambda_-` and `lambda_+` lie in the variational dual, extend to finite
nonnegative Radon measures on the open domain `Omega`, and are supported on
`C_-` and `C_+`, respectively.

For every feasible `v`,

\[
\Lambda(v-u)\ge0,
\]

because `v-u>=0` on `C_-` and `v-u<=0` on `C_+`.

---

## 3. Positive coefficient-box recovery

Use the sampling operator

\[
\theta_h^+=\mathcal B_h^r\theta.
\]

Each coefficient is a value of `theta` and therefore lies in `[0,1]`.  Thus
`theta_h^+` satisfies the full coefficient box and

\[
v_h=\psi+w\theta_h^+\in K_h^{\rm box}.
\]

Linearity and constant reproduction give

\[
1-\theta_h^+
=
\mathcal B_h^r(1-\theta),
\]

which provides symmetric control at lower and upper contact.

---

## 4. Universal bilateral theorem

Let `a` be continuous and coercive, not necessarily symmetric.  Assume:

1. `theta in C^1(bar Omega) cap H_0^1(Omega)` and `0<=theta<=1`;
2. `grad theta` is uniformly continuous;
3. `w in W^{1,infinity}(Omega)` and `w>=w_0>0`;
4. `lambda_-` and `lambda_+` satisfy the dual/measure/support conditions above;
5. the meshes are conforming and uniformly shape regular, with fixed degree
   `r>=1`.

For each closed simplex define

\[
\omega_T(\rho)
=
\sup\left\{
|\nabla\theta(x)-\nabla\theta(y)|:
 x,y\in\overline T,
\ |x-y|\le\rho
\right\}.
\]

Set

\[
\eta_h^2=\sum_T |T|\omega_T(h_T)^2,
\]

\[
q_h(x)=\max_{x\in\overline T}h_T\omega_T(h_T),
\]

\[
\mu_h^- =\int_{C_-}q_h\,d\lambda_-,
\qquad
\mu_h^+ =\int_{C_+}q_h\,d\lambda_+.
\]

Then the coefficient-box discrete variational inequality has a unique solution
and

\[
\boxed{
\|u-u_h\|_{H^1}^2
\le
C_w\left(
\eta_h^2+\mu_h^-+\mu_h^+
\right),
}
\]

hence

\[
\boxed{
\|u-u_h\|_{H^1}
\le
C_w\left(
\eta_h+\sqrt{\mu_h^-+\mu_h^+}
\right).
}
\]

The constant depends on the operator constants, shape regularity, fixed degree,
Poincare's constant, `w_0`, and `||w||_{W^{1,infinity}}`.  It does not require
regularity of either active-set boundary.

---

## 5. Proof

### B1. Approximation

Multiplication by `w` is bounded on `H^1`, so

\[
\|u-v_h\|_{H^1}
=
\|w(\theta-\theta_h^+)\|_{H^1}
\le C_w\|\theta-\theta_h^+\|_{H^1}.
\]

The universal gradient-modulus estimate gives

\[
\|u-v_h\|_{H^1}^2\le C_w\eta_h^2.
\]

### B2. Lower contact

For `x in C_- subset Omega`, `theta>=0`, `theta(x)=0`, and differentiability
imply

\[
\nabla\theta(x)=0.
\]

The segment argument and Bernstein partition of unity give

\[
0\le\theta_h^+(x)\le Cq_h(x).
\]

Since `v_h-u=w\theta_h^+` on `C_-`,

\[
\int_{C_-}(v_h-u)\,d\lambda_-
\le C\|w\|_{L^\infty}\mu_h^-.
\]

### B3. Upper contact

For `x in C_+ subset Omega`, the nonnegative function `1-theta` vanishes and
has zero gradient.  Since

\[
1-\theta_h^+=\mathcal B_h^r(1-\theta),
\]

we obtain

\[
0\le1-\theta_h^+(x)\le Cq_h(x).
\]

On `C_+`, `v_h-u=w(\theta_h^+-1)`, so

\[
-\int_{C_+}(v_h-u)\,d\lambda_+
\le C\|w\|_{L^\infty}\mu_h^+.
\]

Consequently,

\[
0\le\Lambda(v_h-u)
\le
C\|w\|_{L^\infty}(\mu_h^-+\mu_h^+).
\]

### B4. Nonsymmetric transfer

The same coercive Falk argument as in the unilateral theorem gives

\[
\|u-u_h\|_{H^1}^2
\le
C\left[
\|u-v_h\|_{H^1}^2+\Lambda(v_h-u)
\right].
\]

Insert B1--B3.

---

## 6. Holder-gradient corollary

If

\[
\theta\in C^{1,\beta}(\overline\Omega),
\qquad 0<\beta\le1,
\]

then the same exponent comparison as in the unilateral theorem gives

\[
\boxed{
\|u-u_h\|_{H^1}=O(h^\beta).
}
\]

For `beta=1`, this is a universal first-order estimate for exact two-sided
obstacle enforcement.

---

## 7. Formal certificate status

The Lean library proves:

- one-dimensional coefficient interval certification;
- arbitrary-dimensional complete simplicial coefficient interval
  certification;
- affine mapping of `[0,1]` into `[psi(x),phi(x)]`;
- exact one-dimensional and simplicial box certificates for possibly
  nonpolynomial obstacle functions.

The moving Sobolev approximation, multiplier decomposition, and bilateral rate
remain analytical review targets.

---

## 8. Applications and trust boundary

Potential applications include double-obstacle variational inequalities,
box-constrained membranes, bounded phase fractions, normalized bounded-state
models, and unilateral problems as a one-sided limit.

This is a complete internal theorem candidate, not yet an independently
validated or novel theorem.  Audit panel E, issue #122, explicitly tests both
the unilateral and bilateral statements, including prior-art collision.
