# Grand theorem extension: exact Bernstein box constraints

## 1. Double obstacles become coefficient boxes

Let `psi < phi` be lower and upper obstacles and set

\[
w=\phi-\psi.
\]

Assume

\[
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

For a conforming Bernstein finite-element function `theta_h`, impose

\[
0\le b_{T,\alpha}(\theta_h)\le1
\quad\text{for every }T,\alpha.
\]

The Bernstein convex-hull property gives

\[
0\le\theta_h(x)\le1
\]

at every point of every element. Therefore

\[
u_h=\psi+w\theta_h
\]

satisfies

\[
\boxed{\psi\le u_h\le\phi}
\]

pointwise over the complete mesh, even when `psi` and `phi` are not
finite-element polynomials.

The trial set

\[
K_h^{\rm box}
=
\{\psi+w\theta_h:\theta_h\in V_h^r,
\ 0\le b_{T,\alpha}(\theta_h)\le1\}
\]

is a finite-dimensional affine convex set.

For the clean homogeneous statement below, assume that the boundary data agree
with the lower obstacle, so `theta` and `theta_h` have homogeneous trace. More
general boundary data require an exactly represented normalized boundary lift.

---

## 2. Multiplier decomposition

Let

\[
C_-=\{u=\psi\}=\{\theta=0\},
\qquad
C_+=\{u=\phi\}=\{\theta=1\}.
\]

Assume the variational residual decomposes as

\[
\Lambda=a(u,\cdot)-\ell
=\lambda_- - \lambda_+,
\]

where `lambda_-` and `lambda_+` are finite nonnegative Radon measures supported
on `C_-` and `C_+`, respectively.

For any feasible `v`,

\[
\Lambda(v-u)\ge0,
\]

because `v-u>=0` on the lower contact set and `v-u<=0` on the upper contact
set.

---

## 3. Positive box recovery

Use the positive Bernstein sampling operator

\[
\theta_h^+=\mathcal B_h^r\theta.
\]

Every coefficient is a sample of a number in `[0,1]`. Hence

\[
0\le b_{T,\alpha}(\theta_h^+)\le1,
\]

and

\[
v_h=\psi+w\theta_h^+
\]

belongs to `K_h^{box}`.

The identity

\[
\mathcal B_h^r(1-\theta)=1-\mathcal B_h^r\theta
\]

follows from linearity and reproduction of constants. It gives symmetric
control at the two contact sets.

---

## 4. Universal box theorem

Let `a` be continuous and coercive, not necessarily symmetric. Assume:

1. `theta in C^1(closure Omega) cap H_0^1(Omega)` and `0<=theta<=1`;
2. `grad theta` is uniformly continuous;
3. `w in W^{1,infinity}(Omega)` and `w>=w_0>0`;
4. `lambda_-` and `lambda_+` belong to the variational dual, extend to finite
   nonnegative Radon measures, and have the stated contact supports;
5. the meshes are conforming and uniformly shape regular, with fixed degree
   `r>=1`.

Define

\[
\omega_T(\rho)
=
\sup\{|\nabla\theta(x)-\nabla\theta(y)|:
 x,y\in T,\ |x-y|\le\rho\},
\]

\[
\eta_h^2=\sum_T |T|\omega_T(h_T)^2,
\]

\[
q_h(x)=\max_{T\ni x}h_T\omega_T(h_T),
\]

and

\[
\mu_h^- =\int_{C_-}q_h\,d\lambda_-,
\qquad
\mu_h^+ =\int_{C_+}q_h\,d\lambda_+.
\]

Then the coefficient-box discrete solution satisfies

\[
\boxed{
\|u-u_h\|_{H^1}^2
\le
C_w\left(
\eta_h^2+\mu_h^-+\mu_h^+
\right),
}
\]

where `C_w` depends additionally on `w_0`, `||w||_{W^{1,infinity}}`, and the
operator constants.

Consequently,

\[
\boxed{
\|u-u_h\|_{H^1}
\le
C_w\left(
\eta_h+\sqrt{\mu_h^-+\mu_h^+}
\right).
}
\]

No regularity of either active-set boundary is required.

---

## 5. Proof

### B1. Approximation

Multiplication by `w` is bounded in `H^1`, so

\[
\|u-v_h\|_{H^1}
=
\|w(\theta-\theta_h^+)\|_{H^1}
\le
C_w\|\theta-\theta_h^+\|_{H^1}.
\]

The gradient-modulus Bernstein estimate from the universal unilateral theorem
gives

\[
\|u-v_h\|_{H^1}^2\le C_w\eta_h^2.
\]

### B2. Lower contact

At `x in C_-`, `theta(x)=0` and `grad theta(x)=0`. Therefore

\[
0\le\theta_h^+(x)\le Cq_h(x).
\]

Since `v_h-u=w\theta_h^+` on `C_-`,

\[
\int_{C_-}(v_h-u)\,d\lambda_-
\le
C\|w\|_{L^\infty}\mu_h^-.
\]

### B3. Upper contact

At `x in C_+`, the nonnegative function `1-theta` vanishes and has zero
gradient. Since

\[
1-\theta_h^+=\mathcal B_h^r(1-\theta),
\]

we have

\[
0\le1-\theta_h^+(x)\le Cq_h(x).
\]

On `C_+`,

\[
v_h-u=w(\theta_h^+-1),
\]

so the upper multiplier contribution is

\[
-\int_{C_+}(v_h-u)\,d\lambda_+
=
\int_{C_+}w(1-\theta_h^+)\,d\lambda_+
\le
C\|w\|_{L^\infty}\mu_h^+.
\]

Thus

\[
0\le\Lambda(v_h-u)
\le
C\|w\|_{L^\infty}(\mu_h^-+\mu_h^+).
\]

### B4. Nonsymmetric Falk transfer

The same coercive nonsymmetric argument as in the unilateral theorem yields

\[
\|u-u_h\|_{H^1}^2
\le
C\left[
\|u-v_h\|_{H^1}^2+\Lambda(v_h-u)
\right].
\]

Insert B1--B3.

---

## 6. Holder corollary

If

\[
\theta\in C^{1,\beta}(\overline\Omega),
\qquad 0<\beta\le1,
\]

then

\[
\boxed{
\|u-u_h\|_{H^1}=O(h^\beta).
}
\]

For `beta=1`, this is the universal first-order estimate for exact two-sided
obstacle enforcement.

---

## 7. Why this matters

The same Bernstein formal layer already proves coefficient interval bounds,
convexity, clipping, and projection properties. The double-obstacle extension
therefore uses the existing certificate machinery rather than requiring a new
constraint technology.

Potential applications include:

- double-obstacle variational inequalities;
- box-constrained membrane and contact models;
- phase-fraction constraints;
- bounded-state formulations after an affine normalization;
- unilateral problems as the limit `phi -> +infinity`.

This extension remains an internal theorem candidate pending independent
validity and prior-art audits.
