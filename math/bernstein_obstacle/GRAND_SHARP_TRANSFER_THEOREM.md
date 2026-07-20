# Grand Sharp-Rate Transfer Theorem

Status: **complete abstract theorem; applications require verification of its explicit hypotheses**

This theorem isolates the exact mechanism by which a Bernstein clipping recovery
estimate transfers to the discrete minimizer. It contains the corrected
`h^r + h_Gamma^(3/2)` theorem as one specialization.

---

## 1. Abstract setting

Let `X` be a Banach space, let `K subset X` be closed and convex, and let
`K_h subset K` be nonempty closed convex discrete sets.

Let `J:X->R` be Frechet differentiable near `K`. Let `u` minimize `J` over `K`
and let `u_h` minimize `J` over `K_h`.

Write

\[
\lambda=J'(u)\in X^*.
\]

The variational inequality at the continuous minimizer is

\[
\langle\lambda,v-u\rangle\ge0
\qquad\forall v\in K.
\]

Define the Bregman remainder

\[
D_J(v,u)
 =J(v)-J(u)-\langle\lambda,v-u\rangle.
\]

Fix an exponent `q>1`.

Assume there are constants `c_J,C_J>0` such that, for the discrete minimizers
and the recovery functions used below,

\[
c_J\|v-u\|_X^q
 \le D_J(v,u)
 \le C_J\|v-u\|_X^q.
\]

The lower and upper estimates may be replaced by different equivalent error
metrics. The norm formulation is used here to expose the rate directly.

---

## 2. Geometric recovery assumptions

Let `h` be the bulk mesh scale and `h_Gamma` an interface-patch scale.
Suppose there are feasible recoveries `v_h in K_h` satisfying

\[
\|u-v_h\|_X
 \le C_R\left(h^r+h_\Gamma^{\beta-1+\kappa/q}\right).
\]

Interpretation:

- `beta` is the order of the coefficient amplitude near the active interface;
- `kappa` is the power in the patch-volume estimate
  `|omega_h| = O(h_Gamma^kappa)`;
- the exponent `beta-1+kappa/q` is exactly the codimension–growth clipping law.

Assume also the multiplier consistency estimate

\[
0\le\langle\lambda,v_h-u\rangle
 \le C_\lambda h_\Gamma^{\beta+\kappa}.
\]

The lower sign is automatic because `v_h in K` and `u` solves the continuous
variational inequality.

---

## 3. The theorem

### Theorem D — grand sharp-rate transfer

Under Sections 1–2,

\[
\|u-u_h\|_X
 \le C\left(
 h^r
 +h_\Gamma^{\beta-1+\kappa/q}
 +h_\Gamma^{(\beta+\kappa)/q}
 \right).
\]

Equivalently, the interface contribution is governed by

\[
\rho(q,\beta,\kappa)
 =\min\left\{
 \beta-1+\frac\kappa q,
 \frac{\beta+\kappa}{q}
 \right\}.
\]

Thus

\[
\|u-u_h\|_X
 \le C\left(h^r+h_\Gamma^{\rho(q,\beta,\kappa)}\right).
\]

### Proof

Since `u_h in K_h subset K`, the continuous variational inequality gives

\[
\langle\lambda,u_h-u\rangle\ge0.
\]

Therefore the lower Bregman bound yields

\[
J(u_h)-J(u)
 =D_J(u_h,u)+\langle\lambda,u_h-u\rangle
 \ge c_J\|u_h-u\|_X^q.
\]

Discrete minimality and feasibility of `v_h` give

\[
J(u_h)-J(u)\le J(v_h)-J(u).
\]

Using the upper Bregman bound and multiplier consistency,

\[
J(v_h)-J(u)
 \le C_J\|v_h-u\|_X^q
     +C_\lambda h_\Gamma^{\beta+\kappa}.
\]

Insert the recovery estimate and use
`(a+b)^q <= C_q(a^q+b^q)`:

\[
\|u_h-u\|_X^q
 \le C\left(
 h^{rq}
 +h_\Gamma^{q(\beta-1)+\kappa}
 +h_\Gamma^{\beta+\kappa}
 \right).
\]

Taking the `q`-th root proves the first displayed estimate. The smaller of the
two interface exponents governs their sum, proving the equivalent form.

---

## 4. Corrected Hilbert obstacle theorem as a corollary

Take

\[
X=H_0^1(\Omega),
\qquad q=2,
\qquad\beta=2,
\qquad\kappa=1.
\]

Then

\[
\beta-1+\frac\kappa q
 =2-1+\frac12
 =\frac32,
\]

and

\[
\frac{\beta+\kappa}{q}
 =\frac{2+1}{2}
 =\frac32.
\]

Hence Theorem D gives

\[
\|u-u_h\|_{H^1}
 \le C\left(h^r+h_\Gamma^{3/2}\right).
\]

The matching of the repair and multiplier exponents at `3/2` is therefore an
algebraic consequence of quadratic contact, a hypersurface patch, and a
quadratic energy.

---

## 5. Phase diagram

For quadratic contact across a codimension-one patch,

\[
\rho(q,2,1)
 =\min\left\{1+\frac1q,\frac3q\right\}.
\]

Therefore

\[
\rho(q,2,1)=
\begin{cases}
1+1/q,&1<q\le2,\\
3/q,&q\ge2.
\end{cases}
\]

- For `q<2`, the geometric repair term is dominant.
- At `q=2`, repair and multiplier consistency balance exactly.
- For `q>2`, the multiplier term is dominant unless additional cancellation or
  stronger contact decay is available.

This phase diagram is a theorem under the stated Bregman hypotheses. It is not
an unconditional p-Laplacian error estimate.

---

## 6. General contact order

If the primal gap and coefficient defect have order `beta`, Theorem D predicts

\[
\rho(q,\beta,1)
 =\min\left\{\beta-1+\frac1q,
              \frac{\beta+1}{q}\right\}.
\]

The two mechanisms balance precisely when

\[
\beta-1+\frac1q=\frac{\beta+1}{q},
\]

or equivalently

\[
(q-1)\beta=q.
\]

Thus the balanced contact order is

\[
\beta_*(q)=\frac{q}{q-1}.
\]

For `q=2`, this is quadratic contact. More generally, an operator whose natural
contact growth has order `q/(q-1)` places the geometric repair and multiplier
consistency at the same asymptotic scale.

This identity is a structural prediction worth testing in nonlinear obstacle
models.

---

## 7. What remains for a concrete nonlinear operator

To apply Theorem D to a p-growth operator, one must prove all of the following:

1. the correct Banach or natural quasi-norm in which the Bregman remainder has
   two-sided `q`-power control;
2. the regular free-boundary contact order `beta` for the exact operator and
   forcing regime;
3. a coefficient-to-value localization theorem at that contact order;
4. a conforming clipping recovery with the corresponding coefficient
   amplitude;
5. a multiplier representation and the `O(h_Gamma^(beta+kappa))` consistency
   estimate;
6. bulk interpolation in the same Bregman metric.

Until these are supplied, the nonlinear phase diagram is an abstract theorem
and research program, not a completed p-Laplacian rate claim.

---

## 8. Significance

The corrected Bernstein obstacle estimate is now embedded in a three-parameter
family indexed by:

- energy exponent `q`;
- contact-growth order `beta`;
- active-set codimension exponent `kappa`.

The theorem separates the two genuinely different obstructions:

1. geometric cost of enforcing coefficient feasibility;
2. multiplier cost of touching the active set.

This separation makes clear exactly what must improve to obtain a faster rate:
a thinner active patch, higher-order contact decay, a weaker multiplier, or an
operator-specific cancellation.
