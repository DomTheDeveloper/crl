# Grand Positive-Basis Variational-Inequality Theorem

## Universal Minkowski repair law, quadratic-contact saturation, and sharpness

### 1. Positive-basis convergence principle

Let `V_h` be a conforming finite-element family whose local basis functions are
nonnegative and form a partition of unity. Assume shared trace coefficients are
global degrees of freedom and that a positive recovery operator approximates
every smooth nonnegative gap strongly in the energy space.

Then the coefficient-feasible cones

\[
K_h^+=\{v_h:\text{all gap coefficients are nonnegative}\}
\]

Mosco-converge to the continuous obstacle cone. Consequently, minimizers of
symmetric continuous coercive variational inequalities converge strongly.

This layer is not Bernstein-specific. Bernstein–Bézier elements are a canonical
realization because coefficient nonnegativity gives an exact pointwise
certificate and shared coefficients preserve conformity under clipping.

---

### 2. Geometry and approximation parameters

Let `w=u-psi`, let `Sigma` be the boundary of the positive-gap region, and
assume near `Sigma`

\[
c\,\operatorname{dist}(x,\Sigma)^q
\le w(x)\le
C\,\operatorname{dist}(x,\Sigma)^q.
\]

Assume the coefficient-to-value defect is `O(h^m)`. Define

\[
a=\min\{m,q\}.
\]

Assume the interface has Minkowski codimension `s`:

\[
|\{x:\operatorname{dist}(x,\Sigma)\le\delta\}|
\le C\delta^s.
\]

The risky-patch thickness is

\[
\delta_h\simeq h^{a/q}.
\]

The `min` is essential. When coefficient consistency exceeds the physical
vanishing order, true gap values on a cut element—not coefficient error—control
the repair amplitude.

---

### 3. Universal clipping-repair law

Under the positive-basis, conformity, inverse-stability, growth, and tubular
volume assumptions, all negative coefficients are localized to a
`C delta_h` patch and have magnitude `O(h^a)`. Global clipping yields a
conforming pointwise-feasible recovery and

\[
\|d_h\|_{L^2}
\lesssim h^a\delta_h^{s/2},
\]

\[
\|d_h\|_{H^1}
\lesssim h^{a-1}\delta_h^{s/2}.
\]

Therefore the repair exponent is

\[
\boxed{
\rho_{\mathrm{repair}}
=
a-1+\frac{sa}{2q}.
}
\]

If the obstacle multiplier is a bounded density, its contact-consistency term
has size

\[
O(h^a\delta_h^s).
\]

After the energy/Falk square-root transfer, the generic variational-inequality
interface exponent is

\[
\boxed{
\rho_{\mathrm{VI}}
=
\frac{sa}{2q}
+
\min\left\{a-1,\frac a2\right\}.
}
\]

For `a>=2`,

\[
\boxed{
\rho_{\mathrm{VI}}
=
\frac a2\left(1+\frac s q\right).
}
\]

This separates three independent mechanisms:

1. coefficient consistency `m`;
2. physical vanishing order `q`;
3. geometric Minkowski codimension `s`.

---

### 4. Classical Bernstein obstacle theorem as a corollary

For ordinary regular contact,

\[
m=2,\qquad q=2,\qquad s=1.
\]

Thus `a=2` and

\[
\rho_{\mathrm{repair}}
=
\rho_{\mathrm{VI}}
=
\frac32.
\]

Hence

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le C\left(h^r+h_\Gamma^{3/2}\right).
}
\]

---

### 5. Quadratic-contact saturation principle

If the gap vanishes quadratically and `m>=2`, then

\[
a=\min(m,2)=2.
\]

Therefore increasing polynomial degree or coefficient consistency alone does
not improve the unfitted coefficient-clipping interface exponent:

\[
\boxed{
\rho_{\mathrm{VI}}=\frac32.
}
\]

The barrier is geometric. A cut element contains true gap values of order
`h^2`, even when coefficients approximate those values to higher order.

To beat `3/2`, a method must change at least one of:

- interface fitting or subcell geometry;
- repair support thickness;
- multiplier/contact orthogonality;
- the coefficientwise clipping mechanism.

This is not an impossibility theorem for every high-order contact method. It is
a saturation theorem for the stated unfitted positive-basis clipping class.

---

### 6. Exact sharpness model

On a phase-locked cut cell `[0,h]`, let

\[
w_h(x)=(x-\theta h)_+^2,
\qquad \frac12\le\theta<1.
\]

Quadratic interpolation at `0`, `h/2`, and `h`, expressed in the degree-two
Bernstein basis, has coefficients

\[
b_0=0,
\qquad
b_1=-\frac12(1-\theta)^2h^2,
\qquad
b_2=(1-\theta)^2h^2.
\]

Clipping the negative middle coefficient produces

\[
d_h(x)
=(1-\theta)^2x(h-x),
\]

and

\[
\int_0^h|d_h'(x)|^2\,dx
=
\frac{(1-\theta)^4}{3}h^3.
\]

Therefore

\[
\boxed{
|d_h|_{H^1(0,h)}
=
\frac{(1-\theta)^2}{\sqrt3}h^{3/2}.
}
\]

For fixed `theta`, this is a positive lower bound of exact order `h^(3/2)`.
Thus the classical clipping exponent is sharp for this unfitted family.

The exact symbolic calculation is reproduced by
`verification/verify_grand_sharpness.py` in the grand-theorem research PR.

---

### 7. Stratified and rough interfaces

If the active interface decomposes into strata with vanishing orders `q_j`,
coefficient orders `m_j`, and tubular exponents `s_j`, then each stratum
contributes its own exponent

\[
\rho_j
=
\frac{s_j a_j}{2q_j}
+
\min\left\{a_j-1,\frac{a_j}{2}\right\},
\qquad
a_j=\min(m_j,q_j).
\]

The smallest exponent controls the global interface term. This replaces the
need for a globally smooth interface by quantitative growth and tubular-volume
hypotheses. Applying it to a particular singular free boundary still requires
proving those hypotheses for that PDE.

---

### 8. Formal and review status

The live Lean branch now formalizes:

- vanishing-order/codimension repair scales;
- dimension cancellation in strip counts;
- consistency-limited order `min m q`;
- quadratic-contact saturation for every `m>=2`;
- strict negativity of the phase-locked middle coefficient;
- the algebraic correction slope identity;
- the general moving-obstacle and coercive rate-composition endgames.

The exact integral sharpness calculation is symbolically verified, but its
integral identity is not yet kernel-formalized in Lean.

The grand theorem remains internally derived and must receive independent
numerical-analysis and free-boundary review before being called independently
confirmed.
