# The Grand Positive-Basis Obstacle Theorem

## Minkowski-codimension repair laws, multiplier saturation, and sharpness of the three-halves rate

### Status

This document records a new abstract theorem package derived from the Bernstein–Bézier obstacle analysis.

It contains:

1. a positive-basis Mosco principle;
2. a repair-rate law governed by coefficient consistency, gap vanishing order, and Minkowski codimension;
3. a multiplier-saturation principle;
4. a stratified-interface extension;
5. an exact one-dimensional sharpness theorem showing that the classical `h^(3/2)` clipping rate cannot generally be improved on unfitted meshes.

The theorem is conditional on the explicit analytical hypotheses below. It has not yet received independent expert review.

---

## 1. Abstract positive-basis setting

Let `Omega` be a bounded Lipschitz domain and let `V` be a real Hilbert energy space continuously embedded in `H^1(Omega)`. Let

\[
K=\{v\in V:v\ge\psi\text{ a.e.}\}.
\]

For each mesh scale `h`, let `V_h` be a conforming finite-dimensional space. On every element, assume a local basis

\[
\{\phi_{T,i}\}_{i\in I_T}
\]

with the following properties.

### PB1. Positive partition of unity

\[
\phi_{T,i}\ge0,
\qquad
\sum_{i\in I_T}\phi_{T,i}=1.
\]

Thus nonnegative gap coefficients certify pointwise feasibility.

### PB2. Global conformity through shared coefficients

Coefficients associated with a common trace degree of freedom are represented by one global unknown. Clipping a global coefficient therefore preserves all common traces and homogeneous boundary conditions.

### PB3. Positive smooth recovery

There is a recovery operator `R_h` such that, for every nonnegative smooth gap `w`, all local coefficients of `R_h w` are nonnegative and

\[
\|R_h w-w\|_V\longrightarrow0.
\]

### PB4. Coefficient consistency of order `m`

For a reference interpolant or preliminary recovery `I_h w`, coefficient functionals have representative points `x_{T,i}` and satisfy

\[
|b_{T,i}(I_h w)-w(x_{T,i})|
\le C h_T^m.
\]

### PB5. Stable local correction

If coefficient corrections on an element have amplitude at most `A_h`, then

\[
\|d_h\|_{L^2(T)}
\le C A_h |T|^{1/2},
\]

\[
\|\nabla d_h\|_{L^2(T)}
\le C A_h h_T^{-1}|T|^{1/2}.
\]

Bernstein and tensor-product Bernstein bases satisfy PB1. The existing global assembly and clipping theorems supply PB2. The positive Bernstein sampling operator supplies PB3. The coefficient-to-value theorem supplies PB4 with `m=2` under `C^{1,1}` regularity. Fixed-degree inverse estimates supply PB5.

---

## 2. Positive-basis Mosco principle

### Theorem A

Assume PB1--PB3, conforming inclusion `K_h^+ subset K`, and density of smooth nonnegative functions in `K`. Then

\[
K_h^+\xrightarrow{M}K.
\]

For every symmetric continuous coercive quadratic energy, the corresponding discrete minimizers converge strongly in `V`.

### Proof

PB1 gives `K_h^+ subset K`. PB3 gives recovery for every smooth nonnegative gap. Smooth positive density and a diagonal sequence give recovery for every point of `K`. Since `K` is closed and convex, it is weakly closed, which gives the Mosco weak-limit condition. Standard coercive energy compactness and uniqueness then give strong convergence of minimizers.

This theorem is basis-independent. Bernstein–Bézier elements are one concrete instance.

---

## 3. Geometric data

Let

\[
w=u-\psi\ge0,
\qquad
A=\{w=0\},
\qquad
\Sigma=\partial\{w>0\}\cap\Omega.
\]

No smoothness of `Sigma` is required in the abstract rate theorem. Instead assume a tubular-volume estimate.

### G1. Minkowski codimension `s`

For sufficiently small `delta`,

\[
|\{x:\operatorname{dist}(x,\Sigma)\le\delta\}|
\le C_\Sigma\delta^s,
\]

where `s>0`. For a smooth codimension-`c` submanifold, `s=c`.

### G2. Vanishing order `q`

On the positive side near `Sigma`,

\[
c_0\operatorname{dist}(x,\Sigma)^q
\le w(x)
\le C_0\operatorname{dist}(x,\Sigma)^q.
\]

### G3. Contact-interior exactness

Elements contained in the interior of `A` recover the zero gap exactly.

Assume a locally quasi-uniform unfitted mesh of size `h` near `Sigma`.

Define

\[
a=\min\{m,q\},
\qquad
\beta=\frac aq=\min\left\{1,\frac mq\right\},
\qquad
\delta_h=h+h^{m/q}\simeq h^\beta.
\]

---

## 4. Universal localization and repair law

### Theorem B — Minkowski-codimension repair theorem

Under PB1, PB2, PB4, PB5 and G1--G3:

1. every negative coefficient of `I_h w` is supported in a patch `omega_h` contained in a `C delta_h` neighborhood of `Sigma`;
2. every coefficient on that patch has magnitude `O(h^a)`;
3. global clipping produces a conforming pointwise-feasible gap `w_h^+`;
4. the clipping correction satisfies

   \[
   \|w_h^+-I_h w\|_{L^2}
   \le C h^a\delta_h^{s/2},
   \]

   \[
   \|w_h^+-I_h w\|_{H^1}
   \le C h^{a-1}\delta_h^{s/2}.
   \]

Equivalently, the repair exponent is

\[
\boxed{
\rho_{\mathrm{repair}}
=
a-1+\frac{s a}{2q}.
}
\]

### Proof

If a coefficient is negative, PB4 implies its representative value is at most `C h^m`. By the lower growth bound,

\[
\operatorname{dist}(x_{T,i},\Sigma)^q\lesssim h^m,
\]

so its point lies within `O(h^(m/q))` of `Sigma`. Enlarging by one element diameter gives the patch thickness

\[
\delta_h=h+h^{m/q}.
\]

On this patch the upper growth bound gives values of size

\[
O(\delta_h^q)=O(h^a),
\]

and PB4 contributes at most the same order. Thus all risky coefficients are `O(h^a)`.

PB5 and the tubular-volume estimate give

\[
\|\nabla(w_h^+-I_h w)\|_{L^2}^2
\lesssim
h^{2a-2}|\omega_h|
\lesssim
h^{2a-2}\delta_h^s.
\]

Taking square roots proves the result.

---

## 5. Multiplier-saturation law

Let `lambda` be a bounded nonnegative multiplier supported on the contact set. On the contact portion of the risky patch, the clipped recovery has amplitude `O(h^a)`. Therefore

\[
\langle\lambda,w_h^+\rangle
\lesssim h^a\delta_h^s.
\]

### Theorem C — Generic variational-inequality rate

Suppose a preliminary approximation has energy error `E_h`, and the standard energy/Falk transfer holds. Then

\[
\|u-u_h^+\|_V
\le
C\left(
E_h
+
h^{a-1}\delta_h^{s/2}
+
h^{a/2}\delta_h^{s/2}
\right).
\]

Hence the universal interface exponent is

\[
\boxed{
\rho_{\mathrm{VI}}
=
\frac{s a}{2q}
+
\min\left\{a-1,\frac a2\right\}.
}
\]

When `a>=2`, this simplifies to

\[
\boxed{
\rho_{\mathrm{VI}}
=
\frac a2\left(1+\frac s q\right).
}
\]

The multiplier term is rate limiting whenever `a>2`.

### Multiplier-orthogonal improvement

If a recovery is contact-exact, or otherwise satisfies a multiplier consistency bound of the same order as the squared repair norm, then

\[
\boxed{
\rho_{\perp}
=
a-1+\frac{s a}{2q}.
}
\]

Thus higher-order positive approximation can improve the repair itself while the ordinary obstacle multiplier prevents the discrete minimizer from realizing that full gain.

---

## 6. Classical obstacle corollary

For a regular classical obstacle free boundary:

- quadratic gap growth gives `q=2`;
- the coefficient-to-value estimate has `m=2`;
- a smooth hypersurface has Minkowski codimension `s=1`.

Therefore `a=2`, `beta=1`, and

\[
\rho_{\mathrm{repair}}=\rho_{\mathrm{VI}}=\frac32.
\]

Hence

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le
C\left(E_h+h_\Gamma^{3/2}\right).
}
\]

If the bulk approximation satisfies `E_h=O(h^r)`, this is exactly

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le
C\left(h^r+h_\Gamma^{3/2}\right).
}
\]

---

## 7. Quadratic-contact saturation principle

### Corollary

For an unfitted, locally quasi-uniform positive-basis method near a codimension-one interface with quadratic gap growth, increasing the coefficient consistency order beyond two does not improve the generic clipping-layer rate.

Indeed, when `q=2` and `m>=2`,

\[
a=\min(m,2)=2,
\]

so

\[
\rho_{\mathrm{VI}}=\frac32.
\]

The limitation is geometric: a cut element contains true gap values of order `h^2`, regardless of how accurately coefficients approximate those values.

Thus beating the three-halves interface rate requires changing at least one of:

1. interface fitting or subelement geometry;
2. support thickness;
3. the contact consistency term;
4. the pointwise coefficient-repair mechanism.

Merely increasing polynomial degree is insufficient.

---

## 8. Exact sharpness theorem

Consider the phase-locked one-dimensional model on the cut cell `[0,h]`:

\[
w_h(x)=(x-\theta h)_+^2,
\qquad
\frac12\le\theta<1.
\]

Let `I_h^2 w_h` be quadratic interpolation at `0`, `h/2`, and `h`, written in the degree-two Bernstein basis.

The coefficients are

\[
b_0=0,
\qquad
b_1=-\frac12(1-\theta)^2h^2,
\qquad
b_2=(1-\theta)^2h^2.
\]

Thus the middle coefficient is strictly negative.

Clipping changes only `b_1`. The correction is

\[
d_h(x)
=
(1-\theta)^2h^2
\frac{x}{h}\left(1-\frac{x}{h}\right).
\]

Its exact energy is

\[
\int_0^h |d_h'(x)|^2\,dx
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

For every fixed `theta` in `[1/2,1)`, the constant is positive. Consequently, the `h^(3/2)` clipping rate is sharp for this unfitted phase-locked family.

This is a lower bound for the actual clipping correction, not merely an upper bound produced by inverse estimates.

---

## 9. Stratified-interface theorem

Suppose

\[
\Sigma=\bigcup_{j=1}^J\Sigma_j
\]

and stratum `j` has tubular exponent `s_j`, vanishing order `q_j`, and coefficient consistency order `m_j`. Set

\[
a_j=\min(m_j,q_j).
\]

Then the repair and multiplier contributions add:

\[
\|u-u_h^+\|_V
\le
C\left(
E_h+\sum_{j=1}^J h^{\rho_j}
\right),
\]

with

\[
\rho_j
=
\frac{s_j a_j}{2q_j}
+
\min\left\{a_j-1,\frac{a_j}{2}\right\}.
\]

The stratum with the smallest exponent controls the global interface rate.

This formulation can accommodate rough or lower-dimensional singular sets whenever their tubular-volume and gap-growth hypotheses can be proved. It does not automatically assert that every singular obstacle free boundary satisfies those hypotheses.

---

## 10. Significance

The central result is no longer only:

> Bernstein clipping happens to cost `h^(3/2)`.

It becomes:

> Every conforming positive-basis variational-inequality method has a geometry-controlled repair law. The exponent is determined by coefficient consistency, gap vanishing order, and the Minkowski codimension of the active interface. For ordinary quadratic contact, three-halves is a universal and sharp saturation exponent for unfitted coefficient clipping.

Bernstein–Bézier elements are especially valuable because they satisfy the positive-basis and global trace requirements with finitely many linear coefficient inequalities.

---

## 11. Remaining proof obligations

Before this can be advertised as an independently confirmed grand theorem:

1. an expert must audit the abstract PB1--PB5 assumptions and their application to the chosen finite-element family;
2. the tubular-volume theorem must be stated carefully for locally graded meshes;
3. the preliminary approximation term `E_h` must be supplied for each PDE class;
4. multiplier assumptions must be matched to each obstacle/contact model;
5. literature must be searched specifically for equivalent vanishing-order/codimension repair laws;
6. the exact sharpness calculation should be formalized or independently reproduced.

The literature checked to date contains positive high-order bounds, high-order obstacle methods, proximal Galerkin methods, and free-boundary localization, but no retrieved source stated this combined universal Minkowski-codimension law.
