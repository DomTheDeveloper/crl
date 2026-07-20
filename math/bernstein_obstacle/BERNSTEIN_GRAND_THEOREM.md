# The Bernstein certified-inner-approximation grand theorem

## Status and claim boundary

This note records a new internal theorem package built on top of the corrected
Bernstein obstacle proofs. Its main advance is that the certified error analysis
no longer requires a symmetric bilinear form or an underlying minimization
functional.

The package has three levels:

1. an abstract Falk-type estimate for Lipschitz strongly monotone, possibly
   nonlinear and nonsymmetric, variational inequalities on certified inner
   approximations;
2. a codimension calculation that treats an interior obstacle and planar
   Signorini contact in one framework;
3. the resulting `h^r + h_Sigma^(3/2)` estimate for both problems under the
   stated regular-interface, multiplier, lifting, and mesh hypotheses.

This is an internal analytical proof and proposed grand theorem. It is not an
independent novelty verdict or expert endorsement.

---

## Part I. Abstract nonlinear certified-inner approximation

### 1. Setting

Let `V` be a real Hilbert space with norm `||.||_V`. Let `K` be a nonempty
closed convex subset of `V`. Let

\[
F:V\to V^*
\]

satisfy, for constants `alpha > 0` and `L > 0`,

\[
\langle F(v)-F(w),v-w\rangle
\ge \alpha\|v-w\|_V^2,
\tag{1.1}
\]

and

\[
\|F(v)-F(w)\|_{V^*}
\le L\|v-w\|_V.
\tag{1.2}
\]

Thus `F` is strongly monotone and Lipschitz. It need not be linear, symmetric,
or the derivative of an energy.

The continuous variational inequality is:

\[
\text{find }u\in K\text{ such that }
\langle F(u),v-u\rangle\ge0
\quad\forall v\in K.
\tag{1.3}
\]

For every discretization index `h`, let `K_h` be a nonempty closed convex set
satisfying the exact certification property

\[
K_h\subset K.
\tag{1.4}
\]

The discrete variational inequality is:

\[
\text{find }u_h\in K_h\text{ such that }
\langle F(u_h),v_h-u_h\rangle\ge0
\quad\forall v_h\in K_h.
\tag{1.5}
\]

Strong monotonicity and continuity give unique continuous and discrete
solutions.

### 2. Nonlinear certified Falk estimate

**Theorem 2.1.** For every `v_h in K_h`,

\[
\alpha\|u-u_h\|_V^2
\le
L\|u-u_h\|_V\|u-v_h\|_V
+\langle F(u),v_h-u\rangle.
\tag{2.1}
\]

Consequently,

\[
\boxed{
\|u-u_h\|_V^2
\le
\frac{L^2}{\alpha^2}\|u-v_h\|_V^2
+\frac{2}{\alpha}\langle F(u),v_h-u\rangle.
}
\tag{2.2}
\]

Equivalently,

\[
\|u-u_h\|_V
\le
\frac{L}{\alpha}\|u-v_h\|_V
+\sqrt{\frac{2}{\alpha}
\langle F(u),v_h-u\rangle}.
\tag{2.3}
\]

**Proof.** Put `e_h=u_h-u`. Strong monotonicity gives

\[
\alpha\|e_h\|_V^2
\le\langle F(u_h)-F(u),e_h\rangle.
\]

For arbitrary `v_h in K_h`, split

\[
e_h=(u_h-v_h)+(v_h-u).
\]

The discrete variational inequality implies

\[
\langle F(u_h),u_h-v_h\rangle\le0.
\]

Therefore

\[
\begin{aligned}
\alpha\|e_h\|_V^2
&\le
\langle F(u_h)-F(u),u_h-v_h\rangle
+\langle F(u_h)-F(u),v_h-u\rangle\\
&\le
-\langle F(u),u_h-v_h\rangle
+\langle F(u_h)-F(u),v_h-u\rangle.
\end{aligned}
\]

Since `K_h subset K`, one has `u_h in K`; hence the continuous variational
inequality with test function `u_h` gives

\[
\langle F(u),u_h-u\rangle\ge0.
\]

Thus

\[
-\langle F(u),u_h-v_h\rangle
=\langle F(u),v_h-u\rangle
-\langle F(u),u_h-u\rangle
\le\langle F(u),v_h-u\rangle.
\]

The Lipschitz estimate bounds the remaining term by

\[
L\|e_h\|_V\|v_h-u\|_V,
\]

which proves (2.1). Applying Young's inequality

\[
L\|e_h\|_V\|v_h-u\|_V
\le
\frac\alpha2\|e_h\|_V^2
+\frac{L^2}{2\alpha}\|v_h-u\|_V^2
\]

gives (2.2), and the square-root subadditivity gives (2.3). `square`

### 3. Best certified approximation functional

Define

\[
\mathfrak E_h(u)^2
:=
\inf_{v_h\in K_h}
\left(
\frac{L^2}{\alpha^2}\|u-v_h\|_V^2
+\frac{2}{\alpha}\langle F(u),v_h-u\rangle
\right).
\tag{3.1}
\]

Then

\[
\|u-u_h\|_V\le\mathfrak E_h(u).
\tag{3.2}
\]

The first term measures ordinary approximation. The second term measures how
much the feasible recovery enters the active multiplier region. This separation
is what makes the theorem useful for Bernstein clipping.

### 4. Mosco/recovery convergence without symmetry

**Corollary 4.1.** Suppose that for the exact solution `u` there are
`v_h in K_h` with

\[
v_h\to u\quad\text{strongly in }V.
\]

Then

\[
u_h\to u\quad\text{strongly in }V.
\]

**Proof.** Since `F(u)` is a fixed continuous functional,

\[
\langle F(u),v_h-u\rangle\to0.
\]

Apply (2.2). `square`

Thus the moving Bernstein-cone recovery theorem immediately extends from
symmetric coercive energies to all Lipschitz strongly monotone variational
inequalities.

### 5. Perturbed operator/data version

Let `F_h:V -> V*` be the operator actually used in the discrete problem:

\[
\langle F_h(u_h),v_h-u_h\rangle\ge0
\quad\forall v_h\in K_h.
\tag{5.1}
\]

For a chosen `v_h in K_h`, put

\[
\delta_h=\|u-v_h\|_V,
\qquad
R_h=\langle F(u),v_h-u\rangle,
\]

and define the a posteriori consistency defect

\[
\varepsilon_h=\|F_h(u_h)-F(u_h)\|_{V^*}.
\]

The same splitting gives

\[
\alpha\|u-u_h\|_V^2
\le
L\delta_h\|u-u_h\|_V
+R_h
+\varepsilon_h(\|u-u_h\|_V+\delta_h).
\tag{5.2}
\]

Hence

\[
\|u-u_h\|_V
\le
\frac{L\delta_h+\varepsilon_h}{\alpha}
+\sqrt{\frac{R_h+\varepsilon_h\delta_h}{\alpha}}.
\tag{5.3}
\]

This supplies a Strang-Falk form for quadrature, geometry, nonlinear
linearization, or constitutive approximation errors.

---

## Part II. A unified geometric Bernstein constraint

### 6. Constraint manifolds and scalar gaps

Let `Omega subset R^d`. Let `M` be the set on which a scalar unilateral
constraint is imposed. We treat two cases:

- **interior obstacle:** `M=Omega`, so `codim(M)=c=0`;
- **boundary contact:** `M=Gamma_C subset partial Omega`, so `c=1`.

Let

\[
\mathcal G(v)\ge0\quad\text{on }M
\tag{6.1}
\]

be the physical gap. The exact feasible set is

\[
K=\{v\in V:\mathcal G(v)\ge0\text{ a.e. on }M\}.
\tag{6.2}
\]

The two principal examples are:

1. scalar obstacle:
   \[
   \mathcal G(v)=v-\psi;
   \]
2. frictionless planar Signorini contact with constant unit normal `n` and
   clearance `g`:
   \[
   \mathcal G(v)=g-\gamma(v)\cdot n.
   \]

Let the active set and its relative boundary be

\[
\mathcal A=\{x\in M:\mathcal G(u)(x)=0\},
\qquad
\Sigma=\partial_M\{\mathcal G(u)>0\}.
\tag{6.3}
\]

Thus `Sigma` has codimension one inside `M`.

### 7. Bernstein-certified discrete set

Assume that on each discrete constraint entity `E subset M`, the discrete gap
`G(v_h)|_E` is a degree-`r` polynomial with Bernstein representation

\[
\mathcal G(v_h)|_E
=\sum_\alpha b_{E,\alpha}(\mathcal G(v_h))B_{E,\alpha}.
\]

Define

\[
K_h^B
=
\{v_h\in V_h:
 b_{E,\alpha}(\mathcal G(v_h))\ge0
\text{ for every constraint entity and coefficient}\}.
\tag{7.1}
\]

Bernstein nonnegativity and partition of unity imply

\[
K_h^B\subset K.
\tag{7.2}
\]

This exact inner inclusion is the logical hinge in Theorem 2.1.

### 8. Regular-interface and mesh assumptions

Assume:

1. `Sigma` is compact and regular inside `M`;
2. the exact gap has quadratic growth on its positive side:
   \[
   c_0d_M(x,\Sigma)^2
   \le\mathcal G(u)(x)
   \le C_0d_M(x,\Sigma)^2;
   \tag{8.1}
   \]
3. the gap has the local `C^{1,1}` control needed for the coefficient-to-value
   estimate;
4. all negative interpolated gap coefficients are localized to a fixed-layer
   patch `omega_h` around `Sigma`;
5. the local size on the patch is comparable to `h_Sigma`;
6. the patch of constraint entities has `M`-measure
   \[
   |\omega_h\cap M|_M\le C h_\Sigma;
   \tag{8.2}
   \]
7. every affected global gap coefficient has amplitude at most
   \[
   C h_\Sigma^2;
   \tag{8.3}
   \]
8. clipping a shared global gap coefficient admits a conforming stable lifting
   into `V_h`, supported in a fixed ambient-element star.

For the scalar obstacle, the lifting is the ordinary scalar Bernstein basis
correction. For planar Signorini contact, the lifting is constructed explicitly
in Section 12.

### 9. Codimension law for the repair

Let `c=codim(M)` in the ambient domain. Since `Sigma` has dimension

\[
\dim\Sigma=d-c-1,
\]

a locally quasi-uniform patch around `Sigma` contains

\[
O(h_\Sigma^{-(d-c-1)})
\]

ambient `d`-simplices.

A coefficient correction of amplitude `O(h_Sigma^2)` has gradient size
`O(h_Sigma)` on one element. Therefore its squared `H^1` contribution on one
ambient element is

\[
O(h_\Sigma^2 h_\Sigma^d)
=O(h_\Sigma^{d+2}).
\]

Multiplying by the number of affected elements gives

\[
\|d_h\|_V^2
\le C h_\Sigma^{c+3},
\]

and hence

\[
\boxed{
\|d_h\|_V
\le C h_\Sigma^{(c+3)/2}.
}
\tag{9.1}
\]

Thus:

- interior obstacle (`c=0`): repair size `O(h_Sigma^(3/2))`;
- boundary contact (`c=1`): repair size `O(h_Sigma^2)`.

The boundary-contact repair is geometrically higher order because its transition
set has one additional ambient codimension.

### 10. The multiplier law

Assume the exact residual has a bounded nonnegative multiplier representation
on the active set:

\[
\langle F(u),v-u\rangle
=
\int_M\lambda
\bigl(\mathcal G(v)-\mathcal G(u)\bigr),
\tag{10.1}
\]

where

\[
\lambda\in L^\infty(M),
\qquad
\lambda\ge0,
\qquad
\operatorname{supp}\lambda\subset\mathcal A.
\]

Let `v_h^B` be the clipped feasible recovery. On the active part of the
transition patch, assume

\[
0\le\mathcal G(v_h^B)\le C h_\Sigma^2.
\tag{10.2}
\]

Since the patch has `M`-measure `O(h_Sigma)`,

\[
0\le
\langle F(u),v_h^B-u\rangle
\le
C\|\lambda\|_{L^\infty(M)}h_\Sigma^3.
\tag{10.3}
\]

The crucial point is that the exponent `3` is independent of whether the
constraint is imposed in the volume or on the boundary:

- amplitude contributes `h_Sigma^2`;
- the active transition strip inside `M` contributes `h_Sigma`.

After the square root in Theorem 2.1, the multiplier term always contributes

\[
h_\Sigma^{3/2}.
\]

This is the **codimension-universal three-halves law**.

### 11. Grand error theorem

**Theorem 11.1 (nonlinear Bernstein grand theorem).** Assume:

1. `F` is `alpha`-strongly monotone and `L`-Lipschitz;
2. `K_h^B subset K` is the Bernstein-certified inner set;
3. a clipped feasible recovery `v_h^B in K_h^B` satisfies
   \[
   \|u-v_h^B\|_V
   \le C\left(h^r+h_\Sigma^{(c+3)/2}\right);
   \tag{11.1}
   \]
4. the multiplier assumptions (10.1)--(10.2) hold.

Then the unique discrete variational-inequality solution satisfies

\[
\boxed{
\|u-u_h^B\|_V
\le
C\left(h^r+h_\Sigma^{3/2}\right).
}
\tag{11.2}
\]

The theorem requires neither symmetry nor an energy functional.

**Proof.** Insert `v_h^B` into (2.3). The approximation term is bounded by
(11.1). The residual term is bounded by (10.3), so its square root is
`O(h_Sigma^(3/2))`. Since `c >= 0`,

\[
h_\Sigma^{(c+3)/2}
\le h_\Sigma^{3/2}
\]

for `0 < h_Sigma <= 1`. This gives (11.2). `square`

---

## Part III. Two principal corollaries

### 12. Scalar nonzero obstacle

Let

\[
K_\psi
=\{v\in H_0^1(\Omega):v\ge\psi\}.
\]

Let the exact gap be

\[
w=u-\psi\ge0.
\]

Suppose the regular-interface hypotheses apply to `w`, and suppose the
discrete obstacle is represented exactly. Define the discrete cone by requiring
all local Bernstein coefficients of `v_h-psi` to be nonnegative.

Then `c=0`; shared coefficient clipping produces a feasible recovery with

\[
\|u-v_h^B\|_{H^1}
\le C(h^r+h_\Sigma^{3/2}).
\]

If the nonlinear elliptic operator is strongly monotone and Lipschitz and the
contact multiplier is bounded, Theorem 11.1 gives

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Sigma^{3/2}).
\]

This extends the previous symmetric quadratic theorem to nonlinear and
nonsymmetric strongly monotone obstacle problems.

### 13. Planar frictionless Signorini contact

Let `V` be a conforming vector-valued `H^1` displacement space. Let the contact
boundary `Gamma_C` lie in a hyperplane with constant unit normal `n`. Let the
clearance `g` be represented in the scalar degree-`r` Bernstein trace space.
The gap is

\[
\mathcal G(v)=g-\gamma(v)\cdot n.
\]

For a boundary Bernstein control degree of freedom `i`, write the vector
coefficient of the displacement as `U_i` and the scalar clearance coefficient
as `g_i`. The gap coefficient is

\[
c_i=g_i-U_i\cdot n.
\]

Clip it by defining

\[
\widetilde c_i=\max\{c_i,0\}
\]

and update the vector control coefficient once globally by

\[
\widetilde U_i
=U_i+\min\{c_i,0\}n.
\tag{13.1}
\]

Indeed,

\[
g_i-\widetilde U_i\cdot n
=c_i-\min\{c_i,0\}
=\max\{c_i,0\}.
\]

This update:

- changes only the normal component;
- preserves all tangential control components;
- preserves conformity because each shared boundary control degree of freedom
  is updated once globally;
- gives coefficientwise, hence pointwise, nonpenetration over every complete
  contact face.

Under the regular transition-set, quadratic gap, bounded pressure, local
quasi-uniformity, and bulk interpolation assumptions, one has `c=1`. Therefore

\[
\|u-v_h^B\|_V
\le C(h^r+h_\Sigma^2),
\]

while the pressure consistency term is `O(h_Sigma^3)`. Theorem 11.1 yields

\[
\boxed{
\|u-u_h^B\|_V
\le C(h^r+h_\Sigma^{3/2}).
}
\tag{13.2}
\]

Thus the same final three-halves interface term governs both interior obstacle
and planar boundary contact, although the contact lifting itself is higher
order.

### 14. Conservative inexact obstacle or clearance data

The exact-inner property can be retained with one-sided data approximations:

- for `v >= psi`, use a certified majorant `psi_h^+ >= psi`;
- for `g-v.n >= 0`, use a certified minorant `g_h^- <= g`.

Let `q_h` denote the conservative gap-data shift. Suppose a feasible recovery
has an added lifting error `E_h` in `V`, and suppose the active multiplier sees
weighted data error

\[
Q_h^2
:=\int_M\lambda q_h.
\]

Then the same argument gives

\[
\|u-u_h^B\|_V
\le
C\left(
 h^r+h_\Sigma^{3/2}+E_h+Q_h
\right).
\tag{14.1}
\]

This allows geometric clearance errors and nonexact obstacles without losing
pointwise safety, provided the approximation is conservative.

---

## Part IV. Why this is a larger theorem

### 15. What has been removed

The earlier sharp theorem required a symmetric continuous coercive bilinear form
and transferred the recovery estimate through an energy identity or Falk's
linear result.

Theorem 11.1 removes:

- symmetry;
- linearity of the operator;
- existence of a potential energy;
- restriction to scalar volume obstacles.

The proof uses only:

- strong monotonicity;
- Lipschitz continuity;
- exact inner feasibility;
- a certified recovery and multiplier estimate.

### 16. What has been unified

The same theorem now includes:

- zero and nonzero scalar obstacles;
- conservative inexact obstacles;
- planar frictionless Signorini contact;
- nonlinear constitutive operators;
- nonsymmetric strongly monotone operators;
- operator/data perturbations through (5.3).

The geometric count also explains the previously mysterious exponent:

\[
\boxed{
\text{quadratic gap amplitude }h^2
\times
\text{active transition measure }h
=h^3,
}
\]

and the VI estimate takes its square root.

### 17. Literature positioning requiring independent audit

The following are established neighboring ingredients and are not claimed as
new in isolation:

- Falk-type approximation estimates for variational inequalities;
- Bernstein coefficient range certificates;
- bounds-constrained high-order finite-element variational inequalities;
- classical obstacle and Signorini finite-element error analysis;
- Mosco stability for nonlinear unilateral problems.

The candidate contribution requiring a source-by-source novelty audit is the
specific combination of:

1. exact Bernstein coefficient inner cones;
2. the nonlinear certified estimate (2.2);
3. conformity-preserving clipping/lifting;
4. the codimension count (9.1);
5. the codimension-universal multiplier law (10.3);
6. one theorem giving the same final `3/2` interface rate for both interior
   obstacles and planar Signorini contact.

### 18. Deliberate exclusions

This theorem does not yet cover:

- merely monotone operators without strong monotonicity;
- Coulomb friction or set-valued tangential laws;
- curved contact boundaries with incompatible changing normals unless a stable
  normal-gap lifting is separately proved;
- singular or degenerate active-set interfaces;
- measure-valued multipliers;
- anisotropic interface patches without a new scaling audit;
- nonconservative obstacle/geometry approximation without a two-sided set-error
  theorem;
- optimal adaptive complexity.

These are future extension directions, not hidden claims.

## Internal verdict

- Abstract nonlinear certified Falk theorem: **proved**.
- Nonsymmetric/nonpotential extension: **proved under strong monotonicity and
  Lipschitz continuity**.
- Codimension repair law: **proved under stable local lifting and quasi-uniform
  patch assumptions**.
- Codimension-universal multiplier `3/2` law: **proved under bounded multiplier
  density and quadratic gap growth**.
- Scalar obstacle corollary: **proved under the corrected regular-interface
  hypotheses**.
- Planar frictionless Signorini corollary: **proved under constant-normal,
  stable global boundary-DOF lifting, and regular transition hypotheses**.
- Novelty and publication significance: **requires independent literature and
  expert audit**.
