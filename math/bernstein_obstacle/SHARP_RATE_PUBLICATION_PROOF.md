# Publication proof: scoped regular-interface three-halves estimate

## Status and scope

This note expands the corrected free-boundary proof map into a continuous
argument. It proves the stated rate only under the explicit regularity,
local-grading, multiplier, exact-obstacle, dimension, and physical-boundary
hypotheses listed below. It does not cover singular or degenerate free-boundary
points, anisotropic interface meshes, measure-valued multipliers, arbitrary
inexact obstacles, or free boundaries meeting the physical boundary.

The intended mechanics theorem is for spatial dimension `d = 2` or `d = 3`
and fixed polynomial degree `r >= 1`. More generally, the same argument applies
in a fixed finite dimension when the pointwise barycentric interpolation below
is well defined, for example when `r + 1 > d/2`, together with the stated local
`C^{1,1}` assumptions.

This is an internal analytical proof completion. It is not an independent
expert endorsement.

## 1. Variational inequality and finite-element cone

Let

\[
V=H_0^1(\Omega),
\qquad
K=\{v\in V:v\ge0\text{ a.e.}\}.
\]

Let `a` be symmetric, continuous, and coercive on `V`, and let `ell in V*`.
The exact zero-obstacle solution `u in K` minimizes

\[
J(v)=\tfrac12a(v,v)-\ell(v)
\]

over `K`. Equivalently,

\[
a(u,v-u)\ge \ell(v-u)
\qquad\text{for every }v\in K.
\]

Let `V_h^r` be the conforming degree-`r` simplicial finite-element space and
let

\[
K_h^B=\{v_h\in V_h^r:b_i(v_h)\ge0
\text{ for every global Bernstein degree of freedom }i\}.
\]

The discrete solution `u_h^B` minimizes `J` over `K_h^B`.

## 2. Assumptions for the sharp estimate

Let

\[
\Gamma=\partial\{u>0\}\cap\Omega
\]

be the interior free boundary. Assume:

1. `d = 2` or `d = 3` and `r >= 1`; more generally, assume the pointwise
   barycentric interpolant is well defined, for example `r + 1 > d/2`;
2. `Gamma` is compact and `C^1`;
3. `u in C^{1,1}` in a fixed neighborhood of `Gamma` and
   `u=grad u=0` on `Gamma`;
4. on the positive side of that neighborhood,
   \[
   c_0\,d(x,\Gamma)^2\le u(x)\le C_0\,d(x,\Gamma)^2;
   \]
5. a mesh-independent one-sided `H^{r+1}` extension exists from the positive
   phase across `Gamma` in a fixed tubular neighborhood;
6. outside the interface patch defined below,
   \[
   \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{reg};
   \]
7. the multiplier is represented by a nonnegative function
   `lambda in L^infinity(Omega)` supported in the contact set, with
   \[
   a(u,w)-\ell(w)=\int_\Omega\lambda w
   \qquad\text{for every }w\in V;
   \]
8. the local risky set is
   \[
   \mathcal R_h
   =\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
   \]
9. on a fixed one-ring enlargement `omega_h` of `R_h`,
   \[
   c_m h_\Gamma\le h_T\le C_m h_\Gamma,
   \qquad
   |\omega_h|\le C_\Gamma h_\Gamma;
   \]
10. either `Gamma` is separated from the physical boundary by a contact collar,
    or every positive physical-boundary element lies in a fixed collar on
    which `u` has a uniform `C^{1,1}` bound and satisfies a uniform inward
    linear-growth estimate;
11. the original obstacle has been represented exactly and subtracted, so the
    gap problem is genuinely the zero-obstacle problem.

All constants below may depend on the fixed degree, dimension, shape
regularity, the constants in these assumptions, and the continuity/coercivity
constants of `a`, but not on `h` or `h_Gamma`.

## 3. Coefficient-to-grid-value estimate

Let `I_T^r` be interpolation at the degree-`r` barycentric lattice. Let `A_r`
be the inverse of the reference Bernstein collocation matrix, so that

\[
b_{T,\alpha}(I_T^r v)
=\sum_j(A_r)_{\alpha j}v(x_{T,j}).
\]

The barycentric lattice is unisolvent for `P_r`; therefore `A_r` is a fixed
finite matrix depending only on `r` and the dimension. Exact reproduction of
constants and affine functions gives

\[
\sum_j(A_r)_{\alpha j}=1,
\qquad
\sum_j(A_r)_{\alpha j}x_{T,j}=x_{T,\alpha}.
\]

For `v in C^{1,1}(T)`, Taylor expansion at `x_{T,alpha}` yields

\[
v(x_{T,j})
=v(x_{T,\alpha})
+\nabla v(x_{T,\alpha})\cdot(x_{T,j}-x_{T,\alpha})
+R_j,
\]

with

\[
|R_j|\le C h_T^2\operatorname{Lip}(\nabla v;T).
\]

The constant and linear terms cancel after multiplication by `A_r`. Since the
row sums of absolute values of the fixed matrix `A_r` are finite,

\[
|b_{T,\alpha}(I_T^r v)-v(x_{T,\alpha})|
\le C h_T^2\operatorname{Lip}(\nabla v;T).
\tag{3.1}
\]

This estimate is affine invariant; on a uniformly shape-regular family the
constant is uniform.

## 4. Localization of every negative coefficient

We prove that, for sufficiently large fixed `kappa` and sufficiently small
mesh size, a negative coefficient of `I_h^r u` can occur only on `R_h`.

### 4.1 Elements cut by the free boundary

If an element intersects `Gamma`, then its distance to `Gamma` is zero, hence it
belongs to `R_h`.

### 4.2 Contact-interior elements

If `T` lies in the interior of the contact set, then `u=0` on `T`. Therefore
`I_T^r u=0`, and every coefficient is zero.

### 4.3 Positive elements near the free boundary but outside `R_h`

Let `T` lie in the positive phase and outside `R_h`. Then

\[
\operatorname{dist}(T,\Gamma)>\kappa h_T.
\]

Every barycentric lattice point in `T` therefore satisfies

\[
d(x_{T,\alpha},\Gamma)>\kappa h_T.
\]

When `T` lies in the fixed quadratic-growth neighborhood, nondegeneracy gives

\[
u(x_{T,\alpha})\ge c_0\kappa^2 h_T^2.
\]

By (3.1),

\[
b_{T,\alpha}(I_T^r u)
\ge (c_0\kappa^2-C_1)h_T^2.
\]

Choose `kappa` so that `c_0 kappa^2 > 2 C_1`. Then every coefficient is
nonnegative.

### 4.4 Positive interior elements away from the tubular neighborhood

After removing a fixed neighborhood of `Gamma` and the physical boundary, the
remaining positive region is compactly contained in `{u>0}`. Hence `u` has a
strictly positive minimum `m_0` there.

In `d = 2,3`, the assumed broken `H^{r+1}` regularity with `r >= 1` gives a
continuous representative on each such element and the usual local nodal
interpolation estimates. More generally, this is where the condition
`r + 1 > d/2` is used. As `h -> 0`, the values of `u` at all lattice points of
one element become uniformly close to one another. The inverse collocation map
sends a constant value vector to the same constant coefficient vector because
its rows sum to one. Therefore every Bernstein coefficient is at least
`m_0/2` for sufficiently small `h`.

### 4.5 Positive physical-boundary elements

On a boundary face, every interpolation node lies on `partial Omega`, where
`u=0`; the corresponding face Bernstein coefficients are exactly zero.

For a fixed degree and a uniformly shape-regular simplex, every lattice point
not on that face has inward distance at least `c h_T` from the face. Under the
assumed inward linear-growth condition,

\[
u(x_{T,\alpha})\ge c_b h_T
\]

for every off-face lattice point. The uniform `C^{1,1}` boundary-collar bound
makes (3.1) available on these elements, so the coefficient discrepancy is only
`O(h_T^2)`. Thus every off-face coefficient is nonnegative for sufficiently
small `h`.

Together, these cases prove:

**Localization conclusion.** Every negative coefficient of `I_h^r u` is a
global degree of freedom incident to an element of `R_h`.

## 5. Two-sided coefficient bound on the one-ring patch

Every element of the fixed one-ring patch `omega_h` lies within distance
`C h_Gamma` of `Gamma`. For sufficiently small meshes the patch lies in the
quadratic-growth neighborhood. At every interpolation node in the patch,

\[
0\le u(x_{T,j})\le C h_\Gamma^2
\]

on the positive side, while `u=0` on the contact side. The inverse collocation
formula and the fixed row-sum bound of `A_r` imply

\[
|b_{T,\alpha}(I_T^r u)|\le C h_\Gamma^2
\qquad\text{for every }T\subset\omega_h.
\tag{5.1}
\]

This two-sided estimate is essential: it controls not only the negative part
that is clipped, but also the resulting repaired field on the contact set.

## 6. Conforming coefficient clipping

Represent `I_h^r u` by global Bernstein degrees of freedom `b_i`. Define

\[
\widetilde b_i=\max\{b_i,0\}
\]

once per global degree of freedom, and let `v_h^B` be the assembled field with
coefficients `tilde b_i`.

Because a shared face uses the same global coefficients from both neighboring
elements, clipping preserves common-face traces. Homogeneous physical-boundary
coefficients are zero and remain zero. Every local coefficient of `v_h^B` is
nonnegative, hence

\[
v_h^B\in K_h^B.
\]

Let

\[
d_h=v_h^B-I_h^r u.
\]

By localization, only degrees of freedom incident to `R_h` are changed. The
one-ring construction ensures that the support of every changed global basis
function is contained in `omega_h`. By (5.1), every changed coefficient has
magnitude at most `C h_Gamma^2`.

## 7. Three-halves scaling of the repair

On one locally quasi-uniform `d`-simplex in `omega_h`, finite-dimensional norm
equivalence on the reference simplex and affine scaling give

\[
\|d_h\|_{L^2(T)}^2
\le C h_\Gamma^{d+4},
\qquad
\|\nabla d_h\|_{L^2(T)}^2
\le C h_\Gamma^{d+2}.
\]

The patch-volume assumption and local quasi-uniformity imply that the number of
patch elements is at most

\[
C\frac{|\omega_h|}{h_\Gamma^d}
\le C h_\Gamma^{1-d}.
\]

Summing over the patch yields

\[
\|d_h\|_{L^2(\Omega)}^2\le C h_\Gamma^5,
\qquad
\|\nabla d_h\|_{L^2(\Omega)}^2\le C h_\Gamma^3.
\]

Therefore

\[
\|d_h\|_{H^1(\Omega)}\le C h_\Gamma^{3/2}.
\tag{7.1}
\]

The exponent is independent of the ambient dimension once the pointwise
interpolation and local regularity assumptions are valid, because the repair is
supported on a codimension-one patch of volume `O(h_Gamma)`.

## 8. Interpolation error outside and inside the patch

### 8.1 Bulk region

In `d = 2,3`, `r >= 1` makes the nodal interpolation well defined under the
assumed broken `H^{r+1}` regularity. More generally, assume the pointwise
interpolant is defined, for example `r + 1 > d/2`. The mesh-independent
one-sided extension near `Gamma`, together with the uniform broken
`H^{r+1}` bound away from the patch, gives the standard shape-regular
interpolation estimate

\[
\|u-I_h^r u\|_{H^1(\Omega\setminus\omega_h)}
\le C h^r.
\tag{8.1}
\]

Contact-interior elements contribute zero.

### 8.2 Interface patch

On `omega_h`, the `C^{1,1}` bound and local size `h_T comparable h_Gamma` give
on each element

\[
\|\nabla(u-I_T^r u)\|_{L^2(T)}
\le C h_\Gamma |T|^{1/2}\|D^2u\|_{L^\infty(T)}.
\]

After summation and use of `|omega_h| <= C h_Gamma`,

\[
\|u-I_h^r u\|_{H^1(\omega_h)}
\le C h_\Gamma^{3/2}.
\tag{8.2}
\]

The corresponding `L^2` contribution is of higher order.

Combining (7.1), (8.1), and (8.2), the feasible repaired interpolant satisfies

\[
\|u-v_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
\tag{8.3}
\]

## 9. Multiplier consistency

On the contact set, `u=0`. On a contact element in `omega_h`, every coefficient
of the repaired field is nonnegative and, by (5.1), bounded above by
`C h_Gamma^2`. The partition-of-unity property therefore gives

\[
0\le v_h^B\le C h_\Gamma^2
\qquad\text{on contact inside }\omega_h.
\]

Outside `omega_h`, the interpolant was already coefficient-feasible and equals
zero on contact-interior elements. Since `lambda` is nonnegative, bounded, and
supported on contact,

\[
0\le
\langle\lambda,v_h^B-u\rangle
=\int_{\{u=0\}}\lambda v_h^B
\le C\|\lambda\|_{L^\infty}
 h_\Gamma^2|\omega_h|
\le C h_\Gamma^3.
\tag{9.1}
\]

## 10. Transfer from feasible recovery to the discrete minimizer

For every feasible `v in K`, the multiplier identity gives

\[
J(v)-J(u)
=\tfrac12a(v-u,v-u)+\langle\lambda,v-u\rangle.
\tag{10.1}
\]

Apply this first to the discrete minimizer `u_h^B` and then to the feasible
recovery `v_h^B`. Discrete minimality gives

\[
J(u_h^B)-J(u)
\le J(v_h^B)-J(u).
\]

Because `u_h^B>=0` on the support of the nonnegative multiplier,

\[
\langle\lambda,u_h^B-u\rangle\ge0.
\]

Using coercivity, continuity, (8.3), and (9.1),

\[
\frac\alpha2\|u_h^B-u\|_{H^1}^2
\le
\frac M2\|v_h^B-u\|_{H^1}^2
+\langle\lambda,v_h^B-u\rangle
\]

and therefore

\[
\|u_h^B-u\|_{H^1}^2
\le C\bigl(h^{2r}+h_\Gamma^3\bigr).
\]

Taking square roots proves

\[
\boxed{
\|u-u_h^B\|_{H^1(\Omega)}
\le C\bigl(h^r+h_\Gamma^{3/2}\bigr).
}
\]

The same rate follows from the standard Falk inequality after inserting the
feasible recovery and the multiplier estimate (9.1).

## 11. Audit verdict for Panel C

- **C1 coefficient-to-value estimate:** PASS for fixed degree and fixed finite
  dimension on elements with the stated `C^{1,1}` control.
- **C2 local-size localization:** PASS under quadratic growth, sufficiently
  large fixed `kappa`, the far-interior compactness argument, and the explicit
  dimension/pointwise-interpolation scope.
- **C3 physical-boundary split:** PASS under the stated uniform `C^{1,1}`
  boundary-collar and inward linear-growth hypotheses, or a boundary-separating
  contact collar.
- **C4 two-sided risky coefficient amplitude:** PASS under the one-ring
  distance and local quasi-uniformity assumptions.
- **C5 global clipping:** PASS when clipping is performed once per shared global
  Bernstein degree of freedom.
- **C6 three-halves scaling:** PASS for isotropic, locally quasi-uniform,
  shape-regular interface patches with volume `O(h_Gamma)`.
- **C7 bulk and strip interpolation:** PASS in `d = 2,3` for `r >= 1`, or more
  generally when pointwise interpolation is well defined, under the
  mesh-independent one-sided extension and uniform broken regularity
  assumptions.
- **C8 multiplier and minimizer transfer:** PASS for a bounded nonnegative
  multiplier density supported on contact and a symmetric continuous coercive
  energy.

## 12. Claims deliberately not made

This theorem does not establish:

- the same rate at singular or degenerate free-boundary points;
- validity when `Gamma` meets `partial Omega` without a separate corner/contact
  analysis;
- nodal interpolation outside the stated dimension/regularity regime;
- physical-boundary coefficient positivity without the stated collar
  regularity and inward growth;
- anisotropic interface refinement without anisotropic norm and counting
  estimates;
- measure-valued multipliers;
- arbitrary nonexact obstacle shifts;
- optimal adaptive complexity;
- nonsymmetric or merely pseudomonotone operators.

Within the explicit assumptions above, the corrected
`h^r+h_Gamma^(3/2)` estimate is analytically closed. Independent mathematical
review and outside numerical reproduction remain external validation steps.
