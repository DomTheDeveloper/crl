# Convex-target Sobolev density and Bernstein recovery proof

Date: 2026-07-20

Status: **complete analytical lemma under the stated Lipschitz-domain and positive-sampling hypotheses; not yet formalized in Lean**

## Theorem

Let `Omega subset R^d` be a bounded Lipschitz domain, let `1<p<infinity`, and
let `C subset R^m` be nonempty, closed and convex with `0 in C`. Define

\[
K_C=\{u\in W_0^{1,p}(\Omega;\mathbb R^m):u(x)\in C\text{ a.e.}\}.
\]

Then the set

\[
C_c^\infty(\Omega;\mathbb R^m)\cap K_C
\]

is dense in `K_C` in `W^{1,p}`.

If, in addition, a fixed-degree conforming Bernstein sampling operator
`B_h^r` satisfies

1. global conformity from shared barycentric lattice samples;
2. homogeneous boundary preservation for compactly supported inputs;
3. `B_h^r w -> w` in `W^{1,p}` for every smooth compactly supported `w`;

then the Bernstein coefficient inner sets

\[
K_{h,C}^B
=
\{v_h: b_{T,\alpha}(v_h)\in C\text{ for every complete coefficient}\}
\]

satisfy the strong recovery half of Mosco convergence.

---

## 1. Zero extension

Take `u in K_C`. Since `u in W_0^{1,p}(Omega)`, its extension by zero,
written `Eu`, belongs to `W^{1,p}(R^d;R^m)`. Because `0 in C`,

\[
Eu(x)\in C\qquad\text{for a.e. }x\in\mathbb R^d.
\]

No projection or nonlinear retraction is needed.

---

## 2. Boundary cutoff

Let

\[
d(x)=\operatorname{dist}(x,\partial\Omega).
\]

Choose a Lipschitz scalar cutoff `chi_delta` satisfying

\[
0\le\chi_\delta\le1,
\]

\[
\chi_\delta=0\quad\text{when }d(x)\le\delta,
\]

\[
\chi_\delta=1\quad\text{when }d(x)\ge2\delta,
\]

and

\[
|\nabla\chi_\delta|\le C/\delta.
\]

Set

\[
u_\delta=\chi_\delta u.
\]

Since

\[
\chi_\delta(x)y
=(1-\chi_\delta(x))0+\chi_\delta(x)y,
\]

convexity and `0 in C` imply

\[
u_\delta(x)\in C\quad\text{a.e.}
\]

The support of `u_delta` has positive distance from the boundary.

---

## 3. Strong convergence of the cutoff

The `L^p` term satisfies

\[
\|u_\delta-u\|_{L^p}^p
\le
\int_{\{d<2\delta\}}|u|^p\to0
\]

by absolute continuity of the integral.

For the gradient,

\[
\nabla(u_\delta-u)
=(\chi_\delta-1)\nabla u+u\otimes\nabla\chi_\delta.
\]

The first term converges to zero in `L^p`, again by absolute continuity.
For the second term, on the support of `grad chi_delta` one has
`delta <= d(x) <= 2 delta`, and therefore

\[
|u|^p|\nabla\chi_\delta|^p
\le
C\frac{|u|^p}{\delta^p}
\le
C'\frac{|u|^p}{d(x)^p}.
\]

The Hardy inequality on bounded Lipschitz domains gives

\[
\int_\Omega\frac{|u(x)|^p}{d(x)^p}\,dx
\le C_H\|\nabla u\|_{L^p}^p<\infty.
\]

Since the support strip `{delta<d<2 delta}` shrinks to the boundary, absolute
continuity yields

\[
\|u\otimes\nabla\chi_\delta\|_{L^p}\to0.
\]

Consequently,

\[
\boxed{u_\delta\to u\quad\text{strongly in }W^{1,p}.}
\]

This is the reason for cutting off before mollification.

---

## 4. Interior mollification

For fixed `delta`, extend `u_delta` by zero and let `rho_epsilon` be a
nonnegative standard mollifier with

\[
0<\varepsilon<\tfrac12
\operatorname{dist}(\operatorname{supp}u_\delta,\partial\Omega).
\]

Define

\[
w_{\delta,\varepsilon}
=\rho_\varepsilon*u_\delta.
\]

Then

\[
w_{\delta,\varepsilon}
\in C_c^\infty(\Omega;\mathbb R^m).
\]

For every `x`, the mollified value is a Bochner barycenter of `C`-valued
points:

\[
w_{\delta,\varepsilon}(x)
=
\int\rho_\varepsilon(y)u_\delta(x-y)\,dy.
\]

Closed convex sets contain such barycenters. Hence

\[
w_{\delta,\varepsilon}(x)\in C.
\]

For fixed `delta`, standard mollification gives

\[
w_{\delta,\varepsilon}\to u_\delta
\quad\text{in }W^{1,p}
\qquad(\varepsilon\downarrow0).
\]

Choose `delta_j downarrow 0` and then choose `epsilon_j` so that

\[
\|w_{\delta_j,\varepsilon_j}-u_{\delta_j}\|_{W^{1,p}}
\le 2^{-j}.
\]

Then

\[
\boxed{
w_j:=w_{\delta_j,\varepsilon_j}
\in C_c^\infty(\Omega;\mathbb R^m)\cap K_C,
\qquad
w_j\to u\text{ in }W^{1,p}.}
\]

---

## 5. Positive Bernstein recovery

For fixed `j`, define the degree-`r` elementwise Bernstein sampling polynomial
by its barycentric lattice values:

\[
(\mathcal B_h^r w_j)|_T
=
\sum_{|\alpha|=r}
w_j(x_{T,\alpha})B_{T,\alpha}.
\]

Every coefficient belongs to `C`. Since the basis is nonnegative and sums to
one, every element value belongs to `C`.

Shared face lattice points coincide geometrically. Assigning each shared sample
once gives a conforming global field. For sufficiently small `h`, all boundary
coefficient points lie in the collar where `w_j=0`; hence the homogeneous trace
is preserved.

By the assumed fixed-degree positive-sampling estimate,

\[
\|\mathcal B_h^r w_j-w_j\|_{W^{1,p}}\to0
\qquad(h\to0).
\]

Choose a decreasing mesh threshold `h_j` so that whenever `h<=h_j`,

\[
\|\mathcal B_h^r w_j-w_j\|_{W^{1,p}}\le2^{-j}.
\]

Choose a stage map `j(h)->infinity` with `h<=h_{j(h)}` and define

\[
v_h=\mathcal B_h^r w_{j(h)}.
\]

Then

\[
v_h\in K_{h,C}^B
\]

and

\[
\|v_h-u\|_{W^{1,p}}
\le
2^{-j(h)}+
\|w_{j(h)}-u\|_{W^{1,p}}
\to0.
\]

This proves the strong recovery condition.

---

## 6. Mosco conclusion

The exact convex-hull certificate gives

\[
K_{h,C}^B\subset K_C.
\]

The set `K_C` is norm closed and convex and hence weakly closed. Therefore weak
limits of coefficient-feasible sequences remain feasible. Combining this with
the recovery sequence proves

\[
\boxed{K_{h,C}^B\xrightarrow{M}K_C.}
\]

---

## 7. Limitations and variants

1. For nonzero boundary data, use a compatible `C`-valued lifting and translate
   the constraint.
2. If `0 notin C`, scalar cutoff does not necessarily preserve `C`; a lifting or
   a fixed interior anchor is required.
3. On non-Lipschitz domains, the Hardy/cutoff argument requires replacement.
4. For changing spatial targets `C(x)`, convolution does not preserve the
   constraint without additional regularity and retraction estimates.
5. The positive-sampling convergence estimate must be uniform over the mesh
   family and is a separate finite-element approximation lemma.
6. The proof establishes recovery for a fixed finite-dimensional target space
   `R^m`; infinite-dimensional Bochner-valued variants require additional
   measurability and integration hypotheses.
