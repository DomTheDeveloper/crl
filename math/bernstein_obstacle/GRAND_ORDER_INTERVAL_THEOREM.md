# Bernstein–Bézier Grand Order-Interval Theorem

Status: **new analytical theorem candidate; internally derived, not independently verified**

Research branch: `research/bernstein-grand-order-interval`

This note extends the corrected scalar zero-obstacle theorem in two directions:

1. from one homogeneous obstacle in `H_0^1` to exact bilateral variable bounds in `W_0^{1,p}`;
2. from the isolated `h_Gamma^(3/2)` repair exponent to a general codimension–growth scaling law.

It deliberately does not alter the immutable v2 review target.

---

## 1. Setting

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`, let

\[
1<p<\infty,
\qquad X=W_0^{1,p}(\Omega),
\]

and fix a polynomial degree `r >= 1`.

Let `T_h` be a conforming uniformly shape-regular simplicial mesh family with
maximum diameter `h -> 0`, and set

\[
V_h^r=\{v_h\in C^0(\overline\Omega):
       v_h|_T\in\mathbb P_r(T),\ v_h|_{\partial\Omega}=0\}.
\]

Let the lower and upper obstacles satisfy

\[
\psi,\phi\in W^{2,\infty}(\Omega)\cap C(\overline\Omega),
\qquad \phi-\psi\ge \delta_g>0.
\]

Assume boundary clearance: there are a collar `U_partial` of the physical
boundary and `delta_b>0` such that

\[
\psi\le-\delta_b<0<\delta_b\le\phi
\qquad\text{on }U_{\partial}.
\]

Define the continuous order interval

\[
K_{\psi,\phi}
 =\{v\in X:\psi\le v\le\phi\text{ a.e.}\}.
\]

The boundary-clearance hypothesis is a clean sufficient condition ensuring
that the homogeneous trace lies strictly between the obstacles. It can later
be replaced by a compatible nonhomogeneous trace and a boundary lift.

---

## 2. Positive Bernstein sampling

For a sufficiently regular scalar function `w`, define elementwise

\[
\mathcal B_h^r w|_T
 =\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]

Because a physical barycentric lattice point on a shared face is the same
point from either adjacent element, the sampled face coefficients agree.
Hence `B_h^r w` is globally conforming.

For fixed degree and a uniformly shape-regular mesh family,

\[
\|\mathcal B_h^r w-w\|_{L^\infty(\Omega)}
 \le C_B h^2\|D^2w\|_{L^\infty(\Omega)},
\]

and, for every fixed smooth `w`,

\[
\|\mathcal B_h^r w-w\|_{W^{1,p}(\Omega)}\to0.
\]

If `w` vanishes in a boundary collar, then all Bernstein coefficients on every
boundary face vanish, so `B_h^r w` belongs to `V_h^r`.

---

## 3. Conservative discrete obstacles

Set

\[
E_\psi=C_B\|D^2\psi\|_{L^\infty},
\qquad
E_\phi=C_B\|D^2\phi\|_{L^\infty},
\]

and define

\[
\psi_h^+=\mathcal B_h^r\psi+E_\psi h^2,
\qquad
\phi_h^-=\mathcal B_h^r\phi-E_\phi h^2.
\]

The signs of the shifts are essential. They give the pointwise conservative
ordering

\[
\psi\le\psi_h^+,
\qquad
\phi_h^-\le\phi.
\]

For all sufficiently small `h`, the strict obstacle gap also gives

\[
\psi_h^+<\phi_h^-.
\]

Define the coefficient-order interval

\[
K_h^B=\left\{v_h\in V_h^r:
 b_{T,\alpha}(v_h-\psi_h^+)\ge0,
\quad
 b_{T,\alpha}(\phi_h^--v_h)\ge0
\quad\forall T,\alpha\right\}.
\]

The Bernstein convex-hull property immediately yields

\[
\psi\le\psi_h^+\le v_h\le\phi_h^-\le\phi
\quad\text{pointwise on every element}.
\]

Therefore

\[
K_h^B\subset K_{\psi,\phi}.
\]

This is stronger than nodal feasibility: every discrete function obeys both
variable obstacles at every point of the physical domain.

---

## 4. Strict smooth density lemma

### Lemma

Under the obstacle-gap and boundary-collar hypotheses, for every
`v in K_{psi,phi}` there are

\[
w_n\in W^{2,\infty}(\Omega)\cap W_0^{1,p}(\Omega)
\]

and numbers `eta_n>0` such that

\[
w_n\to v\quad\text{strongly in }W^{1,p}(\Omega),
\]

\[
\psi+\eta_n\le w_n\le\phi-\eta_n,
\]

and each `w_n` vanishes in a possibly `n`-dependent boundary collar.

### Proof map

1. Let `m=(psi+phi)/2`.
2. Choose a smooth cutoff `chi` equal to zero near the boundary and one away
   from the boundary collar.
3. The function `q=chi m` is in `W^{2,infinity} cap W_0^{1,p}`. In the collar,
   it is a convex combination of `0` and `m`; both lie a fixed positive
   distance from the two obstacle walls. Away from the collar, `q=m`.
   Consequently there is `eta_0>0` with
   `psi+eta_0 <= q <= phi-eta_0`.
4. Interiorize an arbitrary feasible `v` by
   `v_epsilon=(1-epsilon)v+epsilon q`. It has margin `epsilon eta_0`.
5. Approximate `v_epsilon` in `W_0^{1,p}` by compactly supported smooth
   functions.
6. Apply a Lipschitz pointwise retraction into the smaller interval
   `[psi+epsilon eta_0/2, phi-epsilon eta_0/2]`.
7. The retracted function is Lipschitz and zero in a boundary collar. Extend it
   by zero and mollify on a scale small enough to preserve half of the strict
   obstacle margin. This produces a `W^{2,infinity}` function satisfying the
   displayed strict inequalities.
8. Take a diagonal sequence as `epsilon -> 0`.

The only imported facts are density of `C_c^infinity(Omega)` in
`W_0^{1,p}`, Sobolev stability of Lipschitz compositions, and standard
mollification of a collar-supported Lipschitz function.

---

## 5. Grand order-interval Mosco theorem

### Theorem A

Under Sections 1–4,

\[
K_h^B\xrightarrow{M}K_{\psi,\phi}
\qquad\text{in }W_0^{1,p}(\Omega).
\]

That is:

1. if `v_h in K_h^B` and `v_h` converges weakly to `v` in `W_0^{1,p}`, then
   `v in K_{psi,phi}`;
2. for every `v in K_{psi,phi}` there is a sequence `v_h in K_h^B` converging
   strongly to `v` in `W_0^{1,p}`.

### Proof

#### Weak condition

Exact conservative feasibility gives `K_h^B subset K_{psi,phi}`.
The continuous order interval is norm closed and convex in `W_0^{1,p}`, hence
weakly closed. Every weak limit therefore remains in `K_{psi,phi}`.

#### Recovery condition

Fix `v in K_{psi,phi}` and choose the strict smooth approximation from the
lemma:

\[
\psi+\eta_n\le w_n\le\phi-\eta_n.
\]

For fixed `n`, put

\[
v_{h,n}=\mathcal B_h^r w_n.
\]

The Bernstein coefficient of `v_{h,n}-psi_h^+` at a lattice point is exactly

\[
w_n(x_{T,\alpha})-\psi(x_{T,\alpha})-E_\psi h^2
 \ge\eta_n-E_\psi h^2.
\]

Similarly,

\[
b_{T,\alpha}(\phi_h^--v_{h,n})
 \ge\eta_n-E_\phi h^2.
\]

Thus `v_{h,n} in K_h^B` whenever

\[
h^2\max(E_\psi,E_\phi)\le\eta_n.
\]

For each fixed `n`, positive Bernstein sampling converges strongly:

\[
v_{h,n}\to w_n\quad\text{in }W^{1,p}.
\]

Choose a diagonal index `n=n(h)` increasing slowly enough that both coefficient
margins remain nonnegative and

\[
\|v_{h,n(h)}-w_{n(h)}\|_{W^{1,p}}\to0.
\]

Since `w_n -> v`, the diagonal sequence is the required recovery sequence.

---

## 6. Uniformly convex energy transfer

### Theorem B

Let `J:X->R` satisfy:

1. coercivity;
2. sequential weak lower semicontinuity;
3. continuity under strong `W^{1,p}` convergence;
4. uniform convexity on bounded sets: for each bounded radius `R` there is a
   modulus `omega_R(t)>0` for `t>0` such that

\[
J\!\left(\frac{x+y}{2}\right)
 \le\frac{J(x)+J(y)}2-\omega_R(\|x-y\|_X)
\]

whenever `||x||,||y|| <= R`.

Let `u` minimize `J` over `K_{psi,phi}` and let `u_h` minimize `J` over
`K_h^B`. Then

\[
u_h\to u\quad\text{strongly in }W_0^{1,p}(\Omega),
\qquad
J(u_h)\to J(u).
\]

### Proof

Coercivity bounds the minimizers. Every weakly convergent subsequence has a
limit in `K_{psi,phi}` by Theorem A. Weak lower semicontinuity gives the
liminf inequality. Applying discrete minimality to a Mosco recovery sequence
for `u` gives the matching limsup inequality. Hence every weak cluster point
is the unique continuous minimizer and the energies converge. Uniform
convexity then upgrades weak convergence plus energy convergence to strong
convergence.

### Nonlinear PDE corollary

The theorem applies to

\[
J(v)=\int_\Omega F(x,\nabla v)\,dx-\langle f,v\rangle
\]

when `F` is Caratheodory, has coercive `p`-growth, and is uniformly convex in
the gradient variable. In particular it covers the bilateral obstacle problem
for the `p`-Dirichlet energy

\[
F(x,\xi)=\frac{a(x)}p|\xi|^p,
\qquad 0<a_0\le a(x)\le a_1.
\]

Thus the exact pointwise Bernstein coefficient method is not confined to
symmetric quadratic Hilbert energies.

---

## 7. Universal clipping-scaling theorem

The corrected `h_Gamma^(3/2)` proof contains a more general scaling law.

Let `omega_h` be a locally quasi-uniform patch with local diameter comparable
to `h_Gamma`, and suppose

\[
|\omega_h|\le C h_\Gamma^\kappa.
\]

Here `kappa=1` for a fixed-width layer around a codimension-one interface.
Suppose a conforming shared-coefficient correction `d_h` is supported in
`omega_h` and every corrected coefficient has amplitude at most

\[
C h_\Gamma^\beta.
\]

### Theorem C — codimension–growth law

For every `1 <= q < infinity`, fixed degree and a shape-regular locally
quasi-uniform patch,

\[
\|d_h\|_{L^q(\Omega)}
 \le C h_\Gamma^{\beta+\kappa/q},
\]

\[
\|\nabla d_h\|_{L^q(\Omega)}
 \le C h_\Gamma^{\beta-1+\kappa/q}.
\]

Consequently,

\[
\|d_h\|_{W^{1,q}(\Omega)}
 \le C h_\Gamma^{\beta-1+\kappa/q}
\]

whenever the gradient term is dominant.

### Proof

On each patch element, finite-dimensional norm equivalence on the reference
simplex and affine scaling give pointwise-size estimates

\[
|d_h|\lesssim h_\Gamma^\beta,
\qquad
|\nabla d_h|\lesssim h_\Gamma^{\beta-1}.
\]

Integrating these estimates over a set of measure `O(h_Gamma^kappa)` gives
exactly the displayed powers. No ambient-dimension factor remains after the
patch-volume estimate is inserted.

### Main specialization

For regular quadratic contact,

\[
\beta=2,
\qquad\kappa=1,
\]

so

\[
\|d_h\|_{W^{1,q}}
 \le C h_\Gamma^{1+1/q}.
\]

At `q=2`,

\[
1+\frac12=\frac32,
\]

which recovers the corrected Bernstein obstacle exponent.

The `3/2` rate is therefore the Hilbert member of a full Banach-scale family,
not an isolated numerical coincidence.

---

## 8. Conditional nonlinear free-boundary transfer law

Suppose an operator-specific Falk/Bregman estimate controls the discrete error
in `W^{1,q}` by:

1. the `q`-th power of the feasible recovery error; and
2. a multiplier consistency term.

If the contact amplitude is `O(h_Gamma^beta)` and the contact patch has volume
`O(h_Gamma^kappa)`, then a bounded multiplier density gives

\[
\langle\lambda,v_h-u\rangle
 \lesssim h_\Gamma^{\beta+\kappa}.
\]

Taking the `q`-root predicts the nonlinear interface exponent

\[
\rho(q,\beta,\kappa)
 =\min\left\{
 \beta-1+\frac\kappa q,
 \frac{\beta+\kappa}{q}
 \right\}.
\]

For quadratic hypersurface contact,

\[
\rho(q,2,1)
 =\min\left\{1+\frac1q,\frac3q\right\}.
\]

At `q=2`, both mechanisms coincide at `3/2`.

This section is a **conditional transfer principle**, not yet a claimed
p-Laplacian rate theorem. A full nonlinear result must audit the exact Bregman
coercivity/smoothness inequalities and the correct regular-free-boundary growth
law for the chosen quasilinear operator.

---

## 9. Relation to the corrected v2 theorem

Theorem A strictly extends the general Mosco layer from

- one zero obstacle;
- `H_0^1`;
- a symmetric quadratic minimizer;

to

- two spatially varying obstacles;
- exact everywhere feasibility using conservative coefficient obstacles;
- `W_0^{1,p}` for every `1<p<infinity`;
- arbitrary uniformly convex coercive energies, including nonlinear
  `p`-growth energies.

Theorem C explains and generalizes the sharp-interface repair exponent but does
not modify the already frozen v2 `H^1` theorem.

---

## 10. Collision and novelty boundary

Known neighboring results include:

1. abstract high-order bounds-satisfying variational inequalities and
   `W^{1,p}` approximation by the full set of bounds-constrained polynomials;
2. Bernstein coefficient bounds as a sufficient computational subset;
3. higher-order FEM for p-Laplacian obstacle problems;
4. hp/spectral obstacle methods using transformed GLL constraints and
   Glowinski convergence;
5. classical Mosco convergence for varying one- and two-obstacle sets.

The candidate contribution here is the combined theorem:

- conservative sampled obstacle envelopes;
- exact global bilateral feasibility from Bernstein coefficients;
- a direct Mosco recovery proof for that computable coefficient subset;
- nonlinear uniformly convex minimizer convergence;
- the codimension–growth clipping exponent.

No claim of literature-level novelty should be made until a specialist search
checks every component and combination.

---

## 11. Red-team checklist

The theorem must be narrowed or rejected if any of the following fails:

1. the global `L-infinity` Bernstein sampling estimate under the stated mesh
   and obstacle regularity;
2. conforming identification of physical shared-face lattice coefficients;
3. construction of the strict collar-supported density sequence;
4. preservation of the strict obstacle margin under retraction and
   mollification;
5. nonemptiness of `K_h^B` for all sufficiently small `h`;
6. exact conservative inequalities `psi <= psi_h^+` and
   `phi_h^- <= phi`;
7. strong `W^{1,p}` approximation of fixed smooth functions by positive
   Bernstein sampling on arbitrary shape-regular simplicial meshes;
8. the uniform-convexity upgrade from energy convergence to strong convergence;
9. local quasi-uniformity and patch-volume hypotheses in Theorem C;
10. any attempt to apply the conditional nonlinear rate without a separate
    Bregman and free-boundary audit.

---

## 12. Current verdict

- Theorem A: **complete candidate proof**, pending independent line-by-line
  audit of the strict smooth density lemma and sampling constants.
- Theorem B: **standard abstract transfer proved from Theorem A**.
- Theorem C: **complete finite-dimensional scaling proof**.
- Nonlinear sharp rate: **new scaling prediction only; operator-specific proof
  remains open**.
- Lean: **not formalized**. The existing finite Bernstein and Hilbert layers are
  reusable, but `W^{1,p}`, variable obstacle envelopes and moving physical
  spaces require new infrastructure.
