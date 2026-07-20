# Sobolev/FEM closure note for the Bernstein obstacle theorem

## Purpose and trust status

This note closes the quantifier, diagonal-sequence, constant-dependence, and
energy-transfer details of the moving Sobolev finite-element argument.  It is a
mathematical proof document, not an independent endorsement.

- **Internal mathematical verdict:** PASS under the hypotheses stated below.
- **Machine-checked boundary:** the finite Bernstein, global clipping,
  projection/KKT, assembled finite-energy, abstract Mosco, and Hilbert-space VI
  layers are checked separately under the pinned Lean/mathlib toolchain.
- **Still requiring an outside report:** the physical Sobolev-space recovery
  construction, free-boundary geometry, and the sharp interface estimate in
  Sections 2--5 below.

The notation is sequence-indexed throughout so that no statement relies on an
ambiguous phrase such as “choose a diagonal as `h -> 0`.”

---

## 1. Sequence-indexed setting

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`.  Let

\[
\mathcal T_n,\qquad
h_n:=\max_{T\in\mathcal T_n}h_T\longrightarrow0,
\]

be conforming, uniformly shape-regular simplicial meshes.  Fix the polynomial
degree `r >= 1`.  Set

\[
V=H_0^1(\Omega),\qquad
K=\{v\in V:v\ge0\text{ a.e.}\},
\]

and let `V_n^r` be the continuous piecewise-`P_r` space with homogeneous
trace.  Define

\[
K_n^B
 =\{v_n\in V_n^r:
       b_{T,\alpha}(v_n)\ge0
       \text{ for every }T\in\mathcal T_n,\ |\alpha|=r\}.
\]

Let `a` be symmetric, continuous, and coercive:

\[
|a(v,w)|\le M\|v\|_V\|w\|_V,
\qquad
a(v,v)\ge\alpha\|v\|_V^2,
\]

and let `F in V'`.  Write

\[
J(v)=\frac12a(v,v)-F(v).
\]

The continuous and discrete minimizers are

\[
u=\operatorname*{argmin}_{v\in K}J(v),
\qquad
u_n^B=\operatorname*{argmin}_{v_n\in K_n^B}J(v_n).
\]

---

## 2. General Mosco convergence with an explicit recovery sequence

### Theorem 2.1

\[
K_n^B\xrightarrow{M}K
\quad\text{in }H_0^1(\Omega).
\]

Moreover, `u_n^B -> u` strongly in `H_0^1(Omega)`.

### Step 2.1: inner-cone inclusion

On each simplex the Bernstein basis is nonnegative and sums to one.  Hence
nonnegative Bernstein coefficients imply pointwise nonnegativity, and

\[
K_n^B\subset K.
\]

The use of shared physical face coefficients gives a conforming global
function.  Reversing the orientation of a face only permutes its Bernstein
multi-indices and does not change the trace polynomial.

### Step 2.2: nonnegative smooth density

For every `v in K`, choose `phi_m in C_c^infty(Omega)` with
`phi_m -> v` in `H_0^1`.  The positive-part map is continuous on `H^1`, so

\[
\phi_m^+\longrightarrow v^+=v
\quad\text{in }H^1.
\]

The support of `phi_m^+` is contained in the compact support of `phi_m`.
Convolve `phi_m^+` with a nonnegative mollifier whose radius is smaller than
its support distance to the boundary, and choose that radius so the `H^1`
change is at most `2^{-m-1}`.  After passing to a subsequence if needed, this
produces

\[
w_m\in C_c^\infty(\Omega),\qquad
w_m\ge0,\qquad
\|w_m-v\|_{H^1}\le2^{-m}.
\]

### Step 2.3: positive conforming Bernstein recovery

For a fixed smooth `w`, define on every `T in T_n`

\[
\mathcal B_T^r w
 =\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]

This construction has the following properties.

1. If `w >= 0`, every coefficient is nonnegative.
2. On a common face, the two elements use the same physical barycentric
   lattice points.  Their face coefficient arrays differ only by the vertex
   permutation induced by orientation, and therefore their traces agree.
3. At a physical boundary face, all face lattice points lie on the boundary.
   Since `w in C_c^infty(Omega)`, their sampled values are exactly zero; no
   “sufficiently fine mesh” qualification is needed for trace preservation.
4. The operator reproduces affine functions.

Uniform shape regularity and fixed-degree reference-element stability give a
constant `C_B=C_B(r,d,sigma)` such that

\[
\|w-\mathcal B_T^r w\|_{L^2(T)}
 \le C_B h_T^2|T|^{1/2}\|D^2w\|_{L^\infty(T)},
\]

\[
\|\nabla(w-\mathcal B_T^r w)\|_{L^2(T)}
 \le C_B h_T|T|^{1/2}\|D^2w\|_{L^\infty(T)}.
\]

After squaring and summing,

\[
\|w-\mathcal B_n^r w\|_{H^1(\Omega)}
 \le C(w,r,d,\sigma,\Omega)h_n.
\]

Thus `B_n^r w` is in `K_n^B` when `w >= 0`, and it converges strongly to `w`.

### Step 2.4: explicit diagonal choice

For each `m`, choose an integer `N_m` such that

\[
n\ge N_m
\quad\Longrightarrow\quad
\|\mathcal B_n^r w_m-w_m\|_{H^1}\le2^{-m}.
\]

Replace `N_m` by a strictly increasing majorant.  Define

\[
m(n)=\max\{m:N_m\le n\}
\]

for `n >= N_1`, and set

\[
v_n=\mathcal B_n^r w_{m(n)}.
\]

Then `m(n) -> infinity`, `v_n in K_n^B`, and

\[
\|v_n-v\|_{H^1}
 \le
 \|\mathcal B_n^r w_{m(n)}-w_{m(n)}\|_{H^1}
 +\|w_{m(n)}-v\|_{H^1}
 \le2^{1-m(n)}\longrightarrow0.
\]

This is the Mosco recovery sequence.

### Step 2.5: weak-limit condition

If `v_{n_j} in K_{n_j}^B` and `v_{n_j} weakly -> v` in `H_0^1`, then every
`v_{n_j}` belongs to `K`.  The cone `K` is norm closed and convex, hence
weakly closed.  Therefore `v in K`.

Steps 2.4 and 2.5 prove Mosco convergence.

### Step 2.6: direct strong convergence of minimizers

The inner-cone property gives a shorter proof than a subsequence argument.
For every `z in K`, the continuous variational inequality implies

\[
J(z)-J(u)
 =\frac12a(z-u,z-u)
  +a(u,z-u)-F(z-u)
 \ge\frac12a(z-u,z-u).
\]

Let `v_n in K_n^B` be the recovery sequence for `u`.  Discrete minimality and
`K_n^B subset K` yield

\[
\frac12\alpha\|u_n^B-u\|_V^2
 \le J(u_n^B)-J(u)
 \le J(v_n)-J(u)\longrightarrow0.
\]

Hence `u_n^B -> u` strongly.  This proof avoids a hidden extraction of
subsequences and avoids a separate “weak convergence plus norm convergence”
passage.

---

## 3. Local coefficient estimate and corrected risky set

Let `I_T^r` be barycentric-lattice Lagrange interpolation.  Let `A_r` be the
inverse reference Bernstein collocation matrix.  Affine reproduction gives

\[
\sum_j(A_r)_{\alpha j}=1,
\qquad
\sum_j(A_r)_{\alpha j}x_{T,j}=x_{T,\alpha}.
\]

Taylor expansion at `x_{T,alpha}` therefore cancels the constant and linear
terms.  For `q in C^{1,1}(T)`,

\[
|b_{T,\alpha}(I_T^rq)-q(x_{T,\alpha})|
 \le C_{\rm col}(r,d,\sigma)h_T^2
      \operatorname{Lip}(\nabla q;T).
\]

Now assume that the interior free boundary

\[
\Gamma=\partial\{u>0\}\cap\Omega
\]

is compact and regular, `u in C^{1,1}`, `u=grad u=0` on `Gamma`, and on the
positive side of a fixed tubular neighborhood

\[
c_0\operatorname{dist}(x,\Gamma)^2
 \le u(x)
 \le C_0\operatorname{dist}(x,\Gamma)^2.
\]

For each mesh define the genuinely local risky set

\[
\mathcal R_n
 =\{T\in\mathcal T_n:
     \operatorname{dist}(T,\Gamma)\le\kappa h_T\}.
\]

If `T` lies outside `R_n`, then either it is contained in the contact interior,
where `I_T^r u=0`, or it lies entirely in the positive phase.  In the latter
case every lattice point satisfies

\[
\operatorname{dist}(x_{T,\alpha},\Gamma)>\kappa h_T,
\]

and consequently

\[
u(x_{T,\alpha})\ge c_0\kappa^2h_T^2.
\]

Choosing `kappa` so that

\[
c_0\kappa^2
 > C_{\rm col}\operatorname{Lip}(\nabla u)
\]

makes every interpolant coefficient on such an element nonnegative.
Therefore every negative coefficient is attached to `R_n`, apart from the
separately stated physical-boundary case below.

### Physical boundary

Use either of the following explicit alternatives.

1. A contact collar separates the free-boundary analysis from the physical
   boundary; or
2. on each positive physical-boundary element there is a uniform inward
   linear lower bound.

In alternative 2, coefficients belonging to the boundary face are exactly
zero because the interpolated trace is zero.  An off-face degree-`r` lattice
point has opposite barycentric coordinate at least `1/r`; uniform shape
regularity therefore puts it at inward distance at least
`c_face(r,sigma) h_T`.  The linear lower bound is `Omega(h_T)` and dominates
the `O(h_T^2)` coefficient discrepancy once `h_T` is small.

---

## 4. Sharp feasible recovery and the three-halves exponent

Let `omega_n` be a fixed one-ring enlargement of `R_n`.  Assume there is a
scale `h_{Gamma,n} -> 0` such that

\[
c_m h_{\Gamma,n}\le h_T\le C_m h_{\Gamma,n}
\quad(T\subset\omega_n),
\qquad
|\omega_n|\le C_\Gamma h_{\Gamma,n}.
\]

Assume also:

- a mesh-independent one-sided `H^{r+1}` extension near `Gamma`;
- the uniform broken bound
  \[
  \sum_{T\not\subset\omega_n}|u|_{H^{r+1}(T)}^2
  \le C_{\rm reg};
  \]
- the boundary alternative from Section 3.

Every interpolation node in `omega_n` is at distance
`O(h_{Gamma,n})` from `Gamma`.  Quadratic upper growth on the positive side,
contact-side vanishing, and the fixed inverse collocation matrix give

\[
|b_{T,\alpha}(I_n^ru)|
 \le C_b h_{\Gamma,n}^2
\quad(T\subset\omega_n).
\]

Clip each assembled shared coefficient once:

\[
\widetilde b_i=\max\{b_i,0\},
\qquad
v_n^B=C_nI_n^ru,
\qquad
d_n=v_n^B-I_n^ru.
\]

Face conformity is unchanged, boundary-face zeros remain zero, and
`v_n^B in K_n^B`.  The correction is supported in `omega_n`.  Fixed-degree
norm equivalence and affine scaling give, elementwise,

\[
\|d_n\|_{L^2(T)}^2
 \le C|T|h_{\Gamma,n}^4,
\]

\[
\|\nabla d_n\|_{L^2(T)}^2
 \le C|T|h_T^{-2}h_{\Gamma,n}^4
 \le C|T|h_{\Gamma,n}^2.
\]

Summing by patch volume, rather than by an informal element count, gives

\[
\|d_n\|_{L^2(\Omega)}^2
 \le C h_{\Gamma,n}^5,
\qquad
\|\nabla d_n\|_{L^2(\Omega)}^2
 \le C h_{\Gamma,n}^3.
\]

Thus

\[
\|d_n\|_{H^1(\Omega)}
 \le C h_{\Gamma,n}^{3/2}.
\]

Outside `omega_n`, the broken regularity bound and standard interpolation give

\[
\|u-I_n^ru\|_{H^1(\Omega\setminus\omega_n)}
 \le C h_n^r.
\]

Inside `omega_n`, fixed-degree affine reproduction and `C^{1,1}` regularity
give a gradient error `O(h_{Gamma,n})`; multiplying by
`|omega_n|^{1/2}=O(h_{Gamma,n}^{1/2})` yields

\[
\|u-I_n^ru\|_{H^1(\omega_n)}
 \le C h_{\Gamma,n}^{3/2}.
\]

Consequently

\[
\boxed{
\|u-v_n^B\|_{H^1(\Omega)}
 \le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

The same scale follows from the independent positive-cutoff repair.  The
clipping proof is retained as the implementation-faithful construction.

---

## 5. Direct transfer of the sharp rate to the discrete minimizer

Define the obstacle multiplier by

\[
\langle\lambda,z\rangle=a(u,z)-F(z).
\]

Assume `lambda` is a nonnegative `L^infty` density supported on the contact
set.  For every `z in K`,

\[
J(z)-J(u)
 =\frac12a(z-u,z-u)+\langle\lambda,z-u\rangle.
\]

On contact outside `omega_n`, the interpolant and its clipping are zero.  On
contact inside `omega_n`, coefficient stability and the Bernstein convex-hull
property give

\[
0\le v_n^B\le C h_{\Gamma,n}^2.
\]

Therefore

\[
0\le
\langle\lambda,v_n^B-u\rangle
\le
C\|\lambda\|_{L^\infty}
 h_{\Gamma,n}^2|\omega_n|
\le C h_{\Gamma,n}^3.
\]

Using the direct inner-cone energy estimate from Step 2.6,

\[
\frac12\alpha\|u_n^B-u\|_V^2
\le J(u_n^B)-J(u)
\le J(v_n^B)-J(u).
\]

The recovery estimate and multiplier bound imply

\[
J(v_n^B)-J(u)
\le C\bigl(h_n^{2r}+h_{\Gamma,n}^3\bigr),
\]

and hence

\[
\boxed{
\|u_n^B-u\|_{H^1(\Omega)}
 \le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

This direct proof subsumes the same conclusion obtained from the separate Falk
argument and makes the sign convention for the multiplier explicit.

---

## 6. Constant-dependence ledger

The final constant is independent of `n`.  It may depend on

- fixed degree `r` and dimension `d`;
- the uniform mesh shape-regularity constant;
- `M` and `alpha` for the bilinear form;
- `c_0`, `C_0`, the tubular-neighborhood geometry, and
  `Lip(grad u)`;
- the one-sided extension and broken `H^{r+1}` bounds;
- `c_m`, `C_m`, `C_Gamma`, and the fixed ring depth;
- the physical-boundary growth constants when that alternative is used;
- `||lambda||_{L^infty}`.

It does not depend on the mesh index, element orientation, or the number of
interface elements.

---

## 7. Exact exclusions

The sharp estimate above does not claim coverage of

- singular or degenerate free-boundary points;
- a free boundary meeting the physical boundary without a separate corner
  analysis;
- anisotropic meshes without anisotropic inverse estimates;
- arbitrary inexact obstacles;
- measure-valued multipliers in place of an `L^infty` density;
- nonsymmetric operators;
- optimal adaptive complexity.

The general Mosco theorem and strong minimizer convergence do not require the
regular-free-boundary assumptions.

---

## 8. Reviewer verdict requested

A qualified external reviewer should return `PASS`,
`PASS AFTER STATED CORRECTION`, or `FAIL` separately for:

1. nonnegative smooth density;
2. face-permutation conformity and exact boundary trace preservation;
3. the explicit diagonal sequence;
4. the direct inner-cone minimizer estimate;
5. coefficient localization under the local-size risky set;
6. the physical-boundary split;
7. patch-volume derivation of the `3/2` exponent;
8. multiplier consistency and the final energy transfer.

Until such a report is posted, the accurate description is **internally
closed and reviewer-ready**, not **independently confirmed**.
