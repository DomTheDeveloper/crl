# Panel B proof map: Bernstein-cone Mosco convergence

## Exact claim under review

Let `Omega` be a bounded polyhedral Lipschitz domain and let
`(T_n)_{n>=1}` be a conforming, uniformly shape-regular simplicial mesh
sequence with

\[
h_n:=\max_{T\in\mathcal T_n}h_T\longrightarrow0.
\]

Fix the polynomial degree `r >= 1`. Let `V_n^r` be the conforming continuous
piecewise-`P_r` space with homogeneous trace and

\[
K_n^B=\{v_n\in V_n^r: b_{T,\alpha}(v_n)\ge0\ \forall T,\alpha\},
\qquad
K=\{v\in H_0^1(\Omega):v\ge0\text{ a.e.}\}.
\]

The claim is

\[
K_n^B\xrightarrow{M}K
\]

in `H_0^1(Omega)`. For a symmetric continuous coercive bilinear form and a
continuous linear load, the corresponding constrained minimizers converge
strongly in `H_0^1`.

The complete sequence-indexed proof, including the explicit diagonal and the
direct minimizer estimate, is in
`math/bernstein_obstacle/SOBOLEV_FEM_CLOSURE.md`.

## Dependency map

### B1. Inner-cone inclusion

On each simplex the Bernstein basis is nonnegative and sums to one. Therefore
coefficient nonnegativity implies pointwise nonnegativity. Shared face
coefficients give a conforming global function. Reversing a face orientation
only permutes the face multi-indices and leaves the physical trace polynomial
unchanged. This algebraic layer is formalized in Lean in:

- `Simplex.lean`;
- `SimplexPartition.lean`;
- `GlobalMesh.lean`.

**Failure criterion:** exhibit a point in an element at which a field with all
nonnegative local coefficients is negative, or a shared-face orientation for
which the global trace is discontinuous.

### B2. Positive smooth density

For every `v in K`, construct `w_m in C_c^infty(Omega)` with `w_m >= 0` and

\[
\|w_m-v\|_{H^1}\le2^{-m}.
\]

Start with `phi_m in C_c^infty` converging to `v`; use continuity of the
positive-part map in `H^1`; then mollify `phi_m^+` with a nonnegative kernel
whose radius is smaller than the distance of its compact support from the
boundary. The support of `phi_m^+` is contained in the support of `phi_m`, so
the inward mollification is legitimate.

**Failure criterion:** identify a domain assumption or positive-part/mollifier
step that does not give the stated `H_0^1` convergence.

### B3. Positive Bernstein recovery operator

For smooth `w >= 0`, define on each element

\[
\mathcal B_T^r w=\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]

All coefficients are nonnegative. Face lattice values coincide physically,
hence the piecewise field is conforming. Boundary-face lattice points lie on
the physical boundary, so for `w in C_c^infty(Omega)` their values are exactly
zero on every mesh; no eventual-fineness qualification is required for trace
preservation.

Affine reproduction and scaling give the dimension-safe estimate

\[
\|w-\mathcal B_T^r w\|_{L^2(T)}
 \le C h_T^2 |T|^{1/2}\|D^2w\|_{L^\infty(T)},
\]

\[
\|\nabla(w-\mathcal B_T^r w)\|_{L^2(T)}
 \le C h_T |T|^{1/2}\|D^2w\|_{L^\infty(T)}.
\]

Squaring and summing over the mesh gives

\[
\|w-\mathcal B_n^r w\|_{H^1(\Omega)}\le C_w h_n.
\]

**Failure criterion:** disprove global face conformity, exact boundary
preservation, affine reproduction, or the scaled fixed-degree estimate.

### B4. Explicit diagonal sequence

Choose the functions from B2. For every `m`, choose an increasing integer
`N_m` such that

\[
n\ge N_m
\quad\Longrightarrow\quad
\|\mathcal B_n^r w_m-w_m\|_{H^1}\le2^{-m}.
\]

Define

\[
m(n)=\max\{m:N_m\le n\},
\qquad
v_n=\mathcal B_n^r w_{m(n)}.
\]

Then `m(n) -> infinity`, `v_n in K_n^B`, and

\[
\|v_n-v\|_{H^1}\le2^{1-m(n)}\longrightarrow0.
\]

**Failure criterion:** show that `N_m` cannot be chosen, that `m(n)` does not
tend to infinity, or that the resulting sequence loses feasibility.

### B5. Weak-limit condition

Every `K_n^B` is contained in `K`. The cone `K` is norm closed and convex in
`H_0^1`, hence weakly closed. Therefore every weak limit of a feasible
subsequence belongs to `K`.

The abstract reduction

`mosco_of_recovery_of_subset_of_weaklyClosed`

is included in `MoscoTools.lean`.

**Failure criterion:** find a weakly convergent feasible sequence whose limit
is negative on a set of positive measure.

### B6. Direct strong convergence of minimizers

Let

\[
J(v)=\tfrac12a(v,v)-F(v),
\]

where `a` is symmetric, continuous, and coercive. For every `z in K`, the
continuous variational inequality gives

\[
J(z)-J(u)
=\tfrac12a(z-u,z-u)+a(u,z-u)-F(z-u)
\ge\tfrac12a(z-u,z-u).
\]

Let `v_n in K_n^B` recover `u`. Since `K_n^B subset K`, discrete minimality
gives the direct estimate

\[
\tfrac12\alpha\|u_n^B-u\|_{H^1}^2
\le J(u_n^B)-J(u)
\le J(v_n)-J(u)\longrightarrow0.
\]

This proves strong convergence without a subsequence extraction, a separate
weak-compactness argument, or an additional norm-convergence step. The
coordinate-free Hilbert-space VI/Pythagorean version is machine checked in the
separate Lean layer.

**Failure criterion:** identify a sign error in the energy identity, a failure
of `K_n^B subset K`, or a missing symmetry/coercivity/continuity assumption.

## Required reviewer verdict

For B1--B6, return one of:

- PASS;
- PASS AFTER STATED CORRECTION;
- FAIL, with a counterexample or exact missing theorem.

The report must separately state whether the general theorem is valid in all
finite dimensions and whether any step silently requires `d <= 3`.
