# Panel B proof map: Bernstein-cone Mosco convergence

## Exact claim under review

Let `Omega` be a bounded polyhedral Lipschitz domain and let `T_h` be a
conforming, uniformly shape-regular simplicial mesh family with maximum
diameter tending to zero. Fix the polynomial degree `r >= 1`. Let `V_h^r` be
the conforming continuous piecewise-`P_r` space with homogeneous trace and

\[
K_h^B=\{v_h\in V_h^r: b_{T,\alpha}(v_h)\ge0\ \forall T,\alpha\},
\qquad
K=\{v\in H_0^1(\Omega):v\ge0\text{ a.e.}\}.
\]

The claim is

\[
K_h^B\xrightarrow{M}K
\]

in `H_0^1(Omega)`. For a symmetric continuous coercive bilinear form and a
continuous linear load, the corresponding constrained minimizers converge
strongly in `H_0^1`.

## Dependency map

### B1. Inner-cone inclusion

On each simplex the Bernstein basis is nonnegative and sums to one. Therefore
coefficient nonnegativity implies pointwise nonnegativity. Shared face
coefficients give a conforming global function. This algebraic layer is
formalized in Lean in:

- `Simplex.lean`;
- `SimplexPartition.lean`;
- `GlobalMesh.lean`.

**Failure criterion:** exhibit a point in an element at which a field with all
nonnegative local coefficients is negative, or a shared-face orientation for
which the global trace is discontinuous.

### B2. Positive smooth density

For every `v in K`, construct `w_m in C_c^infty(Omega)` with `w_m >= 0` and
`w_m -> v` in `H_0^1`:

1. approximate `v` by `phi_m in C_c^infty`;
2. use continuity of the positive-part map in `H^1` to obtain
   `phi_m^+ -> v`;
3. mollify `phi_m^+` with a nonnegative kernel, choosing the radius smaller
   than the distance from its support to the boundary.

**Failure criterion:** identify a domain assumption or positive-part/mollifier
step that does not give the stated `H_0^1` convergence.

### B3. Positive Bernstein recovery operator

For smooth `w >= 0`, define on each element

\[
\mathcal B_T^r w=\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha}.
\]

All coefficients are nonnegative. Face lattice values coincide, hence the
piecewise field is conforming. For compactly supported `w`, boundary-face
coefficients vanish for sufficiently fine meshes.

Affine reproduction and scaling give the dimension-safe estimate

\[
\|w-\mathcal B_T^r w\|_{L^2(T)}
 \le C h_T^2 |T|^{1/2}\|D^2w\|_{L^\infty(T)},
\]

\[
\|\nabla(w-\mathcal B_T^r w)\|_{L^2(T)}
 \le C h_T |T|^{1/2}\|D^2w\|_{L^\infty(T)}.
\]

Summation over a shape-regular mesh gives strong `H^1` convergence for each
fixed smooth recovery function.

**Failure criterion:** disprove global face conformity, boundary preservation,
affine reproduction, or the scaled fixed-degree estimate.

### B4. Diagonal sequence

Choose `w_m >= 0` smooth with `w_m -> v`. For every `m`, choose a mesh index
`N_m` such that the Bernstein recovery error is below `1/m` for all later mesh
indices. Use a monotone diagonal choice to define `v_h in K_h^B` and prove
`v_h -> v` strongly.

**Failure criterion:** show the diagonal sequence cannot be chosen on the
stated mesh family or does not remain feasible.

### B5. Weak-limit condition

Every `K_h^B` is contained in `K`. The cone `K` is norm closed and convex in
`H_0^1`, hence weakly closed. Therefore every weak limit of any feasible
subsequence belongs to `K`.

The abstract reduction

`mosco_of_recovery_of_subset_of_weaklyClosed`

is included in `MoscoTools.lean`.

**Failure criterion:** find a weakly convergent feasible sequence whose limit
is negative on a set of positive measure.

### B6. Strong convergence of minimizers

Use recovery for the limsup of energies, weak compactness/coercivity for
subsequences, weak lower semicontinuity for the liminf, and uniqueness of the
continuous minimizer. Energy convergence plus coercivity yields strong
convergence. An equivalent argument uses convergence of energy-metric
projections onto Mosco-converging closed convex sets.

**Failure criterion:** identify a missing compactness, lower-semicontinuity,
uniqueness, or coercivity assumption.

## Required reviewer verdict

For B1--B6, return one of:

- PASS;
- PASS AFTER STATED CORRECTION;
- FAIL, with a counterexample or exact missing theorem.

The report must separately state whether the general theorem is valid in all
finite dimensions and whether any step silently requires `d <= 3`.
