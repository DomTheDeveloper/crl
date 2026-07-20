# Publication proof: moving Bernstein finite-element cones

## Status and trust boundary

This note supplies the detailed analytical proof behind the general Mosco and
strong-minimizer convergence claims. It upgrades the earlier dependency map to a
line-by-line argument, including the moving finite-element spaces, positive
Sobolev recovery, the reference-simplex estimate, the diagonal construction,
and the energy argument.

This is an internal proof completion, not an independent expert endorsement.
The finite algebraic/Hilbert reductions are machine checked elsewhere in this
project; the concrete Sobolev and finite-element realization below remains a
human-readable analytical proof.

## 1. Setting

Let `Omega` be a bounded polyhedral Lipschitz domain in `R^d`, with arbitrary
fixed finite dimension `d >= 1`. Let `(T_n)` be a sequence of conforming
simplicial meshes of `Omega` satisfying

- uniform shape regularity;
- maximum element diameter `h_n -> 0`;
- a fixed polynomial degree `r >= 1`.

Let

\[
V=H_0^1(\Omega),
\qquad
V_n=\{v\in C^0(\overline\Omega):v|_T\in\mathbb P_r(T)
\text{ for every }T\in\mathcal T_n,\ v|_{\partial\Omega}=0\}.
\]

On every simplex `T`, write the degree-`r` Bernstein representation

\[
v|_T=\sum_{|\alpha|=r} b_{T,\alpha}(v)B_{T,\alpha}.
\]

Common-face coefficients are identified by the canonical permutation induced by
restriction to the shared face. Define

\[
K=\{v\in H_0^1(\Omega):v\ge 0\text{ a.e.}\},
\]

and

\[
K_n^B=\{v_n\in V_n:b_{T,\alpha}(v_n)\ge0
\text{ for every }T\in\mathcal T_n\text{ and }|\alpha|=r\}.
\]

## 2. Main theorem

**Theorem 2.1 (Mosco convergence of moving Bernstein cones).**
Under the assumptions above,

\[
K_n^B\xrightarrow{M}K
\qquad\text{in }H_0^1(\Omega).
\]

That is:

1. whenever `v_n in K_n^B` and `v_n` converges weakly to `v` in `H_0^1`, then
   `v in K`;
2. for every `v in K`, there exists `v_n in K_n^B` such that `v_n -> v`
   strongly in `H_0^1`.

**Theorem 2.2 (strong convergence of obstacle minimizers).**
Let `a:V x V -> R` be symmetric, continuous, and coercive:

\[
|a(v,w)|\le M\|v\|_V\|w\|_V,
\qquad
a(v,v)\ge\alpha\|v\|_V^2,
\]

and let `ell in V*`. Define

\[
J(v)=\tfrac12a(v,v)-\ell(v).
\]

Let `u` minimize `J` over `K`, and let `u_n` minimize `J` over `K_n^B`.
Then

\[
u_n\longrightarrow u
\qquad\text{strongly in }H_0^1(\Omega).
\]

## 3. Inner-cone inclusion

On a simplex, every Bernstein basis function is nonnegative and

\[
\sum_{|\alpha|=r}B_{T,\alpha}=1.
\]

Therefore, if all Bernstein coefficients of `v_n|_T` are nonnegative, then
`v_n(x) >= 0` for every `x in T`. The common-face coefficient identification
makes `v_n` globally conforming. Hence

\[
K_n^B\subset K
\qquad\text{for every }n.
\]

This proves the algebraic part of the Mosco weak-limit condition.

## 4. Positive smooth density in the Sobolev cone

**Lemma 4.1.** Nonnegative functions in `C_c^infinity(Omega)` are dense in `K`
with respect to the `H_0^1` norm.

**Proof.** Fix `v in K`. By the definition of `H_0^1`, choose
`phi_m in C_c^infinity(Omega)` with

\[
\phi_m\to v\quad\text{in }H_0^1(\Omega).
\]

The positive-part Nemytskii map

\[
P:H^1(\Omega)\to H^1(\Omega),
\qquad P(z)=z^+=\max\{z,0\},
\]

is continuous. Since `v=v^+`,

\[
z_m:=\phi_m^+\to v\quad\text{in }H_0^1(\Omega).
\]

Each `z_m` is nonnegative, belongs to `H_0^1`, and has compact support contained
in `supp(phi_m)`. Extend `z_m` by zero to `R^d`. Let `rho` be a nonnegative
standard mollifier and put `rho_epsilon(x)=epsilon^{-d}rho(x/epsilon)`.
Because `supp(z_m)` is compactly contained in `Omega`, choose `epsilon_m>0`
smaller than half its distance to `partial Omega` and also small enough that

\[
\|\rho_{\epsilon_m}*z_m-z_m\|_{H^1(\mathbb R^d)}<1/m.
\]

Then

\[
w_m:=\rho_{\epsilon_m}*z_m
\]

belongs to `C_c^infinity(Omega)`, is nonnegative because the mollifier is
nonnegative, and satisfies

\[
\|w_m-v\|_{H_0^1}
\le \|w_m-z_m\|_{H^1}+\|z_m-v\|_{H_0^1}\to0.
\]

This proves the lemma. `square`

No Sobolev embedding or point evaluation of an arbitrary `H^2` function is used
in this argument.

## 5. The positive Bernstein recovery operator

For `w in C^2(overline T)` define

\[
\mathcal B_T^r w
=\sum_{|\alpha|=r}w(x_{T,\alpha})B_{T,\alpha},
\]

where `x_{T,alpha}` is the barycentric lattice point with barycentric
coordinates `alpha/r`.

### 5.1 Positivity

If `w >= 0`, then every sampled coefficient is nonnegative, so

\[
\mathcal B_T^r w\ge0\quad\text{on }T.
\]

### 5.2 Affine reproduction

The multinomial first-moment identities give

\[
\sum_{|\alpha|=r}B_{T,\alpha}(x)=1,
\qquad
\sum_{|\alpha|=r}x_{T,\alpha}B_{T,\alpha}(x)=x.
\]

Consequently

\[
\mathcal B_T^r p=p
\qquad\text{for every affine }p.
\]

### 5.3 Face conformity

Let `F=T^+ cap T^-` be a common face. The restriction of a simplex Bernstein
basis to `F` consists exactly of the Bernstein basis functions whose multiindex
has zero component at the vertex opposite `F`. The physical lattice points on
`F` are the same from `T^+` and `T^-`, up to permutation of barycentric labels.
Thus the sampled face coefficients agree and

\[
(\mathcal B_{T^+}^r w)|_F=(\mathcal B_{T^-}^r w)|_F.
\]

The elementwise recovery therefore assembles to a function in the conforming
space `V_n`.

If `w in C_c^infinity(Omega)`, every lattice point on a physical boundary face
lies on `partial Omega`, where `w=0`. All boundary-face Bernstein coefficients
are therefore zero, so the assembled recovery has homogeneous trace.

### 5.4 Dimension-safe local estimate

**Lemma 5.1.** For fixed `r` and `d`, there is a constant `C=C(r,d,gamma)`,
where `gamma` is the mesh shape-regularity bound, such that

\[
\|w-\mathcal B_T^r w\|_{L^2(T)}
\le C h_T^2 |T|^{1/2}\|D^2w\|_{L^\infty(T)},
\]

and

\[
\|\nabla(w-\mathcal B_T^r w)\|_{L^2(T)}
\le C h_T |T|^{1/2}\|D^2w\|_{L^\infty(T)}.
\]

**Proof.** Map the reference simplex `hat T` affinely to `T` by
`F_T(hat x)=A_T hat x+b_T`, and let `hat w=w circ F_T`. On `hat T`, define

\[
\widehat E_r\hat w=\hat w-\widehat{\mathcal B}_r\hat w.
\]

The operator `widehat E_r` annihilates every affine polynomial. Fix a point
`hat x_0 in hat T` and let `p` be the first-order Taylor polynomial of `hat w`
at `hat x_0`. Taylor's theorem gives

\[
\|\hat w-p\|_{L^\infty(\hat T)}
+\|\nabla(\hat w-p)\|_{L^\infty(\hat T)}
\le C_{\hat T}\|D^2\hat w\|_{L^\infty(\hat T)}.
\]

Because the degree and dimension are fixed, the finitely many reference
Bernstein basis functions and their first derivatives are uniformly bounded.
Hence the sampled operator is bounded from `W^{1,infinity}(hat T)` to itself:

\[
\|\widehat{\mathcal B}_r q\|_{W^{1,\infty}(\hat T)}
\le C_{r,d}\|q\|_{L^\infty(\hat T)}.
\]

Using `widehat E_r p=0`,

\[
\|\widehat E_r\hat w\|_{L^2(\hat T)}
+\|\nabla\widehat E_r\hat w\|_{L^2(\hat T)}
\le C_{r,d}\|D^2\hat w\|_{L^\infty(\hat T)}.
\]

Affine scaling gives

\[
\|D^2\hat w\|_{L^\infty(\hat T)}
\le \|A_T\|^2\|D^2w\|_{L^\infty(T)},
\]

while gradients transform with `A_T^{-T}` and volumes with `|det A_T|`.
Uniform shape regularity implies

\[
\|A_T\|\lesssim h_T,
\qquad
\|A_T^{-1}\|\lesssim h_T^{-1},
\qquad
|\det A_T|\simeq |T|.
\]

Combining these estimates yields the two asserted inequalities. `square`

The use of `W^{2,infinity}` is deliberate and dimension independent. The proof
does not assert bounded point evaluation on `H^2`.

## 6. Strong recovery for a fixed smooth function

For `w in C_c^infinity(Omega)`, assemble

\[
\mathcal B_n^r w|_T=\mathcal B_T^r w.
\]

By positivity, conformity, and the boundary argument,

\[
\mathcal B_n^r w\in K_n^B
\qquad\text{whenever }w\ge0.
\]

Summing Lemma 5.1 over the mesh gives

\[
\|w-\mathcal B_n^r w\|_{L^2(\Omega)}^2
\le C h_n^4 |\Omega|\|D^2w\|_{L^\infty(\Omega)}^2,
\]

and

\[
\|\nabla(w-\mathcal B_n^r w)\|_{L^2(\Omega)}^2
\le C h_n^2 |\Omega|\|D^2w\|_{L^\infty(\Omega)}^2.
\]

Therefore

\[
\mathcal B_n^r w\to w
\qquad\text{strongly in }H_0^1(\Omega)
\]

for every fixed nonnegative `w in C_c^infinity(Omega)`.

## 7. Diagonal recovery for an arbitrary feasible Sobolev function

Fix `v in K`. By Lemma 4.1 choose nonnegative
`w_m in C_c^infinity(Omega)` such that

\[
\|w_m-v\|_{H_0^1}<1/m.
\]

For every fixed `m`, Section 6 gives an index `N_m` such that

\[
\|\mathcal B_n^r w_m-w_m\|_{H_0^1}<1/m
\qquad\text{for every }n\ge N_m.
\]

Replace `N_m` by the monotone sequence

\[
\widetilde N_m=\max_{1\le j\le m}N_j.
\]

Define

\[
m(n)=\max\{m:\widetilde N_m\le n\},
\]

with any harmless initial definition before the first threshold, and set

\[
v_n=\mathcal B_n^r w_{m(n)}.
\]

Then `m(n)->infinity`, `v_n in K_n^B`, and

\[
\|v_n-v\|_{H_0^1}
\le
\|\mathcal B_n^r w_{m(n)}-w_{m(n)}\|_{H_0^1}
+\|w_{m(n)}-v\|_{H_0^1}
\le \frac{2}{m(n)}\to0.
\]

This proves the Mosco recovery condition.

## 8. Weak-limit condition

The cone `K` is convex. It is also strongly closed in `H_0^1`: if `z_j -> z`
in `H_0^1`, then `z_j -> z` in `L^2`; after passage to a subsequence,
`z_j(x)->z(x)` almost everywhere, and nonnegativity passes to the limit.
A strongly closed convex subset of a Hilbert space is weakly closed.

Now suppose `v_n in K_n^B` and `v_n` converges weakly to `v` in `H_0^1`.
Section 3 gives `v_n in K`, and weak closedness gives `v in K`. This proves the
Mosco weak-limit condition and completes the proof of Theorem 2.1.

## 9. Strong convergence of the minimizers

Because `0 in K_n^B`, discrete minimality gives

\[
J(u_n)\le J(0)=0.
\]

Coercivity and dual boundedness imply

\[
\frac\alpha2\|u_n\|_V^2-\|\ell\|_{V^*}\|u_n\|_V\le0,
\]

so `(u_n)` is bounded in `V`. Let a subsequence converge weakly to `u_*`.
The Mosco weak-limit condition gives `u_* in K`.

Let `z_n in K_n^B` be a recovery sequence for the continuous minimizer `u`, so
`z_n -> u` strongly. Weak lower semicontinuity and discrete minimality give

\[
J(u_*)
\le\liminf_n J(u_n)
\le\limsup_n J(u_n)
\le\lim_n J(z_n)
=J(u).
\]

Since `u` is the unique minimizer of the strictly convex functional `J` over
`K`, one has `u_*=u`. Every weakly convergent subsequence has the same limit,
so the full sequence satisfies

\[
u_n\rightharpoonup u\quad\text{in }V,
\qquad
J(u_n)\to J(u).
\]

Weak convergence implies `ell(u_n)->ell(u)`. Therefore

\[
a(u_n,u_n)=2J(u_n)+2\ell(u_n)\to2J(u)+2\ell(u)=a(u,u).
\]

Also `a(u_n,u)->a(u,u)` by weak convergence. Hence

\[
a(u_n-u,u_n-u)
=a(u_n,u_n)-2a(u_n,u)+a(u,u)\to0.
\]

Coercivity yields

\[
\alpha\|u_n-u\|_V^2
\le a(u_n-u,u_n-u)\to0,
\]

which proves Theorem 2.2.

## 10. Constant dependence and dimension statement

The recovery constants depend only on

- the fixed degree `r`;
- the fixed finite dimension `d`;
- the uniform shape-regularity constant;
- the chosen reference simplex.

The theorem is valid in every fixed finite dimension. No step requires
`d <= 3`. The dimension-sensitive error found in an earlier draft is avoided by
applying point sampling only to smooth recovery functions and using a
`W^{2,infinity}` local estimate.

## 11. Audit verdict for Panel B

- **B1 inner-cone inclusion:** PASS.
- **B2 positive smooth density:** PASS.
- **B3 positive Bernstein recovery:** PASS under fixed degree and uniform shape
  regularity, with the `W^{2,infinity}` estimate stated above.
- **B4 diagonal sequence:** PASS.
- **B5 weak-limit condition:** PASS.
- **B6 strong convergence of minimizers:** PASS for symmetric continuous
  coercive quadratic energies and continuous linear loads.

The strongest theorem justified by this note is exactly Theorems 2.1 and 2.2.
The argument does not require free-boundary regularity and does not establish a
quantitative convergence rate. The separate `h^r+h_Gamma^(3/2)` theorem uses
additional interface, multiplier, regularity, grading, and physical-boundary
hypotheses and must remain separately scoped.
