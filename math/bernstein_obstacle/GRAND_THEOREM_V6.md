# Bernstein–Bézier Inner-Cone Grand Theorem

## Operator-independent pointwise-feasible approximation of variational inequalities

**Status:** internally proved under the stated hypotheses; not yet independently
reviewed and not yet fully formalized in Lean.

This note upgrades the Bernstein obstacle result from a theorem about one
symmetric quadratic energy to an operator-independent approximation principle.
The Bernstein construction supplies the moving feasible sets. Strong
monotonicity supplies stability. Symmetry and the existence of an energy
functional are no longer required.

The strongly monotone Falk/Céa transfer mechanism used below is classical in
substance. The candidate project contribution is its combination with the
specific assembled Bernstein coefficient inner cones, exact complete-element
feasibility, positive recovery, conformity-preserving clipping, and the
codimension-one interface estimate.

The main new project conclusion is that the previously established
regular-interface rate

\[
\|u-u_n^B\|_{H^1(\Omega)}
 \le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr)
\]

survives for nonsymmetric linear and nonlinear strongly monotone obstacle
operators, provided the same solution regularity, multiplier, and geometric
recovery hypotheses hold.

---

## 1. Abstract setting

Let `V` be a real Hilbert space with dual `V*`. Let `K` be a nonempty closed
convex subset of `V`, and let `K_n` be nonempty closed convex subsets satisfying

\[
K_n\subset K.
\]

Assume the **strong recovery property**:

\[
\forall v\in K\quad
\exists v_n\in K_n\quad
\|v_n-v\|_V\longrightarrow0.
\]

Let `A : V -> V*` satisfy, for constants `alpha,L>0`,

\[
\langle A(w)-A(z),w-z\rangle
 \ge \alpha\|w-z\|_V^2,
\]

\[
\|A(w)-A(z)\|_{V^*}
 \le L\|w-z\|_V.
\]

Thus `A` is strongly monotone and Lipschitz. It need not be linear,
symmetric, or the derivative of an energy.

Let `f in V*`. Assume standard existence hypotheses, for example
hemicontinuity of `A`. Let `u in K` and `u_n in K_n` be the unique solutions of

\[
\langle A(u)-f,v-u\rangle\ge0
\qquad(v\in K),
\]

\[
\langle A(u_n)-f,v_n-u_n\rangle\ge0
\qquad(v_n\in K_n).
\]

Define the continuous residual

\[
R_u(w):=\langle A(u)-f,w-u\rangle
\qquad(w\in K).
\]

The variational inequality gives `R_u(w)>=0` for every feasible `w`.

---

## 2. Inner-cone theorem

### Theorem 2.1 — Mosco convergence

The inclusion and recovery assumptions imply

\[
K_n\xrightarrow{M}K.
\]

### Proof

The strong recovery property is the Mosco limsup condition. For the weak
liminf condition, let `w_{n_j} in K_{n_j}` converge weakly to `w`. Since every
`K_{n_j}` is contained in `K`, and a norm-closed convex subset of a Hilbert
space is weakly closed, `w in K`. ∎

### Theorem 2.2 — inner-cone Falk inequality

For every competitor `v_n in K_n`,

\[
\boxed{
\alpha\|u_n-u\|_V^2
\le
L\|u_n-u\|_V\,\|v_n-u\|_V
+R_u(v_n).
}
\]

Consequently,

\[
\boxed{
\|u_n-u\|_V^2
\le
\frac{L^2}{\alpha^2}\|v_n-u\|_V^2
+\frac{2}{\alpha}R_u(v_n).
}
\]

### Proof

Set `e_n=u_n-u`. Strong monotonicity gives

\[
\alpha\|e_n\|_V^2
\le
\langle A(u_n)-A(u),e_n\rangle.
\]

Because `u_n in K`, the continuous inequality gives

\[
\langle A(u)-f,e_n\rangle\ge0.
\]

Because `v_n in K_n`, the discrete inequality gives

\[
\langle A(u_n)-f,u_n-v_n\rangle\le0.
\]

Therefore

\[
\begin{aligned}
\alpha\|e_n\|_V^2
&\le
\langle A(u_n)-f,e_n\rangle
 -\langle A(u)-f,e_n\rangle\\
&\le
\langle A(u_n)-f,e_n\rangle\\
&=
\langle A(u_n)-f,u_n-v_n\rangle
 +\langle A(u_n)-f,v_n-u\rangle\\
&\le
\langle A(u_n)-f,v_n-u\rangle\\
&=
\langle A(u_n)-A(u),v_n-u\rangle
 +R_u(v_n)\\
&\le
L\|e_n\|_V\,\|v_n-u\|_V+R_u(v_n).
\end{aligned}
\]

Young's inequality

\[
Lab\le\frac\alpha2a^2+rac{L^2}{2\alpha}b^2
\]

gives the squared-error estimate. No symmetry is used. ∎

### Corollary 2.3 — strong convergence

If `v_n in K_n` is any recovery sequence for `u`, then

\[
u_n\longrightarrow u
\quad\text{strongly in }V.
\]

Indeed, `v_n -> u` and continuity of the fixed functional `A(u)-f` imply
`R_u(v_n)->0`.

### Corollary 2.4 — rate transfer principle

Suppose there is a scale `rho_n -> 0` and a feasible recovery `v_n in K_n`
such that

\[
\|v_n-u\|_V\le C_{\rm app}\rho_n,
\]

\[
R_u(v_n)\le C_{\rm res}\rho_n^2.
\]

Then

\[
\boxed{
\|u_n-u\|_V\le C\rho_n.
}
\]

This separates every convergence proof into two concrete tasks:

1. build a pointwise-feasible recovery with norm error `O(rho_n)`;
2. prove that the continuous complementarity residual of that recovery is
   `O(rho_n^2)`.

The operator endgame is reusable.

---

## 3. Bernstein–Bézier realization

Let

\[
V=H_0^1(\Omega),
\qquad
K=\{v\in V:v\ge0\text{ a.e.}\}.
\]

For fixed degree `r>=1` on conforming uniformly shape-regular simplicial
meshes, define

\[
K_n^B
=\{v_n\in V_n^r:
  b_{T,\alpha}(v_n)\ge0
  \text{ for every element and Bernstein index}\}.
\]

The Bernstein convex-hull property gives

\[
K_n^B\subset K.
\]

The positive smooth-density and positive Bernstein-sampling construction gives
strong recovery for every member of `K`. Therefore Theorems 2.1--2.2 apply to
`K_n^B`.

### Corollary 3.1 — operator-independent Bernstein convergence

Let `A:H_0^1(Omega)->H^{-1}(Omega)` be hemicontinuous, `alpha`-strongly
monotone, and `L`-Lipschitz. Then the Bernstein coefficient-constrained
solutions converge strongly to the exact obstacle solution:

\[
\boxed{
u_n^B\to u\text{ in }H_0^1(\Omega).}
\]

This covers, under the stated operator hypotheses:

- symmetric variable-coefficient elliptic operators;
- nonsymmetric coercive linear operators;
- reaction-diffusion operators;
- globally Lipschitz strongly monotone quasilinear operators;
- coupled product-space systems with componentwise Bernstein inequalities,
  once the corresponding recovery property is supplied.

The theorem does not require an energy minimization formulation.

---

## 4. Nonzero obstacles by Bernstein majorants

Let `C={w in V:w>=0}` and let `psi in V`. Define

\[
K_\psi=\psi+C
=\{v\in V:v\ge\psi\text{ a.e.}\}.
\]

Assume that `psi_n in V_n^r` satisfies

\[
\psi_n\ge\psi\quad\text{a.e.},
\qquad
\|ψ_n-ψ\|_V\to0.
\]

Define

\[
K_{n,\psi_n}^B
=
\{\psi_n+w_n:w_n\in K_n^B\}.
\]

### Theorem 4.1 — nonzero-obstacle Mosco theorem

\[
K_{n,\psi_n}^B\xrightarrow{M}K_\psi.
\]

### Proof

If `v_n=psi_n+w_n` with `w_n in K_n^B`, then

\[
v_n\ge\psi_n\ge\psi,
\]

so `K_{n,psi_n}^B subset K_psi`.

For `v=psi+w in K_psi`, choose `w_n in K_n^B` with `w_n->w`. Then

\[
v_n=\psi_n+w_n\in K_{n,\psi_n}^B,
\qquad
v_n\to v.
\]

The inner-cone weak condition follows as before. ∎

### Corollary 4.2 — exact polynomial obstacles

If the obstacle is represented exactly in every discrete space, take
`psi_n=psi`. The method then gives exact pointwise enforcement of the nonzero
obstacle over every complete element, not merely at nodes or quadrature points.

### Scope

The translation statement assumes `psi in H_0^1(Omega)`, or more generally
that a fixed boundary lift has reduced the admissible set to a translate of the
positive cone. Obstacles with only `psi<=0` on the boundary require a
boundary-compatible majorant construction.

---

## 5. Regular-interface operator-transfer theorem

Assume the corrected regular-interface hypotheses from the V4 theorem:

- a compact regular interior free boundary `Gamma`;
- `u in C^{1,1}` and `u=grad u=0` on `Gamma`;
- two-sided quadratic growth on the positive side;
- local risky set
  \[
  \mathcal R_n
  =\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
  \]
- a fixed-ring enlargement `omega_n` with
  \[
  c_mh_{\Gamma,n}\le h_T\le C_mh_{\Gamma,n},
  \qquad
  |\omega_n|\le C_\Gamma h_{\Gamma,n};
  \]
- a mesh-independent one-sided `H^{r+1}` extension;
- the uniform broken `H^{r+1}` bound outside `omega_n`;
- the corrected physical-boundary alternative;
- a multiplier
  \[
  \lambda=A(u)-f
  \]
  represented by a bounded nonnegative density supported on contact.

The clipping recovery satisfies

\[
\|v_n^B-u\|_{H^1}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
\]

On contact inside the risky patch,

\[
0\le v_n^B-u\le Ch_{\Gamma,n}^2,
\]

and `|omega_n|=O(h_{Gamma,n})`. Thus

\[
R_u(v_n^B)
=\langle\lambda,v_n^B-u\rangle
\le C h_{\Gamma,n}^3.
\]

Set

\[
\rho_n=h_n^r+h_{\Gamma,n}^{3/2}.
\]

Since `h_{Gamma,n}^3 <= rho_n^2`, Corollary 2.4 gives:

### Theorem 5.1 — Bernstein regular-interface operator-transfer theorem

Let `A:H_0^1(Omega)->H^{-1}(Omega)` be hemicontinuous,
`alpha`-strongly monotone, and `L`-Lipschitz. Under the corrected
regular-interface and multiplier hypotheses,

\[
\boxed{
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

The constant depends on `alpha`, `L`, the mesh and free-boundary constants,
regularity bounds, and `||lambda||_{L^infinity}`, but not on the mesh index.

The extension removes symmetry, linearity, the need for an energy functional,
and the metric-projection interpretation from the previous project theorem.
It does not claim to be the first nonlinear or nonsymmetric high-order obstacle
estimate in the literature.

---

## 6. Perturbed operators, quadrature, and data

Let `u_n^* in K_n` solve the exact discrete inequality for `(A,f)`. Let
`u_n^delta in K_n` solve a perturbed inequality for `(A_n,f_n)`, where `A_n`
is `alpha_n`-strongly monotone. Define

\[
\epsilon_n
=
\|(A-A_n)u_n^*-(f-f_n)\|_{V^*}.
\]

### Theorem 6.1 — same-cone perturbation bound

\[
\boxed{
\|u_n^\delta-u_n^*\|_V
\le\frac{\epsilon_n}{\alpha_n}.
}
\]

### Proof

Set `d_n=u_n^delta-u_n^*`. Strong monotonicity of `A_n`, followed by testing
the two variational inequalities against one another, gives

\[
\begin{aligned}
\alpha_n\|d_n\|_V^2
&\le
\langle A_nu_n^\delta-A_nu_n^*,d_n\rangle\\
&\le
\langle (A-A_n)u_n^*-(f-f_n),d_n\rangle\\
&\le
\epsilon_n\|d_n\|_V.
\end{aligned}
\]

Cancel `||d_n||` when nonzero. ∎

### Corollary 6.2 — total error

If

\[
\|u-u_n^*\|_V\le C\rho_n,
\]

then

\[
\boxed{
\|u-u_n^\delta\|_V
\le C\rho_n+rac{\epsilon_n}{\alpha_n}.
}
\]

This is a project specialization of established Strang--Falk perturbation
ideas. Its role is to separate Bernstein geometry error from quadrature,
coefficient, assembly, or load error.

---

## 7. Bernstein inner-cone principle

Whenever Bernstein coefficient constraints produce discrete feasible sets
`K_n` satisfying

1. exact inner feasibility `K_n subset K`;
2. strong feasible recovery;
3. a quantitative recovery estimate;
4. a quantitative complementarity-residual estimate;

then the classical monotone-VI stability machinery yields:

- Mosco convergence of the feasible sets;
- strong convergence of strongly monotone Lipschitz VI solutions;
- inheritance of the concrete recovery rate;
- a separate perturbation term for consistent operator/data errors.

The candidate new content is the Bernstein realization of items 1--4,
especially the clipping and interface scale.

---

## 8. Candidate applications

Subject to problem-specific recovery and regularity inputs:

1. variable-coefficient elliptic obstacle problems;
2. nonsymmetric coercive convection-diffusion obstacle problems;
3. globally Lipschitz strongly monotone quasilinear obstacle operators;
4. exactly represented nonzero polynomial obstacles;
5. vector-valued componentwise unilateral systems;
6. Signorini-type polynomial normal-gap constraints on curved faces;
7. quadrature-perturbed and approximately assembled variational inequalities;
8. adaptive nonnested shape-regular mesh sequences.

Items 5--6 require separate vector or trace feasible-recovery proofs.

---

## 9. Literature and novelty boundary

The following are classical or established neighboring results:

- strongly monotone Céa/Falk estimates;
- Mosco/Glowinski stability of variational inequalities;
- nonlinear and nonsymmetric higher-order obstacle FEM;
- Strang--Falk perturbation estimates;
- Bernstein convex-hull bounds.

The closest current neighboring work includes the 2026 hp/spectral-element
obstacle-cone paper of Bekhouche and Benchettah, which uses transformed
Gauss--Legendre--Lobatto point constraints and proves high-order cone
convergence. The present project must distinguish assembled coefficientwise
complete-element feasibility from pointwise GLL enforcement.

The candidate new synthesis is:

- arbitrary-degree assembled Bernstein coefficient inner cones;
- exact pointwise feasibility over complete simplices and polynomial faces;
- a concrete positive Mosco recovery;
- conformity-preserving codimension-one clipping;
- the `h_Gamma^(3/2)` recovery and multiplier scales;
- transfer of that specific rate to strongly monotone operators.

A targeted search did not establish whether this complete combination is new.
Qualified independent prior-art review remains required.

---

## 10. Trust boundary

Internally completed:

- the inner-cone operator estimate and rate composition;
- the translated nonzero-obstacle theorem;
- the strongly monotone operator-transfer corollary;
- the same-cone perturbation estimate;
- an explicit nonlinear nonsymmetric benchmark.

Still required:

- successful pinned Lean compilation and axiom audit for the V6 bridge;
- qualified independent review of the physical analytical theorem;
- independent novelty review;
- multidimensional nonlinear benchmark or clean-room reproduction;
- boundary-compatible majorants for general nonzero obstacles;
- separate trace-space recovery for a full vector Signorini theorem.

The accurate description is:

> **The project has derived an internally complete operator-transfer theorem
> built on the Bernstein coefficient-cone recovery. Its strongest candidate
> novelty is the exact-feasibility/clipping/interface-rate package, not the
> classical abstract monotone-VI estimate.**
