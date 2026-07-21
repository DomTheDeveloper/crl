# Bernstein–Bézier Inner-Cone Grand Theorem

## Operator-independent pointwise-feasible approximation of variational inequalities

**Status:** internally proved under the stated hypotheses; not yet independently
reviewed and not yet fully formalized in Lean.

This note upgrades the Bernstein obstacle result from a theorem about one
symmetric quadratic energy to an operator-independent approximation principle.
The Bernstein construction supplies the moving feasible sets.  Strong
monotonicity supplies stability.  Symmetry and the existence of an energy
functional are no longer required.

The main new conclusion is that the previously established regular-interface
rate

\[
\|u-u_n^B\|_{H^1(\Omega)}
 \le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr)
\]

survives for nonsymmetric linear and nonlinear strongly monotone obstacle
operators, provided the same solution regularity, multiplier, and geometric
recovery hypotheses hold.

---

## 1. Abstract setting

Let `V` be a real Hilbert space with dual `V*`.  Let `K` be a nonempty closed
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

Thus `A` is strongly monotone and Lipschitz.  It need not be linear,
symmetric, or the derivative of an energy.

Let `f in V*`.  Assume the standard existence hypotheses, for example
hemicontinuity of `A`.  Let `u in K` and `u_n in K_n` be the unique solutions
of

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

## 2. Grand inner-cone theorem

### Theorem 2.1 — Mosco convergence

The inclusion and recovery assumptions imply

\[
K_n\xrightarrow{M}K.
\]

### Proof

The strong recovery property is the Mosco limsup condition.  For the weak
liminf condition, let `w_{n_j} in K_{n_j}` converge weakly to `w`.  Since every
`K_{n_j}` is contained in `K`, and a norm-closed convex subset of a Hilbert
space is weakly closed, `w in K`.  ∎

### Theorem 2.2 — nonlinear Falk inequality for inner cones

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

Set `e_n=u_n-u`.  Strong monotonicity gives

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
Lab\le\frac\alpha2a^2+\frac{L^2}{2\alpha}b^2
\]

gives the squared-error estimate.  No symmetry is used.  ∎

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

This separates every convergence proof into exactly two concrete tasks:

1. build a pointwise-feasible recovery with norm error `O(rho_n)`;
2. prove that the continuous complementarity residual of that recovery is
   `O(rho_n^2)`.

The operator endgame is universal.

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
strong recovery for every member of `K`.  Therefore Theorems 2.1--2.2 apply
verbatim to `K_n^B`.

### Corollary 3.1 — operator-independent Bernstein convergence

Let `A:H_0^1(Omega)->H^{-1}(Omega)` be hemicontinuous, `alpha`-strongly
monotone, and `L`-Lipschitz.  Then the Bernstein coefficient-constrained
solutions converge strongly to the exact obstacle solution:

\[
\boxed{
u_n^B\to u\text{ in }H_0^1(\Omega).}
\]

This includes:

- symmetric variable-coefficient elliptic operators;
- nonsymmetric coercive linear operators;
- reaction-diffusion operators;
- strongly monotone quasilinear elliptic operators;
- coupled product-space systems with componentwise Bernstein inequalities,
  once the corresponding recovery property is supplied.

The theorem does not require an energy minimization formulation.

---

## 4. Nonzero obstacles by Bernstein majorants

Let `C={w in V:w>=0}` and let `psi in V`.  Define

\[
K_\psi=\psi+C
=\{v\in V:v\ge\psi\text{ a.e.}\}.
\]

Assume that `psi_n in V_n^r` satisfies

\[
\psi_n\ge\psi\quad\text{a.e.},
\qquad
\|\psi_n-\psi\|_V\to0.
\]

Define the coefficient-feasible translated cone

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

For `v=psi+w in K_psi`, choose `w_n in K_n^B` with `w_n->w`.  Then

\[
v_n=\psi_n+w_n\in K_{n,\psi_n}^B,
\qquad
v_n\to v.
\]

The inner-cone weak condition follows as before.  ∎

### Corollary 4.2 — exact polynomial obstacles

If the obstacle is represented exactly in every discrete space, take
`psi_n=psi`.  The method then gives exact pointwise enforcement of the
nonzero obstacle over every complete element, not merely at nodes or
quadrature points.

### Scope of the translation theorem

The simple translation statement assumes `psi in H_0^1(Omega)`, or more
generally that a fixed boundary lift has already reduced the admissible set to
a translate of the positive cone.  Obstacles with only `psi<=0` on the
boundary require a boundary-compatible majorant construction and are a
separate concrete recovery problem, not an obstruction to the abstract
theorem.

---

## 5. Grand regular-interface rate

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

The clipping recovery already constructed in the V4 theorem satisfies

\[
\|v_n^B-u\|_{H^1}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
\]

On contact inside the risky patch,

\[
0\le v_n^B-u\le Ch_{\Gamma,n}^2,
\]

and the patch has volume `O(h_{Gamma,n})`.  Thus

\[
R_u(v_n^B)
=\langle\lambda,v_n^B-u\rangle
\le C h_{\Gamma,n}^3.
\]

Set

\[
\rho_n=h_n^r+h_{\Gamma,n}^{3/2}.
\]

Since `h_{Gamma,n}^3 <= rho_n^2`, Corollary 2.4 gives the following.

### Theorem 5.1 — grand nonlinear/nonsymmetric sharp theorem

Let `A:H_0^1(Omega)->H^{-1}(Omega)` be hemicontinuous,
`alpha`-strongly monotone, and `L`-Lipschitz.  Under the corrected
regular-interface and multiplier hypotheses,

\[
\boxed{
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
}
\]

The constant depends on `alpha`, `L`, the mesh and free-boundary constants,
regularity bounds, and `||lambda||_{L^infinity}`, but not on the mesh index.

### What has been enlarged

The former sharp theorem assumed a symmetric coercive quadratic energy.  The
new proof removes:

- symmetry;
- linearity;
- the need for an energy functional;
- the metric-projection interpretation of the physical PDE.

The same geometric Bernstein repair controls the error for the entire strongly
monotone Lipschitz class.

---

## 6. Perturbed operators, quadrature, and solver-consistent data

Let `u_n^* in K_n` solve the exact discrete inequality for `(A,f)`.  Let
`u_n^delta in K_n` solve a perturbed inequality for `(A_n,f_n)`, where `A_n`
is `alpha_n`-strongly monotone.  Define

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

Set `d_n=u_n^delta-u_n^*`.  Strong monotonicity of `A_n`, followed by testing
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

Cancel `||d_n||` when nonzero.  ∎

### Corollary 6.2 — total grand error

If the exact Bernstein solution satisfies

\[
\|u-u_n^*\|_V\le C\rho_n,
\]

then

\[
\boxed{
\|u-u_n^\delta\|_V
\le C\rho_n+\frac{\epsilon_n}{\alpha_n}.
}
\]

This isolates the geometric Bernstein error from quadrature, coefficient,
assembly, or solver-data perturbations.  It is compatible with the modern
Strang–Falk framework for perturbed variational inequalities; the new
Bernstein contribution is the exact inner-cone recovery and its sharp
interface scale.

---

## 7. Unified theorem schema

The project can now be organized around one principle.

### Bernstein Inner-Cone Principle

Whenever a continuum inequality has a closed convex admissible set `K` and
Bernstein coefficient constraints produce discrete sets `K_n` satisfying

1. exact inner feasibility `K_n subset K`;
2. strong feasible recovery;
3. a quantitative recovery estimate;
4. a quantitative complementarity-residual estimate;

then:

- `K_n` Mosco-converges to `K`;
- every strongly monotone Lipschitz variational inequality is strongly stable;
- the discrete solution inherits the recovery rate;
- consistent operator/data perturbations add linearly through a separate
  Strang-type term.

The basis is therefore not tied to the Laplacian obstacle problem.  It is a
general mechanism for high-order exact pointwise inequalities.

---

## 8. Candidate applications

Subject to problem-specific recovery constructions, the theorem applies to:

1. variable-coefficient elliptic obstacle problems;
2. nonsymmetric coercive convection-diffusion obstacle problems;
3. strongly monotone quasilinear obstacle operators;
4. exactly represented nonzero polynomial obstacles;
5. vector-valued componentwise unilateral systems;
6. Signorini-type polynomial normal-gap constraints on curved faces;
7. quadrature-perturbed and approximately assembled variational inequalities;
8. adaptive nonnested shape-regular mesh sequences.

Items 5--6 require a separate proof that the relevant vector or trace feasible
sets have the strong recovery property.  They are consequences of the grand
operator theorem once that geometric obligation is discharged.

---

## 9. Literature and novelty boundary

The abstract facts that Mosco convergence stabilizes variational inequalities,
and that Falk/Strang estimates control perturbed inequalities, are classical.
Recent adjacent references include:

- L. Banz, M. Schönauer, A. Schröder,
  *Error estimates for perturbed variational inequalities of the first kind*,
  Calcolo 62 (2025), article 38, DOI `10.1007/s10092-025-00660-1`;
- L. Boccardo, M. A. Palladino, M. Picerni,
  *Mosco-convergence of convex sets and unilateral problems for differential
  operators with lower order terms having natural growth*, arXiv:2505.05899;
- R. H. Nochetto, E. Otárola, A. J. Salgado,
  *Convergence rates for the classical, thin and fractional elliptic obstacle
  problems*, Philos. Trans. R. Soc. A 373 (2015), 20140449.

The candidate new synthesis is the combination of:

- arbitrary-degree Bernstein coefficient inner cones;
- exact pointwise feasibility over complete simplices and curved faces;
- a concrete positive Mosco recovery;
- codimension-one clipping with the `3/2` interface scale;
- the operator-independent nonlinear Falk inequality above;
- preservation of the same sharp rate for nonsymmetric and nonlinear strongly
  monotone obstacle problems.

A targeted search did not locate this complete combination.  That is not a
proof of novelty.  A qualified numerical-analysis literature review remains
required before the result is advertised as new.

---

## 10. Trust boundary and next formal target

Internally completed here:

- the nonlinear inner-cone Falk inequality;
- strong convergence without symmetry;
- the abstract rate-transfer theorem;
- the translated nonzero-obstacle theorem;
- the nonsymmetric/nonlinear `h^r+h_Gamma^(3/2)` corollary;
- the same-cone operator/data perturbation estimate.

Still required:

- independent review of the proof and novelty boundary;
- concrete examples for a nonlinear operator and a nonsymmetric operator;
- a boundary-compatible majorant construction for general nonzero obstacles;
- extension of the Lean Hilbert VI layer from metric projections to strongly
  monotone operator VIs;
- separate trace-space recovery for the full vector Signorini theorem.

The accurate current description is:

> **A grand operator-independent theorem has been derived internally.  It
> strictly enlarges the previous symmetric obstacle theorem, but it is not yet
> independently confirmed or fully Lean-certified.**
