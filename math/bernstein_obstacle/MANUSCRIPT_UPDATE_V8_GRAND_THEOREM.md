# Manuscript Update V8: Bernstein coefficient inner cones for variational inequalities

## Proposed title

**Pointwise-Feasible Bernstein–Bézier Inner Cones for Variational Inequalities**

## Proposed subtitle

**Mosco recovery, regular-interface clipping, operator transfer, and nonlinear validation**

---

## Revised central claim

The paper should be framed around the **Bernstein coefficient inner cone**

\[
K_n^B
=\{v_n\in V_n^r:
  b_{T,\alpha}(v_n)\ge0\ \forall T,\alpha\}.
\]

The candidate contribution is not a new abstract theory of strongly monotone
variational inequalities. Céa/Falk estimates, nonlinear obstacle FEM,
nonsymmetric obstacle discretizations, and perturbation theory have substantial
prior literature.

The project-specific contribution is the proposed combination of:

1. assembled arbitrary-degree Bernstein coefficient constraints;
2. exact pointwise feasibility over every complete element or polynomial face;
3. a conforming positive recovery and Mosco convergence;
4. shared-coefficient clipping near a regular free boundary;
5. the codimension-one `h_Gamma^(3/2)` recovery scale;
6. transfer of that specific scale to strongly monotone nonsymmetric/nonlinear
   operators;
7. formalized finite, Hilbert, and operator-VI algebraic layers.

The Laplacian obstacle problem, curved Hertz contact, and the nonlinear
convection--reaction example are applications of the same admissible-set
technology.

---

## Proposed abstract

We study conforming high-order finite-element inner approximations of
unilateral constraint sets based on assembled Bernstein–Bézier coefficients.
Requiring every local Bernstein coefficient of the gap field to be
nonnegative guarantees pointwise feasibility over complete simplices and
polynomial faces, rather than only at interpolation or quadrature nodes. For
fixed polynomial degree on uniformly shape-regular simplicial meshes, we
construct positive conforming recovery sequences and prove Mosco convergence
of the coefficient-feasible sets.

Under a regular free boundary, quadratic gap growth, local interface grading,
and a bounded multiplier density, a conformity-preserving clipping repair
gives

\[
\|u-v_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr),
\qquad
\langle\lambda,v_n^B-u\rangle
\le Ch_{\Gamma,n}^3.
\]

Combining this Bernstein-specific recovery with classical strongly monotone
Falk/Céa stability yields the same solution rate for Lipschitz, strongly
monotone nonsymmetric and nonlinear variational inequalities. We also treat
translated cones for exactly represented or conformingly majorized nonzero
obstacles and isolate same-cone operator and data perturbations. A nonlinear
nonsymmetric manufactured example verifies coefficient feasibility, dual
feasibility, and complementarity to numerical precision. Pinned Lean
formalizations accompany the finite Bernstein, Hilbert-space, and
operator-inequality algebra, while the physical Sobolev and free-boundary
realization remains subject to independent analytical review.

---

## Main theorem sequence

### Theorem A — Bernstein coefficient-cone Mosco convergence

For fixed degree `r>=1` and conforming uniformly shape-regular simplicial
meshes,

\[
K_n^B\xrightarrow{M}
K=\{v\in H_0^1(\Omega):v\ge0\}.
\]

### Theorem B — Bernstein regular-interface recovery

Under the corrected regular-interface assumptions,

\[
\|u-v_n^B\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2}),
\]

and the complementarity residual is `O(h_Gamma^3)`.

### Theorem C — strongly monotone operator transfer

The classical inner-cone Falk/Céa inequality transfers Theorem B to

\[
\|u-u_n^B\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2})
\]

for hemicontinuous, strongly monotone, Lipschitz operators satisfying the
stated regularity and multiplier hypotheses.

### Theorem D — translated obstacles

For conforming obstacle majorants `psi_n>=psi` converging in the energy norm,

\[
\psi_n+K_n^B\xrightarrow{M}\psi+K.
\]

### Theorem E — perturbation separation

If `u_n^delta` uses a strongly monotone perturbed operator `A_n` and data
`f_n` over the same cone,

\[
\|u_n^\delta-u_n^*\|_V
\le
\frac{\|(A-A_n)u_n^*-(f-f_n)\|_{V^*}}{\alpha_n}.
\]

This is presented as a specialization of established Strang--Falk ideas.

---

## Required comparison section

The final paper must compare directly with:

- Gwinner's strongly monotone Céa estimate;
- Wang and Hafner on nonlinear/quasilinear obstacle FEM;
- Banz--Schröder on nonsymmetric hp obstacle FEM;
- Banz--Lamichhane--Stephan on higher-order p-Laplacian obstacle FEM;
- Banz--Schönauer--Schröder on perturbed first-kind VIs;
- Bekhouche--Benchettah's 2026 hp/spectral-element obstacle-cone method using
  transformed GLL constraints;
- Bernstein bounds-constrained approximation and positivity-limiter
  literature.

The central distinction to test is **assembled coefficientwise
complete-element feasibility plus clipping/interface analysis**, rather than
high order, nonlinearity, nonsymmetry, or cone convergence by themselves.

---

## Suggested architecture

1. Introduction and corrected novelty statement.
2. Bernstein coefficient inner cones and complete-element feasibility.
3. Face conformity and global shared coefficients.
4. Positive recovery and Mosco convergence.
5. Regular free-boundary localization and clipping.
6. The codimension-one `3/2` estimate.
7. Strongly monotone operator transfer as a corollary.
8. Nonzero obstacles and perturbations.
9. Linear Hertz and nonlinear nonsymmetric validations.
10. Formalization, reproduction, and trust boundary.
11. Detailed prior-art comparison.

---

## Claims to avoid

Do not claim:

- the first Céa/Falk estimate for strongly monotone VIs;
- the first nonlinear or nonsymmetric obstacle FEM;
- the first higher-order obstacle discretization;
- the first Mosco/Glowinski convergence theorem for high-order cones;
- that transformed GLL, nodal, biorthogonal, and Bernstein coefficient
  constraints are equivalent;
- that the full physical theorem is already Lean formalized;
- that a targeted search proves novelty;
- coverage of the general p-Laplacian under a global Lipschitz hypothesis;
- automatic majorants for arbitrary nonzero obstacles;
- completion of the full vector Signorini recovery.

---

## Strong but accurate significance statement

The work may be significant because it proposes a high-order inner-cone
technology that combines exact pointwise feasibility, conforming global
assembly, constructive recovery, and a quantitative free-boundary repair. The
same Bernstein geometry can then be reused across symmetric, nonsymmetric, and
nonlinear strongly monotone problems through established VI stability theory.

That significance remains conditional on successful pinned Lean checking of
the new bridge and qualified external confirmation of the physical proof and
novelty boundary.
