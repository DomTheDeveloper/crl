# Manuscript Update V8: Bernstein inner cones for strongly monotone variational inequalities

## Proposed title

**Pointwise-Feasible Bernstein–Bézier Inner Cones for Strongly Monotone Variational Inequalities**

## Proposed subtitle

**Mosco convergence, nonlinear Falk estimates, sharp free-boundary recovery,
and perturbation stability**

---

## Revised central claim

The paper should no longer be framed primarily as a new discretization of the
Laplacian obstacle problem.  The stronger mathematical object is the
**Bernstein inner cone**:

\[
K_n^B
=\{v_n\in V_n^r:
  b_{T,\alpha}(v_n)\ge0\ \forall T,\alpha\}.
\]

Its role is operator independent:

1. coefficient nonnegativity gives exact pointwise feasibility;
2. positive Bernstein sampling gives Mosco recovery;
3. clipping gives a quantitative regular-interface recovery;
4. strongly monotone VI stability transfers recovery estimates to solutions.

The Laplacian obstacle problem and Hertz contact become principal
applications rather than the limits of the theorem.

---

## Proposed abstract

We introduce conforming high-order finite-element inner approximations of
unilateral constraint sets based on Bernstein–Bézier coefficients.  Requiring
all local Bernstein coefficients of the gap field to be nonnegative guarantees
pointwise feasibility over complete simplices and curved polynomial faces,
not merely at interpolation or quadrature nodes.  For fixed polynomial degree
on uniformly shape-regular simplicial meshes, we construct positive conforming
recovery sequences and prove Mosco convergence of the Bernstein feasible sets.

We establish an operator-independent Falk inequality for strongly monotone
Lipschitz variational inequalities.  Consequently, Bernstein-constrained
solutions converge strongly for nonsymmetric linear and nonlinear operators,
without assuming an energy functional.  Under a regular free boundary,
quadratic gap growth, local interface grading, and a bounded multiplier
density, a conformity-preserving clipping repair gives

\[
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
\]

The same rate holds throughout the strongly monotone Lipschitz class.  We also
prove translated-cone convergence for exactly represented or conformingly
majorized nonzero obstacles and a same-cone perturbation estimate separating
geometric discretization error from quadrature and operator approximation.
The finite Bernstein, clipping, and Hilbert-space layers are accompanied by
pinned Lean formalizations, while the physical Sobolev and free-boundary
realization is presented for independent analytical review.

---

## Main theorem sequence

### Theorem A — Bernstein-cone Mosco convergence

For fixed degree `r>=1` and a conforming uniformly shape-regular simplicial
mesh sequence with maximum diameter tending to zero,

\[
K_n^B\xrightarrow{M}
K=\{v\in H_0^1(\Omega):v\ge0\}.
\]

### Theorem B — strongly monotone inner-cone Falk estimate

For an `alpha`-strongly monotone, `L`-Lipschitz operator,

\[
\|u_n-u\|_V^2
\le
\frac{L^2}{\alpha^2}\|v_n-u\|_V^2
+\frac2\alpha
 \langle A(u)-f,v_n-u\rangle.
\]

### Theorem C — operator-independent strong convergence

Every strongly monotone Lipschitz VI over the Bernstein cones converges
strongly to the continuum solution.

### Theorem D — grand regular-interface rate

Under the corrected regular-interface assumptions,

\[
\|u-u_n^B\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2})
\]

for nonsymmetric linear and nonlinear strongly monotone operators.

### Theorem E — translated nonzero obstacles

For conforming obstacle majorants `psi_n>=psi` converging in the energy norm,

\[
\psi_n+K_n^B\xrightarrow{M}\psi+K.
\]

### Theorem F — perturbation separation

If `u_n^delta` uses a strongly monotone perturbed operator `A_n` and data
`f_n` over the same Bernstein cone, then

\[
\|u_n^\delta-u_n^*\|_V
\le
\frac{\|(A-A_n)u_n^*-(f-f_n)\|_{V^*}}{\alpha_n}.
\]

---

## Suggested paper architecture

1. **Introduction and theorem overview**
   - exact pointwise feasibility;
   - inner versus nodal constraints;
   - operator-independent contribution.

2. **Bernstein–Bézier finite-element cones**
   - simplex basis;
   - face conformity;
   - coefficient clipping;
   - exact feasibility.

3. **Positive recovery and Mosco convergence**
   - nonnegative smooth density;
   - positive sampling;
   - explicit moving-space diagonal.

4. **Strongly monotone variational inequalities**
   - nonlinear Falk inequality;
   - convergence;
   - quantitative rate transfer.

5. **Nonzero and translated obstacles**
   - exact polynomial obstacles;
   - conforming majorants;
   - boundary-lift limitations.

6. **Regular free-boundary recovery**
   - local risky set;
   - coefficient localization;
   - clipping repair;
   - patch-volume `3/2` scale.

7. **Grand sharp theorem**
   - bounded multiplier residual;
   - nonsymmetric/nonlinear rate transfer.

8. **Perturbed operators and quadrature**
   - exact-discrete/perturbed-discrete split;
   - relation to Strang--Falk theory.

9. **Hertz/Signorini mechanics validation**
   - exact curved-edge feasibility;
   - KKT and reaction balance;
   - phase-sensitive contact-width warning.

10. **Formalization and trust boundary**
    - Lean-certified layers;
    - analytical layers;
    - independent-review requirements.

---

## Claims to avoid

Do not claim:

- that Mosco stability or the abstract Falk theorem is itself new;
- that the full physical theorem is already Lean formalized;
- that a targeted literature search proves novelty;
- that every nonlinear obstacle operator is globally Lipschitz;
- that the result covers degenerate monotone operators such as the general
  `p`-Laplacian without reformulating the function space and estimates;
- that arbitrary nonzero obstacles automatically possess conforming Bernstein
  majorants;
- that the vector Signorini recovery is complete merely because the operator
  theorem is complete.

---

## Strong but accurate significance statement

The contribution is potentially substantial because it changes Bernstein
coefficient constraints from a special positivity certificate into a general
high-order inner-approximation technology for variational inequalities.  The
new operator theorem shows that the geometric recovery and free-boundary
analysis are reusable across an entire class of PDE operators.  The sharp
`3/2` interface term is no longer tied to symmetry or quadratic minimization.

This significance remains conditional on independent confirmation of the
proof and a qualified prior-art audit.
