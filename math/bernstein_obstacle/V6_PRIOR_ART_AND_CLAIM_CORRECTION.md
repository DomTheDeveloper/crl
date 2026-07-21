# V6 prior-art audit and corrected claim boundary

## Verdict

**PASS AFTER MATERIAL CLAIM NARROWING.**

The V6 mathematics remains a valid enlargement of this project's earlier
symmetric theorem, but the abstract strongly monotone Falk/Céa layer is not a
new theorem of numerical analysis.  Nonlinear, nonsymmetric, and higher-order
obstacle finite-element methods also have substantial prior literature.

The defensible candidate contribution is narrower and more concrete:

> arbitrary-degree Bernstein coefficient inner cones with exact pointwise
> feasibility over complete elements, a constructive positive Mosco recovery,
> conformity-preserving coefficient clipping near a regular free boundary,
> the codimension-one `h_Gamma^(3/2)` recovery scale, and transfer of that
> specific recovery estimate to strongly monotone nonsymmetric/nonlinear
> variational inequalities.

Independent review is still required to determine whether this complete
combination is new.

---

## 1. Classical abstract layer

The following must be presented as background or a specialized derivation, not
as a stand-alone novelty claim:

- Céa/Falk-type approximation estimates for strongly monotone variational
  inequalities;
- finite-element error estimates for nonlinear monotone obstacle problems;
- Mosco/Glowinski convergence of discrete convex sets;
- Strang--Falk estimates for perturbed variational inequalities;
- data and operator stability on a fixed convex set.

### Key collisions

1. Joachim Gwinner, *Céa's error estimate for strongly monotone variational
   inequalities*, Applicable Analysis 44/45 (1992), extends Céa approximation
   to strongly monotone VIs and applies it to nonlinear two-sided obstacle
   problems.
2. Lie-Heng Wang, *Error Estimates for the Finite Element Solutions of Some
   Variational Inequalities with Nonlinear Monotone Operator*, Journal of
   Computational Mathematics 1(2) (1983), gives finite-element obstacle error
   estimates for monotone operators.
3. Karlheinz Hafner, *Error estimates for the finite element solution of
   quasilinear obstacle problems*, Numerical Functional Analysis and
   Optimization 9 (1987), treats strongly monotone and Lipschitz quasilinear
   obstacle operators.

Accordingly, Theorem 2.2 of the V6 note should be described as the exact
inner-cone specialization needed by this project and as a formalization target,
not as the primary mathematical novelty.

---

## 2. Higher-order nonlinear and nonsymmetric obstacle FEM

These directions also predate V6:

1. L. Banz and A. Schröder,
   *Biorthogonal basis functions in hp-adaptive FEM for elliptic obstacle
   problems*, Computers & Mathematics with Applications 70 (2015), studies
   nonsymmetric elliptic obstacle problems with higher-order hp-FEM,
   complementarity constraints, and semismooth Newton methods.
2. L. Banz, B. P. Lamichhane, and E. P. Stephan,
   *Higher order FEM for the obstacle problem of the p-Laplacian—A variational
   inequality approach*, Computers & Mathematics with Applications 76 (2018),
   proves higher-order a priori rates for nonlinear p-Laplacian obstacle
   problems.
3. The companion 2018 mixed-method paper uses biorthogonal systems to obtain
   pointwise-form discrete complementarity constraints.

Therefore V6 must not claim to be the first high-order method for nonlinear or
nonsymmetric obstacle problems.

---

## 3. Closest recent collision: hp/SEM cone convergence

R. O. E. Bekhouche and D. C. Benchettah,
*hp-adaptive/Spectral Element Methods for Elliptic Obstacle and Free Boundary
Problems*, Communications in Nonlinear Science and Numerical Simulation,
available online 1 June 2026, article 110252,
DOI `10.1016/j.cnsns.2026.110252`, proves convergence of a high-order discrete
convex set and an `O(h/N)` estimate for elliptic obstacle VIs.

Its admissibility mechanism is materially different:

- obstacle constraints are imposed at transformed Gauss--Legendre--Lobatto
  points;
- the reported cone convergence is in the Glowinski framework;
- Bernstein positivity is used as part of the construction, but the headline
  constraint is GLL-point enforcement rather than nonnegativity of every
  assembled Bernstein coefficient;
- the work does not, based on the accessible abstract and introduction,
  advertise complete-element coefficientwise nonpenetration or the
  `h_Gamma^(3/2)` clipping theorem.

This is the closest contemporary paper and must be discussed prominently in
any submission.

---

## 4. Perturbation theory collision

L. Banz, M. Schönauer, and A. Schröder,
*Error estimates for perturbed variational inequalities of the first kind*,
Calcolo 62 (2025), article 38, DOI `10.1007/s10092-025-00660-1`, combines the
first Strang lemma and Falk's theorem, includes operator/data perturbations,
and studies higher-order obstacle FEM with inexact quadrature.

The V6 same-cone perturbation estimate is a useful sharp specialization, but it
is not a new perturbation framework.  Its role is to keep the Bernstein
geometry error separate from implementation error.

---

## 5. Bernstein bounds literature

Bernstein convex-hull bounds themselves are established technology in
high-order finite elements, positivity limiters, mesh validity, and
bounds-constrained polynomial approximation.  Relevant examples include:

- L. Allen and R. C. Kirby, *Bounds-constrained polynomial approximation using
  the Bernstein basis* (2021), including multivariate simplex extensions;
- C. Lohmann, D. Kuzmin, J. N. Shadid, and S. Mabuza, high-order continuous
  Galerkin flux-corrected transport with Bernstein elements (2017);
- recent high-order finite-element bounding and limiter literature comparing
  Bernstein convex-hull bounds with tighter alternatives.

The project contribution cannot be “Bernstein coefficients bound the
polynomial.”  It must be the obstacle-specific global cone, recovery, clipping,
and sharp interface analysis.

---

## 6. Corrected theorem hierarchy

### Classical transfer theorem

For strongly monotone Lipschitz variational inequalities on inner discrete
sets, a Falk/Céa estimate transfers feasible recovery and complementarity
residual bounds to solution error.

**Status:** classical in substance; the exact Lean theorem and clean constants
are useful project infrastructure.

### Bernstein inner-cone convergence theorem

Nonnegative assembled Bernstein coefficients define exact pointwise inner
cones, and positive Bernstein sampling provides strong recovery and Mosco
convergence.

**Status:** candidate contribution, but must be compared carefully with the
2026 hp/SEM construction and older bounds-constrained Bernstein approximation.

### Bernstein regular-interface clipping theorem

Under the corrected local-size, patch-volume, regularity, boundary, and
multiplier assumptions, shared-coefficient clipping produces

\[
\|u-v_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}),
\qquad
\langle\lambda,v_h^B-u\rangle\le Ch_\Gamma^3.
\]

**Status:** strongest candidate novelty.

### Operator-transfer corollary

The same `h^r+h_Gamma^(3/2)` solution rate holds for strongly monotone
Lipschitz nonsymmetric/nonlinear obstacle operators.

**Status:** candidate new consequence of the Bernstein clipping theorem, but
not the first nonlinear or nonsymmetric high-order obstacle estimate.

---

## 7. Corrected significance statement

The potentially significant result is not a universal new theory of monotone
variational inequalities.  It is a new, implementation-faithful admissible-set
technology that may provide simultaneously:

- arbitrary polynomial degree;
- exact pointwise feasibility over each complete element or polynomial face;
- conforming global assembly under shared coefficients;
- a positive Mosco recovery;
- a quantitative regular-interface clipping repair;
- a codimension-one `3/2` energy scale;
- reuse across symmetric, nonsymmetric, and nonlinear strongly monotone
  operators.

That combination would be a substantial numerical-analysis contribution if the
proof and literature boundary survive qualified external review.

---

## 8. Required manuscript corrections

Before submission:

1. call the Falk/Céa operator estimate classical or project-specialized;
2. cite Gwinner (1992), Wang (1983), Hafner (1987), Banz--Schröder (2015),
   Banz--Lamichhane--Stephan (2018), Banz--Schönauer--Schröder (2025), and
   Bekhouche--Benchettah (2026);
3. replace “first nonlinear/nonsymmetric theorem” with “transfer of the
   Bernstein coefficient-cone clipping rate to the strongly monotone class”;
4. compare coefficientwise complete-element feasibility directly with GLL
   point constraints and biorthogonal multiplier constraints;
5. keep independent novelty review as an explicit release gate.

---

## 9. Internal audit conclusion

No counterexample was found to the V6 inner-cone algebra, translated-cone
argument, fixed-cone perturbation estimate, or explicit `tanh` benchmark.
However, the prior-art search invalidates any broad claim that nonlinear,
nonsymmetric, higher-order, Mosco-convergent, or perturbed obstacle FEM is new
by itself.

**Internal verdict: PASS AFTER MATERIAL CLAIM NARROWING.**
