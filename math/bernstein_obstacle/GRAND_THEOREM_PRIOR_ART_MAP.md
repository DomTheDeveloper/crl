# Prior-art collision map for the Bernstein grand theorem

## Purpose

This is a conservative internal literature map. It is not a definitive novelty
opinion. Its role is to separate classical ingredients from the exact combined
claim that now requires qualified external review.

## Established neighboring results

### Falk approximation theory

R. S. Falk, *Error estimates for the approximation of a class of variational
inequalities*, Mathematics of Computation 28 (1974), 963--971.

Classical contribution:

- a general approximation estimate for elliptic variational inequalities;
- application to scalar obstacle problems.

No novelty claim should be made for the existence of Falk-type residual and
best-approximation terms by themselves.

### Bounds-constrained Bernstein approximation

L. Allen and R. C. Kirby, *Bounds-constrained polynomial approximation using
the Bernstein basis*, 2021/2022.

Classical neighboring contribution:

- coefficient bounds imply polynomial range bounds;
- constrained polynomial approximation and optimization;
- multivariate simplex extension.

Nonnegative Bernstein coefficients as a sufficient pointwise certificate are
not new.

### High-order bounds-satisfying finite-element variational inequalities

R. C. Kirby and D. Shapero, *High-order bounds-satisfying approximation of
partial differential equations via finite element variational inequalities*,
Numerische Mathematik 156 (2024), 927--947.

Classical neighboring contribution:

- an abstract best-approximation result for a linear variational inequality;
- high-order bounds-satisfying approximation theory;
- Bernstein coefficient constraints as a practical sufficient subset;
- numerical evidence for high-order constrained PDE approximations.

Their published theory explicitly notes that the approximation power of the
Bernstein-coefficient subset is not fully established by their general
bounds-satisfying polynomial theorem. The present project must not imply that
high-order Bernstein coefficient VI methods themselves are new.

### Classical obstacle and contact FEM

Relevant established literature includes:

- P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*;
- N. Kikuchi and J. T. Oden, *Contact Problems in Elasticity*;
- P. Hild and Y. Renard, improved a priori analysis for Signorini contact;
- F. Chouly and P. Hild, Nitsche methods for unilateral contact;
- B. Wohlmuth, variationally consistent contact discretizations;
- mixed, mortar, stabilized, and penalty formulations for obstacle/contact
  problems.

The scalar obstacle problem, Signorini contact, active-set transition analysis,
and a priori contact error estimates are mature topics.

### Nonlinear and Mosco-stable variational inequalities

Strongly monotone nonlinear variational inequalities have classical existence,
uniqueness, stability, and projection theory. Recent work also studies stability
of nonlinear unilateral problems under Mosco convergence, including Leray--Lions
type operators and natural-growth lower-order terms.

Strong monotonicity, Lipschitz continuity, and Mosco stability are not new
concepts.

## Exact internal theorem now proposed

The candidate combined contribution is:

1. use an exact Bernstein coefficient cone as an inner approximation of the
   physical unilateral set;
2. prove the nonlinear certified estimate
   \[
   \|u-u_h\|_V^2
   \le
   \frac{L^2}{\alpha^2}\|u-v_h\|_V^2
   +\frac{2}{\alpha}\langle F(u),v_h-u\rangle
   \]
   for a strongly monotone Lipschitz operator without symmetry or a potential;
3. instantiate it with conformity-preserving shared-coefficient clipping;
4. derive the repair law
   \[
   \|d_h\|_V=O(h_\Sigma^{(c+3)/2})
   \]
   for a constraint manifold of ambient codimension `c`;
5. derive the multiplier law
   \[
   \langle F(u),v_h-u\rangle=O(h_\Sigma^3),
   \]
   independent of whether the constraint is volumetric or on the boundary;
6. conclude the same final
   \[
   O(h^r+h_\Sigma^{3/2})
   \]
   rate for both a regular interior obstacle and planar frictionless Signorini
   contact;
7. preserve pointwise safety under conservative one-sided obstacle or clearance
   approximation.

## Preliminary collision assessment

### Clearly classical

- Falk-style comparison inequalities;
- strongly monotone Lipschitz VI well-posedness;
- Bernstein range certificates;
- bounds-constrained high-order FEM;
- obstacle and Signorini contact formulations;
- regular-interface and multiplier error analysis;
- conservative geometry/obstacle approximation as a general safety principle.

### Potentially distinctive but not yet externally established

- the exact nonlinear Bernstein-inner-cone specialization;
- the shared proof for both volume obstacle and boundary contact;
- the codimension repair exponent `(c+3)/2`;
- the observation that the bounded-multiplier term restores a universal final
  `3/2` exponent across codimensions zero and one;
- the explicit planar Signorini global Bernstein control-point lifting;
- the combined theorem with conservative inexact gap data.

## Required external searches

A qualified novelty review should search at least:

- MathSciNet and zbMATH for nonlinear Falk estimates with inner finite-element
  sets;
- obstacle/contact FEM papers using Bernstein or Bézier control coefficients;
- high-order Signorini methods with direct coefficientwise gap constraints;
- hp-FEM, mortar, BEM, and isogeometric contact literature;
- positivity-preserving FEM and bounds-constrained approximation literature;
- nonlinear strongly monotone and pseudomonotone VI approximation theory;
- Mosco convergence for obstacle and Signorini sets;
- contact transition-set estimates producing a `3/2` multiplier contribution.

## Safe manuscript language before external review

Use:

> We prove a certified inner-approximation theorem for strongly monotone
> Lipschitz variational inequalities and show, under explicit regular-interface
> and lifting hypotheses, that Bernstein coefficient constraints yield a common
> three-halves interface term for scalar obstacle and planar Signorini contact.
> The relation of this exact combined theorem to prior nonlinear VI and contact
> approximation results is under independent review.

Do not use:

- “first ever”;
- “completely new”;
- “unprecedented”;
- “independently verified”;
- claims covering curved contact, friction, singular interfaces, or merely
  monotone operators.
