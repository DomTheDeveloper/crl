# Panel A: prior-art collision and novelty boundary

## Claims explicitly not new

The manuscript must not claim novelty for any of the following in isolation:

1. Bernstein basis nonnegativity and partition of unity;
2. coefficient bounds as sufficient global polynomial range certificates;
3. Bernstein–Bézier bases for conforming high-order simplex finite elements;
4. high-order finite-element methods for obstacle variational inequalities;
5. active-set, semismooth Newton, proximal, mixed, DG, or spectral obstacle
   solvers;
6. Mosco convergence as an abstract variational-convergence tool;
7. formal Bernstein/de Casteljau theory in proof assistants;
8. free-boundary refinement or contact-pressure benchmarks.

## Candidate combined contribution

The narrow combination requiring a collision search is:

1. the inner obstacle cone defined by nonnegative Bernstein coefficients on
   conforming simplices;
2. a Mosco recovery theorem for that specific coefficient cone;
3. strong convergence of the associated obstacle minimizers;
4. localization of infeasible interpolant coefficients to a regular
   free-boundary strip;
5. conformity-preserving global coefficient clipping;
6. the recovery and minimizer estimate
   \[
   \|u-u_h^B\|_{H^1}\le C(h^r+h_\Gamma^{3/2});
   \]
7. nested coefficient-preserving adaptivity and pointwise-feasible contact
   mechanics;
8. a Lean-verified finite no-penetration/projection certificate.

## Mandatory comparison families

### Bernstein approximation and FEM

- bounds-constrained approximation using Bernstein coefficients;
- high-order bounds-satisfying finite-element variational inequalities;
- classical arbitrary-order Bernstein–Bézier simplex finite elements;
- tighter high-order polynomial range-bounding schemes.

### Obstacle and contact methods

- hp/spectral obstacle methods using Gauss–Lobatto point constraints;
- proximal Galerkin and proximal DG methods;
- mixed multiplier and stabilized obstacle methods;
- Signorini barrier and supremum-norm a posteriori methods;
- isogeometric and virtual-element contact discretizations;
- any earlier use of Bernstein/Bézier control coefficients for unilateral
  contact or variational inequalities.

### Formalization

- Coq formalizations of Bernstein coefficients and de Casteljau subdivision;
- current mathlib Bernstein polynomial infrastructure;
- any Lean FEM, convex projection, variational inequality, or Mosco library.

## Search queries that must be documented

At minimum search combinations of:

- `Bernstein coefficient obstacle variational inequality`;
- `Bernstein Bezier unilateral contact finite element`;
- `Bernstein cone Mosco convergence`;
- `control coefficients obstacle problem`;
- `Bernstein clipping free boundary error estimate`;
- `pointwise feasible high order obstacle finite element`;
- `Bernstein coefficients Signorini contact`;
- `formal Bernstein obstacle Lean Coq`.

Search journal indexes, MathSciNet or zbMATH where available, Crossref/DOI
metadata, arXiv, theses, conference proceedings, and citation graphs of the
closest bounds-constrained FEM papers.

## Collision classification

Every located source must be assigned one of:

- **C0:** terminology-only or irrelevant use of Bernstein methods;
- **C1:** uses Bernstein coefficients for a global bound certificate;
- **C2:** applies coefficient constraints to a PDE or optimization problem;
- **C3:** treats obstacle/contact inequalities with Bernstein or Bézier bases;
- **C4:** proves convergence of the coefficient-constrained obstacle cone;
- **C5:** contains the free-boundary localization/clipping mechanism or the
  `3/2` estimate;
- **C6:** anticipates the full combined theorem.

A C4--C6 source must be analyzed theorem by theorem. A C1--C3 source narrows
language but does not by itself destroy the combined novelty claim.

## Current accessible-index conclusion

The current search found the ingredients separately, including classical
Bernstein–Bézier FEM, bounds-constrained polynomial/FEM work, and modern
high-order obstacle solvers. It did not locate a C4--C6 source. This is evidence,
not proof of novelty; the external panel must try to falsify it.

## Required verdict

Return:

1. the highest collision class found;
2. exact theorem/page references;
3. manuscript sentences that must be weakened;
4. the strongest contribution still supportable;
5. a binary verdict on whether the title/abstract novelty language is fair.
