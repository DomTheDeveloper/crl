# Manuscript update V8 - unified Lean and analytical correction target

This update supersedes the split review situation in which the corrected analytical packet and the newest Lean formalization lived on diverged branches.

## Unified baseline

The V8 integration branch starts from the latest Bernstein Lean/reproduction head `d06444e3d8f500283f5c32381348328fcc7566cc`, whose Lean audit and full numerical reproduction workflows both passed, and then incorporates the full analytical corrections from the internal red-team packet.

## Theorem corrections

1. The risky set is local-size based:
   \[
   \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\}.
   \]
2. On the fixed one-ring patch:
   \[
   c_mh_\Gamma\le h_T\le C_mh_\Gamma,
   \qquad |\omega_h|\le C_\Gamma h_\Gamma.
   \]
3. The sharp theorem assumes a uniform broken regularity bound outside the patch:
   \[
   \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg}.
   \]
4. The physical-boundary proof now treats the union of all physical-boundary faces of a simplex, including corner elements with more than one boundary face.
5. The proof states explicitly that global shared-coefficient clipping enlarges the correction support from the risky set to its one-ring star.
6. Positive elements outside the risky set are split into tubular-near-interface, compact interior, and physical-boundary cases; the quadratic lower bound is not silently applied outside its stated neighborhood.
7. The abstract and theorem statements identify local distance-to-element-size grading, fixed-degree shape regularity, bounded multiplier density, exact obstacle representation, and uniform broken regularity as hypotheses rather than implementation details.

## Numerical corrections

1. The approximately `48.9×` Hertz contact-width comparison is not a general convergence claim.
2. Neighboring curved meshes expose phase sensitivity of bracketed and pressure-fitted contact-width estimators.
3. Pressure error, resultant force, KKT residual, geometry quality, coefficient feasibility, and cross-framework agreement are the primary diagnostics.
4. The scikit-fem calculation is a second project-internal assembly framework, not an external clean-room replication.
5. The three-dimensional spherical experiment is labeled a scalar obstacle benchmark.

## Formalization language

The finite coefficient, polynomial, simplex, face-permutation, global-conformity, clipping, finite energy, abstract Mosco, diagonal recovery, strip-scaling, sharp-rate algebra, and Hilbert-space VI layers are machine checked under a pinned Lean/mathlib toolchain. The actual moving Sobolev finite-element recovery and free-boundary localization theorem remain analytical.

## Internal completion status

- theorem statement coherence: complete after correction;
- finite and abstract Lean layer: current and green at the unified baseline;
- numerical reproduction: current and green at the unified baseline;
- analytical proof packet: internally complete under the explicit hypotheses;
- qualified independent mathematical endorsement: still pending and cannot be replaced by internal AI review.

The V8 branch is the single target that should be used for the next external review cycle.