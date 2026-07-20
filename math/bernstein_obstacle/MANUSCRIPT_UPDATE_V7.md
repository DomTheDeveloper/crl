# Manuscript update V7 - full AI-audit corrections

The venue manuscript was rebuilt after the full internal AI red-team audit.

## Theorem corrections

1. The risky set is now local-size based:
   \[
   \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\}.
   \]
2. On the fixed one-ring patch:
   \[
   c_mh_\Gamma\le h_T\le C_mh_\Gamma,
   \qquad |\omega_h|\le C_\Gamma h_\Gamma.
   \]
3. The sharp theorem now assumes a uniform broken regularity bound outside the patch:
   \[
   \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg}.
   \]
4. The physical-boundary proof explicitly separates zero boundary-face coefficients from off-face control points whose inward linear growth dominates the `O(h_T^2)` discrepancy.
5. The abstract states that the sharp rate uses local distance-to-element-size grading and uniform broken regularity.

## Numerical corrections

1. The approximately `48.9×` Hertz contact-width comparison was removed from the abstract and conclusion as a general claim.
2. The table is now labeled as a selected-mesh comparison.
3. Neighboring curved meshes with 145, 155, 160, 165, and 170 angular intervals are reported to expose mesh-phase sensitivity of the bracketed and pressure-fitted contact-width metrics.
4. Pressure error, resultant force, KKT residual, geometry quality, coefficient feasibility, and cross-framework agreement are treated as the more robust diagnostics.
5. The scikit-fem calculation is described as a second assembly framework developed inside the project, not a third-party clean-room replication.
6. The three-dimensional spherical experiment is explicitly labeled a scalar obstacle benchmark.

## Literature and formalization language

The discussion now cites:

- Banz, Lamichhane, and Stephan's higher-order primal and mixed obstacle FEM;
- Banz, Schönauer, and Schröder's Strang-Falk perturbation analysis;
- Keith and Surowiec's proximal Galerkin method;
- the existing Kirby-Shapero and GLL-constrained hp/spectral comparisons.

The Lean result is described as machine checked under a pinned Lean/mathlib toolchain, not independently machine checked.

## Build result

- 21 pages;
- 238-word abstract;
- two clean `pdflatex` passes;
- no undefined references or citations;
- no overfull boxes;
- PDF preflight passed;
- all pages rendered and visually inspected.

The unified corrected formal-review target is `integration/bernstein-v3-corrected-formal` after its pinned Lean audit passes.
