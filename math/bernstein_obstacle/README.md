# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle methods whose local Bernstein coefficient constraints guarantee pointwise nonpenetration over the entire element.

## Unified V8 review target

The current integration target starts from Lean/reproduction head `d06444e3d8f500283f5c32381348328fcc7566cc` and incorporates the corrected local-size free-boundary analysis, multi-face physical-boundary argument, one-ring support statement, and Hertz mesh-phase sensitivity data. See `MANUSCRIPT_UPDATE_V8.md`.

## Verification layers

### Lean-verified finite, polynomial, and abstract layer

Pinned Lean/mathlib audits prove:

- one-dimensional, tensor-product, and arbitrary-simplex Bernstein basis positivity and partition of unity;
- coefficient interval / convex-hull bounds and obstacle no-penetration;
- arbitrary face permutations, oriented trace equality, concrete shared-face conformity, and boundary-zero preservation;
- coefficient-cone and assembled-feasible-set convexity;
- clipping membership, idempotence, nearest-point, KKT, complementarity, Pythagorean, and nonexpansive properties;
- exact finite quadratic-energy identities and obstacle-VI estimates;
- sequential Mosco definitions, weak-closure reductions, diagonal recovery infrastructure, and abstract moving-cone minimizer convergence;
- all-degree simplex-lattice unisolvence;
- realization of simplicial Bernstein functions as affine multivariate polynomials;
- linear independence, spanning, `Module.Basis`, and unique Bernstein expansion;
- coefficient localization algebra, strip-scaling algebra, and the finite sharp-rate transfer endgame.

The latest baseline runs at commit `d06444e3d8f500283f5c32381348328fcc7566cc` both passed:

- Lean audit: workflow run `29783666712`;
- full numerical reproduction: workflow run `29783666727`.

The terminal axiom audits report no `sorryAx`; audited declarations use only standard mathlib axioms such as `propext`, `Classical.choice`, and `Quot.sound`.

See `LEAN_THEOREM_INDEX.md`, `lean/verification/`, and the audit entry points in `lean/`.

### General analytical theorem

Let `V_h^r` be fixed-degree conforming simplicial finite-element spaces on a uniformly shape-regular mesh family, and let `K_h^B` require every local Bernstein coefficient to be nonnegative. Then
\[
K_h^B\xrightarrow{M}K,
\qquad
K=H_0^1(\Omega)\cap\{v\ge0\}.
\]

The recovery uses nonnegative smooth density and the positive Bernstein sampling operator. Consequently, minimizers of symmetric continuous coercive obstacle energies converge strongly in `H^1`. This theorem needs no free-boundary regularity.

The abstract Mosco and minimizer-convergence logic is Lean checked. The concrete moving Sobolev/FEM recovery operator and its affine-scaling estimate remain analytical.

### Scoped sharp theorem

Under:

- a compact regular interior free boundary separated from the physical boundary;
- quadratic gap growth in a fixed positive-side tubular neighborhood;
- `C^{1,1}` regularity and a mesh-independent one-sided `H^{r+1}` extension;
- a uniform broken `H^{r+1}` bound outside the risky patch;
- bounded multiplier density;
- the local-size risky set
  \[
  \mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\};
  \]
- a locally quasi-uniform one-ring patch with `|omega_h| = O(h_Gamma)`;
- exact obstacle representation and the stated multi-face physical-boundary compatibility;

we obtain
\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

The proof uses an exact coefficient-to-grid-value estimate, phase classification outside the risky set, a one-ring coefficient-amplitude bound, and either shared global coefficient clipping or a positive cutoff repair. Independent energy-identity and Falk arguments give the minimizer estimate.

This analytical theorem has passed an internal adversarial audit after correction but still awaits qualified independent expert review.

## Mechanics validation

The project contains:

1. a certified Bernstein approximation of the analytical Hertz line-contact pressure with exact resultant force;
2. a plane-strain P1 triangular Hertz/Signorini benchmark;
3. a plane-strain P2 triangular Bernstein–Bézier benchmark whose quadratic edge gap is coefficient-certified at every contact-edge point;
4. a curved isoparametric P2 benchmark with positive Jacobians and a fixed-radial mesh-phase sensitivity sweep.

For the selected 20,193-unknown curved P2 mesh:

- PDAS iterations: 13;
- KKT residual: `5.12e-13`;
- bracketed contact-half-width error: `1.01e-4`;
- pressure-fitted half-width error: `9.42e-4`;
- pressure `L2` error: `8.82e-2`;
- half-load error: `1.02e-11`;
- minimum gap coefficient: exactly `0`.

Neighboring angular resolutions show that contact-width estimators are mesh-phase sensitive. The selected-mesh approximately `48.9×` comparison is not a uniform convergence factor. See `benchmarks/HERTZ_SIGNORINI_P2_CURVED.md` and `results/hertz_phase_sensitivity.csv`.

The scikit-fem calculation is a second assembly framework developed within this project, not an external clean-room replication.

## GitHub-only external review

Public review work packages are:

- issue #98: prior-art collision;
- issue #99: Mosco/FEM recovery;
- issue #100: regular free-boundary clipping and the `3/2` rate;
- issue #101: Lean statement faithfulness;
- issue #102: reviewer recruitment.

Counterexamples, prior-art collisions, and corrected narrower theorems are explicitly accepted as successful audit outcomes.

## Important subdivision correction

Subdivision-refined Bernstein cones are nested, and every strictly positive polynomial is certified after sufficiently fine uniformly shape-regular subdivision. Subdivision does **not** certify every nonnegative polynomial having zeros; therefore free-boundary clipping or another repair remains essential.

## Reproduce

The one-command workflow is defined in `.github/workflows/bernstein-obstacle-reproduction.yml`. The focused Lean build and axiom audit are defined in `.github/workflows/bernstein-obstacle-lean-audit.yml`.

Local utilities include:

```bash
python verification/verify_bernstein_coefficient_constants.py
python reproduction/reproduce_all.py --output-dir reproduction-output
```

Dependencies and exact versions are pinned in `reproduction/requirements.txt` and `lean/lean-toolchain`.

## Scope warning

The sharp rate does not claim singular or degenerate free boundaries, boundary-touching free boundaries, anisotropic meshes without a separate audit, arbitrary inexact obstacles, measure-valued multipliers without further hypotheses, nonsymmetric operators, or optimal adaptive complexity without a specified refinement-closure theorem.

The finite and abstract layers are machine checked under pinned toolchains. The moving Sobolev finite-element recovery, local free-boundary geometry, coefficient localization on actual meshes, and complete sharp-rate theorem remain analytical and require independent expert review.