# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle methods whose local
Bernstein coefficient constraints guarantee pointwise nonpenetration over the
entire element.

## Corrected review target

All new analytical review should use:

- branch: `review/bernstein-obstacle-v2-corrected`;
- commit: `f2bd41f19ff5afbcca8a23f9afdcdf084364dae4`;
- correction pull request: `#106`.

The sequence-indexed quantifier and energy closure added after that frozen
baseline is in `SOBOLEV_FEM_CLOSURE.md` and the focused closure branch/PR.

## Verification layers

### Machine-checked finite and Hilbert layers

Pinned Lean/mathlib audits prove, among other results:

- one-dimensional, tensor-product, and arbitrary-simplex Bernstein
  nonnegativity and range certificates;
- the arbitrary-simplex multinomial partition of unity;
- face-orientation and assembled shared-coefficient conformity infrastructure;
- global coefficient clipping and boundary preservation;
- coefficient-cone convexity, clipping feasibility, idempotence, nearest-point
  behavior, KKT inequalities, complementarity, Pythagorean estimates, and
  nonexpansiveness;
- finite quadratic-energy identities and discrete obstacle VI estimates;
- sequential Mosco definitions and abstract recovery reductions;
- weak sequential closedness and constant-family Mosco convergence for the
  finite coefficient and assembled feasible sets;
- coordinate-free Hilbert-space VI projection, error, and uniqueness results;
- abstract recovery-to-strong-minimizer convergence layers.

The frozen complete project audit at commit
`209460f762b24d05534075424a5a3864cc5edb9c` succeeded in workflow run
`29777931837`. The coordinate-free Hilbert extension at commit
`44f59928880992f12e84b3494ccccd93a6ddc0f5` succeeded in workflow run
`29780214748`. The audited terminal declarations contain no `sorryAx` and use
only the standard mathlib axioms `propext`, `Classical.choice`, and
`Quot.sound`.

See `LEAN_THEOREM_INDEX.md`, `lean/verification/`, and the external statement
faithfulness panel.

### General analytical theorem

For a sequence of fixed-degree conforming simplicial Bernstein finite-element
spaces on uniformly shape-regular meshes, the coefficient-feasible cones
Mosco-converge to

\[
K=H_0^1(\Omega)\cap\{v\ge0\}.
\]

Consequently, minimizers of symmetric continuous coercive obstacle energies
converge strongly in `H^1`. The current proof now contains:

- an explicit sequence-indexed diagonal recovery;
- exact face-permutation conformity and boundary-trace statements;
- dimension-safe fixed-degree approximation estimates;
- a direct inner-cone energy-distance proof of strong minimizer convergence.

The full closure is in `SOBOLEV_FEM_CLOSURE.md`. The physical Sobolev recovery
operator has not yet been completely formalized in Lean and still requires an
independent numerical-analysis review.

### Corrected scoped sharp theorem

Let

\[
\mathcal R_n
=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\}
\]

and let `omega_n` be a fixed one-ring enlargement. Under a compact regular
interior free boundary, two-sided quadratic gap growth, a mesh-independent
one-sided `H^{r+1}` extension, a uniform broken regularity bound outside the
patch, bounded multiplier density, local interface size comparability,
`|omega_n| <= C h_{Gamma,n}`, exact obstacle representation, and the stated
physical-boundary alternative,

\[
\|u-u_n^B\|_{H^1}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr).
\]

The proof uses an exact coefficient-to-grid-value estimate and either shared
coefficient clipping or a positive cutoff repair. The closure note strengthens
the proof by:

- localizing coefficients with the actual element size `h_T`;
- summing the repair estimate directly by patch volume rather than by an
  informal element count;
- stating the physical-boundary face/off-face split explicitly;
- deriving the discrete minimizer estimate directly from the inner-cone energy
  identity, with the multiplier sign and support fixed.

The internal adversarial verdict is `PASS AFTER CORRECTION`. The accurate
external status remains **reviewer-ready, not independently confirmed**.

## Mechanics validation

The project contains:

1. a certified Bernstein approximation of the analytical Hertz line-contact
   pressure with exact resultant force;
2. a plane-strain P1 triangular Hertz/Signorini benchmark;
3. a plane-strain P2 triangular Bernstein–Bézier benchmark whose quadratic
   edge gap is coefficient-certified at every point of each contact edge;
4. curved isoparametric P2 geometry and a second project-internal scikit-fem
   assembly.

The robust numerical conclusions are:

- exact coefficientwise nonpenetration over complete curved contact edges;
- small KKT and complementarity residuals;
- accurate total reaction balance;
- positive curved-element Jacobians;
- improved curved pressure-profile diagnostics;
- close agreement between the two project-internal assembly frameworks.

Contact-width estimators are mesh-phase sensitive. A favorable matched mesh
pair is retained as a reported data point, not as a uniform improvement factor.
The second assembly is not described as an external clean-room reproduction.

See `benchmarks/HERTZ_SIGNORINI_P2_CURVED.md` and the corresponding CSV/JSON
files in `results/`.

## Public independent review

Public review work packages are:

- issue #98: prior-art collision and novelty boundary;
- issue #99: Mosco/FEM recovery;
- issue #100: regular free-boundary clipping and the `3/2` rate;
- issue #101: Lean statement faithfulness;
- issue #103: clean-room numerical reproduction.

Counterexamples, prior-art collisions, and corrected narrower theorems are
explicitly accepted as successful audit outcomes. Repository-owner reviews,
automated-agent reviews, and implementations produced within this project do
not count as independent endorsement.

## Important subdivision correction

Subdivision-refined Bernstein cones are nested, and every strictly positive
polynomial is certified after sufficiently fine uniformly shape-regular
subdivision. Subdivision does **not** certify every nonnegative polynomial
having zeros; therefore free-boundary clipping/repair is essential.

## Reproduce

```bash
python verification/verify_bernstein_coefficient_constants.py
python adaptive_triangular_bernstein.py
python adaptive_hybrid_bernstein.py
python nested_bernstein_refinement.py
python constraint_cone_benchmark.py
python pointwise_barrier_contact_benchmark.py
```

The Hertz benchmark programs are distributed in the campaign validation
bundle while their results and reviewer-facing descriptions are archived in
this repository.

Dependencies: Python 3.11+, NumPy, SciPy, SymPy, pandas, Matplotlib.

## Scope warning

The sharp rate does not claim singular or degenerate free boundaries,
boundary-touching free boundaries without a separate corner analysis,
arbitrary inexact obstacles, measure-valued multipliers without further
hypotheses, nonsymmetric operators, anisotropic meshes without a separate
audit, or optimal adaptive complexity without a specified refinement-closure
theorem. The general Mosco and strong-minimizer convergence theorems are
broader.
