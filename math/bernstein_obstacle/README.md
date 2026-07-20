# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle methods whose local
Bernstein coefficient constraints guarantee pointwise nonpenetration over the
entire element.

## Verification layers

### Lean-verified finite certificate

Pinned Lean/mathlib audits now prove:

- one-dimensional Bernstein basis positivity and partition of unity;
- coefficient interval / convex-hull bounds;
- coefficient clipping and obstacle no-penetration;
- tensor-product unit-cube no-penetration;
- convexity of the nonnegative coefficient cone;
- clipping membership, idempotence, and minimal-majorant properties;
- arbitrary-dimensional simplicial basis nonnegativity;
- the arbitrary-simplex multinomial partition of unity;
- arbitrary-simplex coefficient range bounds and clipping no-penetration.

Latest complete theorem audit: workflow run `29758902996`, commit
`f1170dc567bcd53fa79c4d6610d0a30e089ca174`. No `sorryAx` was reported;
printed declarations use only the standard mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`.

See `LEAN_THEOREM_INDEX.md` and `lean/verification/`.

### General analytical theorem

For fixed-degree conforming simplicial Bernstein finite elements on a
shape-regular mesh family, the coefficient-feasible cones Mosco-converge to

\[
K=H_0^1(\Omega)\cap\{v\ge0\}.
\]

Consequently, minimizers of symmetric continuous coercive obstacle energies
converge strongly in `H^1`. This theorem needs no free-boundary regularity, but
has not yet been formalized in Lean or independently endorsed.

### Scoped sharp theorem

Under a compact regular interior free boundary, quadratic gap growth, a
mesh-independent one-sided `H^{r+1}` extension, bounded multiplier density,
local interface quasi-uniformity, exact obstacle representation, and the
stated physical-boundary compatibility condition,

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

The proof uses an exact coefficient-to-grid-value estimate and either shared
coefficient clipping or a positive cutoff repair. Independent energy-identity
and Falk arguments give the minimizer estimate. This analytical theorem has
passed an internal adversarial audit but still awaits external expert review.

## Mechanics validation

The project now contains three contact layers:

1. a certified Bernstein approximation of the analytical Hertz line-contact
   pressure with exact resultant force;
2. a plane-strain P1 triangular Hertz/Signorini benchmark;
3. a plane-strain P2 triangular Bernstein–Bézier benchmark whose quadratic
   edge gap is coefficient-certified at every contact-edge point.

On the finest P2 benchmark:

- 20,193 displacement unknowns;
- 15 PDAS iterations;
- contact half-width error `1.02e-4` against the Hertz reference;
- half-load error `1.04e-11`;
- minimum gap coefficient `0`.

At a comparable number of unknowns, the finest P1 half-width error was
approximately `5.00e-3`. An independently initialized L-BFGS-B solve of the
coarse P2 system agreed with PDAS within `3.85e-11` in objective value.

See `benchmarks/HERTZ_SIGNORINI_P2_BERNSTEIN.md` and the corresponding CSV/JSON
files in `results/`.

## GitHub-only external review

No email campaign is used. Public review work packages are:

- issue #98: prior-art collision;
- issue #99: Mosco/FEM recovery;
- issue #100: regular free-boundary clipping and the `3/2` rate;
- issue #101: Lean statement faithfulness.

Counterexamples, prior-art collisions, and corrected narrower theorems are
explicitly accepted as successful audit outcomes.

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
boundary-touching free boundaries, arbitrary inexact obstacles,
measure-valued multipliers without further hypotheses, nonsymmetric operators,
or optimal adaptive complexity without a specified refinement-closure theorem.
The general Mosco and strong-minimizer convergence theorems are broader but
remain analytical rather than Lean-formalized.
