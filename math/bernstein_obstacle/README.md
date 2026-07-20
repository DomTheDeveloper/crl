# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle and contact methods whose
local Bernstein coefficient constraints guarantee pointwise nonpenetration over
the complete constrained entity.

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

Consequently, solutions of the certified discrete variational inequalities
converge strongly in `H^1`. The complete moving-space analytical argument is in
`GENERAL_MOSCO_PUBLICATION_PROOF.md`; it includes nonnegative smooth density,
the conforming positive Bernstein recovery operator, a dimension-safe
`W^{2,infinity}` estimate, the diagonal sequence, weak closure, and the direct
strong-convergence argument.

The theorem needs no free-boundary regularity and is valid in every fixed finite
dimension. The abstract finite/Hilbert reductions are machine checked, but the
concrete moving Sobolev/FEM realization has not yet been formalized in Lean or
independently endorsed.

### Scoped sharp scalar theorem

The scalar obstacle theorem is stated for `d = 2` or `d = 3` and fixed
polynomial degree `r >= 1`. More generally, it applies when the pointwise
barycentric interpolation is well defined, for example under `r + 1 > d/2`.
Under a compact regular interior free boundary, quadratic gap growth, a
mesh-independent one-sided `H^{r+1}` extension, bounded multiplier density,
local interface quasi-uniformity, exact obstacle representation, and either a
boundary-separating contact collar or a uniform `C^{1,1}` physical-boundary
collar with inward linear growth,

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

The full scoped argument is in `SHARP_RATE_PUBLICATION_PROOF.md`.

## Grand theorem: nonlinear certified inner approximation

`BERNSTEIN_GRAND_THEOREM.md` proves the abstract estimate

\[
\|u-u_h\|_V^2
\le
\frac{L^2}{\alpha^2}\|u-v_h\|_V^2
+\frac{2}{\alpha}\langle F(u),v_h-u\rangle
\qquad(v_h\in K_h\subset K)
\]

for every Lipschitz, strongly monotone operator `F`. The operator may be
nonlinear, nonsymmetric, and nonpotential. Therefore the certified convergence
and sharp recovery mechanism do not fundamentally depend on a quadratic energy.

The same note proves a geometric repair law for a unilateral constraint imposed
on a manifold of ambient codimension `c`:

\[
\|d_h\|_V=O\bigl(h_\Sigma^{(c+3)/2}\bigr).
\]

A bounded multiplier on the active transition strip contributes

\[
\langle F(u),v_h-u\rangle=O(h_\Sigma^3),
\]

independently of `c`. Consequently both

- a scalar interior obstacle (`c=0`), and
- planar frictionless Signorini contact (`c=1`)

obey the common final estimate

\[
\boxed{
\|u-u_h^B\|_V
\le C(h^r+h_\Sigma^{3/2}).
}
\]

The planar-contact corollary uses a constant contact normal and a stable global
normal-control-point lifting. Conservative one-sided obstacle and clearance
approximations are included with explicit additive consistency terms.

This is an internally proved analytical theorem package. Its exact novelty,
contact lifting assumptions, and literature position remain under independent
review; see `GRAND_THEOREM_PRIOR_ART_MAP.md`.

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

The current grand theorem does not claim singular or degenerate active-set
interfaces, contact transitions meeting incompatible essential boundaries,
curved contact with changing normals without a stable gap lifting, Coulomb
friction, merely monotone operators, nodal interpolation outside the stated
dimension/regularity regime, nonconservative obstacle or clearance errors,
measure-valued multipliers, anisotropic interface patches without a new scaling
audit, or optimal adaptive complexity. The moving Sobolev/FEM and nonlinear
physical realizations remain analytical rather than fully Lean-formalized.
