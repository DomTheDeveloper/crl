# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle methods whose local
Bernstein coefficient constraints guarantee pointwise nonpenetration over the
entire element.

## Proved theorem package

The project now separates two theorem levels.

### General convergence

For fixed-degree conforming simplicial Bernstein finite elements on a
shape-regular mesh family, the coefficient-feasible cones Mosco-converge to

\[
K=H_0^1(\Omega)\cap\{v\ge0\}.
\]

Consequently, minimizers of symmetric continuous coercive obstacle energies
converge strongly in \(H^1\). This statement needs no free-boundary regularity.

### Sharp regular-free-boundary rate

Under a compact regular interior free boundary, quadratic gap growth, bounded
multiplier, local mesh regularity, exact obstacle representation, and the
stated physical-boundary compatibility condition,

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

The proof uses an exact coefficient-to-grid-value estimate and either global
Bernstein coefficient clipping or a positive cutoff repair. Independent energy
identity and Falk arguments give the minimizer estimate.

The repository also contains:

- a complete one-dimensional Mosco recovery theorem;
- a one-dimensional Green-barrier pointwise reliability theorem;
- exact rational verification of Bernstein coefficient moment identities;
- raw and subdivided certified Bernstein cones;
- triangular pointwise-feasible PDAS solvers;
- hybrid and nested adaptive refinement prototypes;
- a physical membrane-contact benchmark and contact-pressure reconstruction;
- reproducible CSV results and plots.

Start with `proof_packet_VI_summary.md`, then `research_packet_V.md` for the
full computational history.

## Important subdivision correction

Subdivision-refined Bernstein cones are nested, and every strictly positive
polynomial is certified after sufficiently fine subdivision. Subdivision does
**not** certify every nonnegative polynomial having zeros; therefore the
free-boundary clipping/repair theorem is essential.

## Reproduce

```bash
python verification/verify_bernstein_coefficient_constants.py
python adaptive_triangular_bernstein.py
python adaptive_hybrid_bernstein.py
python nested_bernstein_refinement.py
python constraint_cone_benchmark.py
python pointwise_barrier_contact_benchmark.py
```

Dependencies: Python 3.11+, NumPy, SciPy, SymPy, pandas, Matplotlib.

## Scope warning

The sharp rate does not claim singular or degenerate free boundaries,
boundary-touching free boundaries, arbitrary inexact obstacles,
measure-valued multipliers without further hypotheses, nonsymmetric operators,
or optimal adaptive complexity without a specified refinement-closure theorem.
The general Mosco and strong-minimizer convergence theorems are broader and do
not require those regular-free-boundary assumptions.
