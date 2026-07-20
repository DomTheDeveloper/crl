# Bernstein–Bézier Obstacle Variational Inequalities

Research project on high-order finite-element obstacle methods whose local
Bernstein coefficient constraints guarantee pointwise nonpenetration over the
entire element.

## Current main candidate result

For a regular interior free boundary with quadratic gap growth and a bounded
multiplier, the working theorem is

\[
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
\]

The repository also contains:

- a complete one-dimensional Mosco recovery theorem;
- a one-dimensional Green-barrier pointwise reliability theorem;
- raw and subdivided certified Bernstein cones;
- triangular pointwise-feasible PDAS solvers;
- hybrid and nested adaptive refinement prototypes;
- a physical membrane-contact benchmark and contact-pressure reconstruction;
- reproducible CSV results and plots.

Start with `research_packet_V.md`.

## Reproduce

```bash
python adaptive_triangular_bernstein.py
python adaptive_hybrid_bernstein.py
python nested_bernstein_refinement.py
python constraint_cone_benchmark.py
python pointwise_barrier_contact_benchmark.py
```

Dependencies: Python 3.11+, NumPy, SciPy, SymPy, pandas, Matplotlib.

## Scope warning

The multidimensional free-boundary estimate is currently proved only under a
restricted regular-free-boundary hypothesis and still needs independent
publication-level auditing. Numerical prototypes are deterministic research
code, not production contact mechanics software.
