# Bernstein–Bézier obstacle V5 hardening

Base: immutable V4 theorem target `61594952ad880d2b61759cfa93a19df979183c09`.

This branch targets the concrete analytical gaps that V4 intentionally leaves as hypotheses.

## Current target

Formalize exact affine reproduction of the positive simplex Bernstein sampling operator. The core first-moment identity is

\[
\sum_{|\alpha|=n} \frac{\alpha_j}{n} B_\alpha^n(x)=x_j.
\]

This identity supplies the affine cancellation required by both:

- the fixed-degree local `W^{2,\infty}` Bernstein recovery estimate used in the moving Sobolev/Mosco theorem;
- the `O(h_T^2)` coefficient-to-lattice-value estimate used in free-boundary localization.

## Trust boundary

No V5 result is called verified until it compiles with the pinned Lean/mathlib environment and its exact endpoint appears in a `#print axioms` audit with no `sorryAx`.
