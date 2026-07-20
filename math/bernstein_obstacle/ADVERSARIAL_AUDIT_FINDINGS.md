# Adversarial internal audit findings - corrected status

Date: 2026-07-20

This file records internal attempts to falsify the headline theorems. It is not an independent endorsement.

## Final internal verdict

**PASS AFTER CORRECTION**

No fatal counterexample was found to:

- the general Bernstein-cone Mosco theorem;
- strong convergence of the constrained minimizers;
- the coefficient-to-grid-value estimate;
- conformity-preserving shared-coefficient clipping;
- the codimension-one `h_Gamma^(3/2)` repair mechanism.

The audit found two material issues that are now incorporated into the theorem statement and proof packet:

1. localization must compare distance to the **local element diameter** `h_T`, not only to one global interface scale;
2. the bulk `O(h^r)` estimate needs a uniform broken `H^{r+1}` bound.

It also found that a selected-mesh Hertz contact-width improvement factor was phase sensitive and should not be presented as a uniform numerical rate.

## Corrections incorporated

### 1. Dimension-safe positive sampling estimate

The positive sampling operator is applied only to smooth recovery functions. The local estimate is stated in `W^{2,infinity}` form:

```text
||w - B_T^r w||_L2
  <= C h_T^2 |T|^(1/2) ||D^2 w||_Linfinity,

||grad(w - B_T^r w)||_L2
  <= C h_T |T|^(1/2) ||D^2 w||_Linfinity.
```

This avoids a false dimension-independent point-evaluation assertion on `H^2`.

### 2. Uniform regularity

The sharp theorem now assumes:

- a mesh-independent one-sided `H^{r+1}` extension near the regular interface;
- a uniform broken bound outside the risky patch:
  \[
  \sum_{T\notin\omega_h}|u|_{H^{r+1}(T)}^2\le C_{\rm reg}.
  \]

### 3. Local-distance risky set

The risky set is now
\[
\mathcal R_h=\{T:\operatorname{dist}(T,\Gamma)\le\kappa h_T\}.
\]
On its fixed one-ring enlargement,
\[
c_mh_\Gamma\le h_T\le C_mh_\Gamma,
\qquad |\omega_h|\le C_\Gamma h_\Gamma.
\]

This closes the mismatch between a strip defined using `h_Gamma` and a positivity proof requiring distance larger than a multiple of `h_T`.

### 4. Physical-boundary split

For a positive boundary element:

- boundary-face Bernstein coefficients are exactly zero;
- every off-face lattice point is a distance comparable to `h_T` inside the domain;
- the inward linear lower bound is `O(h_T)` and dominates the `O(h_T^2)` coefficient discrepancy.

### 5. Two-sided risky coefficient bound

On every risky element,
\[
|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2.
\]
This is needed for the repair norm and multiplier term.

### 6. Shape-regular subdivision

Strict-positivity certification by subdivision is stated only for uniformly shape-regular nested subdivisions whose maximum cell diameter tends to zero.

### 7. General-degree unisolvence

Barycentric-lattice interpolation is justified for arbitrary fixed degree by an explicit cardinal-polynomial proof. Exact inversions through degree six are treated only as verification examples.

### 8. Hertz numerical claim

The approximately `48.9×` contact-width comparison occurred at one selected matched-size mesh pair. Neighboring meshes show phase sensitivity in both the bracketed and pressure-fitted contact-width estimators. The corrected manuscript:

- removes the factor from the abstract;
- labels the original table as a selected-mesh comparison;
- adds neighboring-mesh sensitivity data;
- emphasizes pressure error, force balance, KKT residuals, geometry quality, and exact coefficient feasibility.

The scikit-fem calculation is described as a second assembly framework developed within the project, not as a third-party clean-room replication.

## Current status by dependency

| Dependency | Internal status | Remaining external question |
|---|---|---|
| Bernstein coefficients imply pointwise feasibility | Pass | Concrete implementation indexing review |
| Nonnegative smooth density | Pass | Human verification of positive-part/mollifier details |
| Smooth positive Bernstein recovery | Pass | Check affine-scaling constants |
| Mosco weak condition | Pass | Standard weak-closure audit |
| Strong minimizer convergence | Pass | Check exact energy assumptions |
| Coefficient-to-value estimate | Pass | Human review of all-degree presentation |
| Localization | Pass after local-size correction | Are grading assumptions optimal/natural? |
| Clipping conformity | Pass | Concrete mesh orientation audit |
| `h_Gamma^(3/2)` repair scaling | Pass under corrected patch assumptions | Anisotropic extension excluded |
| Multiplier term | Pass for bounded density | Measure multipliers excluded |
| Physical boundary | Pass after face/off-face expansion | Human review of boundary geometry |
| Hertz certificate and force balance | Pass | External independent reproduction |
| Uniform `48.9×` claim | Rejected | Replaced by selected-mesh statement |
| Full sharp theorem | Conditional pass | Independent line-by-line mathematical review |

## Trust boundary

The corrections improve the internal logical consistency of the sharp theorem. They do not constitute independent verification. Publication language should say:

> proved under the stated local grading, regularity, multiplier, and boundary hypotheses; independent expert review requested.

The finite algebraic and Hilbert-space layers are machine checked under pinned Lean/mathlib toolchains. The moving Sobolev finite-element realization and free-boundary analysis remain analytical.
