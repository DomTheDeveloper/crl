# Full Internal AI Red-Team Audit

**Target:** Bernstein-Bézier obstacle theorem package  
**Frozen mathematical baseline:** `review/bernstein-obstacle-v1` at
`209460f762b24d05534075424a5a3864cc5edb9c`  
**Audit type:** Internal AI adversarial review. This is not independent expert
verification.

## Executive verdict

**PASS AFTER CORRECTION**

No fatal counterexample was found to the general Mosco theorem, the
coefficient-to-value estimate, the clipping construction, or the
codimension-one `h_Gamma^(3/2)` scaling mechanism.

Two material corrections are needed before the sharp theorem should be treated
as submission-ready:

1. The localization proof requires an explicit relationship between the
   distance to the free boundary and the *local* element diameter outside the
   risky strip.
2. The bulk `O(h^r)` statement requires a uniform broken `H^(r+1)` assumption
   over all non-risky elements, not the unqualified phrase "piecewise
   H^(r+1)".

The numerical certificate and solver evidence passed. The manuscript's
"nearly factor fifty" Hertz contact-width claim is not robust under neighboring
meshes and should be narrowed or removed from the abstract.

## Severity scale

- **Fatal:** invalidates the central result.
- **Major:** theorem or headline claim requires correction before submission.
- **Moderate:** important scope, literature, or reproducibility correction.
- **Minor:** exposition or terminology.

## Findings

### A1. General Bernstein-cone Mosco convergence

**Verdict: PASS**  
**Confidence: 92%**

The proof has the correct Mosco structure:

- coefficient feasibility gives an inner approximation of the continuous cone;
- nonnegative smooth compactly supported functions are dense in the positive
  `H_0^1` cone;
- the positive Bernstein sampling operator is conforming and boundary
  preserving;
- fixed-degree affine reproduction gives strong `H^1` convergence for each
  smooth recovery;
- a diagonal sequence gives general recovery;
- the continuous cone is closed and convex, hence weakly closed.

The positive-part and mollification argument should cite the continuity of the
positive-part Nemytskii map in `H^1`, but this is not a substantive gap.

### A2. Strong convergence of minimizers

**Verdict: PASS**  
**Confidence: 95%**

Coercivity gives boundedness, Mosco recovery gives the energy limsup, weak
lower semicontinuity gives the liminf, and uniqueness identifies the full weak
limit. Convergence of the quadratic energy norm then gives strong convergence.

### A3. Coefficient-to-grid-value estimate

**Verdict: PASS**  
**Confidence: 96%**

The inverse collocation matrix is fixed for degree and dimension. Exact
constant and affine moment cancellation removes the zero- and first-order
Taylor terms. Taking absolute values of the inverse-matrix entries gives the
required `O(h_T^2)` coefficient error.

The all-degree barycentric-lattice unisolvence argument is valid.

### A4. Localization outside the risky strip

**Verdict: PASS AFTER MAJOR CORRECTION**  
**Severity: Major**

The manuscript defines

```text
R_h = {T : dist(T, Gamma) <= kappa h_Gamma}
```

but the proof then uses

```text
dist(T, Gamma) >= c kappa h_T.
```

That implication does not follow from the stated mesh assumption when the
interface mesh is much finer than elements in a transition region.

A sufficient corrected formulation is:

```text
R_h = {T : dist(T, Gamma) <= kappa h_T},
```

together with

```text
h_T comparable to h_Gamma on the one-ring enlargement omega_h,
|omega_h| <= C h_Gamma.
```

Equivalently, retain the current strip but explicitly assume

```text
dist(T, Gamma) >= kappa_0 h_T
```

for every positive non-risky element in the tubular neighborhood, with
`kappa_0` large enough for coefficient positivity.

This is a theorem-narrowing mesh-grading condition, not a failure of the
clipping idea.

### A5. Uniform bulk interpolation

**Verdict: PASS AFTER MODERATE CORRECTION**  
**Severity: Moderate**

"Piecewise `H^(r+1)` away from the interface" is ambiguous. It does not by
itself guarantee a mesh-independent broken interpolation constant unless the
pieces are mesh aligned or the broken seminorm is uniformly bounded.

A direct sufficient assumption is

```text
sum over T outside omega_h of |u|_(H^(r+1)(T))^2 <= C,
```

or the corresponding weighted estimate needed for the `h^r` interpolation
bound.

### A6. Clipping, conformity, and the `3/2` exponent

**Verdict: PASS under the corrected mesh assumptions**  
**Confidence: 88%**

Once negative coefficients are confined to a locally quasi-uniform
codimension-one patch and are `O(h_Gamma^2)`:

- global clipping preserves common-face traces;
- homogeneous boundary coefficients remain zero;
- the correction gradient is `O(h_Gamma)` pointwise in scale;
- the patch volume is `O(h_Gamma)`;
- therefore the squared `H^1` repair cost is `O(h_Gamma^3)` and the norm is
  `O(h_Gamma^(3/2))`.

The exponent itself is not the weak point. Localization and mesh hypotheses are
the weak point.

### A7. Multiplier and minimizer transfer

**Verdict: PASS under the stated bounded-density assumption**  
**Confidence: 90%**

The energy identity has the correct sign. On contact, the repaired field is
nonnegative and `O(h_Gamma^2)` over a set of measure `O(h_Gamma)`, yielding the
`O(h_Gamma^3)` multiplier contribution. The Falk route gives the same result.

Measure-valued multipliers remain excluded and should stay excluded.

### A8. Physical-boundary treatment

**Verdict: PASS AFTER EXPLANATORY EXPANSION**  
**Severity: Moderate**

The linear inward lower bound can dominate the coefficient discrepancy for
off-boundary control points, while boundary-face coefficients are exactly zero.
The proof should state this face/off-face split explicitly.

### A9. Lean correspondence

**Verdict: PASS**  
**Confidence: 98%**

The formalization accurately verifies the finite certificate, simplicial
basis, global clipping, projection/KKT identities, finite assembly, finite
Mosco infrastructure, energy identities, and the Hilbert-space VI
Pythagorean/uniqueness layer.

It does not verify the moving physical Sobolev finite-element theorem or the
free-boundary rate, and the theorem index discloses this.

The manuscript should use "machine checked" rather than "independently machine
checked" to avoid suggesting an independent research group performed the
formalization.

### A10. Hertz benchmark headline

**Verdict: CLAIM NARROWING REQUIRED**  
**Severity: Major for the abstract, not for the theorem**

The selected quadratic mesh with 160 angular intervals gives a bracketed
contact-width error near `1.01e-4`, approximately 49 times smaller than the
selected finest linear result.

Fresh neighboring-mesh tests show that this metric is strongly phase
sensitive:

| Angular intervals | Unknowns | Bracketed error | Fitted error |
|---:|---:|---:|---:|
| 145 | 15,979 | 3.055e-3 | 3.544e-4 |
| 155 | 19,563 | 2.346e-3 | 8.385e-4 |
| 160 | 20,193 | 1.011e-4 | 9.419e-4 |
| 165 | 20,823 | 2.400e-3 | 2.712e-5 |
| 170 | 22,815 | 4.289e-5 | 1.551e-3 |

The exact-feasibility, KKT, force-balance, and cross-framework conclusions
survive. The single-mesh "nearly fiftyfold" statement should be replaced by:

> At one matched-size mesh pair, the bracketed active-set width metric was
> approximately 49 times smaller; neighboring meshes reveal phase sensitivity,
> while the quadratic method consistently preserves exact coefficient
> feasibility and improves the pressure profile relative to the linear
> discretization.

The pressure `L2` error and convergence envelopes are more credible comparison
metrics than one bracketed active-boundary location.

### A11. Numerical independence

**Verdict: PASS WITH SCOPE LABEL**

The scikit-fem implementation independently assembles the elasticity operator,
but imports the custom project's geometric mesh generator and uses the same
physical benchmark and related active-set logic. It is a valuable
cross-framework check, not a clean-room third-party replication.

### A12. Novelty and literature boundary

**Verdict: LIKELY NOVEL COMBINATION; LITERATURE EXPANSION REQUIRED**

The strongest novelty claim remains plausible:

- coefficient-feasible simplicial obstacle cones;
- Mosco convergence of those cones;
- shared-coefficient free-boundary clipping;
- a quantified `h^r + h_Gamma^(3/2)` rate.

However, the paper should explicitly discuss and cite:

1. Allen-Kirby on Bernstein coefficient-constrained polynomial approximation;
2. Kirby-Shapero, which explicitly leaves the practical Bernstein subset
   without a high-accuracy theorem;
3. Banz et al. on higher-order obstacle FEM;
4. Keith-Surowiec's proximal Galerkin method for high-order pointwise
   constraints;
5. the 2026 GLL-constrained hp/spectral obstacle method.

The paper should not claim to be the first high-order, pointwise
bound-preserving obstacle method. Its defensible novelty is the *specific
coefficient-cone convergence and free-boundary repair theorem*.

## Required manuscript corrections

1. Replace the risky-set/mesh assumption by a local-distance formulation.
2. State a uniform broken `H^(r+1)` assumption outside the interface strip.
3. Expand the boundary-face coefficient argument.
4. Remove or qualify the nearly-50-times claim in the abstract and conclusion.
5. Add the missing nearest-neighbor literature.
6. Replace "independently machine checked" by "machine checked under a pinned
   Lean/mathlib toolchain".
7. Describe the 3D spherical test as a scalar obstacle test unless vector
   elasticity is actually being solved.

## Final confidence assessment

| Claim | Audit confidence |
|---|---:|
| Exact coefficient feasibility | 99% |
| General Mosco convergence | 92% |
| Strong minimizer convergence | 95% |
| Coefficient-to-value estimate | 96% |
| Clipping conformity | 95% |
| `h_Gamma^(3/2)` scaling conditional on localization | 88% |
| Sharp theorem exactly as currently stated | 58% |
| Sharp theorem after the mesh/regularity corrections | 82% |
| Central novelty combination | 75% |
| Strong publishable theorem package after correction | 88% |
| Independently confirmed major breakthrough | Not established |

## Bottom line

The AI audit did not find a fatal flaw. It did find one substantive hypothesis
mismatch in the sharp theorem and one overinterpreted numerical headline.

The appropriate status is:

> **General theorem: passes internal AI audit.**  
> **Sharp theorem: passes after explicit mesh and broken-regularity corrections.**  
> **Numerics: certificate passes; the fiftyfold headline must be narrowed.**  
> **Breakthrough status: credible candidate, still awaiting independent human
> review.**
