# Adversarial internal audit findings

Date: 2026-07-20

This document records an attempt to falsify the headline theorems before
external review. It is not an independent endorsement. The audit deliberately
looked for dimension errors, hidden regularity assumptions, invalid uses of
point evaluation, loss of conformity under clipping, and incorrect
free-boundary scaling.

## Corrections found and incorporated

### 1. Positive sampling operator: dimension-sensitive point evaluation

An earlier draft described a local `H^2 -> H^1` estimate for an operator whose
coefficients are point samples. Point evaluation is not a dimension-free
bounded functional on `H^2(T)`, so that formulation was unsafe in high
dimension.

The corrected statement assumes `w in W^{2,infty}(T)` and proves

```text
||w - B_T^r w||_{L2(T)}
  <= C_r h_T^2 |T|^(1/2) ||D^2 w||_{Linfty(T)},

||grad(w - B_T^r w)||_{L2(T)}
  <= C_r h_T |T|^(1/2) ||D^2 w||_{Linfty(T)}.
```

This is sufficient for the Mosco recovery theorem because the recovery first
approximates a nonnegative `H_0^1` function by a smooth compactly supported
function and only then applies the sampling operator. The general convergence
theorem therefore remains dimension-independent.

### 2. Uniform high-order regularity approaching the free boundary

The phrase “piecewise `H^{r+1}` away from the free boundary” did not by itself
provide a uniform bulk interpolation constant for non-risky elements whose
distance from the interface is proportional to their diameter.

The sharp theorem now assumes a one-sided `H^{r+1}` extension on the positive
side of a fixed tubular neighborhood, with a mesh-independent norm, plus
`H^{r+1}` regularity on the remaining positive phase.

### 3. Two-sided risky-element coefficient bound

The multiplier estimate needs an upper amplitude bound on the clipped recovery
inside the contact portion of the risky strip. The localization lemma now
states explicitly

```text
|b_{T,alpha}(I_h^r u)| <= C h_Gamma^2
```

for every risky element, not merely a lower bound on negative coefficients.
Quadratic upper growth and the coefficient-to-grid-value estimate prove this.

### 4. Subdivision theorem needs shape regularity

The strict-positivity certification theorem now requires a uniformly
shape-regular nested subdivision family with maximal cell diameter tending to
zero. Diameter decay alone does not control affine-scaling constants on
arbitrarily degenerate simplices.

### 5. General-degree interpolation unisolvence

Exact rational inverse collocation matrices were checked only through degree
six. Those computations verify examples and constants, not the general
existence theorem. The paper must cite or prove unisolvence of interpolation at
the degree-`r` barycentric lattice for arbitrary fixed `r` before using the
inverse collocation matrix abstractly.

## Current audit status by dependency

| Dependency | Internal status | Residual external-review question |
|---|---|---|
| Bernstein cone implies pointwise feasibility | Pass | Check global face orientation/index identification in implementation |
| Nonnegative smooth density in the obstacle cone | Pass | Reviewer should verify the positive-part and mollification diagonal argument |
| Smooth positive Bernstein recovery | Pass after W2-infinity correction | Check affine-scaling constants on the chosen mesh family |
| Mosco weak condition | Pass | None beyond standard weak closure of closed convex sets |
| Strong minimizer convergence | Pass by projection and energy routes | Confirm the exact Mosco-to-projection theorem used |
| Coefficient-to-value estimate | Pass conditionally | Requires general barycentric-lattice unisolvence |
| Localization outside risky strip | Pass under stated growth/mesh assumptions | Check constants and physical-boundary hypothesis |
| Clipping preserves conformity | Pass | Verify shared face coefficients use a single global orientation-independent DOF |
| Repair norm `O(h_Gamma^(3/2))` | Pass for locally quasi-uniform isotropic interface patch | Anisotropic meshes are excluded |
| Multiplier term `O(h_Gamma^3)` | Pass for nonnegative `L^infinity` density supported in contact set | Measure-valued multipliers are excluded |
| Subdivision completeness | Corrected | Only strict positivity is eventually certified |
| General sharp theorem | Conditional pass | Needs independent line-by-line review of all explicit hypotheses |

## Falsification tests for external reviewers

The sharp theorem should be rejected or restated if any reviewer finds one of
the following:

1. a conforming finite-element orientation for which shared face Bernstein
   coefficients are not identified consistently under clipping;
2. a regular quadratic-growth free-boundary example satisfying the stated
   hypotheses but having an `O(1)` negative interpolant coefficient outside the
   risky strip;
3. failure of the one-sided extension assumption to imply uniform `h^r` bulk
   interpolation on the non-risky positive elements;
4. a mesh satisfying the stated local quasi-uniformity assumptions whose
   fixed-layer risky patch has volume larger than `C h_Gamma`;
5. a contact-side clipped recovery whose amplitude exceeds `C h_Gamma^2`;
6. an incorrect sign in the multiplier energy identity or Falk estimate;
7. a counterexample to the positive smooth density construction in the stated
   polyhedral Lipschitz domain setting.

## Formal and computational checks completed

- The one-dimensional Bernstein finite certificate, convex-hull bounds,
  coefficient clipping, and obstacle no-penetration theorem compile under
  pinned Lean `v4.33.0-rc1`.
- The terminal `#print axioms` audit reports only the standard mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears.
- A separate 3D L-BFGS-B solve from the zero vector matches the PDAS objective
  to `2.22e-16`, the coefficient vector to `4.08e-9` in `L-infinity`, and
  remains nonnegative at 54,791 independently evaluated points.
- Three pre-existing numerical tables were regenerated exactly from clean
  executions.

## Trust boundary

The corrected theorem package has passed this internal adversarial audit. It
has **not** yet received an independent expert endorsement. The external audit
issue remains open, and publication claims should say “proved under the stated
hypotheses; independent review requested,” not “independently verified.”
