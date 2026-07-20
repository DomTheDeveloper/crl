# Independent audit request: Bernstein–Bézier obstacle theorem

## Purpose

This document is a reviewer-facing checklist. It is deliberately adversarial:
a successful review must verify each dependency independently or identify a
counterexample, missing hypothesis, or unjustified implication.

## Theorems under review

### General theorem

For fixed-degree conforming simplicial Bernstein finite elements on a
shape-regular mesh family, let

\[
K_h^B=\{v_h\in V_h^r: b_{T,\alpha}(v_h)\ge0\ \forall T,\alpha\},
\qquad
K=\{v\in H_0^1(\Omega):v\ge0\text{ a.e.}\}.
\]

Claim:

\[
K_h^B\xrightarrow{M}K,
\]

and minimizers of symmetric continuous coercive obstacle energies converge
strongly in \(H_0^1\).

### Scoped sharp theorem

Under a compact regular interior free boundary, quadratic gap growth,
\(C^{1,1}\) regularity, piecewise \(H^{r+1}\) regularity away from the free
boundary, bounded multiplier, local quasi-uniformity in the interface strip,
exact obstacle representation, and the stated physical-boundary compatibility
condition, claim:

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\left(h^r+h_\Gamma^{3/2}\right).
\]

## Required audit checks

1. **Cone inclusion.** Verify that global coefficient identification on shared
   faces makes coefficient nonnegativity imply a globally continuous,
   pointwise-feasible function.
2. **Positive density.** Verify that nonnegative smooth compactly supported
   functions are dense in \(H_0^1(\Omega)\cap\{v\ge0\}\), including the exact
   construction used for the diagonal recovery sequence.
3. **Positive Bernstein operator.** Verify global conformity, boundary-trace
   preservation, affine reproduction, stability, and fixed-degree \(H^1\)
   convergence on shape-regular simplices.
4. **Mosco weak condition.** Verify weak closure of the continuous obstacle
   cone and ensure no hidden pointwise-convergence assumption is used.
5. **Minimizer convergence.** Check both the Mosco/projection proof and the
   direct energy proof.
6. **Coefficient lemma.** Re-derive the affine moment identities and the
   \(O(h_T^2)\) coefficient-to-barycentric-grid-value estimate.
7. **Localization.** Verify that two-sided quadratic growth dominates the
   coefficient error outside a fixed-width element strip.
8. **Contact interior.** Check exactly when an element interpolant is identically
   zero and how transition elements are classified.
9. **Clipping conformity.** Verify that clipping shared global Bernstein
   coefficients preserves \(C^0\) conformity and homogeneous boundary data.
10. **Repair norm.** Recompute the local and global scaling that yields
    \(O(h_\Gamma^{3/2})\) in the energy norm in dimensions two and three.
11. **Bulk/strip split.** Verify the use of high-order regularity away from the
    interface and only \(C^{1,1}\) regularity in the strip.
12. **Multiplier term.** Verify support, sign, density assumptions, and the
    \(O(h_\Gamma^3)\) estimate before taking square roots.
13. **Physical boundary.** Test whether the stated boundary compatibility is
    sufficient and whether an omitted boundary-strip term is needed.
14. **Subdivision correction.** Confirm that strict positivity is eventually
    certified but general nonnegative polynomials with zeros need not be.
15. **Numerical reproduction.** Re-run the deterministic scripts and compare
    all CSV fields and KKT residuals.
16. **Novelty.** Check the exact combined claim against Allen–Kirby,
    Kirby–Shapero, hp/SEM obstacle methods, proximal DG/Galerkin, Signorini
    barrier methods, and bounds-constrained time-dependent implementations.

## Evidence already supplied

- `proof_packet_VI_summary.md`
- `research_packet_V.md`
- `verification/verify_bernstein_coefficient_constants.py`
- `verification/bernstein_coefficient_constants.csv`
- `results/bernstein_clipping_phase_locked_results.csv`
- deterministic 1D/2D contact and adaptive benchmark programs
- pinned Lean project for the finite certificate/no-penetration bridge

## Acceptance standard

A positive audit must state the exact theorem and hypotheses accepted, list all
files/checks run, and provide either a line-by-line argument or references for
each nontrivial external theorem. “The numerics look correct” is not an
acceptable mathematical audit.

## Proposed audit bounty

- **$7,500:** complete written mathematical audit with explicit pass/fail for
  all 16 items.
- **$15,000:** audit plus independent code reproduction and either a signed
  theorem endorsement or a concrete counterexample/fix for every failed item.

These are proposed project bounties, not claims about a standardized market
rate.
