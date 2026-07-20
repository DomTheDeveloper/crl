# Independent audit request: Bernstein–Bézier obstacle theorem

## Purpose

This document is a reviewer-facing checklist. It is deliberately adversarial:
a successful review must verify each dependency independently or identify a
counterexample, missing hypothesis, or unjustified implication.

The internal audit has already corrected several draft statements. Reviewers
should use the current files, especially `ADVERSARIAL_AUDIT_FINDINGS.md`, and
should not assume that an older manuscript statement remains authoritative.

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

The recovery proof uses nonnegative smooth density followed by a positive
Bernstein sampling operator. The operator is estimated for smooth functions in
`W^{2,infinity}`; no dimension-independent boundedness of point evaluation on
`H^2` may be assumed.

### Scoped sharp theorem

Assume a compact regular interior free boundary, quadratic gap growth,
`C^{1,1}` regularity, a mesh-independent one-sided `H^{r+1}` extension on the
positive side of a fixed tubular neighborhood, bounded multiplier density,
local quasi-uniformity in the interface strip, exact obstacle representation,
and the stated physical-boundary compatibility condition. Claim:

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
   positive-part, mollification, and diagonal construction.
3. **Positive Bernstein operator.** Verify global conformity, boundary-trace
   preservation, affine reproduction, and fixed-degree convergence on
   shape-regular simplices.
4. **Dimension check.** Confirm that the recovery proof uses a
   `W^{2,infinity}` local estimate for sampled coefficients and does not invoke
   dimension-free point evaluation on `H^2`.
5. **Mosco weak condition.** Verify weak closure of the continuous obstacle
   cone and ensure no hidden pointwise-convergence assumption is used.
6. **Minimizer convergence.** Check both the Mosco/projection proof and the
   direct energy proof.
7. **Interpolation unisolvence.** Supply a general-degree proof or a precise
   reference that the degree-`r` barycentric lattice is unisolvent for
   `P_r(T)`. Exact inversions through degree six are evidence, not a general
   theorem.
8. **Coefficient lemma.** Re-derive the affine moment identities and the
   \(O(h_T^2)\) coefficient-to-barycentric-grid-value estimate.
9. **Uniform one-sided regularity.** Verify that the stated extension
   hypothesis supplies a mesh-independent `h^r` interpolation constant for
   non-risky elements approaching the free boundary.
10. **Localization.** Verify that two-sided quadratic growth dominates the
    coefficient error outside a fixed-width element strip.
11. **Risky-element amplitude.** Prove the two-sided bound
    \(|b_{T,\alpha}(I_h^ru)|\le Ch_\Gamma^2\) on every risky element.
12. **Contact interior.** Check exactly when an element interpolant is
    identically zero and how transition elements are classified.
13. **Clipping conformity.** Verify that clipping shared global Bernstein
    coefficients preserves \(C^0\) conformity and homogeneous boundary data,
    including face orientation and multi-index permutations.
14. **Repair norm.** Recompute the local and global scaling that yields
    \(O(h_\Gamma^{3/2})\) in the energy norm in dimensions two and three.
15. **Bulk/strip split.** Verify the use of high-order regularity away from the
    interface and only \(C^{1,1}\) regularity in the strip.
16. **Multiplier term.** Verify support, sign, density assumptions, and the
    \(O(h_\Gamma^3)\) estimate before taking square roots.
17. **Physical boundary.** Test whether the stated boundary compatibility is
    sufficient and whether an omitted boundary-strip term is needed.
18. **Subdivision correction.** Confirm that uniformly shape-regular
    subdivision eventually certifies strict positivity, but general
    nonnegative polynomials with zeros need not be certified.
19. **Numerical reproduction.** Re-run the deterministic scripts and compare
    all CSV fields, independent solver outputs, KKT residuals, and pointwise
    feasibility checks.
20. **Novelty.** Check the exact combined claim against Allen–Kirby,
    Kirby–Shapero, hp/SEM obstacle methods, proximal DG/Galerkin, Signorini
    barrier methods, positive Bernstein finite elements, bounds-constrained
    time-dependent implementations, and prior formal Bernstein/de Casteljau
    work.

## Evidence already supplied

- `proof_packet_VI_summary.md`
- `research_packet_V.md`
- `ADVERSARIAL_AUDIT_FINDINGS.md`
- `verification/verify_bernstein_coefficient_constants.py`
- `verification/bernstein_coefficient_constants.csv`
- `results/bernstein_clipping_phase_locked_results.csv`
- deterministic 1D/2D/3D contact and adaptive benchmark programs
- independent 3D L-BFGS-B versus PDAS comparison
- pinned Lean project for the finite certificate/no-penetration bridge
- successful pinned Lean build and terminal axiom audit

## Acceptance standard

A positive audit must state the exact theorem and hypotheses accepted, list all
files/checks run, and provide either a line-by-line argument or references for
each nontrivial external theorem. “The numerics look correct” is not an
acceptable mathematical audit.

The reviewer must distinguish:

- mathematical validity;
- novelty;
- faithful correspondence between manuscript and code;
- Lean compilation versus faithful formalization of the paper theorem.

## Proposed audit bounty

- **$7,500:** complete written mathematical audit with explicit pass/fail for
  all 20 items.
- **$15,000:** audit plus independent code reproduction and either a signed
  theorem endorsement or a concrete counterexample/fix for every failed item.

These are proposed project bounties, not claims about a standardized market
rate.
