# Grand Bernstein–Bézier formalization map

Date: 2026-07-20

Canonical branch: `formal/bernstein-bezier-grand-canonical`

Base commit: `263acf15f4defef8b6999ce5d6f3d0adb5517028`

## Status vocabulary

- **Verified on base:** compiled and axiom-audited on the inherited v3 branch.
- **Previously verified, newly consolidated:** compiled on a separate pinned branch;
  copied into the canonical branch, which still needs its own integration audit.
- **New Lean proof, integration audit pending:** proof source exists without
  `sorry`; a fresh canonical build is required before verification is claimed.
- **Formal reduction:** Lean proves the endgame from explicit hypotheses, while
  the physical analytical construction of those hypotheses remains outside the
  kernel.
- **Analytical only:** no faithful Lean realization yet.

## I. Exact coefficient certification

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Univariate coefficient interval implies pointwise interval | `curve_mem_Icc` | Verified on base |
| Simplicial coefficient interval implies pointwise interval | `simplexFieldNat_mem_Icc` | Verified on base |
| Variable-obstacle affine normalization preserves bounds | `affineBox_mem_Icc` | Previously verified, newly consolidated |
| Exact univariate bilateral obstacle field | `boxApprox_mem_Icc` | Previously verified, newly consolidated |
| Exact simplicial bilateral obstacle field | `simplexBoxApproxNat_mem_Icc` | Previously verified, newly consolidated |

Canonical component name: **Bézier Inner-Cone Certificate**.

## II. Mosco convergence

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Sequential Mosco definition | `MoscoConverges` | Verified on base |
| Weak closedness + recovery + inner inclusion imply Mosco | `BilateralBarrierEnvelopeData.moscoConverges` | New Lean proof, integration audit pending |
| Exact inner inclusion and Mosco packaged together | `BilateralBarrierEnvelopeData.inner_and_mosco` | New Lean proof, integration audit pending |
| Concrete `W_0^{1,p}` strict feasible density | — | Analytical only |
| Positive Bernstein sampling in moving physical meshes | abstract recovery data only | Formal reduction |
| Conservative sampled variable-obstacle envelopes | exact finite certificate formalized; Sobolev estimates analytical | Formal reduction |

Canonical component name: **Bernstein–Bézier Barrier Envelope Theorem**.

## III. Hilbert variational-inequality endgame

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| VI Pythagorean inequality | `hilbert_vi_pythagorean` | Previously verified, newly consolidated |
| VI uniqueness | `hilbert_vi_unique` | Previously verified, newly consolidated |
| Nested recovery error estimate | `nested_hilbert_vi_recovery_error_sq` | Previously verified, newly consolidated |
| Strong convergence from strong feasible recovery | `nested_hilbert_vi_strongConvergence_of_recovery` | Previously verified, newly consolidated |
| Barrier-envelope Mosco + strong VI convergence | `BilateralBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence` | New Lean proof, integration audit pending |

Canonical umbrella name: **Bernstein–Bézier Grand Barrier Theorem**.

## IV. Universal and nonlinear transfer algebra

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Two squared scales imply a norm-rate sum | `twoScaleRate_of_energy_components` | Previously verified, newly consolidated |
| Universal first-order transfer | `universalFirstOrderRate_of_recovery_and_measure` | Previously verified, newly consolidated |
| Strongly monotone inner-cone Young/Falk endgame | `monotoneInnerCone_falk_sq` | New Lean proof, integration audit pending |
| Exact-recovery strongly monotone estimate | `monotoneInnerCone_exactRecovery_sq` | New Lean proof, integration audit pending |
| Full operator derivation from strong monotonicity and Lipschitz continuity | scalar endgame formalized | Formal reduction |
| Concrete nonsymmetric/nonpotential PDE operators | — | Analytical only |

Canonical component name: **Bernstein–Bézier Inner-Cone Falk Theorem**.

## V. Interface-rate algebra

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Repair exponent `beta-1+kappa/q` | `repairExponent` | New Lean definition, integration audit pending |
| Multiplier exponent `(beta+kappa)/q` | `multiplierExponent` | New Lean definition, integration audit pending |
| Classical exponent is `3/2` | `threeHalvesContactLaw` | New Lean proof, integration audit pending |
| Balanced order is `q/(q-1)` | `balancedContactOrder_equalizes` | New Lean proof, integration audit pending |
| Patch norm estimate producing the repair exponent | existing `StripScaling` for the quadratic case | Verified on base / general `q` analytical |
| General Bregman `q`-root transfer | — | Analytical only |
| Minkowski-codimension geometric patch estimate | — | Analytical only |
| Exact phase-locked sharpness example | Python/SymPy certificate on a separate research branch | Computational, not Lean |

Canonical names:

- **Bernstein–Bézier Codimension–Growth Clipping Law**;
- **Three-Halves Contact Law**;
- **Balanced Contact Exponent Principle**;
- **Bernstein–Bézier Bregman Transfer Theorem**.

## VI. Physical analytical layer still required

The following items cannot honestly be labeled fully formalized yet:

1. a concrete simplicial mesh family embedded in `W_0^{1,p}(Omega)`;
2. trace and conformity theory for the physical moving spaces;
3. strict smooth density inside variable bilateral obstacle intervals;
4. the dimension-safe positive sampling estimates in `W^{1,p}`;
5. conservative envelope estimates uniform over the mesh family;
6. one-sided extension and broken regularity near the free boundary;
7. tubular/interface geometry and patch-measure estimates;
8. multiplier support and density/measure arguments;
9. the general `q`-Bregman coercivity and smoothness inequalities;
10. operator-specific p-Laplacian or Leray–Lions free-boundary growth;
11. curved changing-normal Signorini contact and stable normal lifting;
12. anisotropic mesh variants.

These are not hidden assumptions. Every eventual terminal theorem must expose
them as structure fields until the corresponding mathematical libraries are
built.

## VII. Canonical dependency order

1. `Core`, simplex basis and global face conformity.
2. `UniversalRate` for exact boxes and scalar rate algebra.
3. `Mosco` and `BarrierEnvelopeMosco`.
4. `HilbertVI`, `NestedHilbertVI`, `MovingHilbertVI`.
5. `GrandRateExponents` and `MonotoneInnerConeAlgebra`.
6. `GrandBarrier` as the formal composition theorem.
7. Concrete Sobolev/FEM and free-boundary instances.

## VIII. Verification gate

The canonical branch adds `GrandCanonicalAudit.lean` and updates the pinned
workflow to:

- build the complete `BernsteinObstacle` library;
- execute the new audit file;
- reject `sorryAx`;
- require the canonical theorem names in the transcript.

Until that exact branch has a successful build and inspected axiom transcript,
all newly consolidated declarations must be described as **audit pending**.
