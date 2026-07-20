# Grand Bernstein–Bézier formalization map

Date: 2026-07-20

Canonical branch: `formal/bernstein-bezier-grand-canonical`

Integrated base commit: `263acf15f4defef8b6999ce5d6f3d0adb5517028`

## Status vocabulary

- **Verified on inherited base:** compiled and axiom-audited on the integrated v3 branch.
- **Previously verified, canonically consolidated:** compiled on a separate pinned branch and imported into the canonical stack.
- **Lean source complete; canonical audit pending:** proof source contains no intentional `sorry`; the exact integrated build and axiom transcript still must pass.
- **Formal reduction:** Lean proves the endgame from explicit hypotheses, while the physical analytical construction of those hypotheses remains outside the kernel.
- **Analytical only:** no faithful Lean realization yet.

## I. Exact coefficient certification

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Univariate coefficient interval implies pointwise interval | `curve_mem_Icc` | Verified on inherited base |
| Simplicial coefficient interval implies pointwise interval | `simplexFieldNat_mem_Icc` | Verified on inherited base |
| Variable-obstacle affine normalization preserves bounds | `affineBox_mem_Icc` | Previously verified, canonically consolidated |
| Exact univariate bilateral obstacle field | `boxApprox_mem_Icc` | Previously verified, canonically consolidated |
| Exact simplicial bilateral obstacle field | `simplexBoxApproxNat_mem_Icc` | Previously verified, canonically consolidated |

Canonical component name: **Bézier Inner-Cone Certificate**.

## II. Constructive recovery and Mosco convergence

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Sequential Mosco definition | `MoscoConverges` | Verified on inherited base |
| Threshold schedule tends to infinity | `scheduledStage_tendsto_atTop` | Lean source complete; canonical audit pending |
| Threshold data produce a diagonal recovery | `exists_scheduledDiagonalRecovery` | Lean source complete; canonical audit pending |
| Scheduled inner recovery implies Mosco convergence | `mosco_of_scheduledRecovery_of_subset_closedConvex` | Lean source complete; canonical audit pending |
| Translation preserves Mosco convergence | `moscoConverges_translated` | Lean source complete; canonical audit pending |
| Moving nonzero obstacles converge by translation | `ThresholdSobolevFEMRecoveryData.movingObstacle_moscoConverges` | Lean source complete; canonical audit pending |
| Weak closedness + recovery + inner inclusion imply Mosco | `BilateralBarrierEnvelopeData.moscoConverges` | Lean source complete; canonical audit pending |
| Exact inner inclusion and Mosco packaged together | `BilateralBarrierEnvelopeData.inner_and_mosco` | Lean source complete; canonical audit pending |
| Concrete `W_0^{1,p}` strict feasible density | — | Analytical only |
| Positive Bernstein sampling in moving physical meshes | abstract recovery structures | Formal reduction |
| Conservative sampled variable-obstacle envelopes | exact finite certificate formalized; physical estimates analytical | Formal reduction |

Canonical component name: **Bernstein–Bézier Barrier Envelope Theorem**.

## III. Hilbert variational-inequality endgame

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| VI Pythagorean inequality | `hilbert_vi_pythagorean` | Previously verified, canonically consolidated |
| VI uniqueness | `hilbert_vi_unique` | Previously verified, canonically consolidated |
| Nested recovery error estimate | `nested_hilbert_vi_recovery_error_sq` | Previously verified, canonically consolidated |
| Strong convergence from strong feasible recovery | `nested_hilbert_vi_strongConvergence_of_recovery` | Previously verified, canonically consolidated |
| Moving-obstacle minimizer convergence | `ThresholdSobolevFEMRecoveryData.movingObstacle_minimizers_strongConvergence` | Lean source complete; canonical audit pending |
| Barrier-envelope Mosco + strong VI convergence | `BilateralBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence` | Lean source complete; canonical audit pending |
| Sobolev recovery data instantiate the grand barrier endgame | `SobolevFEMRecoveryData.grandBarrier_hilbertConvergence` | Lean source complete; canonical audit pending |

Canonical umbrella name: **Bernstein–Bézier Grand Barrier Theorem**.

## IV. Universal and nonlinear transfer

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Two squared scales imply a norm-rate sum | `twoScaleRate_of_energy_components` | Previously verified, canonically consolidated |
| Universal first-order transfer | `universalFirstOrderRate_of_recovery_and_measure` | Previously verified, canonically consolidated |
| Strongly monotone inner-cone Young/Falk algebra | `monotoneInnerCone_falk_sq` | Lean source complete; canonical audit pending |
| Operator VI definition | `IsOperatorVISolution` | Lean source complete; canonical audit pending |
| Operator-level inner-cone Falk core from nested VIs, monotonicity and Lipschitz control | `monotoneInnerCone_operator_core` | Lean source complete; canonical audit pending |
| Squared operator-level recovery/residual estimate | `monotoneInnerCone_operator_falk_sq` | Lean source complete; canonical audit pending |
| Concrete nonsymmetric/nonpotential PDE operator instances | — | Analytical only |

Canonical component name: **Bernstein–Bézier Inner-Cone Falk Theorem**.

## V. Codimension, saturation and sharpness

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Integer vanishing-order/codimension scale | `vanishingCodimensionScale` | Lean source complete; canonical audit pending |
| Elementwise energy plus patch cardinality gives global codimension law | `strip_sum_energy_le_vanishingCodimension` | Lean source complete; canonical audit pending |
| Global repair norm estimate | `repair_norm_le_vanishingCodimension_of_element_bounds` | Lean source complete; canonical audit pending |
| Moving-obstacle three-component rate | `grandSharpRate_of_movingObstacle_components` | Lean source complete; canonical audit pending |
| Consistency order saturates at physical vanishing order | `consistencyLimitedOrder_eq_vanishingOrder` | Lean source complete; canonical audit pending |
| Quadratic codimension-one saturation | `quadraticContact_codimOne_saturation` | Lean source complete; canonical audit pending |
| Exact phase-locked slope-energy integral | `intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity` | Lean source complete; canonical audit pending |
| Exact energy equals the square of the `h * sqrt h` scale | `intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity_eq_scale_sq` | Lean source complete; canonical audit pending |
| Positive matching lower bound | `phaseLockedQuadraticSlopeEnergy_lowerBound` | Lean source complete; canonical audit pending |
| Real-parameter repair exponent `beta-1+kappa/q` | `repairExponent` | Lean source complete; canonical audit pending |
| Real-parameter multiplier exponent `(beta+kappa)/q` | `multiplierExponent` | Lean source complete; canonical audit pending |
| Classical exponent is `3/2` | `threeHalvesContactLaw` | Lean source complete; canonical audit pending |
| Balanced order is `q/(q-1)` | `balancedContactOrder_equalizes` | Lean source complete; canonical audit pending |
| General real-power Bregman `q`-root theorem | — | Analytical only |
| Noninteger Minkowski codimension geometry | — | Analytical only |

Canonical names:

- **Bernstein–Bézier Codimension–Growth Clipping Law**;
- **Three-Halves Contact Law**;
- **Balanced Contact Exponent Principle**;
- **Bernstein–Bézier Bregman Transfer Theorem**.

## VI. Terminal composition

| Mathematical claim | Lean declaration | Status |
|---|---|---|
| Moving obstacles + Mosco + strong minimizer convergence + consistency-limited three-scale rate | `bernsteinBezierObstacleGrandTheorem` | Lean source complete; canonical audit pending |
| Quadratic-contact specialization with `hGamma * sqrt hGamma` | `bernsteinBezierObstacleGrandTheorem_quadraticContact` | Lean source complete; canonical audit pending |

Canonical terminal name: **Bernstein–Bézier Obstacle Grand Theorem**.

## VII. Physical analytical layer still required

The following items cannot honestly be labeled fully formalized yet:

1. a concrete shape-regular simplicial mesh family embedded in `W_0^{1,p}(Omega)`;
2. physical trace and conformity theory for the moving spaces;
3. strict smooth density inside variable bilateral obstacle intervals;
4. dimension-safe positive Bernstein sampling estimates in `W^{1,p}`;
5. conservative envelope estimates uniform over the mesh family;
6. one-sided extension and broken regularity near a free boundary;
7. tubular-interface geometry and geometric patch-measure estimates;
8. multiplier support and density/measure arguments;
9. the general real-power Bregman coercivity and smoothness inequalities;
10. operator-specific p-Laplacian or Leray–Lions free-boundary growth;
11. curved changing-normal Signorini contact and stable normal lifting;
12. anisotropic mesh variants;
13. noninteger/fractal Minkowski-codimension geometry.

These are not hidden assumptions. Terminal Lean theorems expose the required recovery, convergence, energy and scaling facts as explicit structure fields or hypotheses until the corresponding physical libraries are built.

## VIII. Canonical verification gate

`GrandCanonicalAudit.lean` checks and prints axioms for the exact certification, scheduling, translated and moving-obstacle Mosco, Hilbert and monotone-operator transfer, codimension and saturation laws, exact lower model, and both terminal grand theorems.

The pinned workflow:

- builds the complete `BernsteinObstacle` library;
- executes all legacy audits and `GrandCanonicalAudit.lean`;
- rejects `sorryAx`;
- requires the canonical endpoint names in the transcript;
- keeps `cancel-in-progress` disabled on the canonical branch so the final audit cannot cancel itself before a runner starts.

Until the canonical Lean run completes successfully and its axiom transcript is inspected, every newly integrated endpoint remains **canonical audit pending**.
