# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related theorem exists,
but the full paper statement is not formalized.

Latest complete audit: workflow run `29783085957`, commit
`8c874366dbc448cd804b370bdcd5f8774dc67336`.

The audit completed all 3,104 `BernsteinObstacle` build jobs, ran eight terminal
audit entry points, rejected `sorryAx`, explicitly found the oriented-face,
diagonal-minimizer, and sharp-rate terminal theorems, and reported only
`propext`, `Classical.choice`, and `Quot.sound`.

| Paper result | Lean declaration / file | Status | Missing work |
|---|---|---|---|
| Nonnegativity of the 1D Bernstein basis on `[0,1]` | `BernsteinObstacle.basis_nonneg` | Verified | None |
| 1D partition of unity | `BernsteinObstacle.basis_sum_eq_one` | Verified | None |
| Finite nonnegative coefficients imply pointwise nonnegative curve | `BernsteinObstacle.curve_nonneg` | Verified | None |
| Coefficient lower/upper range certificate | `curve_lower_bound`, `curve_upper_bound`, `curve_mem_Icc` | Verified | None |
| Coefficient clipping is pointwise monotone | `curve_le_clipped_curve` | Verified | None |
| Arbitrary obstacle plus nonnegative Bernstein gap is nonpenetrating | `noPenetration_of_nonnegative_coefficients` | Verified | None |
| Clipping arbitrary 1D gap coefficients gives nonpenetration | `noPenetration_after_clipping` | Verified | None |
| Nonnegative coefficient orthant is convex | `coefficientCone_convex` in `CoefficientCone.lean` | Verified | Infinite-dimensional coefficient models are outside this finite layer |
| Clipping is feasible, idempotent, and the least nonnegative majorant | `clipCoefficients_mem`, `clipCoefficients_idem`, `clipCoefficients_minimal` | Verified | None for the order-theoretic statement |
| Clipping is the finite Euclidean metric projection | `clipCoefficients_sqDist_minimal`, `clipCoefficients_eq_self_iff`, `coefficientSqDist_clip_eq_zero_iff` in `Projection.lean` | Verified | None for the finite coefficient theorem |
| Clipping satisfies KKT, complementarity, Pythagoras, and nonexpansiveness | `clipCoefficients_variational_inequality`, `clipCoefficients_complementarity`, `clipCoefficients_projection_inequality`, `clipCoefficients_nonexpansive` in `ProjectionVI.lean` | Verified | None for the finite coefficient-space statements |
| Tensor-product 3D basis/field nonnegativity | `basis3_nonneg`, `field3_nonneg` in `Tensor.lean` | Verified | None |
| Clipped tensor-product 3D obstacle field is nonpenetrating | `noPenetration3_after_clipping` | Verified | None |
| Arbitrary-dimensional simplicial Bernstein basis positivity | `simplexBasis_nonneg`, `simplexBasisNat_nonneg` | Verified | None for the algebraic certificate |
| Complete simplicial Bernstein partition of unity | `simplexBasisNat_sum_eq_one` in `SimplexPartition.lean` | Verified | None for the algebraic identity |
| Simplicial coefficient lower/upper range certificate | `simplexFieldNat_mem_Icc` | Verified | None for a single standard simplex |
| Arbitrary-simplex clipping gives pointwise no-penetration | `simplex_noPenetration_after_clipping` | Verified | None for a single simplex |
| Shared global DOFs remain equal after clipping | `clipped_local_coeff_eq_of_shared` in `GlobalMesh.lean` | Verified | A physical mesh must instantiate the local/global DOF map |
| Globally shared clipping preserves boundary zeros and gives elementwise nonpenetration | `boundary_zero_after_clipping`, `global_noPenetration_after_clipping` | Verified | Physical mesh and affine coordinate maps remain |
| Abstract complete common-face trace equality from shared DOFs | `localFaceTrace_eq_sharedFaceTrace`, `localFaceTrace_eq_of_commonFace`, `clipped_localFaceTrace_eq_of_commonFace` | Verified | Physical mesh incidence and shared-DOF identification remain |
| Coordinate-permutation invariance of simplex basis and fields | `simplexBasis_permute`, `simplexField_permute` in `SimplexPermutation.lean` | Verified | None |
| Exact standard and arbitrarily oriented face restriction | `simplexField_lastFace_extension`, `simplexBasis_orientedLastFace_embed`, `simplexField_orientedLastFace_extension` | Verified | Physical affine element maps remain |
| Concrete oriented common-face polynomial equality | `orientedSimplexFaceTrace_eq_of_sharedDofs`, `clipped_orientedSimplexFaceTrace_eq_of_sharedDofs` in `ConcreteFaceConformity.lean` | Verified | Instantiate shared global DOFs on a concrete mesh family |
| Concrete oriented boundary-face polynomial vanishing | `orientedSimplexBoundaryFaceTrace_eq_zero`, `clipped_orientedSimplexBoundaryFaceTrace_eq_zero` | Verified | Identify physical boundary faces and trace maps |
| Positive simplex Bernstein sampling recovery | `simplexSamplingCoefficients_nonneg`, `simplexSamplingRecovery_nonneg` in `SimplexRecovery.lean` | Verified | Physical affine pullbacks and the `H^1` interpolation estimate remain |
| Sampling recovery respects oriented faces and homogeneous boundary data | `simplexSamplingCoefficients_orientedLastFace`, `simplexSamplingCoefficients_orientedBoundary_eq_zero` | Verified | Assemble the local identities on a concrete conforming mesh |
| Assembled coefficient constraints are nonempty and convex | `zero_mem_assemblyFeasibleSet`, `assemblyFeasibleSet_convex` in `AssemblyConvex.lean` | Verified | None for the finite abstract assembly |
| Clipping is the assembled feasible projection for boundary-compatible data | `clipCoefficients_sqDist_minimal_assembly`, `clipCoefficients_projection_inequality_assembly` | Verified | None for the finite abstract assembly |
| Assembled feasibility gives elementwise pointwise no-penetration | `assemblyField_nonneg_of_feasible`, `assembly_noPenetration_of_feasible` in `AssembledObstacle.lean` | Verified | Concrete physical mesh realization remains |
| An assembled VI solution is feasible, nonpenetrating, boundary-zero, and energy-minimizing | `assembledSolution_mem_feasibleSet`, `assembledSolution_noPenetration`, `assembledSolution_boundary_zero`, `assembledSolution_is_energyMinimizer` | Verified | Existence and identification with the physical PDE discretization remain |
| Assembled feasible recovery controls minimizer error | `assembledSolution_half_error_le_energyGap`, `assembledSolution_coercive_error_le_energyGap`, `assembledSolution_coercive_error_le_clippedRecoveryGap` | Verified | Establish physical FEM coercivity and a vanishing recovery energy gap |
| Positive coercivity gives uniqueness of the finite obstacle VI solution | `coefficientNormSq_eq_zero_iff`, `discreteVISolution_unique_of_coercive`, `assembledObstacleSolution_unique_of_coercive` | Verified | Existence and physical FEM identification remain |
| Falling-factorial cardinal values and identity collocation matrix | `latticeCardinalValue_eq_ite`, `latticeCardinalMatrix_eq_one`, `latticeCardinalMatrix_det` | Verified | None |
| Cardinal expressions are affine multivariate polynomials in `P_n` | `affineLatticeCardinalPolynomial`, `totalDegree_affineLatticeCardinalPolynomial_le`, `affineLatticeCardinalPolynomial_mem_restrictTotalDegree` | Verified | None |
| Exact cardinal basis, dimension, nodal equivalence, and unique interpolation | `affineLatticeCardinalBasis`, `finrank_restrictTotalDegree_eq_card_multiIndex`, `affineNodalEvaluationEquiv_apply`, `existsUnique_polynomial_with_simplex_lattice_values` | Verified | None |
| Manuscript simplicial Bernstein functions are actual affine polynomials in `P_n` | `affineBernsteinPolynomial`, `totalDegree_affineBernsteinPolynomial_le`, `eval_affineBernsteinPolynomial_eq_simplexBasis` | Verified | None |
| Positive triangular diagonal and rank separation | `coeff_affineBernsteinPolynomial_at_own_exponent`, `coeff_affineBernsteinPolynomial_eq_zero_of_rank_lt`, `coeff_affineBernsteinPolynomial_eq_zero_of_rank_eq_of_ne` | Verified | None |
| Complete affine Bernstein basis of `P_n` and unique expansion | `affineBernsteinPolynomial_linearIndependent`, `affineBernsteinBasis`, `span_affineBernsteinVector_eq_top`, `affineBernsteinBasis_sum_repr` | Verified | None |
| Full Bernstein lattice-collocation operator is invertible | `affineBernsteinCollocationEquiv`, `affineBernsteinCollocation_injective`, `affineBernsteinCollocation_surjective`, `existsUnique_bernsteinCoefficients_with_latticeValues` | Verified | None |
| Sequential Mosco convergence definition and recovery/weak-limit interfaces | `MoscoConverges`, `mosco_recovery`, `mosco_weak_limit` | Verified infrastructure | None for the abstract definition |
| Every norm-closed convex set is weakly sequentially closed | `weaklySequentiallyClosed_of_convex_isClosed` in `ConvexWeakClosure.lean` | Verified | Apply it to the physical nonnegative `H_0^1` cone after defining that cone |
| Closed-convex inner approximations reduce Mosco convergence to strong recovery | `mosco_of_recovery_of_subset_of_closedConvex`, `mosco_of_recovery_operators_of_subset_of_closedConvex` | Verified | Construct the physical positive recovery operator |
| Diagonal smooth/discrete recovery gives Mosco convergence | `diagonalRecovery_stronglyConverges`, `mosco_of_diagonalRecovery_of_subset_closedConvex` in `DiagonalRecovery.lean` | Verified | Prove positive smooth density and the physical Bernstein recovery estimate |
| Diagonal recovery plus a vanishing solution error gives strong minimizer convergence | `diagonalRecovery_minimizers_strongConvergence` | Verified | Supply the physical solution-to-recovery majorant |
| Moving closed-convex recovery-operator and sequence endgames | `movingClosedConvexRecovery_strongConvergence`, `movingClosedConvexRecoverySequence_strongConvergence` | Verified | Instantiate with changing Bernstein finite-element spaces in `H_0^1` |
| Finite coefficient and assembled feasible sets are weakly closed and Mosco constant | `coefficientCone_mosco_const`, `assemblyFeasibleSet_mosco_const` | Verified | These are finite-dimensional constant-family results |
| Exact symmetric energy identity and finite VI minimization | `discreteEnergy_difference_identity`, `coercive_error_le_energy`, `vi_solution_is_energy_minimizer` | Verified | Connect the matrix form to physical FEM bilinear forms and the `H^1` norm |
| Recovery closeness and energy-gap bounds imply strong convergence | `stronglyConverges_of_recovery_closeness`, `assembledVISolutions_strongConvergence_of_clippedRecoveryEnergyGap` | Verified | Prove physical recovery convergence, coercivity, consistency, and gap limits |
| Coefficient-to-grid-value localization implications | `coefficient_nonneg_of_abs_sub_le`, `value_lt_error_of_coefficient_neg`, `abs_coefficient_le_quadratic_scale` in `CoefficientLocalization.lean` | Verified | Prove the actual `O(h_T^2)` coefficient-to-value estimate from interpolation/Taylor scaling |
| Stable inverse collocation preserves an `O(h^2)` scale | `stableInverse_quadratic_norm_bound` | Verified | Establish a uniform physical/reference inverse-collocation norm bound |
| Dimension-independent codimension-one strip power cancellation | `strip_power_cancellation`, `strip_sum_energy_le_cubic` in `SharpRateAlgebra.lean` and `StripScaling.lean` | Verified | Prove the physical patch cardinality and per-element inverse estimate hypotheses |
| Cubic squared error gives the universal three-halves repair rate | `threeHalvesScale_sq`, `repair_norm_le_threeHalves_of_element_bounds` | Verified | Establish coefficient amplitude, support, and element-energy bounds for the physical repair |
| Bulk interpolation plus clipping repair gives `h^r + h_Gamma^(3/2)` recovery | `feasibleRecoveryRate_of_interpolation_and_repair` in `RecoveryRate.lean` | Verified transfer theorem | Prove the bulk interpolation and localized repair input estimates |
| Falk/energy plus multiplier consistency gives the sharp minimizer rate | `sharpRate_of_energy_components`, `sharpMinimizerRate_of_recovery_and_multiplier` | Verified transfer theorem | Prove physical coercivity, recovery-squared, and multiplier `O(h_Gamma^3)` estimates |
| Full strong convergence of physical Bernstein obstacle minimizers | All abstract geometry, Mosco, energy, VI, uniqueness, recovery, and rate endgames above | Partially represented | Concrete shape-regular meshes and affine maps; fixed ambient `H_0^1`; positive smooth density; physical interpolation/scaling; coercivity, consistency, compactness/existence, and energy-gap limits |
| Nested subdivision and strict-positivity certification | No project declaration | Not formalized | de Casteljau subdivision on simplices and shape-regular refinement |

## Acceptance rule

The paper must not state that the multidimensional physical PDE theorem is
Lean-verified until the remaining physical Sobolev/FEM hypotheses are linked to
corresponding declarations. The verified layer now covers finite coefficient
certificates, complete all-degree polynomial theory, concrete oriented reference
face conformity, positive reference-simplex sampling, norm-closed convex weak
closure, diagonal Mosco and minimizer convergence, coefficient localization
implications, dimension-independent strip scaling, and the full algebraic
`h^r + h_Gamma^(3/2)` recovery/minimizer transfer.

The remaining core is the physical realization: define a conforming uniformly
shape-regular simplicial mesh family and affine pullbacks; embed the changing
spaces in one `H_0^1` ambient space; formalize positive smooth density and the
scaled Bernstein interpolation estimates; prove the actual `O(h_T^2)`
coefficient estimate and free-boundary localization hypotheses; and establish
physical coercivity, consistency, existence/compactness, multiplier bounds, and
the vanishing recovery energy gap.
