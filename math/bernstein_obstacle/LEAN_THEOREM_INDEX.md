# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related theorem exists,
but the full paper statement is not formalized.

Latest complete audit: workflow run `29778234348`, commit
`e09f5c786ec0f23406616989528f9a876eeb8c16`.

The audit completed all 3,090 `BernsteinObstacle` build jobs, ran all four
terminal audit entry points, rejected `sorryAx`, explicitly found the terminal
Bernstein basis reconstruction theorem, and reported only `propext`,
`Classical.choice`, and `Quot.sound`.

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
| Shared global DOFs remain equal after clipping | `clipped_local_coeff_eq_of_shared` in `GlobalMesh.lean` | Verified | A concrete geometric mesh must instantiate the local/global DOF compatibility map |
| Globally shared clipping preserves boundary zeros and gives elementwise nonpenetration | `boundary_zero_after_clipping`, `global_noPenetration_after_clipping` | Verified | Physical mesh and coordinate maps must instantiate the abstract assembly |
| Complete common-face trace equality from shared DOFs | `localFaceTrace_eq_sharedFaceTrace`, `localFaceTrace_eq_of_commonFace` in `FaceTrace.lean` | Verified | Prove the concrete simplex face embedding satisfies `FaceDofCompatible` |
| Global clipping preserves complete common-face traces | `clipped_localFaceTrace_eq_of_commonFace` | Verified | Same geometric compatibility instantiation remains |
| Orientation-reindexed common-face trace equality | `finiteTrace_eq_of_reindex`, `localFaceTrace_eq_of_orientation`, `clipped_localFaceTrace_eq_of_orientation` in `FaceOrientation.lean` | Verified | Instantiate the orientation equivalence for a concrete simplicial mesh |
| Homogeneous boundary-face traces vanish, including clipped recoveries | `sharedBoundaryFaceTrace_eq_zero`, `localBoundaryFaceTrace_eq_zero`, `clippedRecovery_localBoundaryFaceTrace_eq_zero` | Verified | Identify the physical boundary-face DOFs in a concrete mesh |
| Assembled coefficient constraints are nonempty and convex | `zero_mem_assemblyFeasibleSet`, `assemblyFeasibleSet_convex` in `AssemblyConvex.lean` | Verified | None for the finite abstract assembly |
| Clipping is the assembled feasible projection for boundary-compatible data | `clipCoefficients_sqDist_minimal_assembly`, `clipCoefficients_projection_inequality_assembly` | Verified | None for the finite abstract assembly |
| Assembled feasibility gives elementwise pointwise no-penetration | `assemblyField_nonneg_of_feasible`, `assembly_noPenetration_of_feasible` in `AssembledObstacle.lean` | Verified | Concrete mesh/coordinate instantiation remains |
| An assembled VI solution is feasible, nonpenetrating, and boundary-zero | `assembledSolution_mem_feasibleSet`, `assembledSolution_noPenetration`, `assembledSolution_boundary_zero` | Verified | Existence and identification with the PDE discretization remain |
| An assembled VI solution minimizes the symmetric PSD energy | `assembledSolution_is_energyMinimizer` | Verified | Show the assembled FEM stiffness matrix satisfies the hypotheses |
| Assembled feasible recovery controls the minimizer error | `assembledSolution_half_error_le_energyGap`, `assembledSolution_coercive_error_le_energyGap`, `assembledSolution_coercive_error_le_clippedRecoveryGap` | Verified | Establish FEM coercivity and a vanishing recovery energy gap |
| Coefficient squared norm controls the finite product norm | `norm_sq_le_coefficientNormSq`, `norm_le_sqrt_coefficientNormSq` in `CoefficientNorm.lean` | Verified | Relate this finite coefficient norm uniformly to the physical `H^1` norm on changing meshes |
| Vanishing coefficient squared error gives strong convergence | `stronglyConverges_zero_of_coefficientNormSq_tendsto_zero`, `stronglyConverges_of_recovery_coefficientNormSq`, `stronglyConverges_of_recovery_coefficientNormSq_bound` | Verified | Produce the coefficient error from the moving FEM recovery estimate |
| Uniform coercivity plus a vanishing recovery energy gap gives strong convergence | `coefficientNormSq_tendsto_zero_of_scaled_le`, `stronglyConverges_of_recovery_scaledEnergyGap`, `assembledVISolutions_strongConvergence_of_energyGap` in `EnergyGapConvergence.lean` | Verified | Prove uniform assembled FEM coercivity and the recovery energy-gap limit |
| Boundary-compatible clipped recovery plus vanishing energy gap gives strong convergence | `assembledVISolutions_strongConvergence_of_clippedRecoveryEnergyGap` | Verified | Construct the physical Bernstein recovery sequence and prove the energy-gap limit |
| Positive coercivity gives uniqueness of the finite obstacle VI solution | `coefficientNormSq_eq_zero_iff`, `discreteVISolution_unique_of_coercive`, `assembledObstacleSolution_unique_of_coercive` in `Uniqueness.lean` | Verified | Existence and physical FEM identification remain |
| Falling-factorial cardinal values satisfy the all-degree lattice delta formula | `latticeFactor_self`, `latticeFactor_eq_zero_of_lt`, `latticeCardinalValue_eq_ite` in `LatticeCardinal.lean` | Verified | None |
| Cardinal collocation matrix is the identity with determinant one | `latticeCardinalMatrix_apply`, `latticeCardinalMatrix_eq_one`, `latticeCardinalMatrix_det` in `LatticeInterpolation.lean` | Verified | None |
| Cardinal expressions are actual affine multivariate polynomials of total degree at most `n` | `affineLatticeCardinalPolynomial`, `totalDegree_affineLatticeCardinalPolynomial_le`, `affineLatticeCardinalPolynomial_mem_restrictTotalDegree` | Verified | None |
| Exact cardinal delta evaluation and linear independence in `MvPolynomial` | `eval_affineLatticeCardinalPolynomial_eq_ite`, `affineLatticeCardinalPolynomial_linearIndependent` | Verified | None |
| Exact dimension `#A_n = dim P_n` | `finrank_restrictTotalDegree_eq_card_multiIndex` in `PolynomialDimension.lean` | Verified | None |
| All-degree simplex-lattice cardinal basis of `P_n` | `affineLatticeCardinalBasis`, `span_affineLatticeCardinalVector_eq_top`, `affineLatticeCardinalBasis_sum_repr` | Verified | None |
| Nodal evaluation is a linear equivalence and interpolation exists uniquely | `affineNodalEvaluationEquiv_apply`, `polynomial_eq_of_eq_on_simplex_lattice`, `existsUnique_polynomial_with_simplex_lattice_values` | Verified | None |
| The manuscript's simplicial Bernstein functions are actual affine polynomials in `P_n` | `affineBernsteinPolynomial`, `totalDegree_affineBernsteinPolynomial_le`, `affineBernsteinPolynomial_mem_restrictTotalDegree` in `AffineBernsteinPolynomial.lean` | Verified | None |
| Affine polynomial evaluation exactly equals `simplexBasis` on the standard simplex | `eval_affineBernsteinPolynomial_eq_simplexBasis` | Verified | None |
| Positive triangular diagonal and rank separation for affine Bernstein polynomials | `coeff_affineBernsteinPolynomial_at_own_exponent`, `coeff_affineBernsteinPolynomial_eq_zero_of_not_le`, `coeff_affineBernsteinPolynomial_eq_zero_of_rank_lt`, `coeff_affineBernsteinPolynomial_eq_zero_of_rank_eq_of_ne` | Verified | None |
| The affine Bernstein family is a basis of `P_n` | `affineBernsteinPolynomial_linearIndependent`, `affineBernsteinVector_linearIndependent`, `affineBernsteinBasis`, `span_affineBernsteinVector_eq_top`, `affineBernsteinBasis_sum_repr` in `AffineBernsteinBasis.lean` | Verified | None |
| Sequential Mosco convergence definition and strong/weak obligations | `MoscoConverges`, `mosco_recovery`, `mosco_weak_limit` in `Mosco.lean` | Verified infrastructure | Must prove the moving Sobolev Bernstein cones satisfy these obligations |
| Mosco reduction for inner approximations and recovery operators | `mosco_of_recovery_of_subset_of_weaklyClosed`, `mosco_of_recovery_operators_of_subset_of_weaklyClosed` in `MoscoTools.lean` | Verified | Sobolev weak closedness, discrete-set inclusion, and positive recovery remain |
| Finite nonnegative coefficient cone is weakly sequentially closed and Mosco constant | `coefficientCone_weaklySequentiallyClosed`, `coefficientCone_mosco_const` in `CoefficientMosco.lean` | Verified | This is finite-dimensional, not the moving-mesh PDE theorem |
| Assembled feasible set is weakly sequentially closed and Mosco constant | `assemblyFeasibleSet_weaklySequentiallyClosed`, `assemblyFeasibleSet_mosco_const` in `AssemblyMosco.lean` | Verified | Moving DOF spaces and Sobolev embeddings remain |
| Exact symmetric quadratic-energy identity | `discreteEnergy_difference_identity`, `half_error_energy_le`, `coercive_error_le_energy` in `Energy.lean` | Verified | Connect the matrix form to assembled FEM bilinear forms and the `H^1` norm |
| A finite discrete VI solution minimizes the quadratic energy | `vi_solution_is_energy_minimizer` in `FiniteObstacle.lean` | Verified | Existence and assembly from the PDE discretization remain |
| Feasible recovery competitor controls discrete minimizer error | `vi_solution_half_error_le_energy_gap`, `vi_solution_coercive_error_le_energy_gap` | Verified | Prove the recovery energy gap tends to zero in the FEM setting |
| Recovery closeness transfers strong convergence to discrete minimizers | `stronglyConverges_of_recovery_closeness`, `mosco_recovery_closeness_implies_strong_convergence`, `recoveryOperator_closeness_implies_strong_convergence` | Verified | Derive the vanishing norm majorant from FEM estimates |
| Boundary-compatible clipped recovery is assembled-feasible and yields strong convergence | `assembledClippedRecovery_implies_strongConvergence` in `AssemblyConvergence.lean` | Verified | Construct the actual Bernstein recovery and prove its convergence/error majorant |
| Assembled Mosco/operator convergence interfaces | `assemblyMosco_recovery_closeness_implies_strongConvergence`, `assemblyRecoveryOperator_closeness_implies_strongConvergence` | Verified | Instantiate with moving finite-element spaces and the physical `H_0^1` target |
| Full strong convergence of Bernstein obstacle minimizers | Above assembly, Mosco, energy, VI, uniqueness, face-trace, convergence, and polynomial layers | Partially represented | Sobolev/FEM recovery, changing spaces, physical coercivity/consistency, and the vanishing energy gap |
| Coefficient-to-grid-value `O(h_T^2)` estimate | No project declaration | Not formalized | Simplicial interpolation, Taylor/Bramble–Hilbert, affine scaling |
| Localization of negative coefficients near regular free boundary | No project declaration | Not formalized | Free-boundary geometry, quadratic growth, mesh strips |
| Recovery rate `h^r + h_Gamma^(3/2)` | No project declaration | Not formalized | FEM interpolation, coefficient localization, clipping repair, and strip scaling |
| Energy/Falk sharp minimizer rate | Finite and assembled energy/VI layers verified | Partially represented | Multiplier support, continuous/discrete variational inequalities, PDE consistency, and sharp recovery rate |
| Nested subdivision and strict-positivity certification | No project declaration | Not formalized | de Casteljau subdivision on simplices and shape-regular refinement |

## Acceptance rule

The paper must not state that the multidimensional PDE theorem is Lean-verified
until every row needed for that theorem is green and the exact hypotheses are
linked to corresponding declarations. The verified layer now covers finite
coefficient certificates, projection/KKT theory, abstract global assembly,
orientation-independent complete shared-face trace conformity, boundary traces,
finite assembled convexity and weak closure, finite Mosco convergence, assembled
obstacle VI minimization and uniqueness, coercive energy-gap convergence,
clipped recovery, complete all-degree simplex-lattice unisolvence for `P_n`,
exact affine-polynomial realization of the manuscript's simplicial Bernstein
basis functions, and the complete affine Bernstein basis theorem for `P_n`.

The remaining core is the infinite-dimensional and geometric realization:
construct concrete shape-regular simplicial meshes and their face maps, embed
the changing coefficient spaces into `H_0^1`, formalize positive Sobolev
recovery and weak closedness, prove physical assembled coercivity and
consistency, and then formalize interpolation, free-boundary localization,
strip scaling, and the sharp `h^r + h_Gamma^(3/2)` rate.
