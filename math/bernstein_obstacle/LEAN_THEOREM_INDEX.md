# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related theorem exists,
but the full paper statement is not formalized.

Latest complete audit: workflow run `29764936819`, commit
`d6eb3287f5e9251247872363c42caa4ef7500bd9`.

The audit completed all 3,074 `BernsteinObstacle` build jobs, ran both terminal
audit entry points, rejected `sorryAx`, and reported only `propext`,
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
| Homogeneous boundary-face traces vanish, including clipped recoveries | `sharedBoundaryFaceTrace_eq_zero`, `localBoundaryFaceTrace_eq_zero`, `clippedRecovery_localBoundaryFaceTrace_eq_zero` | Verified | Identify the physical boundary-face DOFs in a concrete mesh |
| Assembled coefficient constraints are nonempty and convex | `zero_mem_assemblyFeasibleSet`, `assemblyFeasibleSet_convex` in `AssemblyConvex.lean` | Verified | None for the finite abstract assembly |
| Clipping is the assembled feasible projection for boundary-compatible data | `clipCoefficients_sqDist_minimal_assembly`, `clipCoefficients_projection_inequality_assembly` | Verified | None for the finite abstract assembly |
| Assembled feasibility gives elementwise pointwise no-penetration | `assemblyField_nonneg_of_feasible`, `assembly_noPenetration_of_feasible` in `AssembledObstacle.lean` | Verified | Concrete mesh/coordinate instantiation remains |
| An assembled VI solution is feasible, nonpenetrating, and boundary-zero | `assembledSolution_mem_feasibleSet`, `assembledSolution_noPenetration`, `assembledSolution_boundary_zero` | Verified | Existence and identification with the PDE discretization remain |
| An assembled VI solution minimizes the symmetric PSD energy | `assembledSolution_is_energyMinimizer` | Verified | Show the assembled FEM stiffness matrix satisfies the hypotheses |
| Assembled feasible recovery controls the minimizer error | `assembledSolution_half_error_le_energyGap`, `assembledSolution_coercive_error_le_energyGap`, `assembledSolution_coercive_error_le_clippedRecoveryGap` | Verified | Establish FEM coercivity and a vanishing recovery energy gap |
| General barycentric-lattice unisolvence | Natural-language proof in `UNISOLVENCE_PROOF.md` | Not in Lean | Formal cardinal basis, evaluation matrix, and dimension count |
| Sequential Mosco convergence definition and strong/weak obligations | `MoscoConverges`, `mosco_recovery`, `mosco_weak_limit` in `Mosco.lean` | Verified infrastructure | Must prove the moving Sobolev Bernstein cones satisfy these obligations |
| Mosco reduction for inner approximations and recovery operators | `mosco_of_recovery_of_subset_of_weaklyClosed`, `mosco_of_recovery_operators_of_subset_of_weaklyClosed` in `MoscoTools.lean` | Verified | Sobolev weak closedness, discrete-set inclusion, and positive recovery remain |
| Finite nonnegative coefficient cone is weakly sequentially closed and Mosco constant | `coefficientCone_weaklySequentiallyClosed`, `coefficientCone_mosco_const` in `CoefficientMosco.lean` | Verified | This is finite-dimensional, not the moving-mesh PDE theorem |
| Assembled feasible set is weakly sequentially closed and Mosco constant | `assemblyFeasibleSet_weaklySequentiallyClosed`, `assemblyFeasibleSet_mosco_const` in `AssemblyMosco.lean` | Verified | Moving DOF spaces and Sobolev embeddings remain |
| Exact symmetric quadratic-energy identity | `discreteEnergy_difference_identity`, `half_error_energy_le`, `coercive_error_le_energy` in `Energy.lean` | Verified | Connect the matrix form to assembled FEM bilinear forms and the `H^1` norm |
| A finite discrete VI solution minimizes the quadratic energy | `vi_solution_is_energy_minimizer` in `FiniteObstacle.lean` | Verified | Existence/uniqueness and assembly from the PDE discretization remain |
| Feasible recovery competitor controls discrete minimizer error | `vi_solution_half_error_le_energy_gap`, `vi_solution_coercive_error_le_energy_gap` | Verified | Prove the recovery energy gap tends to zero in the FEM setting |
| Recovery closeness transfers strong convergence to discrete minimizers | `stronglyConverges_of_recovery_closeness`, `mosco_recovery_closeness_implies_strong_convergence`, `recoveryOperator_closeness_implies_strong_convergence` | Verified | Derive the vanishing norm majorant from FEM estimates |
| Boundary-compatible clipped recovery is assembled-feasible and yields strong convergence | `assembledClippedRecovery_implies_strongConvergence` in `AssemblyConvergence.lean` | Verified | Construct the actual Bernstein recovery and prove its convergence/error majorant |
| Assembled Mosco/operator convergence interfaces | `assemblyMosco_recovery_closeness_implies_strongConvergence`, `assemblyRecoveryOperator_closeness_implies_strongConvergence` | Verified | Instantiate with moving finite-element spaces and the physical `H_0^1` target |
| Full strong convergence of Bernstein obstacle minimizers | Above assembly, Mosco, energy, VI, face-trace, and convergence layers | Partially represented | Sobolev/FEM recovery, moving spaces, assembled coercivity, and vanishing energy gap |
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
complete shared-face trace conformity, boundary traces, finite assembled
convexity and weak closure, finite Mosco convergence, assembled obstacle VI and
energy estimates, and the clipped-recovery-to-strong-convergence endgame.

The remaining core is the infinite-dimensional and geometric realization:
construct concrete shape-regular simplicial meshes and their face maps, embed
the changing coefficient spaces into `H_0^1`, formalize positive Sobolev
recovery and weak closedness, prove assembled coercivity and consistency, and
then formalize interpolation, free-boundary localization, strip scaling, and
the sharp `h^r + h_Gamma^(3/2)` rate.
