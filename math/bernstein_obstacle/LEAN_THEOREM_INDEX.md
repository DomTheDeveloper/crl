# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related theorem exists,
but the full paper statement is not formalized.

Latest complete audit: workflow run `29763805484`, commit
`6c433d6e9ba3bca769574618d6c534cc8e44e748`.

The audit completed the full `BernsteinObstacle` build, ran all terminal
`#check` and `#print axioms` commands, rejected `sorryAx`, and reported only
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
| Nonnegative coefficient orthant is convex | `coefficientCone_convex` in `CoefficientCone.lean` | Verified | Topological closedness in an infinite-dimensional coefficient model is not developed |
| Clipping is feasible, idempotent, and the least nonnegative majorant | `clipCoefficients_mem`, `clipCoefficients_idem`, `clipCoefficients_minimal` | Verified | None for the order-theoretic statement |
| Clipping is the finite Euclidean metric projection | `clipCoefficients_sqDist_minimal`, `clipCoefficients_eq_self_iff`, `coefficientSqDist_clip_eq_zero_iff` in `Projection.lean` | Verified | Hilbert-space projection API is not required for the finite coefficient theorem |
| Clipping satisfies KKT, complementarity, Pythagoras, and nonexpansiveness | `clipCoefficients_variational_inequality`, `clipCoefficients_complementarity`, `clipCoefficients_projection_inequality`, `clipCoefficients_nonexpansive` in `ProjectionVI.lean` | Verified | None for the finite coefficient-space statements |
| Tensor-product 3D basis/field nonnegativity | `basis3_nonneg`, `field3_nonneg` in `Tensor.lean` | Verified | None |
| Clipped tensor-product 3D obstacle field is nonpenetrating | `noPenetration3_after_clipping` | Verified | None |
| Arbitrary-dimensional simplicial Bernstein basis positivity | `simplexBasis_nonneg`, `simplexBasisNat_nonneg` | Verified | None for the algebraic certificate |
| Complete simplicial Bernstein partition of unity | `simplexBasisNat_sum_eq_one` in `SimplexPartition.lean` | Verified | None for the algebraic identity |
| Simplicial coefficient lower/upper range certificate | `simplexFieldNat_mem_Icc` | Verified | None for a single standard simplex |
| Arbitrary-simplex clipping gives pointwise no-penetration | `simplex_noPenetration_after_clipping` | Verified | None for a single simplex |
| Shared global DOFs remain equal after clipping | `clipped_local_coeff_eq_of_shared` in `GlobalMesh.lean` | Verified | Geometric face maps, orientation, and trace equality remain |
| Globally shared clipping preserves boundary zeros and gives elementwise nonpenetration | `boundary_zero_after_clipping`, `global_noPenetration_after_clipping` | Verified | Full finite-element mesh and boundary-trace structures remain |
| General barycentric-lattice unisolvence | Natural-language proof in `UNISOLVENCE_PROOF.md` | Not in Lean | Formal cardinal basis, evaluation matrix, and dimension count |
| Sequential Mosco convergence definition and strong/weak obligations | `MoscoConverges`, `mosco_recovery`, `mosco_weak_limit` in `Mosco.lean` | Verified infrastructure | Must prove the Bernstein finite-element cones satisfy these obligations |
| Mosco reduction for inner approximations and recovery operators | `mosco_of_recovery_of_subset_of_weaklyClosed`, `mosco_of_recovery_operators_of_subset_of_weaklyClosed` in `MoscoTools.lean` | Verified | Sobolev weak closedness, discrete-set inclusion, and a positive recovery operator remain |
| Exact symmetric quadratic-energy identity | `discreteEnergy_difference_identity`, `half_error_energy_le`, `coercive_error_le_energy` in `Energy.lean` | Verified | Must connect the abstract matrix form to assembled FEM bilinear forms and the `H^1` norm |
| A finite discrete VI solution minimizes the quadratic energy | `vi_solution_is_energy_minimizer` in `FiniteObstacle.lean` | Verified | Existence/uniqueness and assembly from the PDE discretization remain |
| Feasible recovery competitor controls discrete minimizer error | `vi_solution_half_error_le_energy_gap`, `vi_solution_coercive_error_le_energy_gap` | Verified | Must prove the recovery energy gap tends to zero in the FEM setting |
| Recovery closeness transfers strong convergence to discrete minimizers | `stronglyConverges_of_recovery_closeness`, `mosco_recovery_closeness_implies_strong_convergence`, `recoveryOperator_closeness_implies_strong_convergence` in `MinimizerConvergence.lean` | Verified | Must derive the vanishing norm majorant from the FEM energy/coercivity estimates |
| Full strong convergence of Bernstein obstacle minimizers | Above Mosco, energy, VI, and transfer layers | Partially represented | Sobolev/FEM recovery, assembled coercivity, compactness/weak closure, and vanishing energy gap |
| Coefficient-to-grid-value `O(h_T^2)` estimate | No project declaration | Not formalized | Simplicial interpolation, Taylor/Bramble–Hilbert, affine scaling |
| Localization of negative coefficients near regular free boundary | No project declaration | Not formalized | Free-boundary geometry, quadratic growth, mesh strips |
| Recovery rate `h^r + h_Gamma^(3/2)` | No project declaration | Not formalized | FEM interpolation, coefficient localization, clipping repair, and strip scaling |
| Energy/Falk sharp minimizer rate | Finite energy/VI layer verified | Partially represented | Multiplier support, continuous/discrete variational inequalities, and the PDE consistency term |
| Nested subdivision and strict-positivity certification | No project declaration | Not formalized | de Casteljau subdivision on simplices and shape-regular refinement |

## Acceptance rule

The paper must not state that the multidimensional PDE theorem is Lean-verified
until every row needed for that theorem is green and the exact hypotheses are
linked to corresponding declarations. The verified layer now covers the finite
coefficient cone, metric projection and KKT properties, global shared-DOF
clipping algebra, simplex and tensor-product nonpenetration, the finite
quadratic-energy/VI bridge, the sequential Mosco interfaces, and the abstract
recovery-to-minimizer strong-convergence transfer. The remaining core is the
actual Sobolev finite-element realization: mesh geometry and traces, positive
recovery approximation, weak closedness, assembled coercivity, interpolation
and free-boundary estimates, and the sharp `h^r + h_Gamma^(3/2)` rate.
