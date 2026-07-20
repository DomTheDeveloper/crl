# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related algebraic theorem
exists, but the full paper statement is not formalized.

Latest complete audit: workflow run `29758902996`, commit
`f1170dc567bcd53fa79c4d6610d0a30e089ca174`.

| Paper result | Lean declaration / file | Status | Missing work |
|---|---|---|---|
| Nonnegativity of the 1D Bernstein basis on `[0,1]` | `BernsteinObstacle.basis_nonneg` | Verified | None |
| 1D partition of unity | `BernsteinObstacle.basis_sum_eq_one` | Verified | None |
| Finite nonnegative coefficients imply pointwise nonnegative curve | `BernsteinObstacle.curve_nonneg` | Verified | None |
| Coefficient lower/upper range certificate | `curve_lower_bound`, `curve_upper_bound`, `curve_mem_Icc` | Verified | None |
| Coefficient clipping is pointwise monotone | `curve_le_clipped_curve` | Verified | None |
| Arbitrary obstacle plus nonnegative Bernstein gap is nonpenetrating | `noPenetration_of_nonnegative_coefficients` | Verified | None |
| Clipping arbitrary 1D gap coefficients gives nonpenetration | `noPenetration_after_clipping` | Verified | None |
| Nonnegative coefficient orthant is convex | `coefficientCone_convex` in `CoefficientCone.lean` | Verified | Closedness and Hilbert projection API not yet developed |
| Clipping lies in the coefficient cone, is idempotent, and is the least nonnegative majorant | `clipCoefficients_mem`, `clipCoefficients_idem`, `clipCoefficients_minimal` | Verified | Metric-projection theorem not yet formalized |
| Tensor-product 3D basis/field nonnegativity | `basis3_nonneg`, `field3_nonneg` in `Tensor.lean` | Verified | None |
| Clipped tensor-product 3D obstacle field is nonpenetrating | `noPenetration3_after_clipping` | Verified | None |
| Arbitrary-dimensional simplicial Bernstein basis positivity | `simplexBasis_nonneg`, `simplexBasisNat_nonneg` | Verified | None for the algebraic certificate |
| Complete simplicial Bernstein partition of unity | `simplexBasisNat_sum_eq_one` in `SimplexPartition.lean` | Verified | None for the algebraic identity |
| Simplicial coefficient lower/upper range certificate | `simplexFieldNat_mem_Icc` | Verified | None for a single standard simplex |
| Arbitrary-simplex clipping gives pointwise no-penetration | `simplex_noPenetration_after_clipping` | Verified | None for a single simplex |
| Shared-face coefficient conformity | No project declaration | Not formalized | Mesh, face orientation, trace, and global DOF infrastructure |
| General barycentric-lattice unisolvence | Natural-language proof in `UNISOLVENCE_PROOF.md` | Not in Lean | Formal cardinal basis and dimension count |
| General Mosco convergence of Bernstein cones | No project declaration | Not formalized | Sobolev spaces, moving convex sets, positive density, FEM recovery |
| Strong convergence of obstacle minimizers | No project declaration | Not formalized | Convex minimizers / energy projection / Mosco API |
| Coefficient-to-grid-value `O(h_T^2)` estimate | No project declaration | Not formalized | Simplicial interpolation, Taylor/Bramble–Hilbert, affine scaling |
| Localization of negative coefficients near regular free boundary | No project declaration | Not formalized | Free-boundary geometry, quadratic growth, mesh strips |
| Conformity-preserving global coefficient clipping | Local simplex clipping is verified | Partially represented | Shared global simplicial control coefficients and boundary trace |
| Recovery rate `h^r + h_Gamma^(3/2)` | No project declaration | Not formalized | FEM interpolation and strip scaling |
| Energy/Falk minimizer rate | No project declaration | Not formalized | Multiplier support, variational inequalities, coercive bilinear forms |
| Nested subdivision and strict-positivity certification | No project declaration | Not formalized | de Casteljau subdivision on simplices and shape-regular refinement |

## Acceptance rule

The paper must not state that the multidimensional PDE theorem is Lean-verified
until every row needed for that theorem is green and the exact hypotheses are
linked to corresponding declarations. The verified Lean results now cover the
finite coefficient cone, clipping, partition-of-unity, convex-hull/range, and
pointwise no-penetration bridges on `[0,1]`, the unit cube, and an arbitrary
standard simplex in any dimension. Shared finite-element conformity, Mosco
convergence, free-boundary localization, and the energy-error theorem are not
yet Lean-formalized.
