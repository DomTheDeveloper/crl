# Paper-to-Lean theorem correspondence

This index prevents statement drift between the manuscript and the formal
files. “Verified” means compiled under the pinned toolchain and included in a
terminal `#print axioms` audit. “Represented” means a related algebraic theorem
exists, but the full paper statement is not formalized.

| Paper result | Lean declaration / file | Status | Missing work |
|---|---|---|---|
| Nonnegativity of the 1D Bernstein basis on `[0,1]` | `BernsteinObstacle.basis_nonneg` | Verified | None |
| 1D partition of unity | `BernsteinObstacle.basis_sum_eq_one` | Verified | None |
| Finite nonnegative coefficients imply pointwise nonnegative curve | `BernsteinObstacle.curve_nonneg` | Verified | None |
| Coefficient lower/upper range certificate | `curve_lower_bound`, `curve_upper_bound`, `curve_mem_Icc` | Verified | None |
| Coefficient clipping is pointwise monotone | `curve_le_clipped_curve` | Verified | None |
| Arbitrary obstacle plus nonnegative Bernstein gap is nonpenetrating | `noPenetration_of_nonnegative_coefficients` | Verified | None |
| Clipping arbitrary 1D gap coefficients gives nonpenetration | `noPenetration_after_clipping` | Verified | None |
| Tensor-product 3D basis/field nonnegativity | `basis3_nonneg`, `field3_nonneg` in `Tensor.lean` | Verified | None |
| Clipped tensor-product 3D obstacle field is nonpenetrating | `noPenetration3_after_clipping` | Verified | None |
| Simplicial Bernstein basis positivity and partition of unity | No project declaration | Not formalized | Multi-index simplex basis library |
| Shared-face coefficient conformity | No project declaration | Not formalized | Mesh, face orientation, trace, and global DOF infrastructure |
| General barycentric-lattice unisolvence | Natural-language proof in `UNISOLVENCE_PROOF.md` | Not in Lean | Formal multi-index cardinal basis and dimension count |
| General Mosco convergence of Bernstein cones | No project declaration | Not formalized | Sobolev spaces, moving convex sets, positive density, FEM recovery |
| Strong convergence of obstacle minimizers | No project declaration | Not formalized | Convex minimizers / energy projection / Mosco API |
| Coefficient-to-grid-value `O(h_T^2)` estimate | No project declaration | Not formalized | Simplicial interpolation, Taylor/Bramble–Hilbert, affine scaling |
| Localization of negative coefficients near regular free boundary | No project declaration | Not formalized | Free-boundary geometry, quadratic growth, mesh strips |
| Conformity-preserving global coefficient clipping | Scalar and tensor clipping represented by `clip` and `clip3` | Partially represented | Shared simplicial global control coefficients and boundary trace |
| Recovery rate `h^r + h_Gamma^(3/2)` | No project declaration | Not formalized | FEM interpolation and strip scaling |
| Energy/Falk minimizer rate | No project declaration | Not formalized | Multiplier support, variational inequalities, coercive bilinear forms |
| Nested subdivision and strict-positivity certification | No project declaration | Not formalized | de Casteljau subdivision on simplices and shape-regular refinement |

## Acceptance rule

The paper must not state that the multidimensional PDE theorem is
Lean-verified until every row needed for that theorem is green and the exact
hypotheses are linked to corresponding declarations. The currently verified
Lean results are the finite algebraic certificate, clipping, and no-penetration
bridges on `[0,1]` and for tensor-product fields on the unit cube. The Mosco,
simplicial-conformity, free-boundary, and energy-error theorems are not yet
Lean-formalized.
