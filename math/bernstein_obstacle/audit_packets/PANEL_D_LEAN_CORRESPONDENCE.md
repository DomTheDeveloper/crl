# Panel D: Lean theorem correspondence and trust boundary

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0-rc1`
- mathlib: `4608056c77c52468b80773e8dcd585ef821c7c5e`
- build: `lake build BernsteinObstacle`
- audit: `lake env lean Audit.lean`

A successful audit must reject any theorem whose transcript contains
`sorryAx`, a project-local axiom, or a statement weaker than the prose claim.

## Formalized algebraic certificate layer

| Mathematical claim | Lean theorem/module |
|---|---|
| 1D basis nonnegativity | `basis_nonneg` |
| 1D partition of unity | `basis_sum_eq_one` |
| coefficient lower/upper range | `curve_lower_bound`, `curve_upper_bound`, `curve_mem_Icc` |
| clipping gives nonnegative coefficients | `clipCoefficients_mem` |
| clipping no-penetration on `[0,1]` | `noPenetration_after_clipping` |
| tensor-product cube certificate | `noPenetration3_after_clipping` |
| simplex basis nonnegativity | `simplexBasis_nonneg` |
| simplex partition of unity | `simplexBasisNat_sum_eq_one` |
| simplex convex-hull/range theorem | `simplexFieldNat_mem_Icc` |
| arbitrary-simplex clipping certificate | `simplex_noPenetration_after_clipping` |
| global shared-face clipping | `clipped_local_coeff_eq_of_shared` |
| meshwise pointwise no-penetration | `global_noPenetration_after_clipping` |
| homogeneous boundary preservation | `boundary_zero_after_clipping` |

## Formalized projection and optimization layer

| Mathematical claim | Lean theorem/module |
|---|---|
| clipping is a nearest feasible coefficient vector | `clipCoefficients_sqDist_minimal` |
| scalar KKT projection inequality | `clip_variational_inequality` |
| global KKT projection inequality | `clipCoefficients_variational_inequality` |
| complementarity | `clipCoefficients_complementarity` |
| Pythagorean projection estimate | `clipCoefficients_projection_inequality` |
| clipping nonexpansiveness | `clipCoefficients_nonexpansive` |
| exact quadratic energy identity | `discreteEnergy_difference_identity` |
| VI solution minimizes discrete energy | `vi_solution_is_energy_minimizer` |
| feasible competitor controls error energy | `vi_solution_half_error_le_energy_gap` |
| coordinate coercivity gives squared-error control | `vi_solution_coercive_error_le_energy_gap` |

## Formalized Mosco logic layer

| Mathematical claim | Lean theorem/module |
|---|---|
| sequential Mosco definition | `MoscoConverges` |
| constant weakly closed set Mosco-converges | `moscoConverges_const_self` |
| inner approximation reduces to recovery plus weak closure | `mosco_of_recovery_of_subset_of_weaklyClosed` |
| recovery-operator form of the same reduction | `mosco_of_recovery_operators_of_subset_of_weaklyClosed` |

## Not yet formalized

The following must not be described as Lean verified:

1. density of nonnegative `C_c^infty` functions in the Sobolev obstacle cone;
2. finite-element mesh and trace infrastructure sufficient for the sampled
   Bernstein recovery operator;
3. the `W^{2,infinity}` local interpolation estimate on affine simplices;
4. the actual Bernstein-cone Mosco theorem in `H_0^1`;
5. minimizer convergence from Mosco convergence in the Sobolev energy metric;
6. regular-free-boundary tubular geometry and strip-volume estimates;
7. coefficient localization near `Gamma`;
8. the `h_Gamma^(3/2)` repair estimate;
9. multiplier consistency and the full Falk theorem.

## Required reviewer tests

1. Run the exact pinned commands from a clean clone.
2. Search all project Lean files for `sorry`, `axiom`, `admit`, and unsafe
   declarations.
3. Inspect every `#print axioms` result in `Audit.lean`.
4. Compare definitions with the displayed mathematical formulas.
5. Verify that `GlobalMesh.lean` models shared global coefficients rather than
   silently assuming local face orientation agreement.
6. Confirm that the projection theorems quantify over every finite coefficient
   type and every feasible competitor.
7. Confirm that the Mosco helper theorem proves only an abstract reduction and
   does not claim the missing Sobolev recovery construction.
8. Return a line-item PASS/FAIL table and list every prose sentence that
   overstates current formal coverage.
