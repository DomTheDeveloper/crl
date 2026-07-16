import Checkerboard.LP.LimitTransfer

/-!
# Asymptotic squeeze for continuum-to-finite certificate families

The analytic construction will produce two explicit finite sequences:

* a primal sequence below the odd-fat optimum;
* a sampled-dual sequence above the odd-fat optimum.

Once both normalized objectives tend to the same continuum value, the finite LP
limit follows by a single order-topological squeeze.  Keeping this lemma separate
makes the remaining obligations completely explicit.
-/

namespace Checkerboard

noncomputable section

open Filter
open scoped Topology

/-- Exact interface supplied by a continuum primal discretization and a sampled
continuum dual certificate.  No asymptotic conclusion is stored in the record.
-/
structure OddFatTransferPackage where
  primalValue : ℕ → ℝ
  dualValue : ℕ → ℝ
  primal_le : ∀ m, primalValue m ≤ oddFatL4 m
  le_dual : ∀ m, oddFatL4 m ≤ dualValue m
  primal_limit :
    Tendsto (fun m => primalValue m / oddScale m) atTop (𝓝 checkerboardAlpha)
  dual_limit :
    Tendsto (fun m => dualValue m / oddScale m) atTop (𝓝 checkerboardAlpha)

/-- A matched lower discretization and upper sampled-dual family force the exact
odd-fat fractional limit. -/
theorem oddFat_limit_of_transfer_package (P : OddFatTransferPackage) :
    Tendsto (fun m => oddFatL4 m / oddScale m) atTop (𝓝 checkerboardAlpha) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    P.primal_limit P.dual_limit ?_ ?_
  · filter_upwards with m
    exact div_le_div_of_nonneg_right (P.primal_le m) (le_of_lt (oddScale_pos m))
  · filter_upwards with m
    exact div_le_div_of_nonneg_right (P.le_dual m) (le_of_lt (oddScale_pos m))

/-- Complete fractional asymptotic package, with the thin and even comparisons
kept as finite combinatorial lemmas rather than hidden inside the analytic
continuum transfer.
-/
structure FourDirectionFractionalPackage extends OddFatTransferPackage where
  thinComparisonConstant : ℝ
  thinComparisonConstant_nonneg : 0 ≤ thinComparisonConstant
  thinComparison :
    ∀ m, |oddThinL4 m - oddFatL4 m| ≤ thinComparisonConstant
  evenComparisonConstant : ℝ
  evenComparisonConstant_nonneg : 0 ≤ evenComparisonConstant
  evenComparison :
    ∀ m, |evenL4 m - oddFatL4 m| ≤ evenComparisonConstant

/-- The three fractional symmetry classes have the same exact limit once the
continuum transfer and bounded finite comparisons are supplied. -/
theorem four_direction_fractional_limits
    (P : FourDirectionFractionalPackage) :
    Tendsto (fun m => oddFatL4 m / oddScale m) atTop (𝓝 checkerboardAlpha) ∧
    Tendsto (fun m => oddThinL4 m / oddScale m) atTop (𝓝 checkerboardAlpha) ∧
    Tendsto (fun m => evenL4 m / evenScale m) atTop (𝓝 checkerboardAlpha) := by
  have hfat : Tendsto (fun m => oddFatL4 m / oddScale m) atTop (𝓝 checkerboardAlpha) :=
    oddFat_limit_of_transfer_package P.toOddFatTransferPackage
  refine ⟨hfat, ?_, ?_⟩
  · exact oddThin_limit_of_oddFat_limit hfat P.thinComparisonConstant_nonneg P.thinComparison
  · exact even_limit_of_oddFat_limit hfat P.evenComparisonConstant_nonneg P.evenComparison

end

end Checkerboard
