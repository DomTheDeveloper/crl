import BernsteinObstacle.LocalDistanceLocalization
import BernsteinObstacle.StripScaling
import BernsteinObstacle.RecoveryRate

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Corrected sharp-rate composition

This file packages the complete algebraic endgame of the corrected
regular-interface theorem. The physical analytical inputs remain explicit:
local coefficient localization, an elementwise repair-energy estimate, a
codimension-one patch count, a bulk interpolation term, multiplier consistency,
and coercive transfer to the discrete minimizer.
-/

/-- Elementwise repair energy on a codimension-one local-size patch, a bulk
interpolation contribution, and an `O(g^3)` multiplier term imply the corrected
`h^r + g^(3/2)` minimizer rate. -/
theorem correctedSharpMinimizerRate_of_local_strip
    {ι : Type*} (S : Finset ι) (elementEnergy : ι → ℝ)
    (e repairEnergy recoverySq multiplier α A C N D h g : ℝ)
    (d r : ℕ)
    (he : 0 ≤ e)
    (hα : 0 < α)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hh : 0 ≤ h) (hg : 0 < g) (hd : 1 ≤ d)
    (htransfer : α * e ^ 2 ≤ recoverySq + multiplier)
    (hrecovery : recoverySq ≤ A * h ^ (2 * r) + repairEnergy)
    (hrepair : repairEnergy ≤ ∑ i ∈ S, elementEnergy i)
    (helement : ∀ i ∈ S, elementEnergy i ≤ C * g ^ (d + 2))
    (hcard : (S.card : ℝ) ≤ N / g ^ (d - 1))
    (hmultiplier : multiplier ≤ D * g ^ 3) :
    e ≤ Real.sqrt (max A (C * N + D) / α) *
      (h ^ r + g * Real.sqrt g) := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hstrip : ∑ i ∈ S, elementEnergy i ≤ C * N * g ^ 3 :=
    strip_sum_energy_le_cubic
      S elementEnergy C N g d hd hg hC hN helement hcard
  have hrepairCubic : repairEnergy ≤ C * N * g ^ 3 :=
    hrepair.trans hstrip
  have hrecoveryCubic :
      recoverySq ≤ A * h ^ (2 * r) + (C * N) * g ^ 3 := by
    calc
      recoverySq ≤ A * h ^ (2 * r) + repairEnergy := hrecovery
      _ ≤ A * h ^ (2 * r) + C * N * g ^ 3 :=
        add_le_add_left hrepairCubic _
  exact sharpMinimizerRate_of_recovery_and_multiplier
    e recoverySq multiplier α A (C * N) D h g r
    he hα hA hCN hD hh (le_of_lt hg)
    htransfer hrecoveryCubic hmultiplier

/-- The corrected local-distance localization theorem and sharp-rate theorem
can be used together without changing scales: every negative coefficient lies
in the local-size patch, and any patch satisfying the stated element/cardinality
energy assumptions yields the universal three-halves contribution. -/
theorem corrected_localization_and_sharp_rate
    {ι : Type*} (S : Finset ι) (elementEnergy : ι → ℝ)
    (b v errorConstant growthConstant κ localH dist : ℝ)
    (e repairEnergy recoverySq multiplier α A C N D bulkH interfaceH : ℝ)
    (d r : ℕ)
    (hlocalH : 0 ≤ localH) (hκ : 1 ≤ κ)
    (herrorConstant : 0 ≤ errorConstant)
    (hgrowthConstant : 0 ≤ growthConstant)
    (hvalue : growthConstant * (dist - localH) ^ 2 ≤ v)
    (hcoefficientError : |b - v| ≤ errorConstant * localH ^ 2)
    (hdominates : errorConstant ≤ growthConstant * (κ - 1) ^ 2)
    (hb : b < 0)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hbulkH : 0 ≤ bulkH) (hinterfaceH : 0 < interfaceH) (hd : 1 ≤ d)
    (htransfer : α * e ^ 2 ≤ recoverySq + multiplier)
    (hrecovery : recoverySq ≤ A * bulkH ^ (2 * r) + repairEnergy)
    (hrepair : repairEnergy ≤ ∑ i ∈ S, elementEnergy i)
    (helement : ∀ i ∈ S, elementEnergy i ≤ C * interfaceH ^ (d + 2))
    (hcard : (S.card : ℝ) ≤ N / interfaceH ^ (d - 1))
    (hmultiplier : multiplier ≤ D * interfaceH ^ 3) :
    dist < κ * localH ∧
      e ≤ Real.sqrt (max A (C * N + D) / α) *
        (bulkH ^ r + interfaceH * Real.sqrt interfaceH) := by
  constructor
  · exact local_distance_lt_of_coefficient_neg
      b v errorConstant growthConstant κ localH dist
      hlocalH hκ herrorConstant hgrowthConstant
      hvalue hcoefficientError hdominates hb
  · exact correctedSharpMinimizerRate_of_local_strip
      S elementEnergy e repairEnergy recoverySq multiplier
      α A C N D bulkH interfaceH d r
      he hα hA hC hN hD hbulkH hinterfaceH hd
      htransfer hrecovery hrepair helement hcard hmultiplier

end BernsteinObstacle
