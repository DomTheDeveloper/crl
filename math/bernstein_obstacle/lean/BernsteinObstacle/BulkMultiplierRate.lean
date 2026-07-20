import BernsteinObstacle.CorrectedSharpRate
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Uniform broken regularity and multiplier strip bounds

These lemmas certify the remaining rate bookkeeping in the corrected theorem:

* summing elementwise bulk interpolation errors under a uniform broken
  `H^{r+1}` bound produces the global `O(h^(2r))` squared-error contribution;
* bounded multiplier density, an `O(g^2)` contact-side recovery amplitude, and
  an `O(g)` strip measure produce an `O(g^3)` consistency contribution;
* together with the local-strip repair estimate, these imply the complete
  corrected sharp minimizer rate.
-/

/-- A uniform broken-regularity bound turns elementwise squared interpolation
estimates into the global bulk rate. -/
theorem broken_bulk_sum_le_rate
    {ι : Type*} (S : Finset ι)
    (bulkElement regularity : ι → ℝ)
    (A M h : ℝ) (r : ℕ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (helement : ∀ i ∈ S,
      bulkElement i ≤ A * h ^ (2 * r) * regularity i)
    (hregularity : ∑ i ∈ S, regularity i ≤ M) :
    ∑ i ∈ S, bulkElement i ≤ A * M * h ^ (2 * r) := by
  have hfactor : 0 ≤ A * h ^ (2 * r) :=
    mul_nonneg hA (pow_nonneg hh _)
  calc
    ∑ i ∈ S, bulkElement i ≤
        ∑ i ∈ S, A * h ^ (2 * r) * regularity i := by
      exact Finset.sum_le_sum fun i hi => helement i hi
    _ = (A * h ^ (2 * r)) * ∑ i ∈ S, regularity i := by
      rw [Finset.mul_sum]
    _ ≤ (A * h ^ (2 * r)) * M :=
      mul_le_mul_of_nonneg_left hregularity hfactor
    _ = A * M * h ^ (2 * r) := by ring

/-- Bounded multiplier density times `O(g^2)` recovery amplitude times an
`O(g)` strip measure gives the cubic consistency scale. -/
theorem multiplier_strip_le_cubic
    (pairing densityNorm amplitude measure A M g : ℝ)
    (hdensity : 0 ≤ densityNorm)
    (hamplitudeNonneg : 0 ≤ amplitude)
    (hmeasureNonneg : 0 ≤ measure)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hpairing : pairing ≤ densityNorm * amplitude * measure)
    (hamplitude : amplitude ≤ A * g ^ 2)
    (hmeasure : measure ≤ M * g) :
    pairing ≤ densityNorm * A * M * g ^ 3 := by
  have hAg2 : 0 ≤ A * g ^ 2 := mul_nonneg hA (pow_nonneg hg _)
  have hleft : 0 ≤ densityNorm * amplitude :=
    mul_nonneg hdensity hamplitudeNonneg
  calc
    pairing ≤ densityNorm * amplitude * measure := hpairing
    _ ≤ densityNorm * (A * g ^ 2) * measure := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hamplitude hdensity) hmeasureNonneg
    _ ≤ densityNorm * (A * g ^ 2) * (M * g) := by
      exact mul_le_mul_of_nonneg_left hmeasure
        (mul_nonneg hdensity hAg2)
    _ = densityNorm * A * M * g ^ 3 := by ring

/-- Complete corrected algebraic theorem from broken bulk estimates, local-strip
repair estimates, multiplier amplitude/measure estimates, and coercive transfer
to the discrete minimizer. -/
theorem correctedSharpMinimizerRate_of_broken_bulk_and_multiplier
    {ι κ : Type*}
    (bulkSet : Finset ι) (stripSet : Finset κ)
    (bulkElement regularity : ι → ℝ)
    (stripElement : κ → ℝ)
    (e bulkEnergy repairEnergy recoverySq multiplier : ℝ)
    (amplitude measure α A Mreg C N densityNorm B M h g : ℝ)
    (d r : ℕ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hMreg : 0 ≤ Mreg)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hdensity : 0 ≤ densityNorm) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hamplitudeNonneg : 0 ≤ amplitude) (hmeasureNonneg : 0 ≤ measure)
    (hh : 0 ≤ h) (hg : 0 < g) (hd : 1 ≤ d)
    (htransfer : α * e ^ 2 ≤ recoverySq + multiplier)
    (hrecovery : recoverySq ≤ bulkEnergy + repairEnergy)
    (hbulkEnergy : bulkEnergy ≤ ∑ i ∈ bulkSet, bulkElement i)
    (hbulkElement : ∀ i ∈ bulkSet,
      bulkElement i ≤ A * h ^ (2 * r) * regularity i)
    (hregularity : ∑ i ∈ bulkSet, regularity i ≤ Mreg)
    (hrepairEnergy : repairEnergy ≤ ∑ i ∈ stripSet, stripElement i)
    (hstripElement : ∀ i ∈ stripSet,
      stripElement i ≤ C * g ^ (d + 2))
    (hcard : (stripSet.card : ℝ) ≤ N / g ^ (d - 1))
    (hpairing : multiplier ≤ densityNorm * amplitude * measure)
    (hamplitude : amplitude ≤ B * g ^ 2)
    (hmeasure : measure ≤ M * g) :
    e ≤ Real.sqrt
        (max (A * Mreg) (C * N + densityNorm * B * M) / α) *
      (h ^ r + g * Real.sqrt g) := by
  have hAMreg : 0 ≤ A * Mreg := mul_nonneg hA hMreg
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hDBM : 0 ≤ densityNorm * B * M :=
    mul_nonneg (mul_nonneg hdensity hB) hM
  have hbulkSum :
      ∑ i ∈ bulkSet, bulkElement i ≤ A * Mreg * h ^ (2 * r) :=
    broken_bulk_sum_le_rate
      bulkSet bulkElement regularity A Mreg h r
      hA hMreg hh hbulkElement hregularity
  have hbulk : bulkEnergy ≤ (A * Mreg) * h ^ (2 * r) := by
    exact hbulkEnergy.trans hbulkSum
  have hstripSum :
      ∑ i ∈ stripSet, stripElement i ≤ C * N * g ^ 3 :=
    strip_sum_energy_le_cubic
      stripSet stripElement C N g d hd hg hC hN hstripElement hcard
  have hrepair : repairEnergy ≤ (C * N) * g ^ 3 := by
    exact hrepairEnergy.trans hstripSum
  have hrecoveryRate :
      recoverySq ≤ (A * Mreg) * h ^ (2 * r) + (C * N) * g ^ 3 := by
    calc
      recoverySq ≤ bulkEnergy + repairEnergy := hrecovery
      _ ≤ (A * Mreg) * h ^ (2 * r) + (C * N) * g ^ 3 :=
        add_le_add hbulk hrepair
  have hmultiplier : multiplier ≤ (densityNorm * B * M) * g ^ 3 := by
    simpa [mul_assoc] using multiplier_strip_le_cubic
      multiplier densityNorm amplitude measure B M g
      hdensity hamplitudeNonneg hmeasureNonneg hB hM (le_of_lt hg)
      hpairing hamplitude hmeasure
  exact sharpMinimizerRate_of_recovery_and_multiplier
    e recoverySq multiplier α (A * Mreg) (C * N) (densityNorm * B * M)
    h g r he hα hAMreg hCN hDBM hh (le_of_lt hg)
    htransfer hrecoveryRate hmultiplier

end BernsteinObstacle
