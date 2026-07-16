import Checkerboard.LP.IntervalDensityMeasure
import Mathlib.Data.ENNReal.BigOperators

/-!
# Arithmetic bridge for generated density cells

The generated certificates state cell densities as exact real identities.
These lemmas transport such identities to finite sums in `ℝ≥0∞`, provided the
component densities are nonnegative.
-/

namespace Checkerboard

noncomputable section

/-- A finite exact real sum of nonnegative terms may be transported through
`ENNReal.ofReal`. -/
theorem sum_ofReal_eq_of_real_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hsum : ∑ i ∈ s, f i = c) :
    ∑ i ∈ s, ENNReal.ofReal (f i) = ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_sum_of_nonneg hf, hsum]

/-- Version for a complete finite type. -/
theorem univ_sum_ofReal_eq_of_real_sum
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hsum : ∑ i, f i = c) :
    ∑ i, ENNReal.ofReal (f i) = ENNReal.ofReal c := by
  simpa using sum_ofReal_eq_of_real_sum Finset.univ f c
    (fun i _ => hf i) hsum

/-- A positive quotient is nonnegative. -/
theorem div_nonneg_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a / b := le_of_lt (div_pos ha hb)

end

end Checkerboard
