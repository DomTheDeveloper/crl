import BernsteinObstacle.StripScaling
import BernsteinObstacle.FreeBoundaryRemainderSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Higher-order free-boundary remainder scaling

A gradient remainder of order `h^(1+κ)` has squared `H¹` cost
`h^(d+2+2κ)` on one `d`-dimensional element. Summing over a codimension-one
patch and taking square roots gives `h^κ * (h * sqrt h)`.
-/

theorem remainderPatch_sum_energy_le_higherOrder
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (C N h : ℝ) (d κ : ℕ)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy :
      ∀ i ∈ S, energy i ≤ C * h ^ (d + 2 + 2 * κ))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - 1)) :
    ∑ i ∈ S, energy i ≤ C * N * h ^ (2 * κ) * h ^ 3 := by
  have hpowκ : 0 ≤ h ^ (2 * κ) := pow_nonneg (le_of_lt hh) _
  have hCκ : 0 ≤ C * h ^ (2 * κ) := mul_nonneg hC hpowκ
  have henergy' :
      ∀ i ∈ S, energy i ≤ (C * h ^ (2 * κ)) * h ^ (d + 2) := by
    intro i hi
    calc
      energy i ≤ C * h ^ (d + 2 + 2 * κ) := henergy i hi
      _ = (C * h ^ (2 * κ)) * h ^ (d + 2) := by
        rw [show d + 2 + 2 * κ = 2 * κ + (d + 2) by omega, pow_add]
        ring
  have hsum := strip_sum_energy_le_cubic
    S energy (C * h ^ (2 * κ)) N h d
    hd hh hCκ hN henergy' hcard
  calc
    ∑ i ∈ S, energy i ≤ (C * h ^ (2 * κ)) * N * h ^ 3 := hsum
    _ = C * N * h ^ (2 * κ) * h ^ 3 := by ring

theorem remainderPatch_error_le_higherOrder
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (remainderError C N h : ℝ) (d κ : ℕ)
    (herror : 0 ≤ remainderError)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (herrorSq : remainderError ^ 2 ≤ ∑ i ∈ S, energy i)
    (henergy :
      ∀ i ∈ S, energy i ≤ C * h ^ (d + 2 + 2 * κ))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - 1)) :
    remainderError ≤
      Real.sqrt (C * N) * h ^ κ * (h * Real.sqrt h) := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hscaleNonneg :
      0 ≤ Real.sqrt (C * N) * h ^ κ * (h * Real.sqrt h) := by
    positivity
  have hsum := remainderPatch_sum_energy_le_higherOrder
    S energy C N h d κ hd hh hC hN henergy hcard
  have hsquareUpper :
      remainderError ^ 2 ≤ C * N * h ^ (2 * κ) * h ^ 3 :=
    herrorSq.trans hsum
  have hkappa : (h ^ κ) ^ 2 = h ^ (2 * κ) := by
    rw [pow_two, ← pow_add, two_mul]
  have htargetSq :
      (Real.sqrt (C * N) * h ^ κ * (h * Real.sqrt h)) ^ 2 =
        C * N * h ^ (2 * κ) * h ^ 3 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hCN,
      threeHalvesScale_sq h (le_of_lt hh), hkappa]
  nlinarith

theorem physicalLowerBound_of_remainderPatchScaling
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (idealError actualError remainderError leading C N h : ℝ)
    (d κ : ℕ)
    (herror : 0 ≤ remainderError)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hideal : leading * (h * Real.sqrt h) ≤ idealError)
    (htriangle : idealError ≤ actualError + remainderError)
    (herrorSq : remainderError ^ 2 ≤ ∑ i ∈ S, energy i)
    (henergy :
      ∀ i ∈ S, energy i ≤ C * h ^ (d + 2 + 2 * κ))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - 1))
    (hsmall :
      2 * Real.sqrt (C * N) * h ^ κ ≤ leading) :
    (leading / 2) * (h * Real.sqrt h) ≤ actualError := by
  have hremainder := remainderPatch_error_le_higherOrder
    S energy remainderError C N h d κ
    herror hd hh hC hN herrorSq henergy hcard
  exact threeHalvesLowerBound_survives_higherOrderRemainder
    idealError actualError remainderError leading
    (Real.sqrt (C * N)) h κ
    (Real.sqrt_nonneg _) (le_of_lt hh)
    hideal htriangle hremainder hsmall

end BernsteinObstacle
