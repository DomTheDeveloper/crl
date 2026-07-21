import BernsteinObstacle.TransversePrismSaturation
import BernsteinObstacle.StripScaling
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Codimension-one cut-patch saturation

This file is the lower-bound counterpart of `StripScaling`. Uniform
`h^(d+2)` squared error on each nondegenerately cut element, together with a
codimension-one lower bound on the number of such elements, produces a global
`h^3` squared obstruction and hence an `h * sqrt h` norm obstruction.
-/

/-- Summing a uniform elementwise lower bound produces cardinality times that
bound. -/
theorem card_mul_le_sum_of_le
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ) (q : ℝ)
    (henergy : ∀ i ∈ S, q ≤ energy i) :
    (S.card : ℝ) * q ≤ ∑ i ∈ S, energy i := by
  calc
    (S.card : ℝ) * q = ∑ _i ∈ S, q := by simp
    _ ≤ ∑ i ∈ S, energy i := by
      exact Finset.sum_le_sum fun i hi => henergy i hi

/-- Per-element `h^(d+2)` lower bounds and a codimension-one lower patch count
produce a cubic global squared-energy lower bound, independently of `d`. -/
theorem cutPatch_sum_energy_ge_cubic
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (C N h : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ S, C * h ^ (d + 2) ≤ energy i)
    (hcard : N / h ^ (d - 1) ≤ (S.card : ℝ)) :
    C * N * h ^ 3 ≤ ∑ i ∈ S, energy i := by
  have hpow : 0 ≤ h ^ (d + 2) := pow_nonneg (le_of_lt hh) _
  have hq : 0 ≤ C * h ^ (d + 2) := mul_nonneg hC hpow
  have hcountScaled :
      (N / h ^ (d - 1)) * (C * h ^ (d + 2)) ≤
        (S.card : ℝ) * (C * h ^ (d + 2)) :=
    mul_le_mul_of_nonneg_right hcard hq
  calc
    C * N * h ^ 3 =
        C * N * (h ^ (d + 2) / h ^ (d - 1)) := by
      rw [strip_power_cancellation h d hd (ne_of_gt hh)]
    _ = (N / h ^ (d - 1)) * (C * h ^ (d + 2)) := by ring
    _ ≤ (S.card : ℝ) * (C * h ^ (d + 2)) := hcountScaled
    _ ≤ ∑ i ∈ S, energy i :=
      card_mul_le_sum_of_le S energy (C * h ^ (d + 2)) henergy

/-- The cubic cut-patch squared lower bound yields the universal
`h^(3/2)` norm obstruction. -/
theorem cutPatch_error_ge_threeHalves
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (error C N h : ℝ) (d : ℕ)
    (herror : 0 ≤ error)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (herrorSq : error ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S, C * h ^ (d + 2) ≤ energy i)
    (hcard : N / h ^ (d - 1) ≤ (S.card : ℝ)) :
    Real.sqrt (C * N) * (h * Real.sqrt h) ≤ error := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have htargetNonneg :
      0 ≤ Real.sqrt (C * N) * (h * Real.sqrt h) :=
    mul_nonneg (Real.sqrt_nonneg _) <|
      mul_nonneg (le_of_lt hh) (Real.sqrt_nonneg _)
  have htargetSq :
      (Real.sqrt (C * N) * (h * Real.sqrt h)) ^ 2 =
        C * N * h ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hCN, threeHalvesScale_sq h (le_of_lt hh)]
  have hsum := cutPatch_sum_energy_ge_cubic
    S energy C N h d hd hh hC hN henergy hcard
  have hsquare :
      (Real.sqrt (C * N) * (h * Real.sqrt h)) ^ 2 ≤ error ^ 2 := by
    rw [htargetSq, herrorSq]
    exact hsum
  nlinarith

end BernsteinObstacle
