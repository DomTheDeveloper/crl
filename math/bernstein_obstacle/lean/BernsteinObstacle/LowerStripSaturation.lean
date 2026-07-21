import BernsteinObstacle.TransversePrismSaturation
import BernsteinObstacle.StripScaling
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Codimension-one lower-strip saturation

This file is the lower-bound counterpart of `StripScaling.lean`.  A uniform
`h^(d+2)` obstruction on every nondegenerately cut element, together with a
lower bound of order `h^(-(d-1))` on the number of such elements, forces a
cubic global squared error and therefore the universal `h^(3/2)` norm
obstruction.
-/

/-- Summing a uniform lower bound over a finite patch produces cardinality
multiplied by that lower bound. -/
theorem card_mul_le_sum_of_le
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ) (q : ℝ)
    (henergy : ∀ i ∈ S, q ≤ energy i) :
    (S.card : ℝ) * q ≤ ∑ i ∈ S, energy i := by
  calc
    (S.card : ℝ) * q = ∑ _i ∈ S, q := by simp
    _ ≤ ∑ i ∈ S, energy i :=
      Finset.sum_le_sum fun i hi => henergy i hi

/-- Per-element `h^(d+2)` lower bounds and a codimension-one lower patch count
produce a global cubic squared-error lower bound. -/
theorem strip_sum_energy_ge_cubic
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (C N h : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ S, C * h ^ (d + 2) ≤ energy i)
    (hcard : N / h ^ (d - 1) ≤ (S.card : ℝ)) :
    C * N * h ^ 3 ≤ ∑ i ∈ S, energy i := by
  have hpow : 0 ≤ h ^ (d + 2) := pow_nonneg (le_of_lt hh) _
  have hq : 0 ≤ C * h ^ (d + 2) := mul_nonneg hC hpow
  have hsum :
      (S.card : ℝ) * (C * h ^ (d + 2)) ≤ ∑ i ∈ S, energy i :=
    card_mul_le_sum_of_le S energy (C * h ^ (d + 2)) henergy
  calc
    C * N * h ^ 3 = C * N * (h ^ (d + 2) / h ^ (d - 1)) := by
      rw [strip_power_cancellation h d hd (ne_of_gt hh)]
    _ = (N / h ^ (d - 1)) * (C * h ^ (d + 2)) := by ring
    _ ≤ (S.card : ℝ) * (C * h ^ (d + 2)) :=
      mul_le_mul_of_nonneg_right hcard hq
    _ ≤ ∑ i ∈ S, energy i := hsum

/-- A cubic lower bound on squared error gives the matching three-halves lower
bound on the error norm. -/
theorem threeHalves_lowerBound_of_cubic_le_sq
    (e C N h : ℝ)
    (he : 0 ≤ e) (hC : 0 ≤ C) (hN : 0 ≤ N) (hh : 0 ≤ h)
    (hsq : C * N * h ^ 3 ≤ e ^ 2) :
    Real.sqrt (C * N) * (h * Real.sqrt h) ≤ e := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hsqrtCN : (Real.sqrt (C * N)) ^ 2 = C * N :=
    Real.sq_sqrt hCN
  have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
    threeHalvesScale_sq h hh
  have htargetNonneg :
      0 ≤ Real.sqrt (C * N) * (h * Real.sqrt h) := by
    positivity
  have htargetSq :
      (Real.sqrt (C * N) * (h * Real.sqrt h)) ^ 2 =
        C * N * h ^ 3 := by
    rw [mul_pow, hsqrtCN, hscale]
  nlinarith

/-- Complete local-obstruction-to-global-saturation theorem.  If the global
squared approximation error dominates the sum of the cut-element energies,
then the full approximation error has the universal `h * sqrt h` lower bound. -/
theorem fullSpace_error_ge_threeHalves_of_element_lowerBounds
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (e C N h : ℝ) (d : ℕ)
    (he : 0 ≤ e) (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ S, C * h ^ (d + 2) ≤ energy i)
    (hcard : N / h ^ (d - 1) ≤ (S.card : ℝ))
    (hsum : ∑ i ∈ S, energy i ≤ e ^ 2) :
    Real.sqrt (C * N) * (h * Real.sqrt h) ≤ e := by
  have hcubic := strip_sum_energy_ge_cubic
    S energy C N h d hd hh hC hN henergy hcard
  exact threeHalves_lowerBound_of_cubic_le_sq
    e C N h he hC hN (le_of_lt hh) (hcubic.trans hsum)

end BernsteinObstacle
