import BernsteinObstacle.SharpRateAlgebra
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Dimension-independent free-boundary strip scaling

A correction of coefficient amplitude `O(h^2)` has per-element squared
`H^1` cost `O(h^(d+2))`.  A locally quasi-uniform codimension-one strip has
`O(h^(-(d-1)))` elements.  The product is `O(h^3)` in every ambient
dimension, and taking the square root gives the universal `h^(3/2)` rate.
-/

/-- Summing a uniform elementwise upper bound over a finite patch produces the
cardinality times that bound. -/
theorem sum_le_card_mul_of_le
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ) (q : ℝ)
    (henergy : ∀ i ∈ S, energy i ≤ q) :
    ∑ i ∈ S, energy i ≤ (S.card : ℝ) * q := by
  calc
    ∑ i ∈ S, energy i ≤ ∑ _i ∈ S, q := by
      exact Finset.sum_le_sum fun i hi => henergy i hi
    _ = (S.card : ℝ) * q := by simp

/-- Per-element `h^(d+2)` energy and codimension-one strip cardinality give a
cubic total squared-energy bound, independently of `d`. -/
theorem strip_sum_energy_le_cubic
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (C N h : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ S, energy i ≤ C * h ^ (d + 2))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - 1)) :
    ∑ i ∈ S, energy i ≤ C * N * h ^ 3 := by
  have hpow : 0 ≤ h ^ (d + 2) := pow_nonneg (le_of_lt hh) _
  have hq : 0 ≤ C * h ^ (d + 2) := mul_nonneg hC hpow
  calc
    ∑ i ∈ S, energy i ≤ (S.card : ℝ) * (C * h ^ (d + 2)) :=
      sum_le_card_mul_of_le S energy (C * h ^ (d + 2)) henergy
    _ ≤ (N / h ^ (d - 1)) * (C * h ^ (d + 2)) :=
      mul_le_mul_of_nonneg_right hcard hq
    _ = C * N * (h ^ (d + 2) / h ^ (d - 1)) := by ring
    _ = C * N * h ^ 3 := by
      rw [strip_power_cancellation h d hd (ne_of_gt hh)]

/-- A cubic squared-error bound gives a three-halves norm bound. -/
theorem repair_norm_le_threeHalves
    (e C N h : ℝ)
    (he : 0 ≤ e) (hC : 0 ≤ C) (hN : 0 ≤ N) (hh : 0 ≤ h)
    (hsq : e ^ 2 ≤ C * N * h ^ 3) :
    e ≤ Real.sqrt (C * N) * (h * Real.sqrt h) := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hrate := sharpRate_of_energy_components
    e 1 0 (C * N) 0 h 1
    he zero_lt_one (le_refl 0) hCN (le_refl 0) hh
    (by simpa using hsq)
  simpa [max_eq_right hCN] using hrate

/-- Complete strip-count-to-repair-rate theorem. -/
theorem repair_norm_le_threeHalves_of_element_bounds
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (e C N h : ℝ) (d : ℕ)
    (he : 0 ≤ e) (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (herror : e ^ 2 ≤ ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S, energy i ≤ C * h ^ (d + 2))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - 1)) :
    e ≤ Real.sqrt (C * N) * (h * Real.sqrt h) := by
  have hsum := strip_sum_energy_le_cubic
    S energy C N h d hd hh hC hN henergy hcard
  exact repair_norm_le_threeHalves e C N h he hC hN (le_of_lt hh)
    (herror.trans hsum)

end BernsteinObstacle
