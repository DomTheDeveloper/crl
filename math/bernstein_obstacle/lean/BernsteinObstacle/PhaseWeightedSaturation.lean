import BernsteinObstacle.CutPatchSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Phase-weighted cut-patch saturation

Uniform phase separation is sufficient but not necessary for three-halves saturation.
This file records the exact weighted replacement.  Each cut element contributes a
nonnegative quality weight, for example a product of Jacobian, tangential mass,
quadratic-contact amplitude, and the exact phase factor
`theta^3 * (1-theta)^3`.

The global lower constant is controlled by the codimension-one density of the sum of
those weights.  Interface-aligned meshes have zero density; uniformly nondegenerate
and generic-shift meshes have a positive density.
-/

/-- Weighted local lower bounds sum to the weighted cardinality. -/
theorem weighted_sum_local_lowerBound
    {ι : Type*} (S : Finset ι) (energy weight : ι → ℝ)
    (C h : ℝ) (d : ℕ)
    (henergy : ∀ i ∈ S,
      C * weight i * h ^ (d + 2) ≤ energy i) :
    C * (∑ i ∈ S, weight i) * h ^ (d + 2) ≤
      ∑ i ∈ S, energy i := by
  calc
    C * (∑ i ∈ S, weight i) * h ^ (d + 2) =
        ∑ i ∈ S, C * weight i * h ^ (d + 2) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ i ∈ S, energy i := by
      exact Finset.sum_le_sum fun i hi => henergy i hi

/-- A codimension-one lower bound on the total phase weight yields the same cubic
squared-error obstruction as a uniform lower count of good elements. -/
theorem phaseWeighted_sum_energy_ge_cubic
    {ι : Type*} (S : Finset ι) (energy weight : ι → ℝ)
    (C N h : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ S,
      C * weight i * h ^ (d + 2) ≤ energy i)
    (hweight : N / h ^ (d - 1) ≤ ∑ i ∈ S, weight i) :
    C * N * h ^ 3 ≤ ∑ i ∈ S, energy i := by
  have hpow : 0 ≤ h ^ (d + 2) := pow_nonneg (le_of_lt hh) _
  have hscale : 0 ≤ C * h ^ (d + 2) := mul_nonneg hC hpow
  have hweightedScaled :
      (N / h ^ (d - 1)) * (C * h ^ (d + 2)) ≤
        (∑ i ∈ S, weight i) * (C * h ^ (d + 2)) :=
    mul_le_mul_of_nonneg_right hweight hscale
  have hsum := weighted_sum_local_lowerBound
    S energy weight C h d henergy
  calc
    C * N * h ^ 3 =
        C * N * (h ^ (d + 2) / h ^ (d - 1)) := by
      rw [strip_power_cancellation h d hd (ne_of_gt hh)]
    _ = (N / h ^ (d - 1)) * (C * h ^ (d + 2)) := by ring
    _ ≤ (∑ i ∈ S, weight i) * (C * h ^ (d + 2)) :=
      hweightedScaled
    _ = C * (∑ i ∈ S, weight i) * h ^ (d + 2) := by ring
    _ ≤ ∑ i ∈ S, energy i := hsum

/-- Phase-density form of the global three-halves lower bound. -/
theorem phaseWeighted_error_ge_threeHalves_of_sum_le_sq
    {ι : Type*} (S : Finset ι) (energy weight : ι → ℝ)
    (error C N h : ℝ) (d : ℕ)
    (herror : 0 ≤ error)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (henergy : ∀ i ∈ S,
      C * weight i * h ^ (d + 2) ≤ energy i)
    (hweight : N / h ^ (d - 1) ≤ ∑ i ∈ S, weight i) :
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
  have hsum := phaseWeighted_sum_energy_ge_cubic
    S energy weight C N h d hd hh hC hN henergy hweight
  have hsquare :
      (Real.sqrt (C * N) * (h * Real.sqrt h)) ^ 2 ≤ error ^ 2 := by
    rw [htargetSq]
    exact hsum.trans hsumSq
  nlinarith

end BernsteinObstacle