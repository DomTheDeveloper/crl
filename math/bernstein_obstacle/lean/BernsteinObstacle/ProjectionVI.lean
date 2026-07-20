import BernsteinObstacle.Projection
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Variational characterization of coefficient clipping

This file strengthens the nearest-point result in `Projection.lean`.  It proves
that coefficientwise clipping satisfies the KKT variational inequality, a
Pythagorean projection estimate, complementarity, and nonexpansiveness.  These
are the finite-dimensional convex-analysis facts used by projection, active-set,
and feasible-repair algorithms.
-/

/-- The scalar clipping residual is nonnegative. -/
theorem clip_sub_nonneg (a : ℝ) : 0 ≤ clip a - a := by
  exact sub_nonneg.mpr (le_clip a)

/-- Scalar complementarity between the clipped coefficient and its residual. -/
theorem clip_complementarity (a : ℝ) :
    clip a * (clip a - a) = 0 := by
  by_cases ha : 0 ≤ a
  · have hclip : clip a = a := by
      simp [clip, max_eq_left ha]
    rw [hclip]
    ring
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    have hclip : clip a = 0 := by
      simp [clip, max_eq_right ha0]
    rw [hclip]
    ring

/-- Scalar KKT variational inequality for projection onto `[0,∞)`. -/
theorem clip_variational_inequality (a b : ℝ) (hb : 0 ≤ b) :
    0 ≤ (clip a - a) * (b - clip a) := by
  by_cases ha : 0 ≤ a
  · have hclip : clip a = a := by
      simp [clip, max_eq_left ha]
    rw [hclip]
    ring_nf
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    have hclip : clip a = 0 := by
      simp [clip, max_eq_right ha0]
    rw [hclip]
    have hminus : 0 ≤ -a := neg_nonneg.mpr ha0
    nlinarith [mul_nonneg hminus hb]

/-- Pointwise Pythagorean inequality for projection onto `[0,∞)`. -/
theorem clip_pythagorean (a b : ℝ) (hb : 0 ≤ b) :
    (clip a - a) ^ 2 + (b - clip a) ^ 2 ≤ (b - a) ^ 2 := by
  have hvi := clip_variational_inequality a b hb
  nlinarith

/-- Scalar clipping is nonexpansive. -/
theorem clip_sqDist_nonexpansive (a b : ℝ) :
    (clip b - clip a) ^ 2 ≤ (b - a) ^ 2 := by
  by_cases ha : 0 ≤ a
  · have hca : clip a = a := by
      simp [clip, max_eq_left ha]
    by_cases hb : 0 ≤ b
    · have hcb : clip b = b := by
        simp [clip, max_eq_left hb]
      rw [hca, hcb]
    · have hb0 : b ≤ 0 := le_of_not_ge hb
      have hcb : clip b = 0 := by
        simp [clip, max_eq_right hb0]
      rw [hca, hcb]
      have hab : b * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 ha
      nlinarith
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    have hca : clip a = 0 := by
      simp [clip, max_eq_right ha0]
    by_cases hb : 0 ≤ b
    · have hcb : clip b = b := by
        simp [clip, max_eq_left hb]
      rw [hca, hcb]
      have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hb
      nlinarith
    · have hb0 : b ≤ 0 := le_of_not_ge hb
      have hcb : clip b = 0 := by
        simp [clip, max_eq_right hb0]
      rw [hca, hcb]
      positivity

/-- Euclidean pairing between two finite coefficient vectors. -/
def coefficientDot {ι : Type*} [Fintype ι]
    (c d : ι → ℝ) : ℝ :=
  ∑ i, c i * d i

/-- Coefficientwise clipping satisfies the finite-dimensional KKT variational
inequality for every feasible coefficient vector. -/
theorem clipCoefficients_variational_inequality
    {ι : Type*} [Fintype ι] (c d : ι → ℝ)
    (hd : d ∈ coefficientCone ι) :
    0 ≤ coefficientDot
      (fun i => clipCoefficients c i - c i)
      (fun i => d i - clipCoefficients c i) := by
  unfold coefficientDot
  exact Finset.sum_nonneg fun i _ =>
    clip_variational_inequality (c i) (d i) (hd i)

/-- Global coefficient complementarity. -/
theorem clipCoefficients_complementarity
    {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    coefficientDot (clipCoefficients c)
      (fun i => clipCoefficients c i - c i) = 0 := by
  unfold coefficientDot
  apply Finset.sum_eq_zero
  intro i hi
  exact clip_complementarity (c i)

/-- Pythagorean projection inequality in the finite coefficient space. -/
theorem clipCoefficients_projection_inequality
    {ι : Type*} [Fintype ι] (c d : ι → ℝ)
    (hd : d ∈ coefficientCone ι) :
    coefficientSqDist c (clipCoefficients c)
      + coefficientSqDist (clipCoefficients c) d
      ≤ coefficientSqDist c d := by
  unfold coefficientSqDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    clip_pythagorean (c i) (d i) (hd i)

/-- Coefficient clipping is nonexpansive in squared Euclidean distance. -/
theorem clipCoefficients_nonexpansive
    {ι : Type*} [Fintype ι] (c d : ι → ℝ) :
    coefficientSqDist (clipCoefficients c) (clipCoefficients d)
      ≤ coefficientSqDist c d := by
  unfold coefficientSqDist
  exact Finset.sum_le_sum fun i _ =>
    clip_sqDist_nonexpansive (c i) (d i)

/-- The projection estimate written as an obstacle-energy error bound. -/
theorem clipCoefficients_energy_bound
    {ι : Type*} [Fintype ι] (c d : ι → ℝ)
    (hd : d ∈ coefficientCone ι) :
    coefficientSqDist (clipCoefficients c) d ≤
      coefficientSqDist c d - coefficientSqDist c (clipCoefficients c) := by
  have h := clipCoefficients_projection_inequality c d hd
  linarith

end BernsteinObstacle
