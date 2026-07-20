import BernsteinObstacle.CoefficientCone
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Projection onto the coefficient cone

For a finite coefficient space, coefficientwise clipping is not merely a
feasible repair: it is the Euclidean metric projection onto the nonnegative
orthant.  This is the precise finite-dimensional optimization statement used
by active-set and clipping arguments.
-/

/-- Scalar clipping minimizes squared distance among all nonnegative
candidates. -/
theorem clip_sqDist_le_of_nonneg (a b : ℝ) (hb : 0 ≤ b) :
    (clip a - a) ^ 2 ≤ (b - a) ^ 2 := by
  by_cases ha : 0 ≤ a
  · have hclip : clip a = a := by
      simp [clip, max_eq_left ha]
    rw [hclip]
    nlinarith [sq_nonneg (b - a)]
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    have hclip : clip a = 0 := by
      simp [clip, max_eq_right ha0]
    rw [hclip]
    have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hb
    nlinarith [sq_nonneg b]

/-- Squared Euclidean distance between two finite coefficient vectors. -/
def coefficientSqDist {ι : Type*} [Fintype ι]
    (c d : ι → ℝ) : ℝ :=
  ∑ i, (d i - c i) ^ 2

@[simp]
theorem coefficientSqDist_nonneg {ι : Type*} [Fintype ι]
    (c d : ι → ℝ) :
    0 ≤ coefficientSqDist c d := by
  unfold coefficientSqDist
  positivity

/-- Coefficientwise clipping is a nearest point in the nonnegative orthant. -/
theorem clipCoefficients_sqDist_minimal {ι : Type*} [Fintype ι]
    (c d : ι → ℝ) (hd : d ∈ coefficientCone ι) :
    coefficientSqDist c (clipCoefficients c) ≤ coefficientSqDist c d := by
  unfold coefficientSqDist
  apply Finset.sum_le_sum
  intro i hi
  exact clip_sqDist_le_of_nonneg (c i) (d i) (hd i)

/-- A coefficient vector is fixed by clipping exactly when it is feasible. -/
theorem clipCoefficients_eq_self_iff {ι : Type*} (c : ι → ℝ) :
    clipCoefficients c = c ↔ c ∈ coefficientCone ι := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [clipCoefficients] at hi
    exact hi ▸ clip_nonneg (c i)
  · intro hc
    funext i
    simp [clipCoefficients, clip, max_eq_left (hc i)]

/-- Clipping has zero squared displacement exactly on the coefficient cone. -/
theorem coefficientSqDist_clip_eq_zero_iff {ι : Type*} [Fintype ι]
    (c : ι → ℝ) :
    coefficientSqDist c (clipCoefficients c) = 0 ↔
      c ∈ coefficientCone ι := by
  constructor
  · intro h
    have hterm : ∀ i, (clipCoefficients c i - c i) ^ 2 = 0 := by
      intro i
      have hzero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_hj : j ∈ (Finset.univ : Finset ι)) =>
            sq_nonneg (clipCoefficients c j - c j))).mp h
      exact hzero i (Finset.mem_univ i)
    apply (clipCoefficients_eq_self_iff c).mp
    funext i
    have hi := hterm i
    nlinarith
  · intro hc
    have hfix : clipCoefficients c = c :=
      (clipCoefficients_eq_self_iff c).2 hc
    rw [hfix]
    simp [coefficientSqDist]

end BernsteinObstacle
