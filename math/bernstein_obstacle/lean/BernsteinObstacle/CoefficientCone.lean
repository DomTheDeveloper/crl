import BernsteinObstacle.Core
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

/-- The nonnegative orthant of coefficient functions. -/
def coefficientCone (ι : Type*) :=
  {c : ι → ℝ | ∀ i, 0 ≤ c i}

@[simp]
theorem mem_coefficientCone_iff {ι : Type*} (c : ι → ℝ) :
    c ∈ coefficientCone ι ↔ ∀ i, 0 ≤ c i := by
  rfl

/-- The nonnegative coefficient orthant is convex. -/
theorem coefficientCone_convex (ι : Type*) :
    Convex ℝ (coefficientCone ι) := by
  intro c hc d hd a b ha hb hab
  intro i
  change 0 ≤ a * c i + b * d i
  exact add_nonneg (mul_nonneg ha (hc i)) (mul_nonneg hb (hd i))

/-- Coefficientwise clipping for an arbitrary index type. -/
def clipCoefficients {ι : Type*} (c : ι → ℝ) : ι → ℝ :=
  fun i => clip (c i)

/-- Clipped coefficients belong to the nonnegative coefficient cone. -/
theorem clipCoefficients_mem {ι : Type*} (c : ι → ℝ) :
    clipCoefficients c ∈ coefficientCone ι := by
  intro i
  exact clip_nonneg (c i)

/-- Every coefficient is bounded above by its clipped value. -/
theorem coefficient_le_clipCoefficients {ι : Type*} (c : ι → ℝ) :
    ∀ i, c i ≤ clipCoefficients c i := by
  intro i
  exact le_clip (c i)

/-- Clipping is idempotent. -/
theorem clipCoefficients_idem {ι : Type*} (c : ι → ℝ) :
    clipCoefficients (clipCoefficients c) = clipCoefficients c := by
  funext i
  simp [clipCoefficients, clip, max_eq_left (clip_nonneg (c i))]

/-- Clipping is the least nonnegative coefficient vector above the original one. -/
theorem clipCoefficients_minimal {ι : Type*} (c d : ι → ℝ)
    (hd : d ∈ coefficientCone ι) (hcd : ∀ i, c i ≤ d i) :
    ∀ i, clipCoefficients c i ≤ d i := by
  intro i
  exact max_le (hcd i) (hd i)

/-- The coefficient cone is closed under nonnegative addition. -/
theorem coefficientCone_add {ι : Type*} {c d : ι → ℝ}
    (hc : c ∈ coefficientCone ι) (hd : d ∈ coefficientCone ι) :
    (fun i => c i + d i) ∈ coefficientCone ι := by
  intro i
  exact add_nonneg (hc i) (hd i)

/-- The coefficient cone is closed under multiplication by a nonnegative scalar. -/
theorem coefficientCone_smul {ι : Type*} {c : ι → ℝ}
    (hc : c ∈ coefficientCone ι) {a : ℝ} (ha : 0 ≤ a) :
    (fun i => a * c i) ∈ coefficientCone ι := by
  intro i
  exact mul_nonneg ha (hc i)

end BernsteinObstacle
