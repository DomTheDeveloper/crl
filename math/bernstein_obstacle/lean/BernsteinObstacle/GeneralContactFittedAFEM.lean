import BernsteinObstacle.OneStepFittedAFEMBestError
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# One-step contact fitting on an arbitrary interval

Let `a ≤ ξ ≤ b` and consider the quadratic contact profile

`u(x) = (x - ξ)^2`.

Splitting `[a,b]` at the contact point `ξ` produces the children `[a,ξ]`
and `[ξ,b]`. On the left child the pullback is
`(ξ-a)^2 (1-t)^2`; on the right child it is `(b-ξ)^2 t^2`.
Consequently every fixed degree `p ≥ 2` has an exact nonnegative Bernstein
representation on both children. If both child widths are at most one, all
coefficients lie in `[0,1]`, so the genuine coefficient-box best error is zero.
-/

/-- Width of the fitted left child. -/
def leftContactWidth (a ξ : ℝ) : ℝ := ξ - a

/-- Width of the fitted right child. -/
def rightContactWidth (b ξ : ℝ) : ℝ := b - ξ

/-- Exact degree-`p` coefficients on the fitted left child. -/
def leftContactQuadraticCoeff (p k : ℕ) (a ξ : ℝ) : ℝ :=
  leftContactWidth a ξ ^ 2 * oneMinusQuadraticCoeff p k

/-- Exact degree-`p` coefficients on the fitted right child. -/
def rightContactQuadraticCoeff (p k : ℕ) (b ξ : ℝ) : ℝ :=
  rightContactWidth b ξ ^ 2 * quadraticMonomialCoeff p k

/-- Exact representation on the arbitrary fitted left child. -/
theorem leftContactQuadratic_exact
    (p : ℕ) (hp : 2 ≤ p) (a ξ t : ℝ) :
    curve p (fun k => leftContactQuadraticCoeff p k a ξ) t =
      (a + leftContactWidth a ξ * t - ξ) ^ 2 := by
  unfold curve leftContactQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        (leftContactWidth a ξ ^ 2 * oneMinusQuadraticCoeff p k) * basis p k t) =
        leftContactWidth a ξ ^ 2 * curve p (oneMinusQuadraticCoeff p) t := by
      unfold curve
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = leftContactWidth a ξ ^ 2 * (1 - t) ^ 2 := by
      rw [oneMinusQuadraticCoeff_curve_eq p hp t]
    _ = (a + leftContactWidth a ξ * t - ξ) ^ 2 := by
      unfold leftContactWidth
      ring

/-- Exact representation on the arbitrary fitted right child. -/
theorem rightContactQuadratic_exact
    (p : ℕ) (hp : 2 ≤ p) (b ξ t : ℝ) :
    curve p (fun k => rightContactQuadraticCoeff p k b ξ) t =
      (ξ + rightContactWidth b ξ * t - ξ) ^ 2 := by
  unfold curve rightContactQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        (rightContactWidth b ξ ^ 2 * quadraticMonomialCoeff p k) * basis p k t) =
        rightContactWidth b ξ ^ 2 *
          (∑ k ∈ Finset.range (p + 1),
            quadraticMonomialCoeff p k * basis p k t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = rightContactWidth b ξ ^ 2 * t ^ 2 := by
      have hquad := quadraticMonomial_eq_bernsteinCurve p hp t
      simpa [curve] using congrArg
        (fun z => rightContactWidth b ξ ^ 2 * z) hquad
    _ = (ξ + rightContactWidth b ξ * t - ξ) ^ 2 := by ring

/-- All left-child coefficients are nonnegative. -/
theorem leftContactQuadraticCoeff_nonneg
    (p k : ℕ) (a ξ : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1)) :
    0 ≤ leftContactQuadraticCoeff p k a ξ := by
  unfold leftContactQuadraticCoeff
  exact mul_nonneg (sq_nonneg _)
    (oneMinusQuadraticCoeff_nonneg p k hp hk)

/-- All right-child coefficients are nonnegative. -/
theorem rightContactQuadraticCoeff_nonneg
    (p k : ℕ) (b ξ : ℝ) (hp : 2 ≤ p) :
    0 ≤ rightContactQuadraticCoeff p k b ξ := by
  unfold rightContactQuadraticCoeff
  exact mul_nonneg (sq_nonneg _)
    (quadraticMonomialCoeff_nonneg p k hp)

/-- Full `[0,1]` certificate on the fitted left child. -/
theorem leftContactQuadraticCoeff_mem_Icc
    (p k : ℕ) (a ξ : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1))
    (hw0 : 0 ≤ leftContactWidth a ξ)
    (hw1 : leftContactWidth a ξ ≤ 1) :
    leftContactQuadraticCoeff p k a ξ ∈ Set.Icc 0 1 := by
  have hbase0 := oneMinusQuadraticCoeff_nonneg p k hp hk
  have hbase1 := oneMinusQuadraticCoeff_le_one p k hp hk
  have hscale1 : leftContactWidth a ξ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
  constructor
  · exact leftContactQuadraticCoeff_nonneg p k a ξ hp hk
  · unfold leftContactQuadraticCoeff
    calc
      leftContactWidth a ξ ^ 2 * oneMinusQuadraticCoeff p k ≤
          1 * oneMinusQuadraticCoeff p k :=
        mul_le_mul_of_nonneg_right hscale1 hbase0
      _ = oneMinusQuadraticCoeff p k := one_mul _
      _ ≤ 1 := hbase1

/-- Full `[0,1]` certificate on the fitted right child. -/
theorem rightContactQuadraticCoeff_mem_Icc
    (p k : ℕ) (b ξ : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1))
    (hw0 : 0 ≤ rightContactWidth b ξ)
    (hw1 : rightContactWidth b ξ ≤ 1) :
    rightContactQuadraticCoeff p k b ξ ∈ Set.Icc 0 1 := by
  have hbase0 := quadraticMonomialCoeff_nonneg p k hp
  have hbase1 := quadraticMonomialCoeff_le_one p k hp hk
  have hscale1 : rightContactWidth b ξ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
  constructor
  · exact rightContactQuadraticCoeff_nonneg p k b ξ hp
  · unfold rightContactQuadraticCoeff
    calc
      rightContactWidth b ξ ^ 2 * quadraticMonomialCoeff p k ≤
          1 * quadraticMonomialCoeff p k :=
        mul_le_mul_of_nonneg_right hscale1 hbase0
      _ = quadraticMonomialCoeff p k := one_mul _
      _ ≤ 1 := hbase1

/-- Coefficient pair on an arbitrary contact-fitted element. -/
def generalContactCoefficientPair (p : ℕ) (a b ξ : ℝ) :
    FittedQuadraticCoefficientPair p :=
  (fun k => leftContactQuadraticCoeff p k a ξ,
   fun k => rightContactQuadraticCoeff p k b ξ)

/-- The exact arbitrary-contact coefficient pair lies in the full box. -/
theorem generalContactCoefficientPair_mem_box
    (p : ℕ) (a b ξ : ℝ) (hp : 2 ≤ p)
    (hl0 : 0 ≤ leftContactWidth a ξ)
    (hl1 : leftContactWidth a ξ ≤ 1)
    (hr0 : 0 ≤ rightContactWidth b ξ)
    (hr1 : rightContactWidth b ξ ≤ 1) :
    generalContactCoefficientPair p a b ξ ∈ fittedQuadraticCoefficientBox p := by
  constructor
  · intro k
    exact leftContactQuadraticCoeff_mem_Icc p k a ξ hp
      (Finset.mem_range.mpr k.isLt) hl0 hl1
  · intro k
    exact rightContactQuadraticCoeff_mem_Icc p k b ξ hp
      (Finset.mem_range.mpr k.isLt) hr0 hr1

/-- One exact contact-fitting split collapses the genuine coefficient-box best
approximation error to zero on every admissible interval. -/
theorem generalContactFitted_bestApproximationError_eq_zero
    (p : ℕ) (a b ξ : ℝ) (hp : 2 ≤ p)
    (hl0 : 0 ≤ leftContactWidth a ξ)
    (hl1 : leftContactWidth a ξ ≤ 1)
    (hr0 : 0 ≤ rightContactWidth b ξ)
    (hr1 : rightContactWidth b ξ ≤ 1) :
    bestApproximationError (generalContactCoefficientPair p a b ξ)
      (fittedQuadraticCoefficientBox p) = 0 := by
  unfold bestApproximationError
  exact Metric.infDist_zero_of_mem
    (generalContactCoefficientPair_mem_box p a b ξ hp hl0 hl1 hr0 hr1)

/-- A direct shape-regularity certificate. If the parent width is bounded by
`R` times each child width, then both parent-to-child ratios are bounded by `R`. -/
theorem generalContactFitted_shapeRegular
    (a b ξ R : ℝ)
    (hl : 0 < leftContactWidth a ξ)
    (hr : 0 < rightContactWidth b ξ)
    (hleft : b - a ≤ R * leftContactWidth a ξ)
    (hright : b - a ≤ R * rightContactWidth b ξ) :
    (b - a) / leftContactWidth a ξ ≤ R ∧
      (b - a) / rightContactWidth b ξ ≤ R := by
  constructor
  · exact (div_le_iff₀ hl).2 hleft
  · exact (div_le_iff₀ hr).2 hright

/-- Terminal arbitrary-contact theorem: exact reproduction, full coefficient
feasibility, zero genuine best error, and an explicit shape-ratio bound. -/
theorem generalContactFittedAFEM_complete
    (p : ℕ) (a b ξ R : ℝ) (hp : 2 ≤ p)
    (hl0 : 0 < leftContactWidth a ξ)
    (hl1 : leftContactWidth a ξ ≤ 1)
    (hr0 : 0 < rightContactWidth b ξ)
    (hr1 : rightContactWidth b ξ ≤ 1)
    (hleft : b - a ≤ R * leftContactWidth a ξ)
    (hright : b - a ≤ R * rightContactWidth b ξ) :
    bestApproximationError (generalContactCoefficientPair p a b ξ)
        (fittedQuadraticCoefficientBox p) = 0 ∧
    (∀ t, curve p (fun k => leftContactQuadraticCoeff p k a ξ) t =
      (a + leftContactWidth a ξ * t - ξ) ^ 2) ∧
    (∀ t, curve p (fun k => rightContactQuadraticCoeff p k b ξ) t =
      (ξ + rightContactWidth b ξ * t - ξ) ^ 2) ∧
    (b - a) / leftContactWidth a ξ ≤ R ∧
    (b - a) / rightContactWidth b ξ ≤ R := by
  constructor
  · exact generalContactFitted_bestApproximationError_eq_zero
      p a b ξ hp hl0.le hl1 hr0.le hr1
  constructor
  · exact leftContactQuadratic_exact p hp a ξ
  constructor
  · exact rightContactQuadratic_exact p hp b ξ
  · exact generalContactFitted_shapeRegular a b ξ R hl0 hr0 hleft hright

end

end BernsteinObstacle
