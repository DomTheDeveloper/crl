import BernsteinObstacle.PhysicalOddMeshQuadratic
import BernsteinObstacle.GlobalSmoothSaturation
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Concrete coefficient-space saturation on the physical central cell

This file removes the final abstract coefficient-error variable from the local
obstruction.  The target is the actual degree-`2m` coefficient vector of `x²`
on `[-h/2,h/2]`; the feasible set is the actual nonnegative coefficient cone;
and the distance is the genuine metric infimum distance in the finite sup norm.
-/

/-- The central index of an even degree `2m`. -/
def evenCentralIndex (m : ℕ) : Fin (2 * m + 1) :=
  ⟨m, by omega⟩

/-- Actual coefficient vector of the physical centered quadratic. -/
def evenCentralPhysicalVector (m : ℕ) (h : ℝ) : Fin (2 * m + 1) → ℝ :=
  fun k => centralPhysicalCoeff (2 * m) k h

/-- Actual nonnegative coefficient cone on the physical central cell. -/
def nonnegativePhysicalCoefficientCone (m : ℕ) :
    Set (Fin (2 * m + 1) → ℝ) :=
  {c | ∀ k, 0 ≤ c k}

/-- Exact positive size of the even-degree central defect. -/
def evenPhysicalDefect (m : ℕ) (h : ℝ) : ℝ :=
  h ^ 2 / (4 * (((2 * m : ℕ) : ℝ) - 1))

/-- The defect is nonnegative. -/
theorem evenPhysicalDefect_nonneg
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    0 ≤ evenPhysicalDefect m h := by
  unfold evenPhysicalDefect
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 4 * (((2 * m : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  exact div_nonneg (sq_nonneg h) hden.le

/-- The target's selected central coordinate is exactly minus the defect. -/
theorem evenCentralPhysicalVector_center
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    evenCentralPhysicalVector m h (evenCentralIndex m) =
      -evenPhysicalDefect m h := by
  unfold evenCentralPhysicalVector evenCentralIndex evenPhysicalDefect
  simpa using centralPhysicalCoeff_even_center m hm h

/-- Every feasible control vector differs from the target by at least the exact
central defect in the selected coordinate. -/
theorem evenPhysicalDefect_le_coordinate_error
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (c : Fin (2 * m + 1) → ℝ)
    (hc : c ∈ nonnegativePhysicalCoefficientCone m) :
    evenPhysicalDefect m h ≤
      |(evenCentralPhysicalVector m h - c) (evenCentralIndex m)| := by
  have hd0 := evenPhysicalDefect_nonneg m hm h
  have hc0 : 0 ≤ c (evenCentralIndex m) := hc (evenCentralIndex m)
  have hcenter := evenCentralPhysicalVector_center m hm h
  simp only [Pi.sub_apply, hcenter]
  rw [abs_of_nonpos]
  · linarith
  · linarith

/-- Any coordinate norm is bounded by the finite sup norm. -/
theorem coordinate_norm_le_pi_norm
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).1 le_rfl i

/-- Concrete physical central-cell saturation in coefficient space. -/
theorem evenPhysicalCoefficient_bestApproximation_lower
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    evenPhysicalDefect m h ≤
      bestApproximationError (evenCentralPhysicalVector m h)
        (nonnegativePhysicalCoefficientCone m) := by
  have hK : (nonnegativePhysicalCoefficientCone m).Nonempty := by
    refine ⟨0, ?_⟩
    intro k
    simp
  unfold bestApproximationError
  apply (Metric.le_infDist hK).2
  intro c hc
  rw [dist_eq_norm]
  have hcoord := evenPhysicalDefect_le_coordinate_error m hm h c hc
  have hnorm :
      |(evenCentralPhysicalVector m h - c) (evenCentralIndex m)| ≤
        ‖evenCentralPhysicalVector m h - c‖ := by
    rw [← Real.norm_eq_abs]
    exact coordinate_norm_le_pi_norm
      (evenCentralPhysicalVector m h - c) (evenCentralIndex m)
  exact hcoord.trans hnorm

/-- On every nondegenerate cell, the concrete best coefficient error is
strictly positive. -/
theorem evenPhysicalCoefficient_bestApproximation_pos
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) (hh : h ≠ 0) :
    0 < bestApproximationError (evenCentralPhysicalVector m h)
      (nonnegativePhysicalCoefficientCone m) := by
  have hdefectPos : 0 < evenPhysicalDefect m h := by
    unfold evenPhysicalDefect
    have hnum : 0 < h ^ 2 := sq_pos_of_ne_zero hh
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hden : 0 < 4 * (((2 * m : ℕ) : ℝ) - 1) := by
      push_cast
      nlinarith
    exact div_pos hnum hden
  exact hdefectPos.trans_le
    (evenPhysicalCoefficient_bestApproximation_lower m hm h)

end

end BernsteinObstacle
