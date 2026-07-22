import BernsteinObstacle.PhysicalOddMeshQuadratic
import BernsteinObstacle.GlobalSmoothSaturation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
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

/-- Coordinate projection has operator norm at most one for the finite sup norm. -/
theorem centralProjection_opNorm_le_one (m : ℕ) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * m + 1) => ℝ)
      (evenCentralIndex m))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro c
  simpa using norm_apply_le_norm c (evenCentralIndex m)

/-- Every feasible control vector differs from the target by at least the exact
central defect in the selected coordinate. -/
theorem evenPhysicalDefect_le_projection_error
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (c : Fin (2 * m + 1) → ℝ)
    (hc : c ∈ nonnegativePhysicalCoefficientCone m) :
    evenPhysicalDefect m h ≤
      |(ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (2 * m + 1) => ℝ)
        (evenCentralIndex m))
        (evenCentralPhysicalVector m h - c)| := by
  have hd0 := evenPhysicalDefect_nonneg m hm h
  have hc0 : 0 ≤ c (evenCentralIndex m) := hc (evenCentralIndex m)
  have hcenter := evenCentralPhysicalVector_center m hm h
  simp only [ContinuousLinearMap.proj_apply, Pi.sub_apply, hcenter]
  rw [abs_of_nonpos]
  · linarith
  · linarith

/-- Concrete physical central-cell saturation in coefficient space. -/
theorem evenPhysicalCoefficient_bestApproximation_lower
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    evenPhysicalDefect m h ≤
      bestApproximationError (evenCentralPhysicalVector m h)
        (nonnegativePhysicalCoefficientCone m) := by
  let L : (Fin (2 * m + 1) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (2 * m + 1) => ℝ) (evenCentralIndex m)
  have hK : (nonnegativePhysicalCoefficientCone m).Nonempty := by
    refine ⟨0, ?_⟩
    intro k
    simp
  have hL : ‖L‖ ≤ 1 := by
    simpa [L] using centralProjection_opNorm_le_one m
  have hdefect : ∀ c ∈ nonnegativePhysicalCoefficientCone m,
      evenPhysicalDefect m h ≤ |L (evenCentralPhysicalVector m h - c)| := by
    intro c hc
    simpa [L] using evenPhysicalDefect_le_projection_error m hm h c hc
  have hlower := bestApproximationError_lower_of_coefficientDefect
    (evenCentralPhysicalVector m h)
    (nonnegativePhysicalCoefficientCone m) L
    (evenPhysicalDefect m h) 1 hK (by norm_num) hL hdefect
  simpa using hlower

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
