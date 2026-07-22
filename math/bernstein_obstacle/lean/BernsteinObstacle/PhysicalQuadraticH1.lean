import BernsteinObstacle.PhysicalOddMeshQuadratic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped Interval

namespace BernsteinObstacle

noncomputable section

/-!
# Exact physical H¹ cost of the global quadratic repair

For `u(x)=x²`, the global feasible repair is

`v_d(x) = (x²+d)/(1+d)`.

Its error is `d(1-x²)/(1+d)`.  This file computes the actual `H¹(-1,1)`
squared norm exactly and recovers the upper constant `sqrt(56/15)`.
-/

/-- Unscaled physical repair profile. -/
def quadraticRepairProfile (x : ℝ) : ℝ := 1 - x ^ 2

/-- Derivative of the unscaled repair profile. -/
def quadraticRepairProfileDeriv (x : ℝ) : ℝ := -2 * x

/-- Physical `H¹` density of the unscaled repair profile. -/
def quadraticRepairH1Density (x : ℝ) : ℝ :=
  quadraticRepairProfile x ^ 2 + quadraticRepairProfileDeriv x ^ 2

/-- Exact `L²` contribution of the repair profile. -/
theorem intervalIntegral_quadraticRepairProfile_sq :
    (∫ x in (-1 : ℝ)..1, quadraticRepairProfile x ^ 2) = 16 / 15 := by
  have hI1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x : ℝ => 2 * x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ => 2 * x ^ 2)).intervalIntegrable _ _
  have hI4 : IntervalIntegrable (fun x : ℝ => x ^ 4) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4)).intervalIntegrable _ _
  have hexpand :
      (fun x : ℝ => quadraticRepairProfile x ^ 2) =
        fun x : ℝ => 1 - 2 * x ^ 2 + x ^ 4 := by
    funext x
    simp [quadraticRepairProfile]
    ring
  rw [hexpand]
  rw [intervalIntegral.integral_add (hI1.sub hI2) hI4,
    intervalIntegral.integral_sub hI1 hI2,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const, integral_pow, integral_pow]
  norm_num

/-- Exact derivative contribution of the repair profile. -/
theorem intervalIntegral_quadraticRepairProfileDeriv_sq :
    (∫ x in (-1 : ℝ)..1, quadraticRepairProfileDeriv x ^ 2) = 8 / 3 := by
  have hfun :
      (fun x : ℝ => quadraticRepairProfileDeriv x ^ 2) =
        fun x : ℝ => 4 * x ^ 2 := by
    funext x
    simp [quadraticRepairProfileDeriv]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- Exact squared `H¹(-1,1)` norm of `1-x²`. -/
theorem intervalIntegral_quadraticRepairH1Density :
    (∫ x in (-1 : ℝ)..1, quadraticRepairH1Density x) = 56 / 15 := by
  have hI0 : IntervalIntegrable
      (fun x : ℝ => quadraticRepairProfile x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ => quadraticRepairProfile x ^ 2)).intervalIntegrable _ _
  have hI1 : IntervalIntegrable
      (fun x : ℝ => quadraticRepairProfileDeriv x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ => quadraticRepairProfileDeriv x ^ 2)).intervalIntegrable _ _
  unfold quadraticRepairH1Density
  rw [intervalIntegral.integral_add hI0 hI1,
    intervalIntegral_quadraticRepairProfile_sq,
    intervalIntegral_quadraticRepairProfileDeriv_sq]
  norm_num

/-- Repair amplitude `d/(1+d)`. -/
def quadraticRepairAmplitude (d : ℝ) : ℝ := d / (1 + d)

/-- Actual physical repair error. -/
def quadraticRepairError (d x : ℝ) : ℝ :=
  quadraticRepairAmplitude d * quadraticRepairProfile x

/-- Actual derivative of the physical repair error. -/
def quadraticRepairErrorDeriv (d x : ℝ) : ℝ :=
  quadraticRepairAmplitude d * quadraticRepairProfileDeriv x

/-- Exact physical squared `H¹` error of the inward repair. -/
theorem intervalIntegral_quadraticRepairError_H1_sq (d : ℝ) :
    (∫ x in (-1 : ℝ)..1,
      quadraticRepairError d x ^ 2 + quadraticRepairErrorDeriv d x ^ 2) =
        quadraticRepairAmplitude d ^ 2 * (56 / 15) := by
  have hfun :
      (fun x : ℝ =>
        quadraticRepairError d x ^ 2 + quadraticRepairErrorDeriv d x ^ 2) =
      fun x : ℝ => quadraticRepairAmplitude d ^ 2 * quadraticRepairH1Density x := by
    funext x
    simp [quadraticRepairError, quadraticRepairErrorDeriv,
      quadraticRepairH1Density]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral_quadraticRepairH1Density]

/-- The exact squared error is bounded by the expected quadratic scale. -/
theorem intervalIntegral_quadraticRepairError_H1_sq_le
    (d : ℝ) (hd : 0 ≤ d) :
    (∫ x in (-1 : ℝ)..1,
      quadraticRepairError d x ^ 2 + quadraticRepairErrorDeriv d x ^ 2) ≤
        d ^ 2 * (56 / 15) := by
  rw [intervalIntegral_quadraticRepairError_H1_sq]
  have hden : 1 ≤ 1 + d := by linarith
  have hamp : quadraticRepairAmplitude d ≤ d := by
    exact inwardRepairWeight_le_defect d hd
  have hamp0 : 0 ≤ quadraticRepairAmplitude d :=
    div_nonneg hd (by positivity)
  have hsq : quadraticRepairAmplitude d ^ 2 ≤ d ^ 2 :=
    sq_le_sq₀ hamp0 hamp
  exact mul_le_mul_of_nonneg_right hsq (by norm_num)

end

end BernsteinObstacle
