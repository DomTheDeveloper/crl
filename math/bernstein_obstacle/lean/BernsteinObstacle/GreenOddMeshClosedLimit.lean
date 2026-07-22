import BernsteinObstacle.GreenInterpolationRate
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Filter Topology

namespace BernsteinObstacle

noncomputable section

/-!
# Closed-form odd-mesh Green energy limit

The exact finite-sum computation for the odd uniform P1 interpolant reduces its
squared `H¹` norm to a continuous expression in the mesh width.  The only
apparent singularities are ratios of `sinh`; they are removed using the
continuous extension `sinhc(0)=1`.
-/

/-- Continuous extension of `sinh x / x` at the origin. -/
def sinhc (x : ℝ) : ℝ :=
  Function.update
    (fun y : ℝ => (Real.sinh y - Real.sinh 0) / (y - 0)) 0 1 x

@[simp] theorem sinhc_zero : sinhc 0 = 1 := by
  simp [sinhc]

/-- Away from zero, `sinhc` is the usual quotient. -/
theorem sinhc_eq_sinh_div (x : ℝ) (hx : x ≠ 0) :
    sinhc x = Real.sinh x / x := by
  simp [sinhc, hx]

/-- The removable singularity is genuinely continuous. -/
@[fun_prop] theorem continuousAt_sinhc_zero : ContinuousAt sinhc 0 := by
  simpa [sinhc] using (Real.hasDerivAt_sinh 0).continuousAt_div

/-- Central-cell value contribution to the exact odd-mesh P1 energy. -/
def oddGreenCentralEnergyClosed (h : ℝ) : ℝ :=
  h * (Real.sinh (1 - h / 2) / Real.sinh 1) ^ 2

/-- Derivative contribution to the exact odd-mesh P1 energy, written with
removable singularities already filled. -/
def oddGreenDerivativeEnergyClosed (h : ℝ) : ℝ :=
  ((1 - h / 2) * sinhc (h / 2) ^ 2 +
      sinhc (h / 2) * (sinhc (h / 2) / (2 * sinhc h)) *
        Real.sinh (2 - h)) /
    (Real.sinh 1) ^ 2

/-- Noncentral value contribution to the exact odd-mesh P1 energy. -/
def oddGreenValueEnergyClosed (h : ℝ) : ℝ :=
  (2 / (3 * (Real.sinh 1) ^ 2)) *
    ((1 / sinhc h) *
        (Real.sinh 2 + Real.sinh (2 - h) + Real.sinh (2 - 2 * h) -
          2 * Real.sinh h) / 4 -
      (1 - h) - (1 / 2 - h / 4) * Real.cosh h)

/-- Exact closed squared-energy expression for the odd uniform interpolant. -/
def oddGreenInterpolantEnergyClosed (h : ℝ) : ℝ :=
  oddGreenCentralEnergyClosed h +
    oddGreenDerivativeEnergyClosed h +
    oddGreenValueEnergyClosed h

/-- The closed energy expression is continuous at zero. -/
@[fun_prop] theorem continuousAt_oddGreenInterpolantEnergyClosed_zero :
    ContinuousAt oddGreenInterpolantEnergyClosed 0 := by
  unfold oddGreenInterpolantEnergyClosed oddGreenCentralEnergyClosed
    oddGreenDerivativeEnergyClosed oddGreenValueEnergyClosed
  fun_prop

/-- Evaluation of the closed expression at the removable singularity. -/
theorem oddGreenInterpolantEnergyClosed_zero :
    oddGreenInterpolantEnergyClosed 0 =
      Real.sinh 2 / (Real.sinh 1) ^ 2 := by
  simp [oddGreenInterpolantEnergyClosed, oddGreenCentralEnergyClosed,
    oddGreenDerivativeEnergyClosed, oddGreenValueEnergyClosed]
  ring

/-- Hyperbolic simplification of the exact Green energy constant. -/
theorem sinh_two_div_sinh_one_sq :
    Real.sinh 2 / (Real.sinh 1) ^ 2 = 2 / Real.tanh 1 := by
  have hs : Real.sinh (1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr zero_lt_one)
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.sinh_add]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hs]
  ring

/-- Any mesh-width sequence tending to zero has the exact odd-mesh energy
limit. -/
theorem oddGreenInterpolantEnergyClosed_tendsto
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => oddGreenInterpolantEnergyClosed (h n)) atTop
      (𝓝 (2 / Real.tanh 1)) := by
  have ht := continuousAt_oddGreenInterpolantEnergyClosed_zero.tendsto.comp hh
  rw [oddGreenInterpolantEnergyClosed_zero, sinh_two_div_sinh_one_sq] at ht
  exact ht

/-- Closed-form norm of the odd-mesh Green interpolant. -/
def oddGreenInterpolantNormClosed (h : ℝ) : ℝ :=
  Real.sqrt (oddGreenInterpolantEnergyClosed h)

/-- The exact closed interpolant norm converges to the Green trace norm. -/
theorem oddGreenInterpolantNormClosed_tendsto
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => oddGreenInterpolantNormClosed (h n)) atTop
      (𝓝 greenTraceProfileNorm) := by
  have henergy := oddGreenInterpolantEnergyClosed_tendsto h hh
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp henergy
  simpa [oddGreenInterpolantNormClosed, greenTraceProfileNorm] using hsqrt

end

end BernsteinObstacle
