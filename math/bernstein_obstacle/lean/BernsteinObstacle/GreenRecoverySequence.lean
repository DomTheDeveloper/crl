import BernsteinObstacle.GreenProfileAsymptotic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Filter Topology

namespace BernsteinObstacle

noncomputable section

/-!
# Green-profile recovery sequence

This file formalizes the final limit calculus used by the concrete recovery

`r_h = (gamma h^2 / c_h) I_h phi`.

The three physical inputs are deliberately separated:

* `c_h → 1`, the value of the interpolated profile on the central cell;
* `||I_h phi||_{H^1} → ||phi||_{H^1}`;
* the coefficient-to-trace discrepancy tends to zero.

From these inputs, the exact normalized best-error limit follows by a genuine
squeeze argument.
-/

/-- The normalized one-dimensional Green profile. -/
def normalizedGreenProfile (x : ℝ) : ℝ :=
  Real.sinh (1 - |x|) / Real.sinh 1

/-- The normalized Green profile has unit value at the contact point. -/
@[simp] theorem normalizedGreenProfile_zero : normalizedGreenProfile 0 = 1 := by
  have hs : Real.sinh (1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr zero_lt_one)
  simp [normalizedGreenProfile, hs]

/-- The actual central-cell profile value used by the recovery. -/
def greenCentralValue (h : ℝ) : ℝ := normalizedGreenProfile (h / 2)

/-- Any mesh-width sequence tending to zero has Green central value tending to
one.  Thus the central rescaling input is discharged concretely. -/
theorem greenCentralValue_tendsto_one
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => greenCentralValue (h n)) atTop (𝓝 1) := by
  have harg : Tendsto (fun n => h n / 2) atTop (𝓝 0) := by
    simpa using hh.div_const 2
  have hcont : Continuous normalizedGreenProfile := by
    unfold normalizedGreenProfile
    fun_prop
  have ht := hcont.continuousAt.tendsto.comp harg
  simpa [greenCentralValue] using ht

/-- Normalized size of the explicit Green-profile recovery. -/
def greenRecoveryNormalizedError
    (gamma : ℝ) (centerValue profileNorm : ℕ → ℝ) (n : ℕ) : ℝ :=
  (gamma / centerValue n) * profileNorm n

/-- The central rescaling factor tends to `gamma` when the central value tends
to one. -/
theorem greenRecoveryScale_tendsto
    (centerValue : ℕ → ℝ) (gamma : ℝ)
    (hcenter : Tendsto centerValue atTop (𝓝 1)) :
    Tendsto (fun n => gamma / centerValue n) atTop (𝓝 gamma) := by
  have hdiv := tendsto_const_nhds.div hcenter (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hdiv

/-- The rescaling factor for the concrete Green central values tends to
`gamma`. -/
theorem concreteGreenRecoveryScale_tendsto
    (h : ℕ → ℝ) (gamma : ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => gamma / greenCentralValue (h n)) atTop (𝓝 gamma) := by
  exact greenRecoveryScale_tendsto
    (fun n => greenCentralValue (h n)) gamma
    (greenCentralValue_tendsto_one h hh)

/-- Strong convergence of the interpolated Green profile and convergence of its
central value give the predicted recovery constant. -/
theorem greenRecoveryNormalizedError_tendsto
    (centerValue profileNorm : ℕ → ℝ) (gamma : ℝ)
    (hcenter : Tendsto centerValue atTop (𝓝 1))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm)) :
    Tendsto (greenRecoveryNormalizedError gamma centerValue profileNorm)
      atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  have hscale := greenRecoveryScale_tendsto centerValue gamma hcenter
  have hmul := hscale.mul hnorm
  simpa [greenRecoveryNormalizedError, smoothContactGreenConstant] using hmul

/-- Concrete central-value specialization of the recovery limit. -/
theorem concreteGreenRecoveryNormalizedError_tendsto
    (h profileNorm : ℕ → ℝ) (gamma : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm)) :
    Tendsto
      (greenRecoveryNormalizedError gamma
        (fun n => greenCentralValue (h n)) profileNorm)
      atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenRecoveryNormalizedError_tendsto
    (fun n => greenCentralValue (h n)) profileNorm gamma
    (greenCentralValue_tendsto_one h hh) hnorm

/-- Exact Green-profile asymptotic from the physical liminf defect and the
explicit recovery sequence.

The lower sequence is `constant - traceDefect`; the upper sequence is the
actual normalized recovery norm. Both converge to the same Green constant. -/
theorem greenProfile_exact_limit_from_recovery
    (F centerValue profileNorm traceDefect : ℕ → ℝ) (gamma : ℝ)
    (hcenter : Tendsto centerValue atTop (𝓝 1))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm))
    (htrace : Tendsto traceDefect atTop (𝓝 0))
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤ F n)
    (hupper : ∀ᶠ n in atTop,
      F n ≤ greenRecoveryNormalizedError gamma centerValue profileNorm n) :
    Tendsto F atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  have hlowerT :
      Tendsto (fun n => smoothContactGreenConstant gamma - traceDefect n)
        atTop (𝓝 (smoothContactGreenConstant gamma)) := by
    simpa using tendsto_const_nhds.sub htrace
  have hupperT := greenRecoveryNormalizedError_tendsto
    centerValue profileNorm gamma hcenter hnorm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerT hupperT hlower hupper

/-- Exact limit with the concrete Green central value already discharged. -/
theorem greenProfile_exact_limit_concrete_center
    (F h profileNorm traceDefect : ℕ → ℝ) (gamma : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm))
    (htrace : Tendsto traceDefect atTop (𝓝 0))
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤ F n)
    (hupper : ∀ᶠ n in atTop,
      F n ≤ greenRecoveryNormalizedError gamma
        (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto F atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_from_recovery F
    (fun n => greenCentralValue (h n)) profileNorm traceDefect gamma
    (greenCentralValue_tendsto_one h hh) hnorm htrace hlower hupper

/-- Mesh-error specialization of the exact Green recovery theorem. -/
theorem normalizedQuadraticError_greenProfile_tendsto
    (E h centerValue profileNorm traceDefect : ℕ → ℝ) (gamma : ℝ)
    (hcenter : Tendsto centerValue atTop (𝓝 1))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm))
    (htrace : Tendsto traceDefect atTop (𝓝 0))
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤
        normalizedQuadraticError E h n)
    (hupper : ∀ᶠ n in atTop,
      normalizedQuadraticError E h n ≤
        greenRecoveryNormalizedError gamma centerValue profileNorm n) :
    Tendsto (normalizedQuadraticError E h) atTop
      (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_from_recovery
    (normalizedQuadraticError E h) centerValue profileNorm traceDefect gamma
    hcenter hnorm htrace hlower hupper

end

end BernsteinObstacle
