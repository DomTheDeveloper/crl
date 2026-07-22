import BernsteinObstacle.GreenTraceDefect
import Mathlib.Tactic

open Filter Topology

namespace BernsteinObstacle

noncomputable section

/-!
# Quantitative Green interpolation-norm convergence

The Green representer has a derivative jump at the contact point.  On a
phase-locked mesh, a direct `H¹` interpolation-error estimate is therefore
naturally of order `sqrt h`; on fitted or specially aligned meshes a stronger
first-order norm estimate may be available.  Both rates tend to zero and are
sufficient for the exact Green-profile squeeze theorem.
-/

/-- Linear mesh-width majorant for a stronger Green interpolant norm estimate. -/
def greenInterpolationNormMajorant
    (C : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * |h n|

/-- Phase-robust square-root majorant for the Green interpolant norm error. -/
def greenInterpolationSqrtMajorant
    (C : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * Real.sqrt |h n|

/-- Absolute mesh width tends to zero with the mesh width. -/
theorem abs_meshWidth_tendsto_zero
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => |h n|) atTop (𝓝 0) := by
  have ht := continuous_abs.continuousAt.tendsto.comp hh
  simpa using ht

/-- The first-order interpolation majorant tends to zero. -/
theorem greenInterpolationNormMajorant_tendsto_zero
    (C : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (greenInterpolationNormMajorant C h) atTop (𝓝 0) := by
  have habs := abs_meshWidth_tendsto_zero h hh
  have hmul := tendsto_const_nhds.mul habs
  simpa [greenInterpolationNormMajorant] using hmul

/-- The phase-robust square-root interpolation majorant tends to zero. -/
theorem greenInterpolationSqrtMajorant_tendsto_zero
    (C : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (greenInterpolationSqrtMajorant C h) atTop (𝓝 0) := by
  have habs := abs_meshWidth_tendsto_zero h hh
  have hsqrt : Tendsto (fun n => Real.sqrt |h n|) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp habs
    simpa using ht
  have hmul := tendsto_const_nhds.mul hsqrt
  simpa [greenInterpolationSqrtMajorant] using hmul

/-- A quantitative `O(h)` interpolation-norm estimate implies convergence to
the exact Green-profile norm. -/
theorem greenProfileNorm_tendsto_of_linear_bound
    (profileNorm h : ℕ → ℝ) (C : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hbound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationNormMajorant C h n) :
    Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    simpa [Real.norm_eq_abs] using hbound n
  · exact greenInterpolationNormMajorant_tendsto_zero C h hh

/-- The sharp phase-robust `O(sqrt h)` interpolation estimate also implies
convergence to the exact Green-profile norm. -/
theorem greenProfileNorm_tendsto_of_sqrt_bound
    (profileNorm h : ℕ → ℝ) (C : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hbound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationSqrtMajorant C h n) :
    Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    simpa [Real.norm_eq_abs] using hbound n
  · exact greenInterpolationSqrtMajorant_tendsto_zero C h hh

/-- Exact Green-profile asymptotic from the stronger linear interpolation
estimate and the square-root coefficient-to-trace estimate. -/
theorem greenProfile_exact_limit_of_quantitative_bounds
    (F h profileNorm traceDefect : ℕ → ℝ) (gamma Cinterp Ctrace : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnormBound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationNormMajorant Cinterp h n)
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n,
      traceDefect n ≤ greenTraceDefectMajorant Ctrace h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤ F n)
    (hupper : ∀ᶠ n in atTop,
      F n ≤ greenRecoveryNormalizedError gamma
        (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto F atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_of_sqrt_trace_bound
    F h profileNorm traceDefect gamma Ctrace hh
    (greenProfileNorm_tendsto_of_linear_bound profileNorm h Cinterp hh hnormBound)
    hdefect0 hdefect hlower hupper

/-- Exact Green-profile asymptotic from the phase-robust square-root
interpolation estimate and square-root coefficient-to-trace estimate. -/
theorem greenProfile_exact_limit_of_sqrt_quantitative_bounds
    (F h profileNorm traceDefect : ℕ → ℝ) (gamma Cinterp Ctrace : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnormBound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationSqrtMajorant Cinterp h n)
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n,
      traceDefect n ≤ greenTraceDefectMajorant Ctrace h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤ F n)
    (hupper : ∀ᶠ n in atTop,
      F n ≤ greenRecoveryNormalizedError gamma
        (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto F atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_of_sqrt_trace_bound
    F h profileNorm traceDefect gamma Ctrace hh
    (greenProfileNorm_tendsto_of_sqrt_bound profileNorm h Cinterp hh hnormBound)
    hdefect0 hdefect hlower hupper

/-- Mesh-error specialization using the stronger linear profile-norm bound. -/
theorem normalizedQuadraticError_greenProfile_tendsto_of_quantitative_bounds
    (E h profileNorm traceDefect : ℕ → ℝ) (gamma Cinterp Ctrace : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnormBound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationNormMajorant Cinterp h n)
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n,
      traceDefect n ≤ greenTraceDefectMajorant Ctrace h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤
        normalizedQuadraticError E h n)
    (hupper : ∀ᶠ n in atTop,
      normalizedQuadraticError E h n ≤
        greenRecoveryNormalizedError gamma
          (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto (normalizedQuadraticError E h) atTop
      (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_of_quantitative_bounds
    (normalizedQuadraticError E h) h profileNorm traceDefect
    gamma Cinterp Ctrace hh hnormBound hdefect0 hdefect hlower hupper

/-- Mesh-error specialization using the phase-robust square-root profile-norm
bound. -/
theorem normalizedQuadraticError_greenProfile_tendsto_of_sqrt_quantitative_bounds
    (E h profileNorm traceDefect : ℕ → ℝ) (gamma Cinterp Ctrace : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnormBound : ∀ n,
      |profileNorm n - greenTraceProfileNorm| ≤
        greenInterpolationSqrtMajorant Cinterp h n)
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n,
      traceDefect n ≤ greenTraceDefectMajorant Ctrace h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤
        normalizedQuadraticError E h n)
    (hupper : ∀ᶠ n in atTop,
      normalizedQuadraticError E h n ≤
        greenRecoveryNormalizedError gamma
          (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto (normalizedQuadraticError E h) atTop
      (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_of_sqrt_quantitative_bounds
    (normalizedQuadraticError E h) h profileNorm traceDefect
    gamma Cinterp Ctrace hh hnormBound hdefect0 hdefect hlower hupper

end

end BernsteinObstacle
