import BernsteinObstacle.GreenRecoverySequence
import Mathlib.Tactic

open Filter Topology

namespace BernsteinObstacle

noncomputable section

/-!
# Vanishing coefficient-to-trace defect

On the phase-locked central cell, the normalized Bernstein coefficient differs
from midpoint evaluation by `O(sqrt h)` once the normalized error is bounded in
`H¹`.  This file formalizes the exact limit consequence of that physical bound.
-/

/-- The square-root mesh majorant for the normalized trace defect. -/
def greenTraceDefectMajorant (C : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * Real.sqrt |h n|

/-- Square root of the absolute mesh width tends to zero whenever the mesh width
tends to zero. -/
theorem sqrt_abs_meshWidth_tendsto_zero
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt |h n|) atTop (𝓝 0) := by
  have habs : Tendsto (fun n => |h n|) atTop (𝓝 0) := by
    have ht := continuous_abs.continuousAt.tendsto.comp hh
    simpa using ht
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp habs
  simpa using hsqrt

/-- The explicit `C sqrt(|h|)` majorant tends to zero. -/
theorem greenTraceDefectMajorant_tendsto_zero
    (C : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (greenTraceDefectMajorant C h) atTop (𝓝 0) := by
  have hsqrt := sqrt_abs_meshWidth_tendsto_zero h hh
  have hmul := tendsto_const_nhds.mul hsqrt
  simpa [greenTraceDefectMajorant] using hmul

/-- A nonnegative trace defect bounded by `C sqrt(|h|)` vanishes. -/
theorem greenTraceDefect_tendsto_zero_of_sqrt_bound
    (traceDefect h : ℕ → ℝ) (C : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n, traceDefect n ≤ greenTraceDefectMajorant C h n) :
    Tendsto traceDefect atTop (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall hdefect0)
    (Eventually.of_forall hdefect)
    (greenTraceDefectMajorant_tendsto_zero C h hh)

/-- Exact Green-profile limit with both the central normalization and the
coefficient-to-trace remainder discharged from concrete mesh-width data. -/
theorem greenProfile_exact_limit_of_sqrt_trace_bound
    (F h profileNorm traceDefect : ℕ → ℝ) (gamma C : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm))
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n, traceDefect n ≤ greenTraceDefectMajorant C h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤ F n)
    (hupper : ∀ᶠ n in atTop,
      F n ≤ greenRecoveryNormalizedError gamma
        (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto F atTop (𝓝 (smoothContactGreenConstant gamma)) := by
  apply greenProfile_exact_limit_concrete_center
    F h profileNorm traceDefect gamma hh hnorm
  · exact greenTraceDefect_tendsto_zero_of_sqrt_bound
      traceDefect h C hh hdefect0 hdefect
  · exact hlower
  · exact hupper

/-- Mesh-error specialization with the physical square-root trace estimate. -/
theorem normalizedQuadraticError_greenProfile_tendsto_of_sqrt_trace_bound
    (E h profileNorm traceDefect : ℕ → ℝ) (gamma C : ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (hnorm : Tendsto profileNorm atTop (𝓝 greenTraceProfileNorm))
    (hdefect0 : ∀ n, 0 ≤ traceDefect n)
    (hdefect : ∀ n, traceDefect n ≤ greenTraceDefectMajorant C h n)
    (hlower : ∀ᶠ n in atTop,
      smoothContactGreenConstant gamma - traceDefect n ≤
        normalizedQuadraticError E h n)
    (hupper : ∀ᶠ n in atTop,
      normalizedQuadraticError E h n ≤
        greenRecoveryNormalizedError gamma
          (fun n => greenCentralValue (h n)) profileNorm n) :
    Tendsto (normalizedQuadraticError E h) atTop
      (𝓝 (smoothContactGreenConstant gamma)) := by
  exact greenProfile_exact_limit_of_sqrt_trace_bound
    (normalizedQuadraticError E h) h profileNorm traceDefect gamma C
    hh hnorm hdefect0 hdefect hlower hupper

end

end BernsteinObstacle
