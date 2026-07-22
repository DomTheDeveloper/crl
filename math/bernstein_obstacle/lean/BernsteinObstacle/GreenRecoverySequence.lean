import BernsteinObstacle.GreenProfileAsymptotic
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
