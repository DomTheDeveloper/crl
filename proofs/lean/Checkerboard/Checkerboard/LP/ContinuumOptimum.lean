import Checkerboard.LP.ContinuumPrimalCertificate
import Checkerboard.LP.DualObjectiveIntegral

/-!
# Exact continuum optimum

The explicit primal and dual certificates have the same objective
`checkerboardAlpha`.  Weak duality therefore proves optimality of both.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- Every feasible continuum primal has value at most the checkerboard constant. -/
theorem continuumPrimalValue_le_alpha
    {μ : Measure ContinuumPoint} (hμ : ContinuumPrimalFeasible μ) :
    continuumPrimalValue μ ≤ ENNReal.ofReal checkerboardAlpha := by
  rw [← certifiedDual_value]
  exact continuum_weak_duality hμ certifiedDual_feasible

/-- Every feasible continuum dual has value at least the checkerboard constant. -/
theorem alpha_le_continuumDualValue
    {A B : ℝ → ℝ≥0∞} (hAB : ContinuumDualFeasible A B) :
    ENNReal.ofReal checkerboardAlpha ≤ continuumDualValue A B := by
  rw [← checkerboardContinuumPrimal_value]
  exact continuum_weak_duality checkerboardContinuumPrimal_feasible hAB

/-- The explicit primal certificate is optimal. -/
theorem checkerboardContinuumPrimal_optimal
    {μ : Measure ContinuumPoint} (hμ : ContinuumPrimalFeasible μ) :
    continuumPrimalValue μ ≤
      continuumPrimalValue checkerboardContinuumPrimal := by
  rw [checkerboardContinuumPrimal_value]
  exact continuumPrimalValue_le_alpha hμ

/-- The explicit dual certificate is optimal. -/
theorem certifiedDual_optimal
    {A B : ℝ → ℝ≥0∞} (hAB : ContinuumDualFeasible A B) :
    continuumDualValue certifiedDualA certifiedDualB ≤
      continuumDualValue A B := by
  rw [certifiedDual_value]
  exact alpha_le_continuumDualValue hAB

/-- Exact strong duality at the explicit witnesses. -/
theorem checkerboard_continuum_strong_duality :
    continuumPrimalValue checkerboardContinuumPrimal =
      continuumDualValue certifiedDualA certifiedDualB ∧
    continuumPrimalValue checkerboardContinuumPrimal =
      ENNReal.ofReal checkerboardAlpha := by
  rw [checkerboardContinuumPrimal_value, certifiedDual_value]
  exact ⟨rfl, rfl⟩

end

end Checkerboard
