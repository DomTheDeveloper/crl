import Checkerboard.LP.ContinuumModel
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Pushforward formulation of continuum primal feasibility

Concrete certificates are most naturally verified by computing their four
one-dimensional pushforwards.  This file proves once and for all that domination
of the two paired pushforward measures implies the test-function formulation in
`ContinuumPrimalFeasible`.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- Paired row/column pushforward. -/
def pairedAMeasure (μ : Measure ContinuumPoint) : Measure ℝ :=
  Measure.map coordX μ + Measure.map coordOneSubY μ

/-- Paired sum/difference pushforward. -/
def pairedBMeasure (μ : Measure ContinuumPoint) : Measure ℝ :=
  Measure.map coordSum μ + Measure.map coordDiff μ

lemma lintegral_pairedAMeasure
    {μ : Measure ContinuumPoint} {A : ℝ → ℝ≥0∞} (hA : Measurable A) :
    (∫⁻ t, A t ∂pairedAMeasure μ) =
      (∫⁻ z, A (coordX z) ∂μ) +
        (∫⁻ z, A (coordOneSubY z) ∂μ) := by
  rw [pairedAMeasure, lintegral_add_measure,
    lintegral_map hA measurable_coordX,
    lintegral_map hA measurable_coordOneSubY]

lemma lintegral_pairedBMeasure
    {μ : Measure ContinuumPoint} {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    (∫⁻ t, B t ∂pairedBMeasure μ) =
      (∫⁻ z, B (coordSum z) ∂μ) +
        (∫⁻ z, B (coordDiff z) ∂μ) := by
  rw [pairedBMeasure, lintegral_add_measure,
    lintegral_map hB measurable_coordSum,
    lintegral_map hB measurable_coordDiff]

/-- The obstacle integral is exactly the sum of the two paired pushforward
integrals. -/
theorem lintegral_pairedObstacle_eq
    {μ : Measure ContinuumPoint} {A B : ℝ → ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B) :
    (∫⁻ z, pairedObstacle A B z ∂μ) =
      (∫⁻ t, A t ∂pairedAMeasure μ) +
        (∫⁻ t, B t ∂pairedBMeasure μ) := by
  rw [lintegral_pairedAMeasure hA, lintegral_pairedBMeasure hB]
  unfold pairedObstacle
  rw [lintegral_add_left (hA.comp measurable_coordX)]
  rw [lintegral_add_left ((hA.comp measurable_coordX).add
    (hA.comp measurable_coordOneSubY))]
  rw [lintegral_add_left (((hA.comp measurable_coordX).add
    (hA.comp measurable_coordOneSubY)).add (hB.comp measurable_coordSum))]
  ring

/-- Measure domination of the two paired pushforwards is sufficient for
continuum primal feasibility. -/
theorem continuumPrimalFeasible_of_paired_le
    {μ : Measure ContinuumPoint}
    (hsupport : ∀ᵐ z ∂μ, z ∈ continuumTriangle)
    (hAmeasure : pairedAMeasure μ ≤ 4 • unitIntervalVolume)
    (hBmeasure : pairedBMeasure μ ≤ 4 • unitIntervalVolume) :
    ContinuumPrimalFeasible μ := by
  refine ⟨hsupport, ?_⟩
  intro A B hA hB
  rw [lintegral_pairedObstacle_eq hA hB]
  calc
    (∫⁻ t, A t ∂pairedAMeasure μ) +
        (∫⁻ t, B t ∂pairedBMeasure μ) ≤
      (∫⁻ t, A t ∂(4 • unitIntervalVolume)) +
        (∫⁻ t, B t ∂(4 • unitIntervalVolume)) := by
          exact add_le_add
            (lintegral_mono' hAmeasure le_rfl)
            (lintegral_mono' hBmeasure le_rfl)
    _ = 4 * ((∫⁻ t, A t ∂unitIntervalVolume) +
        (∫⁻ t, B t ∂unitIntervalVolume)) := by
      simp [mul_add]

/-- Exact equality with the capacity measure is a convenient specialization. -/
theorem continuumPrimalFeasible_of_paired_eq
    {μ : Measure ContinuumPoint}
    (hsupport : ∀ᵐ z ∂μ, z ∈ continuumTriangle)
    (hAmeasure : pairedAMeasure μ = 4 • unitIntervalVolume)
    (hBmeasure : pairedBMeasure μ ≤ 4 • unitIntervalVolume) :
    ContinuumPrimalFeasible μ :=
  continuumPrimalFeasible_of_paired_le hsupport hAmeasure.le hBmeasure

end

end Checkerboard
