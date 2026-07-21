import BernsteinObstacle.GenericShiftLimsup
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# A fixed translation with sharp subsequence lower bounds

The limsup theorem supplies one translation that is good at arbitrarily large
mesh levels. The good-length estimate then gives a retained-element count, and
any certified count-to-error theorem supplies the sharp `h^(3/2)` obstruction
on the same subsequence.
-/

/-- One fixed translation has both the retained-count estimate and the sharp
error lower bound at arbitrarily fine levels. -/
theorem exists_fixedTranslation_sharp_subsequence
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (meshSize retainedCount error : ℕ → Ω → ℝ)
    (p L D C N : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hL : 0 ≤ L) (hD : 0 < D)
    (hXmeas : ∀ n, Measurable (X n))
    (hXint : ∀ n, MeasureTheory.Integrable (X n) μ)
    (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hXL : ∀ n ω, X n ω ≤ L)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = p * L)
    (hh : ∀ n ω, 0 < meshSize n ω)
    (hcoverage : ∀ n ω,
      X n ω ≤ 2 * D * meshSize n ω * retainedCount n ω)
    (hsharp : ∀ n ω,
      p * L / (4 * D * meshSize n ω) ≤ retainedCount n ω →
      Real.sqrt (C * N) *
          (meshSize n ω * Real.sqrt (meshSize n ω)) ≤ error n ω) :
    ∃ ω, ∀ n₀, ∃ n, n₀ ≤ n ∧
      p * L / (4 * D * meshSize n ω) ≤ retainedCount n ω ∧
      Real.sqrt (C * N) *
          (meshSize n ω * Real.sqrt (meshSize n ω)) ≤ error n ω := by
  rcases exists_translation_good_infinitelyOften
    μ X p L hp0 hp1 hL hXmeas hXint hX0 hXL hmean with
    ⟨ω, hω⟩
  refine ⟨ω, ?_⟩
  intro n₀
  rcases hω n₀ with ⟨n, hn, hgood⟩
  have hcount :
      p * L / (4 * D * meshSize n ω) ≤ retainedCount n ω := by
    exact retainedCount_of_goodTranslation
      p L D (meshSize n ω) (retainedCount n ω)
      hp0.le hL hD (hh n ω) (hgood.trans (hcoverage n ω))
  exact ⟨n, hn, hcount, hsharp n ω hcount⟩

end

end BernsteinObstacle
