import BernsteinObstacle.FlatInterfaceBenchmark
import BernsteinObstacle.GenericShiftAveraging
import BernsteinObstacle.DesignedTubularMesh
import BernsteinObstacle.AlignedMeshObstruction
import BernsteinObstacle.PhaseWeightedSaturation
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators Interval

namespace BernsteinObstacle

noncomputable section

/-!
# Terminal mesh-instantiation compositions

These declarations package the certified bridge lemmas into the four mathematical
endpoints used by the paper:

1. an explicit deterministic flat-interface sandwich;
2. a positive-measure generic-shift theorem with retained-element density;
3. uniform phase/Jacobian/remainder constants for a designed tubular mesh;
4. the arbitrary-mesh counterexample together with the phase-weighted replacement.
-/

/-- Complete explicit flat-interface estimate from the prism lower bound and the
standard Falk comparison inequality evaluated on the certified quadratic repair.

The only hypotheses left at this endpoint are the actual global lower-energy
domination by the retained prisms and the usual Falk transfer for the discrete
solution.  Every geometric inclusion and every scalar integral on the right-hand
side has already been proved exactly. -/
theorem flatInterface_discreteError_sharp
    (a W h error : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 ≤ h) (herror : 0 ≤ error)
    (hprismLower : a ^ 2 * W * h ^ 3 / 768 ≤ error ^ 2)
    (hFalk :
      error ^ 2 ≤ W *
        ((∫ y in -h / 2..0, (flatComparisonDerivative a h y) ^ 2) +
          (∫ y in 0..h / 2,
            (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) +
          2 * (∫ y in -h / 2..0, 2 * a * flatComparisonValue a h y))) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ error ∧
      error ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hupperSq : error ^ 2 ≤ a ^ 2 * W * h ^ 3 / 12 := by
    calc
      error ^ 2 ≤ W *
          ((∫ y in -h / 2..0, (flatComparisonDerivative a h y) ^ 2) +
            (∫ y in 0..h / 2,
              (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) +
            2 * (∫ y in -h / 2..0, 2 * a * flatComparisonValue a h y)) := hFalk
      _ = W * (a ^ 2 * h ^ 3 / 12) := by
        rw [flatComparison_falk_total_per_unitWidth]
      _ = a ^ 2 * W * h ^ 3 / 12 := by ring
  exact flatBenchmark_sharp_sandwich
    a W h error ha hW hh herror hprismLower hupperSq

/-- Generic-shift endpoint.  A positive fraction `p/(2-p)` of translations
retain at least half the expected core length, and every such translation has
the codimension-one retained-element count required by the saturation theorem. -/
theorem genericShift_goodMeasure_and_retainedCount
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X retained : Ω → ℝ) (p L D h : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (hD : 0 < D) (hh : 0 < h)
    (hXmeas : Measurable X)
    (hXint : Integrable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω)
    (hXL : ∀ ω, X ω ≤ L)
    (hmean : (∫ ω, X ω ∂μ) = p * L)
    (hpacking : ∀ ω ∈ goodTranslationSet X p L,
      p * L / 2 ≤ 2 * D * h * retained ω) :
    p / (2 - p) ≤ μ.real (goodTranslationSet X p L) ∧
      ∀ ω ∈ goodTranslationSet X p L,
        p * L / (4 * D * h) ≤ retained ω := by
  constructor
  · exact goodTranslationSet_measure_lowerBound
      μ X p L hp0 hp1 hL hXmeas hXint hX0 hXL hmean
  · intro ω hω
    exact retainedCount_of_goodTranslation
      p L D h (retained ω) hp0 hL hD hh (hpacking ω hω)

/-- Positive-measure sharp-family form of the generic-shift theorem. -/
theorem genericShift_positiveMeasure_sharpFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X error : Ω → ℝ) (p L c h : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (hXmeas : Measurable X)
    (hXint : Integrable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω)
    (hXL : ∀ ω, X ω ≤ L)
    (hmean : (∫ ω, X ω ∂μ) = p * L)
    (hsharp : ∀ ω ∈ goodTranslationSet X p L,
      c * (h * Real.sqrt h) ≤ error ω) :
    p / (2 - p) ≤ μ.real (goodTranslationSet X p L) ∧
      ∀ ω ∈ goodTranslationSet X p L,
        c * (h * Real.sqrt h) ≤ error ω := by
  exact ⟨goodTranslationSet_measure_lowerBound
    μ X p L hp0 hp1 hL hXmeas hXint hX0 hXL hmean, hsharp⟩

/-- Designed curved-mesh endpoint.  One common small-mesh condition yields the
uniform phase interval, positive tubular Jacobian, and higher-order element
remainder estimate used by the certified physical saturation theorem. -/
theorem designedTubularMesh_uniformPackage
    (K c h delta k t energy C V : ℝ) (kappa : ℕ)
    (hK : 0 ≤ K) (hc : 0 < c) (hh : 0 < h)
    (hk : |k| ≤ K) (ht : |t| ≤ c * h)
    (hsmall : K * c * h ≤ 1 / 2)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2)
    (henergy : energy ≤ (C * h ^ (1 + kappa)) ^ 2 * (V * h ^ 2)) :
    ((1 / 4 : ℝ) ≤ (delta + c * h) / (2 * c * h) ∧
      (delta + c * h) / (2 * c * h) ≤ 3 / 4) ∧
    ((1 / 2 : ℝ) ≤ 1 - t * k ∧ 1 - t * k ≤ 3 / 2) ∧
    energy ≤ C ^ 2 * V * h ^ (4 + 2 * kappa) := by
  have hsmallOne : K * c * h ≤ 1 := hsmall.trans (by norm_num)
  exact ⟨
    curvedFiber_phase_bounds K c h delta hK hc hh hsmallOne hdelta,
    curvedFiber_jacobian_bounds K c h k t hK hc.le hh.le hk ht hsmall,
    curvedElement_remainderEnergy_bound energy C V h kappa henergy
  ⟩

/-- Final arbitrary-mesh dichotomy.  Exact representability refutes a universal
positive constant, while a positive codimension-one density of local phase
weights restores the sharp `h^(3/2)` lower bound. -/
theorem arbitraryMesh_obstruction_and_phaseWeighted_replacement
    {E ι : Type*} [NormedAddCommGroup E]
    (V : Set E) (u : E) (hu : u ∈ V)
    (S : Finset ι) (energy weight : ι → ℝ)
    (error c C N h : ℝ) (d : ℕ)
    (hc : 0 < c) (herror : 0 ≤ error)
    (hd : 1 ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (henergy : ∀ i ∈ S,
      C * weight i * h ^ (d + 2) ≤ energy i)
    (hweight : N / h ^ (d - 1) ≤ ∑ i ∈ S, weight i) :
    (¬ (∀ v ∈ V, c * (h * Real.sqrt h) ≤ ‖u - v‖)) ∧
      Real.sqrt (C * N) * (h * Real.sqrt h) ≤ error := by
  constructor
  · exact exactRepresentability_refutes_positiveLowerBound
      V u hu c h hc hh
  · exact phaseWeighted_error_ge_threeHalves_of_sum_le_sq
      S energy weight error C N h d herror hd hh hC hN
      hsumSq henergy hweight

end

end BernsteinObstacle
