import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

/-!
# Generic-shift averaging
-/

def goodTranslationSet {Ω : Type*} (X : Ω → ℝ) (p L : ℝ) : Set Ω :=
  {ω | p * L / 2 ≤ X ω}

theorem goodTranslationSet_measure_lowerBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (p L : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (hXmeas : Measurable X)
    (hXint : Integrable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω)
    (hXL : ∀ ω, X ω ≤ L)
    (hmean : (∫ ω, X ω ∂μ) = p * L) :
    p / (2 - p) ≤ μ.real (goodTranslationSet X p L) := by
  let G : Set Ω := goodTranslationSet X p L
  have hG : MeasurableSet G := by
    dsimp [G, goodTranslationSet]
    exact measurableSet_le measurable_const hXmeas
  have hgoodNonneg : 0 ≤ ∫ ω in G, X ω ∂μ :=
    setIntegral_nonneg hG fun ω _ => hX0 ω
  have hbadNonneg : 0 ≤ ∫ ω in Gᶜ, X ω ∂μ :=
    setIntegral_nonneg hG.compl fun ω _ => hX0 ω
  have hgoodNorm :
      ‖∫ ω in G, X ω ∂μ‖ ≤ L * μ.real G := by
    apply norm_setIntegral_le_of_norm_le_const
    · finiteness
    · intro ω _hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      exact hXL ω
  have hbadNorm :
      ‖∫ ω in Gᶜ, X ω ∂μ‖ ≤ (p * L / 2) * μ.real Gᶜ := by
    apply norm_setIntegral_le_of_norm_le_const
    · finiteness
    · intro ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      have hnot : ¬ p * L / 2 ≤ X ω := by
        simpa [G, goodTranslationSet] using hω
      exact le_of_lt (lt_of_not_ge hnot)
  have hgoodLe :
      (∫ ω in G, X ω ∂μ) ≤ L * μ.real G := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hgoodNonneg] using hgoodNorm
  have hbadLe :
      (∫ ω in Gᶜ, X ω ∂μ) ≤ (p * L / 2) * μ.real Gᶜ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hbadNonneg] using hbadNorm
  have hsplit :
      (∫ ω in G, X ω ∂μ) + (∫ ω in Gᶜ, X ω ∂μ) = p * L := by
    rw [integral_add_compl hG hXint, hmean]
  have hcompl : μ.real Gᶜ = 1 - μ.real G :=
    probReal_compl_eq_one_sub hG
  by_cases hLpos : 0 < L
  · have htotal :
        p * L ≤ L * μ.real G + (p * L / 2) * (1 - μ.real G) := by
      rw [← hcompl]
      nlinarith
    have hcore : p ≤ μ.real G * (2 - p) := by
      nlinarith
    have hden : 0 < 2 - p := by linarith
    exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hcore)
  · have hLzero : L = 0 := by linarith
    have hGuniv : G = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      change p * L / 2 ≤ X ω
      simpa [hLzero] using hX0 ω
    change p / (2 - p) ≤ μ.real G
    rw [hGuniv, probReal_univ]
    have hden : 0 < 2 - p := by linarith
    exact (div_le_iff₀ hden).2 (by nlinarith)

def diagonalTriangleInradius : ℝ :=
  1 - 1 / Real.sqrt 2

def diagonalCoreFraction (r : ℝ) : ℝ :=
  ((diagonalTriangleInradius - r) / diagonalTriangleInradius) ^ 2

theorem diagonalTriangleInradius_pos : 0 < diagonalTriangleInradius := by
  have hsqrt2 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : 0 ≤ (1 : ℝ))]
    norm_num
  have hsqrt2pos : 0 < Real.sqrt 2 := by positivity
  dsimp [diagonalTriangleInradius]
  rw [sub_pos, div_lt_one hsqrt2pos]
  exact hsqrt2

theorem diagonalCoreFraction_pos
    (r : ℝ) (_hr0 : 0 ≤ r) (hrR : r < diagonalTriangleInradius) :
    0 < diagonalCoreFraction r := by
  have hR := diagonalTriangleInradius_pos
  dsimp [diagonalCoreFraction]
  positivity

theorem goodTranslationFraction_pos
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 < p / (2 - p) := by
  have hden : 0 < 2 - p := by linarith
  positivity

theorem retainedCount_of_arclength_cover
    (goodLength D h m : ℝ)
    (hD : 0 < D) (hh : 0 < h)
    (hcover : goodLength ≤ 2 * D * h * m) :
    goodLength / (2 * D * h) ≤ m := by
  have hden : 0 < 2 * D * h := by positivity
  exact (div_le_iff₀ hden).2 (by nlinarith)

theorem retainedCount_of_goodTranslation
    (p L D h m : ℝ)
    (_hp : 0 ≤ p) (_hL : 0 ≤ L)
    (hD : 0 < D) (hh : 0 < h)
    (hgood : p * L / 2 ≤ 2 * D * h * m) :
    p * L / (4 * D * h) ≤ m := by
  have hden : 0 < 4 * D * h := by positivity
  exact (div_le_iff₀ hden).2 (by nlinarith)

end

end BernsteinObstacle
