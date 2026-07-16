import Checkerboard.LP.AffineIntervalMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite interval-density assembly

Generated certificate arithmetic proves that constant densities sum to the
required value on every atomic cell.  This file supplies the generic measure
lemmas that turn those pointwise identities into equalities of finite sums of
restricted Lebesgue measures.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set

/-- A constant `ℝ≥0∞` density on a closed interval.  Endpoint overlaps are
irrelevant for Lebesgue measure and are handled later by almost-everywhere
congruence. -/
def intervalDensity (a b c : ℝ) (x : ℝ) : ℝ≥0∞ :=
  (Set.Icc a b).indicator (fun _ => ENNReal.ofReal c) x

lemma measurable_intervalDensity (a b c : ℝ) :
    Measurable (intervalDensity a b c) := by
  unfold intervalDensity
  exact measurable_const.indicator measurableSet_Icc

/-- A constant multiple of restricted Lebesgue measure is the corresponding
interval-density measure. -/
theorem volume_withDensity_intervalDensity (a b c : ℝ) :
    volume.withDensity (intervalDensity a b c) =
      ENNReal.ofReal c • volume.restrict (Set.Icc a b) := by
  unfold intervalDensity
  rw [withDensity_indicator measurableSet_Icc]
  simp

/-- `withDensity` distributes over a finite sum of measurable densities. -/
theorem withDensity_finset_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    volume.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, volume.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : Measurable (f a) := hf a (by simp)
      have hfs : ∀ i ∈ s, Measurable (f i) := by
        intro i hi
        exact hf i (by simp [hi])
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change volume.withDensity (f a + fun x => ∑ i ∈ s, f i x) = _
      rw [withDensity_add_left hfa]
      rw [ih hfs]

/-- Pushforward distributes over a finite sum of measures. -/
theorem map_finset_sum
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DecidableEq ι]
    (s : Finset ι) (μ : ι → Measure α) (f : α → β)
    (hf : Measurable f) :
    Measure.map f (∑ i ∈ s, μ i) = ∑ i ∈ s, Measure.map f (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Measure.map_add _ _ hf, ih]

/-- The full finite-type version of `map_finset_sum`. -/
theorem map_fintype_sum
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι]
    (μ : ι → Measure α) (f : α → β) (hf : Measurable f) :
    Measure.map f (∑ i, μ i) = ∑ i, Measure.map f (μ i) := by
  simpa using map_finset_sum Finset.univ μ f hf

/-- Finite sums of weighted restricted intervals are represented by the sum of
their interval densities. -/
theorem sum_smul_restrict_eq_withDensity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b c : ι → ℝ) :
    (∑ i ∈ s, ENNReal.ofReal (c i) • volume.restrict (Set.Icc (a i) (b i))) =
      volume.withDensity (fun x => ∑ i ∈ s, intervalDensity (a i) (b i) (c i) x) := by
  classical
  rw [withDensity_finset_sum s (fun i => intervalDensity (a i) (b i) (c i))
    (fun i _ => measurable_intervalDensity _ _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (volume_withDensity_intervalDensity (a i) (b i) (c i)).symm

/-- Multiplying an affine component by a nonnegative weight produces exactly
its weight-over-length interval density. -/
theorem weighted_map_centered_interval_affine
    {w m s : ℝ} (hw : 0 ≤ w) (hs : 0 < s) :
    ENNReal.ofReal w •
        Measure.map (fun t : ℝ => m + s * t) centeredUnitIntervalMeasure =
      volume.withDensity (intervalDensity (m - s / 2) (m + s / 2) (w / s)) := by
  rw [map_centered_interval_affine m hs]
  rw [smul_smul]
  rw [volume_withDensity_intervalDensity]
  congr 1
  rw [← ENNReal.ofReal_mul hw]
  congr 1
  field_simp

/-- The reversed affine orientation has the same interval pushforward. -/
theorem weighted_map_centered_interval_affine_neg
    {w m s : ℝ} (hw : 0 ≤ w) (hs : 0 < s) :
    ENNReal.ofReal w •
        Measure.map (fun t : ℝ => m - s * t) centeredUnitIntervalMeasure =
      volume.withDensity (intervalDensity (m - s / 2) (m + s / 2) (w / s)) := by
  rw [map_centered_interval_affine_neg m hs]
  rw [smul_smul]
  rw [volume_withDensity_intervalDensity]
  congr 1
  rw [← ENNReal.ofReal_mul hw]
  congr 1
  field_simp

/-- Almost-everywhere equality of finite density sums gives equality of the
corresponding measures. -/
theorem withDensity_eq_of_ae_density_eq
    {f g : ℝ → ℝ≥0∞} (h : f =ᵐ[volume] g) :
    volume.withDensity f = volume.withDensity g :=
  withDensity_congr_ae h

end

end Checkerboard
