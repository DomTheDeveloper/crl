import Checkerboard.LP.IntervalDensityMeasure
import Mathlib.MeasureTheory.Group.Measure

/-!
# Affine transport of constant interval densities

This is the reusable measure-theoretic scaling lemma needed to turn normalized
certificate projections into physical checkerboard projections.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set

/-- Positive affine maps send restricted Lebesgue measure to the corresponding
restricted interval with reciprocal-slope density. -/
theorem map_volume_restrict_Icc_affine
    (a lo hi : ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x : ℝ => a + s * x)
        (volume.restrict (Set.Icc lo hi)) =
      ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (a + s * lo) (a + s * hi)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hpre :
      (fun x : ℝ => a + s * x) ⁻¹'
          Set.Icc (a + s * lo) (a + s * hi) = Set.Icc lo hi := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> nlinarith
  have hrestrict := Measure.restrict_map
    (μ := volume) (f := fun x : ℝ => a + s * x)
    (by fun_prop) measurableSet_Icc
  rw [hpre] at hrestrict
  have hmap :
      Measure.map (fun x : ℝ => a + s * x) volume =
        ENNReal.ofReal s⁻¹ • volume := by
    calc
      Measure.map (fun x : ℝ => a + s * x) volume =
          Measure.map (fun y : ℝ => a + y)
            (Measure.map (fun x : ℝ => s * x) volume) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
      _ = Measure.map (fun y : ℝ => a + y)
          (ENNReal.ofReal |s⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hs0]
      _ = ENNReal.ofReal |s⁻¹| •
          Measure.map (fun y : ℝ => a + y) volume := by
        rw [Measure.map_smul]
      _ = ENNReal.ofReal |s⁻¹| • volume := by
        rw [MeasureTheory.map_add_left_eq_self]
      _ = ENNReal.ofReal s⁻¹ • volume := by
        rw [abs_of_nonneg (inv_nonneg.mpr hs.le)]
  calc
    Measure.map (fun x : ℝ => a + s * x)
        (volume.restrict (Set.Icc lo hi)) =
      (Measure.map (fun x : ℝ => a + s * x) volume).restrict
        (Set.Icc (a + s * lo) (a + s * hi)) := hrestrict.symm
    _ = (ENNReal.ofReal s⁻¹ • volume).restrict
        (Set.Icc (a + s * lo) (a + s * hi)) := by rw [hmap]
    _ = ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (a + s * lo) (a + s * hi)) := by
      rw [Measure.restrict_smul]

/-- Reversed affine maps give the reversed endpoint interval. -/
theorem map_volume_restrict_Icc_affine_neg
    (a lo hi : ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x : ℝ => a - s * x)
        (volume.restrict (Set.Icc lo hi)) =
      ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (a - s * hi) (a - s * lo)) := by
  have hs0 : (-s : ℝ) ≠ 0 := by positivity
  have hpre :
      (fun x : ℝ => a - s * x) ⁻¹'
          Set.Icc (a - s * hi) (a - s * lo) = Set.Icc lo hi := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> nlinarith
  have hrestrict := Measure.restrict_map
    (μ := volume) (f := fun x : ℝ => a - s * x)
    (by fun_prop) measurableSet_Icc
  rw [hpre] at hrestrict
  have hmap :
      Measure.map (fun x : ℝ => a - s * x) volume =
        ENNReal.ofReal s⁻¹ • volume := by
    calc
      Measure.map (fun x : ℝ => a - s * x) volume =
          Measure.map (fun y : ℝ => a + y)
            (Measure.map (fun x : ℝ => (-s) * x) volume) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext x
        ring
      _ = Measure.map (fun y : ℝ => a + y)
          (ENNReal.ofReal |(-s)⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hs0]
      _ = ENNReal.ofReal |(-s)⁻¹| •
          Measure.map (fun y : ℝ => a + y) volume := by
        rw [Measure.map_smul]
      _ = ENNReal.ofReal |(-s)⁻¹| • volume := by
        rw [MeasureTheory.map_add_left_eq_self]
      _ = ENNReal.ofReal s⁻¹ • volume := by
        have : |(-s)⁻¹| = s⁻¹ := by
          rw [abs_inv, abs_neg, abs_of_pos hs]
        rw [this]
  calc
    Measure.map (fun x : ℝ => a - s * x)
        (volume.restrict (Set.Icc lo hi)) =
      (Measure.map (fun x : ℝ => a - s * x) volume).restrict
        (Set.Icc (a - s * hi) (a - s * lo)) := hrestrict.symm
    _ = (ENNReal.ofReal s⁻¹ • volume).restrict
        (Set.Icc (a - s * hi) (a - s * lo)) := by rw [hmap]
    _ = ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (a - s * hi) (a - s * lo)) := by
      rw [Measure.restrict_smul]

/-- Positive affine transport of a constant interval density. -/
theorem map_intervalDensity_affine
    (a lo hi c : ℝ) {s : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    Measure.map (fun x : ℝ => a + s * x)
        (volume.withDensity (intervalDensity lo hi c)) =
      volume.withDensity
        (intervalDensity (a + s * lo) (a + s * hi) (c / s)) := by
  rw [volume_withDensity_intervalDensity]
  rw [Measure.map_smul]
  rw [map_volume_restrict_Icc_affine a lo hi hs]
  rw [volume_withDensity_intervalDensity]
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hmul :
      ENNReal.ofReal c * ENNReal.ofReal s⁻¹ = ENNReal.ofReal (c / s) := by
    rw [← ENNReal.ofReal_mul hc hs0]
    congr 1
    field_simp [ne_of_gt hs]
  rw [smul_smul, hmul]

/-- Reversed affine transport of a constant interval density. -/
theorem map_intervalDensity_affine_neg
    (a lo hi c : ℝ) {s : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    Measure.map (fun x : ℝ => a - s * x)
        (volume.withDensity (intervalDensity lo hi c)) =
      volume.withDensity
        (intervalDensity (a - s * hi) (a - s * lo) (c / s)) := by
  rw [volume_withDensity_intervalDensity]
  rw [Measure.map_smul]
  rw [map_volume_restrict_Icc_affine_neg a lo hi hs]
  rw [volume_withDensity_intervalDensity]
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hmul :
      ENNReal.ofReal c * ENNReal.ofReal s⁻¹ = ENNReal.ofReal (c / s) := by
    rw [← ENNReal.ofReal_mul hc hs0]
    congr 1
    field_simp [ne_of_gt hs]
  rw [smul_smul, hmul]

end

end Checkerboard
