import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Affine images of restricted one-dimensional Lebesgue measure

Every primal certificate component is the pushforward of Lebesgue measure on
`[-1/2,1/2]` along an affine map.  This file proves the exact density of that
pushforward from translation invariance and the scaling law for Lebesgue
measure.  It is the measure-theoretic bridge from generated interval arithmetic
to the continuum primal constraints.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set

/-- The unit-mass centered interval measure used to parameterize components. -/
def centeredUnitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (-1 / 2 : ℝ) (1 / 2))

/-- Scaling the centered unit interval by a positive factor gives the expected
constant-density measure on the centered target interval. -/
theorem map_centered_interval_mul
    {s : ℝ} (hs : 0 < s) :
    Measure.map (fun t : ℝ => s * t) centeredUnitIntervalMeasure =
      ENNReal.ofReal s⁻¹ • volume.restrict (Set.Icc (-s / 2) (s / 2)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hpre :
      (fun t : ℝ => s * t) ⁻¹' Set.Icc (-s / 2) (s / 2) =
        Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hl, hu⟩
      constructor <;> nlinarith
    · rintro ⟨hl, hu⟩
      constructor <;> nlinarith
  have hrestrict := Measure.restrict_map
    (μ := volume) (f := fun t : ℝ => s * t)
    (s := Set.Icc (-s / 2) (s / 2))
    (by fun_prop) measurableSet_Icc
  rw [hpre] at hrestrict
  calc
    Measure.map (fun t : ℝ => s * t) centeredUnitIntervalMeasure =
        (Measure.map (fun t : ℝ => s * t) volume).restrict
          (Set.Icc (-s / 2) (s / 2)) := by
      simpa [centeredUnitIntervalMeasure] using hrestrict.symm
    _ = (ENNReal.ofReal |s⁻¹| • volume).restrict
          (Set.Icc (-s / 2) (s / 2)) := by
      rw [Real.map_volume_mul_left hs0]
    _ = ENNReal.ofReal s⁻¹ • volume.restrict
          (Set.Icc (-s / 2) (s / 2)) := by
      rw [Measure.restrict_smul, abs_of_nonneg (inv_nonneg.mpr hs.le)]

/-- Translation sends a restricted interval measure to the translated interval. -/
theorem map_restrict_Icc_add_left (m a b : ℝ) :
    Measure.map (fun t : ℝ => m + t) (volume.restrict (Set.Icc a b)) =
      volume.restrict (Set.Icc (m + a) (m + b)) := by
  have hpre :
      (fun t : ℝ => m + t) ⁻¹' Set.Icc (m + a) (m + b) = Set.Icc a b := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  have hrestrict := Measure.restrict_map
    (μ := volume) (f := fun t : ℝ => m + t)
    (s := Set.Icc (m + a) (m + b))
    (by fun_prop) measurableSet_Icc
  rw [hpre] at hrestrict
  calc
    Measure.map (fun t : ℝ => m + t) (volume.restrict (Set.Icc a b)) =
        (Measure.map (fun t : ℝ => m + t) volume).restrict
          (Set.Icc (m + a) (m + b)) := hrestrict.symm
    _ = volume.restrict (Set.Icc (m + a) (m + b)) := by
      rw [MeasureTheory.map_add_left_eq_self]

/-- Exact affine pushforward formula for positive slope. -/
theorem map_centered_interval_affine
    (m : ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun t : ℝ => m + s * t) centeredUnitIntervalMeasure =
      ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (m - s / 2) (m + s / 2)) := by
  have hmul : Measurable (fun t : ℝ => s * t) := by fun_prop
  have hadd : Measurable (fun t : ℝ => m + t) := by fun_prop
  calc
    Measure.map (fun t : ℝ => m + s * t) centeredUnitIntervalMeasure =
        Measure.map (fun u : ℝ => m + u)
          (Measure.map (fun t : ℝ => s * t) centeredUnitIntervalMeasure) := by
      rw [Measure.map_map hadd hmul]
      congr 1
    _ = Measure.map (fun u : ℝ => m + u)
        (ENNReal.ofReal s⁻¹ • volume.restrict (Set.Icc (-s / 2) (s / 2))) := by
      rw [map_centered_interval_mul hs]
    _ = ENNReal.ofReal s⁻¹ •
        Measure.map (fun u : ℝ => m + u)
          (volume.restrict (Set.Icc (-s / 2) (s / 2))) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (m + (-s / 2)) (m + s / 2)) := by
      rw [map_restrict_Icc_add_left]
    _ = ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (m - s / 2) (m + s / 2)) := by
      ring_nf

/-- The reversed orientation has the same interval pushforward. -/
theorem map_centered_interval_affine_neg
    (m : ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun t : ℝ => m - s * t) centeredUnitIntervalMeasure =
      ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (m - s / 2) (m + s / 2)) := by
  have hreflect :
      Measure.map (fun t : ℝ => -t) centeredUnitIntervalMeasure =
        centeredUnitIntervalMeasure := by
    have hpre :
        (fun t : ℝ => -t) ⁻¹' Set.Icc (-1 / 2 : ℝ) (1 / 2) =
          Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
    have hrestrict := Measure.restrict_map
      (μ := volume) (f := fun t : ℝ => -t)
      (s := Set.Icc (-1 / 2 : ℝ) (1 / 2))
      (by fun_prop) measurableSet_Icc
    rw [hpre] at hrestrict
    have hmap : Measure.map (fun t : ℝ => -t) volume = volume := by
      simpa using Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
    simpa [centeredUnitIntervalMeasure, hmap] using hrestrict.symm
  have haff : Measurable (fun u : ℝ => m + s * u) := by fun_prop
  have hneg : Measurable (fun t : ℝ => -t) := by fun_prop
  calc
    Measure.map (fun t : ℝ => m - s * t) centeredUnitIntervalMeasure =
        Measure.map (fun u : ℝ => m + s * u)
          (Measure.map (fun t : ℝ => -t) centeredUnitIntervalMeasure) := by
      rw [Measure.map_map haff hneg]
      congr 1
      funext t
      simp only [Function.comp_apply]
      ring
    _ = Measure.map (fun u : ℝ => m + s * u) centeredUnitIntervalMeasure := by
      rw [hreflect]
    _ = ENNReal.ofReal s⁻¹ •
        volume.restrict (Set.Icc (m - s / 2) (m + s / 2)) :=
      map_centered_interval_affine m hs

/-- The centered source has total mass one. -/
theorem centeredUnitIntervalMeasure_univ :
    centeredUnitIntervalMeasure Set.univ = 1 := by
  norm_num [centeredUnitIntervalMeasure, Real.volume_Icc]

end

end Checkerboard
