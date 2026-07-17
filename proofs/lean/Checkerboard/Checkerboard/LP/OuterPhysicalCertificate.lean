import Checkerboard.LP.OuterMeasureCertificate
import Checkerboard.LP.AffineDensityPushforward
import Checkerboard.LP.ContinuumProjection

/-!
# Physical outer continuum primal block

The generated 35-component coupling is normalized on `[0,1]²`.  This module
applies the exact affine transformation

`(A,B) ↦ (p + L A, L B)`

and multiplies the mass by `4L`.  It proves exact physical pushforwards, support
in the continuum triangle, and total mass `4L`.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- Affine map from normalized outer coordinates to the continuum triangle. -/
def outerPhysicalMap (z : ℝ × ℝ) : ContinuumPoint :=
  (checkerboardP + outerLength * z.1, outerLength * z.2)

lemma measurable_outerPhysicalMap : Measurable outerPhysicalMap := by
  unfold outerPhysicalMap
  fun_prop

/-- Total physical mass multiplier of the normalized outer probability coupling. -/
def outerPhysicalScale : ℝ := 4 * outerLength

lemma outerPhysicalScale_pos : 0 < outerPhysicalScale := by
  simp [outerPhysicalScale, outerLength_pos]

/-- The physical outer measure. -/
def outerPhysicalMeasure : Measure ContinuumPoint :=
  ENNReal.ofReal outerPhysicalScale •
    Measure.map outerPhysicalMap outerNormalizedCoupling

private theorem outer_scale_cancel :
    ENNReal.ofReal outerPhysicalScale * ENNReal.ofReal outerLength⁻¹ = 4 := by
  rw [← ENNReal.ofReal_mul (le_of_lt outerPhysicalScale_pos)
    (inv_nonneg.mpr (le_of_lt outerLength_pos))]
  have hreal : outerPhysicalScale * outerLength⁻¹ = 4 := by
    simp [outerPhysicalScale, outerLength_ne]
  rw [hreal]
  norm_num

/-! ## Exact physical endpoints -/

theorem checkerboardP_add_outerLength :
    checkerboardP + outerLength = primalC := by
  simp [outerLength]

theorem one_sub_outerLength : 1 - outerLength = primalD := by
  linarith [outerLength_eq_one_sub_primalD]

theorem checkerboardP_sub_outerLength_mul_outerR :
    checkerboardP - outerLength * outerR = 0 := by
  simp [outerR, outerLength_ne]

theorem checkerboardP_add_outerLength_mul_neg_outerR :
    checkerboardP + outerLength * (-outerR) = 0 := by
  linarith [checkerboardP_sub_outerLength_mul_outerR]

theorem checkerboardP_add_outerLength_mul_outerQ :
    checkerboardP + outerLength * outerQ = primalF := by
  simp [outerQ, outerLength_ne]

theorem checkerboardP_sub_outerLength_mul_outerQ :
    checkerboardP - outerLength * outerQ = primalE := by
  rw [show outerLength * outerQ = primalF - checkerboardP by
    simp [outerQ, outerLength_ne]]
  linarith [p_sub_primalE_eq_primalF_sub_p]

theorem checkerboardP_add_outerLength_mul_neg_outerQ :
    checkerboardP + outerLength * (-outerQ) = primalE := by
  linarith [checkerboardP_sub_outerLength_mul_outerQ]

theorem checkerboardP_add_outerLength_mul_outerH :
    checkerboardP + outerLength * outerH = primalG := by
  simp [outerH, outerLength_ne]

private theorem outerEndpointRep0_eval_zero : outerEndpointRep0.eval = 0 := by
  norm_num [outerEndpointRep0, CubicRep.eval]

private theorem outerEndpointRep7_eval_one : outerEndpointRep7.eval = 1 := by
  norm_num [outerEndpointRep7, CubicRep.eval]

/-! ## Exact row and column pushforwards -/

theorem outerPhysicalMeasure_coordX :
    Measure.map coordX outerPhysicalMeasure =
      4 • volume.restrict (Set.Icc checkerboardP primalC) := by
  rw [outerPhysicalMeasure, Measure.map_smul]
  rw [Measure.map_map measurable_outerPhysicalMap measurable_coordX]
  change ENNReal.ofReal outerPhysicalScale •
      Measure.map (fun z : ℝ × ℝ => checkerboardP + outerLength * z.1)
        outerNormalizedCoupling = _
  calc
    ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun z : ℝ × ℝ => checkerboardP + outerLength * z.1)
          outerNormalizedCoupling =
      ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
          (Measure.map Prod.fst outerNormalizedCoupling) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
          (volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval)) := by
            rw [outerNormalizedCoupling_fst]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            rw [outerEndpointRep0_eval_zero, outerEndpointRep7_eval_one]
    _ = ENNReal.ofReal outerPhysicalScale •
        (ENNReal.ofReal outerLength⁻¹ •
          volume.restrict (Set.Icc checkerboardP (checkerboardP + outerLength))) := by
            rw [map_volume_restrict_Icc_affine checkerboardP 0 1 outerLength_pos]
            ring_nf
    _ = 4 • volume.restrict (Set.Icc checkerboardP primalC) := by
      rw [smul_smul, outer_scale_cancel, checkerboardP_add_outerLength]

theorem outerPhysicalMeasure_coordOneSubY :
    Measure.map coordOneSubY outerPhysicalMeasure =
      4 • volume.restrict (Set.Icc primalD 1) := by
  rw [outerPhysicalMeasure, Measure.map_smul]
  rw [Measure.map_map measurable_outerPhysicalMap measurable_coordOneSubY]
  change ENNReal.ofReal outerPhysicalScale •
      Measure.map (fun z : ℝ × ℝ => 1 - outerLength * z.2)
        outerNormalizedCoupling = _
  calc
    ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun z : ℝ × ℝ => 1 - outerLength * z.2)
          outerNormalizedCoupling =
      ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => 1 - outerLength * x)
          (Measure.map Prod.snd outerNormalizedCoupling) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => 1 - outerLength * x)
          (volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval)) := by
            rw [outerNormalizedCoupling_snd]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => 1 - outerLength * x)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            rw [outerEndpointRep0_eval_zero, outerEndpointRep7_eval_one]
    _ = ENNReal.ofReal outerPhysicalScale •
        (ENNReal.ofReal outerLength⁻¹ •
          volume.restrict (Set.Icc (1 - outerLength) 1)) := by
            rw [map_volume_restrict_Icc_affine_neg 1 0 1 outerLength_pos]
            ring_nf
    _ = 4 • volume.restrict (Set.Icc primalD 1) := by
      rw [smul_smul, outer_scale_cancel, one_sub_outerLength]

/-- Exact paired row/column projection of the outer block. -/
theorem pairedAMeasure_outerPhysicalMeasure :
    pairedAMeasure outerPhysicalMeasure =
      4 • volume.restrict (Set.Icc checkerboardP primalC) +
        4 • volume.restrict (Set.Icc primalD 1) := by
  rw [pairedAMeasure, outerPhysicalMeasure_coordX,
    outerPhysicalMeasure_coordOneSubY]

/-! ## Normalized and physical diagonal target measures -/

private theorem outerQ_pos : 0 < outerQ := outer_breakpoint_order.1

private theorem outerProjectionTargetDensity_split (x : ℝ) :
    outerProjectionTargetDensity x =
      intervalDensity (-outerR) (-outerQ) 1 x +
        intervalDensity outerQ outerH 1 x := by
  by_cases hn : x ∈ Set.Icc (-outerR) (-outerQ)
  · have hp : x ∉ Set.Icc outerQ outerH := by
      rintro ⟨hqx,_⟩
      have hxq := hn.2
      linarith [outerQ_pos]
    simp [outerProjectionTargetDensity, intervalDensity, hn, hp]
  · by_cases hp : x ∈ Set.Icc outerQ outerH
    · simp [outerProjectionTargetDensity, intervalDensity, hn, hp]
    · simp [outerProjectionTargetDensity, intervalDensity, hn, hp]

private theorem outerProjectionTargetMeasure_split :
    volume.withDensity outerProjectionTargetDensity =
      volume.withDensity (intervalDensity (-outerR) (-outerQ) 1) +
        volume.withDensity (intervalDensity outerQ outerH 1) := by
  rw [← withDensity_add_left
    (measurable_intervalDensity (-outerR) (-outerQ) 1)]
  congr 1
  funext x
  exact outerProjectionTargetDensity_split x

private theorem outerNormalizedProjection_split :
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) outerNormalizedCoupling +
        Measure.map (fun z : ℝ × ℝ => z.1 - z.2) outerNormalizedCoupling =
      volume.withDensity (intervalDensity (-outerR) (-outerQ) 1) +
        volume.withDensity (intervalDensity outerQ outerH 1) := by
  rw [outerNormalizedCoupling_projection,
    outerProjectionTargetMeasure_split]

/-- Exact physical paired sum/difference projection of the outer block. -/
theorem pairedBMeasure_outerPhysicalMeasure :
    pairedBMeasure outerPhysicalMeasure =
      4 • volume.restrict (Set.Icc 0 primalE) +
        4 • volume.restrict (Set.Icc primalF primalG) := by
  rw [pairedBMeasure, outerPhysicalMeasure]
  rw [Measure.map_smul, Measure.map_smul]
  rw [Measure.map_map measurable_outerPhysicalMap measurable_coordSum]
  rw [Measure.map_map measurable_outerPhysicalMap measurable_coordDiff]
  change
    ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun z : ℝ × ℝ => checkerboardP + outerLength * (z.1 + z.2))
          outerNormalizedCoupling +
      ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun z : ℝ × ℝ => checkerboardP + outerLength * (z.1 - z.2))
          outerNormalizedCoupling = _
  calc
    _ = ENNReal.ofReal outerPhysicalScale •
        (Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
            (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) outerNormalizedCoupling) +
          Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
            (Measure.map (fun z : ℝ × ℝ => z.1 - z.2) outerNormalizedCoupling)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rw [smul_add]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
          (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) outerNormalizedCoupling +
            Measure.map (fun z : ℝ × ℝ => z.1 - z.2) outerNormalizedCoupling) := by
      rw [Measure.map_add _ _ (by fun_prop)]
    _ = ENNReal.ofReal outerPhysicalScale •
        Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
          (volume.withDensity (intervalDensity (-outerR) (-outerQ) 1) +
            volume.withDensity (intervalDensity outerQ outerH 1)) := by
      rw [outerNormalizedProjection_split]
    _ = ENNReal.ofReal outerPhysicalScale •
        (Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
            (volume.withDensity (intervalDensity (-outerR) (-outerQ) 1)) +
          Measure.map (fun x : ℝ => checkerboardP + outerLength * x)
            (volume.withDensity (intervalDensity outerQ outerH 1))) := by
      rw [Measure.map_add _ _ (by fun_prop)]
    _ = ENNReal.ofReal outerPhysicalScale •
        (volume.withDensity (intervalDensity
            (checkerboardP + outerLength * (-outerR))
            (checkerboardP + outerLength * (-outerQ))
            (1 / outerLength)) +
          volume.withDensity (intervalDensity
            (checkerboardP + outerLength * outerQ)
            (checkerboardP + outerLength * outerH)
            (1 / outerLength))) := by
      rw [map_intervalDensity_affine checkerboardP (-outerR) (-outerQ) 1
        outerLength_pos (by norm_num)]
      rw [map_intervalDensity_affine checkerboardP outerQ outerH 1
        outerLength_pos (by norm_num)]
    _ = ENNReal.ofReal outerPhysicalScale •
        (ENNReal.ofReal outerLength⁻¹ •
            volume.restrict (Set.Icc 0 primalE) +
          ENNReal.ofReal outerLength⁻¹ •
            volume.restrict (Set.Icc primalF primalG)) := by
      rw [volume_withDensity_intervalDensity,
        volume_withDensity_intervalDensity]
      rw [checkerboardP_add_outerLength_mul_neg_outerR,
        checkerboardP_add_outerLength_mul_neg_outerQ,
        checkerboardP_add_outerLength_mul_outerQ,
        checkerboardP_add_outerLength_mul_outerH]
      simp [div_eq_mul_inv]
    _ = 4 • volume.restrict (Set.Icc 0 primalE) +
        4 • volume.restrict (Set.Icc primalF primalG) := by
      rw [smul_add, smul_smul, smul_smul, outer_scale_cancel]

/-! ## Support and total mass -/

private theorem outerPhysicalMap_outerNormalizedPair
    (i : Fin 35) (t : ℝ) :
    outerPhysicalMap (outerNormalizedPair i t) = outerMappedPoint i t := by
  fin_cases i <;>
    simp [outerPhysicalMap, outerNormalizedPair, outerNormalizedA,
      outerNormalizedB, outerMappedPoint]

private theorem outerComponentMeasure_bad_set_zero (i : Fin 35) :
    outerComponentMeasure i (outerPhysicalMap ⁻¹' continuumTriangleᶜ) = 0 := by
  rw [outerComponentMeasure, Measure.smul_apply]
  rw [Measure.map_apply (measurable_outerNormalizedPair i)
    (measurableSet_continuumTriangle.compl.preimage measurable_outerPhysicalMap)]
  have hmeas : MeasurableSet
      (outerNormalizedPair i ⁻¹' (outerPhysicalMap ⁻¹' continuumTriangleᶜ)) :=
    (measurableSet_continuumTriangle.compl.preimage measurable_outerPhysicalMap).preimage
      (measurable_outerNormalizedPair i)
  rw [centeredUnitIntervalMeasure, Measure.restrict_apply hmeas]
  have hset :
      outerNormalizedPair i ⁻¹' (outerPhysicalMap ⁻¹' continuumTriangleᶜ) ∩
          Set.Icc (-1 / 2 : ℝ) (1 / 2) = ∅ := by
    ext t
    constructor
    · rintro ⟨htbad,ht⟩
      have hpoint : outerMappedPoint i t ∈ continuumTriangle :=
        outerMappedPoint_mem i ht
      rw [← outerPhysicalMap_outerNormalizedPair i t] at hpoint
      exact (htbad hpoint).elim
    · simp
  rw [hset]
  simp

theorem outerNormalizedCoupling_physical_bad_set_zero :
    outerNormalizedCoupling (outerPhysicalMap ⁻¹' continuumTriangleᶜ) = 0 := by
  rw [outerNormalizedCoupling]
  rw [Measure.sum_apply _
    (measurableSet_continuumTriangle.compl.preimage measurable_outerPhysicalMap)]
  simp [outerComponentMeasure_bad_set_zero]

theorem outerPhysicalMeasure_support :
    ∀ᵐ z ∂outerPhysicalMeasure, z ∈ continuumTriangle := by
  rw [mem_ae_iff]
  rw [outerPhysicalMeasure, Measure.smul_apply]
  rw [Measure.map_apply measurable_outerPhysicalMap measurableSet_continuumTriangle.compl]
  rw [outerNormalizedCoupling_physical_bad_set_zero]
  simp

private theorem outerNormalizedCoupling_univ :
    outerNormalizedCoupling Set.univ = 1 := by
  have hmap := congrArg (fun μ : Measure ℝ => μ Set.univ)
    outerNormalizedCoupling_fst
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at hmap
  rw [outerEndpointRep0_eval_zero, outerEndpointRep7_eval_one] at hmap
  simpa [Real.volume_Icc] using hmap

theorem outerPhysicalMeasure_univ :
    outerPhysicalMeasure Set.univ = ENNReal.ofReal (4 * outerLength) := by
  rw [outerPhysicalMeasure, Measure.smul_apply]
  rw [Measure.map_apply measurable_outerPhysicalMap MeasurableSet.univ]
  simp [outerNormalizedCoupling_univ, outerPhysicalScale]

end

end Checkerboard
