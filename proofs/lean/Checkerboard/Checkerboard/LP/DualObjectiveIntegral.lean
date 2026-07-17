import Checkerboard.LP.ContinuumDualCertificate
import Checkerboard.LP.DualObjectiveAlgebra
import Checkerboard.LP.DualPieceSelection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact integration of the continuum dual certificate

The two exact profiles are piecewise quadratic/affine.  We split the interval at
their algebraic breakpoints, identify each open subinterval with the relevant
polynomial piece, and evaluate it with an explicit antiderivative.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter intervalIntegral

/-- Derivative of the generic quadratic primitive. -/
theorem hasDerivAt_quadraticPrimitive (a b c x : ℝ) :
    HasDerivAt (quadraticPrimitive a b c) (a + b * x + c * x ^ 2) x := by
  unfold quadraticPrimitive
  convert (((hasDerivAt_id x).const_mul a).add
      (((hasDerivAt_id x).pow 2).const_mul (b / 2))).add
    (((hasDerivAt_id x).pow 3).const_mul (c / 3)) using 1 <;> ring

/-- Exact integral of a quadratic polynomial. -/
theorem intervalIntegral_quadratic
    (a b c l u : ℝ) (hlu : l ≤ u) :
    (∫ t in l..u, a + b * t + c * t ^ 2) =
      quadraticPrimitive a b c u - quadraticPrimitive a b c l := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlu
  intro x _hx
  exact hasDerivAt_quadraticPrimitive a b c x

private theorem zero_lt_checkerboardP : 0 < checkerboardP := by
  have hp := checkerboardP_mem.1
  norm_num [pLower] at hp ⊢
  linarith

private theorem checkerboardP_lt_primalC_obj : checkerboardP < primalC := by
  simpa [outerLength] using outerLength_pos

private theorem primalC_lt_primalD_obj : primalC < primalD := by
  simpa [middleLength] using middleLength_pos

private theorem primalD_lt_one_obj : primalD < 1 := by
  have h := outerLength_pos
  rw [outerLength_eq_one_sub_primalD] at h
  linarith

private theorem primalG_lt_one_obj : primalG < 1 :=
  primalG_lt_one_sub_middleLength_twoSegment.trans
    one_sub_middleLength_lt_one_twoSegment

/-! ## Interval integrability -/

private theorem A_zero_integrable :
    IntervalIntegrable certifiedDualAReal volume 0 checkerboardP := by
  refine IntervalIntegrable.zero.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le zero_lt_checkerboardP.le] at ht
  symm
  exact certifiedDualAReal_eq_zero_of_nonneg_of_le_p ht.1.le ht.2.le

private theorem A1_integrable :
    IntervalIntegrable certifiedDualAReal volume checkerboardP primalC := by
  have hpoly : IntervalIntegrable certifiedDualA1 volume checkerboardP primalC :=
    (by fun_prop : Continuous certifiedDualA1).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le checkerboardP_lt_primalC_obj.le] at ht
  symm
  exact certifiedDualAReal_eq_A1
    (zero_lt_checkerboardP.trans ht.1).le ht.1 ht.2.le

private theorem AL_integrable :
    IntervalIntegrable certifiedDualAReal volume primalC primalD := by
  have hpoly : IntervalIntegrable certifiedDualAL volume primalC primalD :=
    (by fun_prop : Continuous certifiedDualAL).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalC_lt_primalD_obj.le] at ht
  symm
  exact certifiedDualAReal_eq_AL
    (zero_lt_checkerboardP.trans checkerboardP_lt_primalC_obj |>.trans ht.1).le
    ht.1 ht.2.le

private theorem A2_integrable :
    IntervalIntegrable certifiedDualAReal volume primalD 1 := by
  have hpoly : IntervalIntegrable certifiedDualA2 volume primalD 1 :=
    (by fun_prop : Continuous certifiedDualA2).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalD_lt_one_obj.le] at ht
  symm
  exact certifiedDualAReal_eq_A2 (by linarith [zero_lt_checkerboardP,
    checkerboardP_lt_primalC_obj, primalC_lt_primalD_obj]) ht.1 ht.2.le

private theorem BQ_left_integrable :
    IntervalIntegrable certifiedDualBReal volume 0 primalE := by
  have hpoly : IntervalIntegrable certifiedDualBQ volume 0 primalE :=
    (by fun_prop : Continuous certifiedDualBQ).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalE_pos_twoSegment.le] at ht
  symm
  exact certifiedDualBReal_eq_BQ_left ht.1.le ht.2.le

private theorem BL_integrable :
    IntervalIntegrable certifiedDualBReal volume primalE primalF := by
  have hpoly : IntervalIntegrable certifiedDualBL volume primalE primalF :=
    (by fun_prop : Continuous certifiedDualBL).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalE_lt_primalF_twoSegment.le] at ht
  symm
  exact certifiedDualBReal_eq_BL (primalE_pos_twoSegment.trans ht.1).le
    ht.1 ht.2.le

private theorem BQ_right_integrable :
    IntervalIntegrable certifiedDualBReal volume primalF primalG := by
  have hpoly : IntervalIntegrable certifiedDualBQ volume primalF primalG :=
    (by fun_prop : Continuous certifiedDualBQ).intervalIntegrable _ _
  refine hpoly.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalF_lt_primalG_twoSegment.le] at ht
  symm
  exact certifiedDualBReal_eq_BQ_right
    (primalE_pos_twoSegment.trans
      (primalE_lt_primalF_twoSegment.trans ht.1)).le ht.1 ht.2.le

private theorem B_zero_integrable :
    IntervalIntegrable certifiedDualBReal volume primalG 1 := by
  refine IntervalIntegrable.zero.congr_uIoo ?_
  intro t ht
  rw [uIoo_of_le primalG_lt_one_obj.le] at ht
  symm
  exact certifiedDualBReal_eq_zero_of_g_lt
    (by linarith [primalE_pos_twoSegment,
      primalE_lt_primalF_twoSegment, primalF_lt_primalG_twoSegment]) ht.1

/-- Both profiles are interval integrable on `[0,1]`. -/
theorem certifiedDualAReal_intervalIntegrable :
    IntervalIntegrable certifiedDualAReal volume 0 1 :=
  (A_zero_integrable.trans A1_integrable).trans
    (AL_integrable.trans A2_integrable)

theorem certifiedDualBReal_intervalIntegrable :
    IntervalIntegrable certifiedDualBReal volume 0 1 :=
  (BQ_left_integrable.trans BL_integrable).trans
    (BQ_right_integrable.trans B_zero_integrable)

/-! ## Exact interval integrals -/

private theorem integral_A_zero :
    (∫ t in 0..checkerboardP, certifiedDualAReal t) = 0 := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simp
  intro t ht
  rw [uIoo_of_le zero_lt_checkerboardP.le] at ht
  exact certifiedDualAReal_eq_zero_of_nonneg_of_le_p ht.1.le ht.2.le

private theorem integral_A1 :
    (∫ t in checkerboardP..primalC, certifiedDualAReal t) =
      quadraticPrimitive certifiedDualN1 (-2 * certifiedDualR)
          (-certifiedDualK) primalC -
        quadraticPrimitive certifiedDualN1 (-2 * certifiedDualR)
          (-certifiedDualK) checkerboardP := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualA1] using intervalIntegral_quadratic
      certifiedDualN1 (-2 * certifiedDualR) (-certifiedDualK)
      checkerboardP primalC checkerboardP_lt_primalC_obj.le
  intro t ht
  rw [uIoo_of_le checkerboardP_lt_primalC_obj.le] at ht
  exact certifiedDualAReal_eq_A1
    (zero_lt_checkerboardP.trans ht.1).le ht.1 ht.2.le

private theorem integral_AL :
    (∫ t in primalC..primalD, certifiedDualAReal t) =
      quadraticPrimitive certifiedDualNu certifiedDualEll 0 primalD -
        quadraticPrimitive certifiedDualNu certifiedDualEll 0 primalC := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualAL] using intervalIntegral_quadratic
      certifiedDualNu certifiedDualEll 0 primalC primalD
      primalC_lt_primalD_obj.le
  intro t ht
  rw [uIoo_of_le primalC_lt_primalD_obj.le] at ht
  exact certifiedDualAReal_eq_AL
    (by linarith [zero_lt_checkerboardP, checkerboardP_lt_primalC_obj])
    ht.1 ht.2.le

private theorem integral_A2 :
    (∫ t in primalD..1, certifiedDualAReal t) =
      quadraticPrimitive certifiedDualN2 (2 * certifiedDualK)
          (-certifiedDualK) 1 -
        quadraticPrimitive certifiedDualN2 (2 * certifiedDualK)
          (-certifiedDualK) primalD := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualA2] using intervalIntegral_quadratic
      certifiedDualN2 (2 * certifiedDualK) (-certifiedDualK)
      primalD 1 primalD_lt_one_obj.le
  intro t ht
  rw [uIoo_of_le primalD_lt_one_obj.le] at ht
  exact certifiedDualAReal_eq_A2
    (by linarith [zero_lt_checkerboardP, checkerboardP_lt_primalC_obj,
      primalC_lt_primalD_obj]) ht.1 ht.2.le

private theorem integral_BQ_left :
    (∫ t in 0..primalE, certifiedDualBReal t) =
      quadraticPrimitive certifiedDualS certifiedDualR
          (certifiedDualK / 2) primalE -
        quadraticPrimitive certifiedDualS certifiedDualR
          (certifiedDualK / 2) 0 := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualBQ] using intervalIntegral_quadratic
      certifiedDualS certifiedDualR (certifiedDualK / 2)
      0 primalE primalE_pos_twoSegment.le
  intro t ht
  rw [uIoo_of_le primalE_pos_twoSegment.le] at ht
  exact certifiedDualBReal_eq_BQ_left ht.1.le ht.2.le

private theorem integral_BL :
    (∫ t in primalE..primalF, certifiedDualBReal t) =
      quadraticPrimitive certifiedDualQ (-certifiedDualEll) 0 primalF -
        quadraticPrimitive certifiedDualQ (-certifiedDualEll) 0 primalE := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualBL] using intervalIntegral_quadratic
      certifiedDualQ (-certifiedDualEll) 0 primalE primalF
      primalE_lt_primalF_twoSegment.le
  intro t ht
  rw [uIoo_of_le primalE_lt_primalF_twoSegment.le] at ht
  exact certifiedDualBReal_eq_BL (primalE_pos_twoSegment.trans ht.1).le
    ht.1 ht.2.le

private theorem integral_BQ_right :
    (∫ t in primalF..primalG, certifiedDualBReal t) =
      quadraticPrimitive certifiedDualS certifiedDualR
          (certifiedDualK / 2) primalG -
        quadraticPrimitive certifiedDualS certifiedDualR
          (certifiedDualK / 2) primalF := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simpa [certifiedDualBQ] using intervalIntegral_quadratic
      certifiedDualS certifiedDualR (certifiedDualK / 2)
      primalF primalG primalF_lt_primalG_twoSegment.le
  intro t ht
  rw [uIoo_of_le primalF_lt_primalG_twoSegment.le] at ht
  exact certifiedDualBReal_eq_BQ_right
    (by linarith [primalE_pos_twoSegment, primalE_lt_primalF_twoSegment])
    ht.1 ht.2.le

private theorem integral_B_zero :
    (∫ t in primalG..1, certifiedDualBReal t) = 0 := by
  rw [intervalIntegral.integral_congr_uIoo]
  · simp
  intro t ht
  rw [uIoo_of_le primalG_lt_one_obj.le] at ht
  exact certifiedDualBReal_eq_zero_of_g_lt
    (by linarith [primalE_pos_twoSegment, primalE_lt_primalF_twoSegment,
      primalF_lt_primalG_twoSegment]) ht.1

/-- Exact real integrals of the two profiles. -/
theorem intervalIntegral_certifiedDualAReal :
    (∫ t in 0..1, certifiedDualAReal t) = certifiedDualAIntegralFormula := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      A_zero_integrable
      (A1_integrable.trans (AL_integrable.trans A2_integrable)),
    ← intervalIntegral.integral_add_adjacent_intervals
      A1_integrable (AL_integrable.trans A2_integrable),
    ← intervalIntegral.integral_add_adjacent_intervals
      AL_integrable A2_integrable,
    integral_A_zero, integral_A1, integral_AL, integral_A2]
  simp [certifiedDualAIntegralFormula]
  ring

theorem intervalIntegral_certifiedDualBReal :
    (∫ t in 0..1, certifiedDualBReal t) = certifiedDualBIntegralFormula := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      BQ_left_integrable
      (BL_integrable.trans (BQ_right_integrable.trans B_zero_integrable)),
    ← intervalIntegral.integral_add_adjacent_intervals
      BL_integrable (BQ_right_integrable.trans B_zero_integrable),
    ← intervalIntegral.integral_add_adjacent_intervals
      BQ_right_integrable B_zero_integrable,
    integral_BQ_left, integral_BL, integral_BQ_right, integral_B_zero]
  simp [certifiedDualBIntegralFormula]
  ring

/-- Real measure integrals over the restricted unit interval. -/
theorem integral_certifiedDualAReal :
    (∫ t, certifiedDualAReal t ∂unitIntervalVolume) =
      certifiedDualAIntegralFormula := by
  rw [unitIntervalVolume, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral_certifiedDualAReal

theorem integral_certifiedDualBReal :
    (∫ t, certifiedDualBReal t ∂unitIntervalVolume) =
      certifiedDualBIntegralFormula := by
  rw [unitIntervalVolume, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral_certifiedDualBReal

private theorem certifiedDualAReal_integrable :
    Integrable certifiedDualAReal unitIntervalVolume := by
  rw [unitIntervalVolume]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    certifiedDualAReal_intervalIntegrable

private theorem certifiedDualBReal_integrable :
    Integrable certifiedDualBReal unitIntervalVolume := by
  rw [unitIntervalVolume]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    certifiedDualBReal_intervalIntegrable

/-- Exact extended-real integrals of the dual profiles. -/
theorem lintegral_certifiedDualA :
    (∫⁻ t, certifiedDualA t ∂unitIntervalVolume) =
      ENNReal.ofReal certifiedDualAIntegralFormula := by
  calc
    (∫⁻ t, certifiedDualA t ∂unitIntervalVolume) =
        ENNReal.ofReal (∫ t, certifiedDualAReal t ∂unitIntervalVolume) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal certifiedDualAReal_integrable
    _ = ENNReal.ofReal certifiedDualAIntegralFormula := by
      rw [integral_certifiedDualAReal]

theorem lintegral_certifiedDualB :
    (∫⁻ t, certifiedDualB t ∂unitIntervalVolume) =
      ENNReal.ofReal certifiedDualBIntegralFormula := by
  calc
    (∫⁻ t, certifiedDualB t ∂unitIntervalVolume) =
        ENNReal.ofReal (∫ t, certifiedDualBReal t ∂unitIntervalVolume) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal certifiedDualBReal_integrable
    _ = ENNReal.ofReal certifiedDualBIntegralFormula := by
      rw [integral_certifiedDualBReal]

private theorem certifiedDualAIntegralFormula_nonneg :
    0 ≤ certifiedDualAIntegralFormula := by
  rw [← integral_certifiedDualAReal]
  exact integral_nonneg_of_ae
    (Eventually.of_forall certifiedDualAReal_nonneg)

private theorem certifiedDualBIntegralFormula_nonneg :
    0 ≤ certifiedDualBIntegralFormula := by
  rw [← integral_certifiedDualBReal]
  exact integral_nonneg_of_ae
    (Eventually.of_forall certifiedDualBReal_nonneg)

/-- The exact continuum dual objective is `alpha`. -/
theorem certifiedDual_value :
    continuumDualValue certifiedDualA certifiedDualB =
      ENNReal.ofReal checkerboardAlpha := by
  rw [continuumDualValue, lintegral_certifiedDualA,
    lintegral_certifiedDualB]
  rw [← ENNReal.ofReal_add certifiedDualAIntegralFormula_nonneg
    certifiedDualBIntegralFormula_nonneg]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)
    (add_nonneg certifiedDualAIntegralFormula_nonneg
      certifiedDualBIntegralFormula_nonneg)]
  rw [certifiedDualIntegralFormula_objective]

end

end Checkerboard
