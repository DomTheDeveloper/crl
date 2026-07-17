import Checkerboard.LP.DualFunctionIdentities
import Checkerboard.LP.MiddleTwoSegmentFacts

/-!
# Nonnegativity of the exact one-dimensional dual profiles

The row/column quadratics are concave and the middle pieces are affine.  The
diagonal quadratic is decreasing through its zero at `g`.  The endpoint values
were already reduced exactly to cubic-field representatives; this module turns
those finite sign checks into global profile nonnegativity.
-/

namespace Checkerboard

noncomputable section

/-- An affine function with nonnegative endpoint values is nonnegative on the
whole interval. -/
theorem affine_nonneg_of_endpoints
    {a b l u x : ℝ} (hlu : l < u) (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : 0 ≤ a * l + b) (hu : 0 ≤ a * u + b) :
    0 ≤ a * x + b := by
  have hden : 0 < u - l := sub_pos.mpr hlu
  have hux : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hxl : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hid :
      (u - l) * (a * x + b) =
        (u - x) * (a * l + b) + (x - l) * (a * u + b) := by
    ring
  have hscaled : 0 ≤ (u - l) * (a * x + b) := by
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_left hscaled hden

/-- Exact positivity of the curvature coefficient. -/
theorem certifiedDualK_pos : 0 < certifiedDualK := by
  have h : 0 < evalAtCheckerboardP
      (-213929 / 52782 : ℚ) (1727819 / 52782) (-953578 / 26391) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [certifiedDualK, certifiedDualKRep, CubicRep.eval,
    evalAtCheckerboardP, quadraticAt] using h

/-- The derivative of the diagonal quadratic is still negative at `g`; hence it
is nonpositive throughout `(-∞,g]`. -/
theorem certifiedDualBQ_deriv_at_g_neg :
    certifiedDualK * primalG + certifiedDualR < 0 := by
  have h : 0 < evalAtCheckerboardP
      (379217 / 211128 : ℚ) (-275404 / 26391) (2360687 / 211128) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  have heq :
      -(certifiedDualK * primalG + certifiedDualR) =
        evalAtCheckerboardP
          (379217 / 211128 : ℚ) (-275404 / 26391) (2360687 / 211128) := by
    have hp := checkerboardP_root
    simp [pPoly] at hp
    simp [certifiedDualK, certifiedDualR, certifiedDualKRep,
      certifiedDualRRep, primalG_reduced, CubicRep.eval,
      evalAtCheckerboardP, quadraticAt]
    linear_combination
      ((2360687 * checkerboardP - 1801591) / 84662328) * hp
  rw [← heq] at h
  linarith

private theorem A1_at_p_nonneg : 0 ≤ certifiedDualA1 checkerboardP := by
  rw [dualA1_p_eq]
  exact dualA1_p_nonneg

private theorem A1_at_c_nonneg : 0 ≤ certifiedDualA1 primalC := by
  rw [dualA1_c_eq]
  exact dualA1_c_nonneg

private theorem AL_at_c_nonneg : 0 ≤ certifiedDualAL primalC := by
  rw [dualAL_c_eq]
  exact dualAL_c_nonneg

private theorem AL_at_d_nonneg : 0 ≤ certifiedDualAL primalD := by
  rw [dualAL_d_eq]
  exact dualAL_d_nonneg

private theorem A2_at_d_nonneg : 0 ≤ certifiedDualA2 primalD := by
  rw [dualA2_d_eq]
  exact dualA2_d_nonneg

private theorem A2_at_one_nonneg : 0 ≤ certifiedDualA2 1 := by
  rw [dualA2_one_eq]
  exact dualA2_one_nonneg

private theorem BL_at_e_nonneg : 0 ≤ certifiedDualBL primalE := by
  rw [dualBL_e_eq]
  exact dualBL_e_nonneg

private theorem BL_at_f_nonneg : 0 ≤ certifiedDualBL primalF := by
  rw [dualBL_f_eq]
  exact dualBL_f_nonneg

private theorem BQ_at_g_nonneg : 0 ≤ certifiedDualBQ primalG := by
  rw [dualBQ_g_eq]
  exact dualBQ_g_nonneg

private theorem checkerboardP_lt_primalC : checkerboardP < primalC := by
  simpa [outerLength] using outerLength_pos

private theorem primalC_lt_primalD_profile : primalC < primalD := by
  simpa [middleLength] using middleLength_pos

private theorem primalD_lt_one_profile : primalD < 1 := by
  have h := outerLength_pos
  rw [outerLength_eq_one_sub_primalD] at h
  linarith

/-- The first row/column quadratic is nonnegative on `[p,c]`. -/
theorem certifiedDualA1_nonneg_on
    {t : ℝ} (hpt : checkerboardP ≤ t) (htc : t ≤ primalC) :
    0 ≤ certifiedDualA1 t := by
  have h := quadraticAt_nonneg_of_concave_endpoints
    checkerboardP_lt_primalC
    (show -certifiedDualK ≤ 0 by linarith [certifiedDualK_pos])
    hpt htc A1_at_p_nonneg A1_at_c_nonneg
  simpa [quadraticAt, certifiedDualA1] using h

/-- The affine row/column piece is nonnegative on `[c,d]`. -/
theorem certifiedDualAL_nonneg_on
    {t : ℝ} (hct : primalC ≤ t) (htd : t ≤ primalD) :
    0 ≤ certifiedDualAL t := by
  have h := affine_nonneg_of_endpoints primalC_lt_primalD_profile hct htd
    AL_at_c_nonneg AL_at_d_nonneg
  simpa [certifiedDualAL] using h

/-- The final row/column quadratic is nonnegative on `[d,1]`. -/
theorem certifiedDualA2_nonneg_on
    {t : ℝ} (hdt : primalD ≤ t) (ht1 : t ≤ 1) :
    0 ≤ certifiedDualA2 t := by
  have h := quadraticAt_nonneg_of_concave_endpoints
    primalD_lt_one_profile
    (show -certifiedDualK ≤ 0 by linarith [certifiedDualK_pos])
    hdt ht1 A2_at_d_nonneg A2_at_one_nonneg
  simpa [quadraticAt, certifiedDualA2] using h

/-- The shared diagonal quadratic is nonnegative everywhere to the left of its
zero at `g`. -/
theorem certifiedDualBQ_nonneg_of_le_g
    {t : ℝ} (htg : t ≤ primalG) : 0 ≤ certifiedDualBQ t := by
  have hderiv :
      certifiedDualR + 2 * (certifiedDualK / 2) * primalG ≤ 0 := by
    nlinarith [certifiedDualBQ_deriv_at_g_neg]
  have h := quadraticAt_ge_right_of_vertex_ge
    (show 0 ≤ certifiedDualK / 2 by positivity) htg hderiv
  have hg := BQ_at_g_nonneg
  have htrans :
      quadraticAt certifiedDualS certifiedDualR (certifiedDualK / 2) primalG ≤
        quadraticAt certifiedDualS certifiedDualR (certifiedDualK / 2) t := h
  simpa [quadraticAt, certifiedDualBQ] using hg.trans htrans

/-- The affine diagonal bridge is nonnegative on `[e,f]`. -/
theorem certifiedDualBL_nonneg_on
    {t : ℝ} (het : primalE ≤ t) (htf : t ≤ primalF) :
    0 ≤ certifiedDualBL t := by
  have h := affine_nonneg_of_endpoints primalE_lt_primalF_twoSegment het htf
    BL_at_e_nonneg BL_at_f_nonneg
  simpa [certifiedDualBL] using h

/-- Global row/column profile nonnegativity. -/
theorem certifiedDualAReal_nonneg (t : ℝ) : 0 ≤ certifiedDualAReal t := by
  by_cases hneg : t < 0
  · simp [certifiedDualAReal, hneg]
  have h0 : ¬ t < 0 := hneg
  by_cases hp : t ≤ checkerboardP
  · simp [certifiedDualAReal, h0, hp]
  have hpt : checkerboardP ≤ t := le_of_not_ge hp
  by_cases hc : t ≤ primalC
  · simp [certifiedDualAReal, h0, hp, hc,
      certifiedDualA1_nonneg_on hpt hc]
  have hct : primalC ≤ t := le_of_not_ge hc
  by_cases hd : t ≤ primalD
  · simp [certifiedDualAReal, h0, hp, hc, hd,
      certifiedDualAL_nonneg_on hct hd]
  have hdt : primalD ≤ t := le_of_not_ge hd
  by_cases h1 : t ≤ 1
  · simp [certifiedDualAReal, h0, hp, hc, hd, h1,
      certifiedDualA2_nonneg_on hdt h1]
  · simp [certifiedDualAReal, h0, hp, hc, hd, h1]

/-- Global diagonal profile nonnegativity. -/
theorem certifiedDualBReal_nonneg (t : ℝ) : 0 ≤ certifiedDualBReal t := by
  by_cases hneg : t < 0
  · simp [certifiedDualBReal, hneg]
  have h0 : ¬ t < 0 := hneg
  by_cases he : t ≤ primalE
  · simp [certifiedDualBReal, h0, he,
      certifiedDualBQ_nonneg_of_le_g (he.trans
        (primalE_lt_primalF_twoSegment.le.trans
          primalF_lt_primalG_twoSegment.le))]
  have het : primalE ≤ t := le_of_not_ge he
  by_cases hf : t ≤ primalF
  · simp [certifiedDualBReal, h0, he, hf,
      certifiedDualBL_nonneg_on het hf]
  have hft : primalF ≤ t := le_of_not_ge hf
  by_cases hg : t ≤ primalG
  · simp [certifiedDualBReal, h0, he, hf, hg,
      certifiedDualBQ_nonneg_of_le_g hg]
  · simp [certifiedDualBReal, h0, he, hf, hg]

@[simp] theorem certifiedDualA_ofReal (t : ℝ) :
    ENNReal.toReal (certifiedDualA t) = certifiedDualAReal t := by
  rw [certifiedDualA, ENNReal.toReal_ofReal (certifiedDualAReal_nonneg t)]

@[simp] theorem certifiedDualB_ofReal (t : ℝ) :
    ENNReal.toReal (certifiedDualB t) = certifiedDualBReal t := by
  rw [certifiedDualB, ENNReal.toReal_ofReal (certifiedDualBReal_nonneg t)]

end

end Checkerboard
