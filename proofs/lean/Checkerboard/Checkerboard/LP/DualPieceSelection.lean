import Checkerboard.LP.DualCertifiedFunctions

/-!
# Piece-selection lemmas for the exact dual profiles

Generated obstacle certificates use these lemmas instead of repeatedly
simplifying nested `if` expressions.
-/

namespace Checkerboard

noncomputable section

/-- The row/column profile vanishes below zero. -/
theorem certifiedDualAReal_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    certifiedDualAReal t = 0 := by
  simp [certifiedDualAReal, ht]

/-- The row/column profile vanishes on `[0,p]`. -/
theorem certifiedDualAReal_eq_zero_of_nonneg_of_le_p
    {t : ℝ} (h0 : 0 ≤ t) (hp : t ≤ checkerboardP) :
    certifiedDualAReal t = 0 := by
  simp [certifiedDualAReal, not_lt.mpr h0, hp]

/-- First quadratic row/column piece. -/
theorem certifiedDualAReal_eq_A1
    {t : ℝ} (h0 : 0 ≤ t) (hp : checkerboardP < t) (hc : t ≤ primalC) :
    certifiedDualAReal t = certifiedDualA1 t := by
  simp [certifiedDualAReal, not_lt.mpr h0, not_le.mpr hp, hc]

/-- Middle affine row/column piece. -/
theorem certifiedDualAReal_eq_AL
    {t : ℝ} (h0 : 0 ≤ t) (hc : primalC < t) (hd : t ≤ primalD) :
    certifiedDualAReal t = certifiedDualAL t := by
  have hp : checkerboardP < t :=
    (show checkerboardP < primalC by simpa [outerLength] using outerLength_pos).trans hc
  simp [certifiedDualAReal, not_lt.mpr h0, not_le.mpr hp,
    not_le.mpr hc, hd]

/-- Final quadratic row/column piece. -/
theorem certifiedDualAReal_eq_A2
    {t : ℝ} (h0 : 0 ≤ t) (hd : primalD < t) (h1 : t ≤ 1) :
    certifiedDualAReal t = certifiedDualA2 t := by
  have hcd : primalC < primalD := by simpa [middleLength] using middleLength_pos
  have hct : primalC < t := hcd.trans hd
  have hpt : checkerboardP < t :=
    (show checkerboardP < primalC by simpa [outerLength] using outerLength_pos).trans hct
  simp [certifiedDualAReal, not_lt.mpr h0, not_le.mpr hpt,
    not_le.mpr hct, not_le.mpr hd, h1]

/-- The row/column profile vanishes above one. -/
theorem certifiedDualAReal_eq_zero_of_one_lt {t : ℝ} (h1 : 1 < t) :
    certifiedDualAReal t = 0 := by
  have h0 : ¬ t < 0 := by linarith
  have hp : ¬ t ≤ checkerboardP := by
    have hp1 : checkerboardP < 1 := checkerboardP_mem.2.trans_le (by norm_num [pUpper])
    linarith
  have hc : ¬ t ≤ primalC := by
    have hcd : primalC < primalD := by simpa [middleLength] using middleLength_pos
    have hd1 : primalD < 1 := by
      have h := outerLength_pos
      rw [outerLength_eq_one_sub_primalD] at h
      linarith
    linarith
  have hd : ¬ t ≤ primalD := by
    have hd1 : primalD < 1 := by
      have h := outerLength_pos
      rw [outerLength_eq_one_sub_primalD] at h
      linarith
    linarith
  simp [certifiedDualAReal, h0, hp, hc, hd, not_le.mpr h1]

/-- First diagonal quadratic piece. -/
theorem certifiedDualBReal_eq_BQ_left
    {t : ℝ} (h0 : 0 ≤ t) (he : t ≤ primalE) :
    certifiedDualBReal t = certifiedDualBQ t := by
  simp [certifiedDualBReal, not_lt.mpr h0, he]

/-- Middle affine diagonal piece. -/
theorem certifiedDualBReal_eq_BL
    {t : ℝ} (h0 : 0 ≤ t) (he : primalE < t) (hf : t ≤ primalF) :
    certifiedDualBReal t = certifiedDualBL t := by
  simp [certifiedDualBReal, not_lt.mpr h0, not_le.mpr he, hf]

/-- Second diagonal quadratic piece. -/
theorem certifiedDualBReal_eq_BQ_right
    {t : ℝ} (h0 : 0 ≤ t) (hf : primalF < t) (hg : t ≤ primalG) :
    certifiedDualBReal t = certifiedDualBQ t := by
  have hef : primalE < primalF := by
    rw [← middleTwo_diff_lower, ← middleTwo_diff_upper]
    nlinarith [middleLength_pos]
  have het : primalE < t := hef.trans hf
  simp [certifiedDualBReal, not_lt.mpr h0, not_le.mpr het,
    not_le.mpr hf, hg]

/-- The diagonal profile vanishes to the right of `g`. -/
theorem certifiedDualBReal_eq_zero_of_g_lt
    {t : ℝ} (h0 : 0 ≤ t) (hg : primalG < t) :
    certifiedDualBReal t = 0 := by
  have hfg : primalF < primalG := primalF_lt_primalG_twoSegment
  have hef : primalE < primalF := primalE_lt_primalF_twoSegment
  simp [certifiedDualBReal, not_lt.mpr h0,
    not_le.mpr (hef.trans (hfg.trans hg)),
    not_le.mpr (hfg.trans hg), not_le.mpr hg]

end

end Checkerboard
