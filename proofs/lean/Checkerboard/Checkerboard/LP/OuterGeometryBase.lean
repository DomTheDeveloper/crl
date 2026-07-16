import Checkerboard.LP.PrimalParameterBounds
import Checkerboard.LP.ContinuumModel

/-!
# Generic affine geometry for the outer transport certificate

The generated 35-component module instantiates these elementary lemmas with
exact cubic-field endpoints.  This hand-written layer is small enough to audit
independently and contains the only generic real-order reasoning needed for the
outer support proof.
-/

namespace Checkerboard

noncomputable section

/-- Affine parametrization of `[lo,hi]` by `t ∈ [-1/2,1/2]`. -/
def affineIntervalPoint (lo hi t : ℝ) : ℝ :=
  (lo + hi) / 2 + (hi - lo) * t

/-- Reversed affine parametrization of the same interval. -/
def affineIntervalPointRev (lo hi t : ℝ) : ℝ :=
  (lo + hi) / 2 - (hi - lo) * t

/-- Forward affine parametrization stays in the closed interval. -/
theorem affineIntervalPoint_mem_Icc
    {lo hi t : ℝ} (hlohi : lo ≤ hi)
    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    affineIntervalPoint lo hi t ∈ Set.Icc lo hi := by
  rcases ht with ⟨htl, htu⟩
  constructor <;> simp [affineIntervalPoint] <;> nlinarith

/-- Reversing the orientation does not change the image interval. -/
theorem affineIntervalPointRev_mem_Icc
    {lo hi t : ℝ} (hlohi : lo ≤ hi)
    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    affineIntervalPointRev lo hi t ∈ Set.Icc lo hi := by
  rcases ht with ⟨htl, htu⟩
  constructor <;> simp [affineIntervalPointRev] <;> nlinarith

/-- A midpoint-slope affine function fills the interval determined by the
absolute slope.  Generated component proofs supply the two endpoint identities. -/
theorem affine_mid_slope_mem
    {mid slope lo hi t : ℝ}
    (hlen : 0 ≤ hi - lo)
    (hlo : lo = mid - |slope| / 2)
    (hhi : hi = mid + |slope| / 2)
    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    mid + slope * t ∈ Set.Icc lo hi := by
  rcases ht with ⟨htl, htu⟩
  rw [hlo, hhi]
  constructor
  · by_cases hs : 0 ≤ slope
    · rw [abs_of_nonneg hs]
      nlinarith
    · have hs' : slope ≤ 0 := le_of_not_ge hs
      rw [abs_of_nonpos hs']
      nlinarith
  · by_cases hs : 0 ≤ slope
    · rw [abs_of_nonneg hs]
      nlinarith
    · have hs' : slope ≤ 0 := le_of_not_ge hs
      rw [abs_of_nonpos hs']
      nlinarith

/-- The normalized endpoint `r` satisfies the defining scaling identity. -/
theorem outerR_mul_outerLength : outerR * outerLength = checkerboardP := by
  unfold outerR
  field_simp [outerLength_ne]

/-- The normalized endpoint `q` satisfies the defining scaling identity. -/
theorem outerQ_mul_outerLength :
    outerQ * outerLength = primalF - checkerboardP := by
  unfold outerQ
  field_simp [outerLength_ne]

/-- The normalized endpoint `h` satisfies the defining scaling identity. -/
theorem outerH_mul_outerLength :
    outerH * outerLength = primalG - checkerboardP := by
  unfold outerH
  field_simp [outerLength_ne]

/-- The outer diagonal endpoint lies strictly below the hypotenuse value one. -/
theorem primalG_lt_one : primalG < 1 := by
  have h : 0 < evalAtCheckerboardP (33 / 76 : ℚ) (-71 / 38) (401 / 76) := by
    apply evalAtCheckerboardP_pos_of_left
    · norm_num
    · norm_num [pLower]
    · norm_num [quadraticAt, pLower]
  rw [primalG_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

/-- Pointwise triangle support from unit-coordinate bounds and the two active
sum/difference bands.  This is the geometric core used by all 35 components. -/
theorem outer_scaled_point_mem_triangle
    {a b : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hdiff : -outerR ≤ a - b)
    (hsum : a + b ≤ outerH) :
    (checkerboardP + outerLength * a, outerLength * b) ∈ continuumTriangle := by
  have hL : 0 ≤ outerLength := le_of_lt outerLength_pos
  have hy : 0 ≤ outerLength * b := mul_nonneg hL hb0
  have hdiagScaled :
      -outerLength * outerR ≤ outerLength * (a - b) := by
    have := mul_le_mul_of_nonneg_left hdiff hL
    nlinarith
  have hr := outerR_mul_outerLength
  have hdiag :
      outerLength * b ≤ checkerboardP + outerLength * a := by
    nlinarith
  have hsumScaled :
      outerLength * (a + b) ≤ outerLength * outerH :=
    mul_le_mul_of_nonneg_left hsum hL
  have hh := outerH_mul_outerLength
  have hhyp :
      checkerboardP + outerLength * a + outerLength * b ≤ 1 := by
    have : checkerboardP + outerLength * (a + b) ≤ primalG := by
      nlinarith
    nlinarith [primalG_lt_one]
  exact ⟨hy, hdiag, by ring_nf at hhyp ⊢; exact hhyp⟩

end

end Checkerboard
