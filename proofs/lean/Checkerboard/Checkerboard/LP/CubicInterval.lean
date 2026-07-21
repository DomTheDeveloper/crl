import Checkerboard.LP.AlgebraicParameter

/-!
# Rational quadratic sign certificates on the isolating interval

Every generated outer-transport weight and every dual Bernstein coefficient is
represented by `a + b*p + c*p^2`.  The independent checkers establish signs by
minimizing this quadratic on the rational isolating interval for `p`.

The lemmas below are the small trusted kernel for the generated sign proofs.
They cover the three possible locations of a quadratic minimum: at the vertex,
at the left endpoint, or at the right endpoint.  They use no floating point.
-/

namespace Checkerboard

noncomputable section

/-- A quadratic written in coefficient form. -/
def quadraticAt (a b c x : ℝ) : ℝ := a + b * x + c * x ^ 2

/-- A convex quadratic with nonpositive discriminant is nonnegative globally. -/
theorem quadraticAt_nonneg_of_discriminant
    {a b c x : ℝ} (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * c * a) :
    0 ≤ quadraticAt a b c x := by
  have hsquare : 0 ≤ (2 * c * x + b) ^ 2 := sq_nonneg _
  have hscale : 0 < 4 * c := by positivity
  have hid :
      4 * c * quadraticAt a b c x =
        (2 * c * x + b) ^ 2 + (4 * c * a - b ^ 2) := by
    unfold quadraticAt
    ring
  have hscaled : 0 ≤ 4 * c * quadraticAt a b c x := by
    rw [hid]
    positivity
  nlinarith

/-- If the vertex of a convex quadratic lies weakly to the left of an
interval, the left endpoint is a lower bound throughout the interval. -/
theorem quadraticAt_ge_left_of_vertex_le
    {a b c l x : ℝ} (hc : 0 ≤ c) (hlx : l ≤ x)
    (hderiv : 0 ≤ b + 2 * c * l) :
    quadraticAt a b c l ≤ quadraticAt a b c x := by
  have hfactor :
      quadraticAt a b c x - quadraticAt a b c l =
        (x - l) * (b + c * (x + l)) := by
    unfold quadraticAt
    ring
  have hsecond : 0 ≤ b + c * (x + l) := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hlx)]
  rw [sub_nonneg, hfactor]
  exact mul_nonneg (sub_nonneg.mpr hlx) hsecond

/-- If the vertex of a convex quadratic lies weakly to the right of an
interval, the right endpoint is a lower bound throughout the interval. -/
theorem quadraticAt_ge_right_of_vertex_ge
    {a b c x u : ℝ} (hc : 0 ≤ c) (hxu : x ≤ u)
    (hderiv : b + 2 * c * u ≤ 0) :
    quadraticAt a b c u ≤ quadraticAt a b c x := by
  have hfactor :
      quadraticAt a b c x - quadraticAt a b c u =
        (x - u) * (b + c * (x + u)) := by
    unfold quadraticAt
    ring
  have hsecond : b + c * (x + u) ≤ 0 := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxu)]
  rw [sub_nonneg, hfactor]
  exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxu) hsecond

/-- A concave quadratic is bounded below on a compact interval by the smaller
endpoint value. -/
theorem quadraticAt_nonneg_of_concave_endpoints
    {a b c l u x : ℝ}
    (hlu : l < u) (hc : c ≤ 0) (hlx : l ≤ x) (hxu : x ≤ u)
    (hleft : 0 ≤ quadraticAt a b c l)
    (hright : 0 ≤ quadraticAt a b c u) :
    0 ≤ quadraticAt a b c x := by
  have hden : 0 < u - l := sub_pos.mpr hlu
  have hux : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hxl : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hinterp :
      (u - l) * quadraticAt a b c x =
        (u - x) * quadraticAt a b c l +
          (x - l) * quadraticAt a b c u -
            c * (x - l) * (u - x) * (u - l) := by
    unfold quadraticAt
    ring
  have h₁ : 0 ≤ (u - x) * quadraticAt a b c l :=
    mul_nonneg hux hleft
  have h₂ : 0 ≤ (x - l) * quadraticAt a b c u :=
    mul_nonneg hxl hright
  have h₃ : 0 ≤ -c * (x - l) * (u - x) * (u - l) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hc) hxl) hux) hden.le
  have hscaled : 0 ≤ (u - l) * quadraticAt a b c x := by
    rw [hinterp]
    nlinarith
  nlinarith

/-- Strict endpoint values force a concave quadratic to be strictly positive
throughout the interval. -/
theorem quadraticAt_pos_of_concave_endpoints
    {a b c l u x : ℝ}
    (hlu : l < u) (hc : c ≤ 0) (hlx : l ≤ x) (hxu : x ≤ u)
    (hleft : 0 < quadraticAt a b c l)
    (hright : 0 < quadraticAt a b c u) :
    0 < quadraticAt a b c x := by
  let m : ℝ := min (quadraticAt a b c l) (quadraticAt a b c u)
  have hm : 0 < m := lt_min hleft hright
  have hleft' : 0 ≤ quadraticAt (a - m) b c l := by
    rw [show quadraticAt (a - m) b c l = quadraticAt a b c l - m by
      unfold quadraticAt
      ring]
    exact sub_nonneg.mpr (min_le_left _ _)
  have hright' : 0 ≤ quadraticAt (a - m) b c u := by
    rw [show quadraticAt (a - m) b c u = quadraticAt a b c u - m by
      unfold quadraticAt
      ring]
    exact sub_nonneg.mpr (min_le_right _ _)
  have hx' : 0 ≤ quadraticAt (a - m) b c x :=
    quadraticAt_nonneg_of_concave_endpoints hlu hc hlx hxu hleft' hright'
  have hshift : quadraticAt (a - m) b c x = quadraticAt a b c x - m := by
    unfold quadraticAt
    ring
  rw [hshift] at hx'
  linarith

/-- Strict left-endpoint certificate. -/
theorem quadraticAt_pos_of_left_certificate
    {a b c l x : ℝ} (hc : 0 ≤ c) (hlx : l ≤ x)
    (hderiv : 0 ≤ b + 2 * c * l)
    (hleft : 0 < quadraticAt a b c l) :
    0 < quadraticAt a b c x :=
  hleft.trans_le (quadraticAt_ge_left_of_vertex_le hc hlx hderiv)

/-- Strict right-endpoint certificate. -/
theorem quadraticAt_pos_of_right_certificate
    {a b c x u : ℝ} (hc : 0 ≤ c) (hxu : x ≤ u)
    (hderiv : b + 2 * c * u ≤ 0)
    (hright : 0 < quadraticAt a b c u) :
    0 < quadraticAt a b c x :=
  hright.trans_le (quadraticAt_ge_right_of_vertex_ge hc hxu hderiv)

/-- The real evaluation of a rational coefficient triple at the exact root. -/
def evalAtCheckerboardP (a b c : ℚ) : ℝ :=
  quadraticAt a b c checkerboardP

/-- Generated certificates may use the left endpoint when the vertex lies to
its left. -/
theorem evalAtCheckerboardP_pos_of_left
    {a b c : ℚ}
    (hc : 0 ≤ (c : ℝ))
    (hderiv : 0 ≤ (b : ℝ) + 2 * c * pLower)
    (hvalue : 0 < quadraticAt a b c pLower) :
    0 < evalAtCheckerboardP a b c := by
  exact quadraticAt_pos_of_left_certificate hc checkerboardP_mem.1 hderiv hvalue

/-- Generated certificates may use the right endpoint when the vertex lies to
its right. -/
theorem evalAtCheckerboardP_pos_of_right
    {a b c : ℚ}
    (hc : 0 ≤ (c : ℝ))
    (hderiv : (b : ℝ) + 2 * c * pUpper ≤ 0)
    (hvalue : 0 < quadraticAt a b c pUpper) :
    0 < evalAtCheckerboardP a b c := by
  exact quadraticAt_pos_of_right_certificate hc checkerboardP_mem.2 hderiv hvalue

/-- Generated certificates may use the exact vertex minimum. -/
theorem evalAtCheckerboardP_nonneg_of_discriminant
    {a b c : ℚ}
    (hc : 0 < (c : ℝ))
    (hdisc : (b : ℝ) ^ 2 ≤ 4 * c * a) :
    0 ≤ evalAtCheckerboardP a b c :=
  quadraticAt_nonneg_of_discriminant hc hdisc

/-- Generated certificates for concave quadratics use both endpoints. -/
theorem evalAtCheckerboardP_nonneg_of_concave
    {a b c : ℚ}
    (hc : (c : ℝ) ≤ 0)
    (hleft : 0 ≤ quadraticAt a b c pLower)
    (hright : 0 ≤ quadraticAt a b c pUpper) :
    0 ≤ evalAtCheckerboardP a b c := by
  exact quadraticAt_nonneg_of_concave_endpoints pLower_lt_pUpper hc
    checkerboardP_mem.1 checkerboardP_mem.2 hleft hright

/-- Strict concave endpoint certificate. -/
theorem evalAtCheckerboardP_pos_of_concave
    {a b c : ℚ}
    (hc : (c : ℝ) ≤ 0)
    (hleft : 0 < quadraticAt a b c pLower)
    (hright : 0 < quadraticAt a b c pUpper) :
    0 < evalAtCheckerboardP a b c := by
  exact quadraticAt_pos_of_concave_endpoints pLower_lt_pUpper hc
    checkerboardP_mem.1 checkerboardP_mem.2 hleft hright

end

end Checkerboard
