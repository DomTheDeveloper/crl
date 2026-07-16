import Mathlib

/-!
# Degree-two Bernstein positivity on a triangle

The exact dual certificate subdivides the continuum chamber into triangles and
expresses the obstacle polynomial in the quadratic Bernstein basis.  This file
contains the kernel lemma used by every cell: nonnegative barycentric
coordinates and nonnegative Bernstein coefficients imply a nonnegative value.
-/

namespace Checkerboard

/-- Evaluation of a degree-two triangular Bernstein form.

The six coefficients correspond to multi-indices
`(2,0,0)`, `(0,2,0)`, `(0,0,2)`, `(1,1,0)`, `(1,0,1)`, `(0,1,1)`.
The mixed basis elements carry the multinomial factor two.
-/
def quadraticBernstein
    (c200 c020 c002 c110 c101 c011 l0 l1 l2 : ℝ) : ℝ :=
  c200 * l0^2 + c020 * l1^2 + c002 * l2^2 +
    2 * c110 * l0 * l1 + 2 * c101 * l0 * l2 + 2 * c011 * l1 * l2

/-- Positivity of the quadratic Bernstein basis on the nonnegative barycentric
cone.  The equation `l0+l1+l2=1` is not needed for positivity itself.
-/
theorem quadraticBernstein_nonneg
    {c200 c020 c002 c110 c101 c011 l0 l1 l2 : ℝ}
    (hc200 : 0 ≤ c200) (hc020 : 0 ≤ c020) (hc002 : 0 ≤ c002)
    (hc110 : 0 ≤ c110) (hc101 : 0 ≤ c101) (hc011 : 0 ≤ c011)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) :
    0 ≤ quadraticBernstein c200 c020 c002 c110 c101 c011 l0 l1 l2 := by
  unfold quadraticBernstein
  positivity

/-- Convenient certificate record for one quadratic cell. -/
structure QuadraticBernsteinCertificate where
  c200 : ℝ
  c020 : ℝ
  c002 : ℝ
  c110 : ℝ
  c101 : ℝ
  c011 : ℝ
  c200_nonneg : 0 ≤ c200
  c020_nonneg : 0 ≤ c020
  c002_nonneg : 0 ≤ c002
  c110_nonneg : 0 ≤ c110
  c101_nonneg : 0 ≤ c101
  c011_nonneg : 0 ≤ c011

/-- Any checked coefficient record evaluates nonnegatively at nonnegative
barycentric coordinates. -/
theorem QuadraticBernsteinCertificate.eval_nonneg
    (C : QuadraticBernsteinCertificate) {l0 l1 l2 : ℝ}
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) :
    0 ≤ quadraticBernstein C.c200 C.c020 C.c002 C.c110 C.c101 C.c011 l0 l1 l2 :=
  quadraticBernstein_nonneg C.c200_nonneg C.c020_nonneg C.c002_nonneg
    C.c110_nonneg C.c101_nonneg C.c011_nonneg hl0 hl1 hl2

/-- The normalized quadratic Bernstein basis sums to one on a triangle. -/
theorem quadraticBernstein_basis_sum
    {l0 l1 l2 : ℝ} (hsum : l0 + l1 + l2 = 1) :
    l0^2 + l1^2 + l2^2 + 2*l0*l1 + 2*l0*l2 + 2*l1*l2 = 1 := by
  calc
    l0^2 + l1^2 + l2^2 + 2*l0*l1 + 2*l0*l2 + 2*l1*l2 =
        (l0 + l1 + l2)^2 := by ring
    _ = 1 := by rw [hsum]; norm_num

/-- A uniform lower bound on all six coefficients gives the same lower bound on
the polynomial over normalized barycentric coordinates. -/
theorem quadraticBernstein_lower_bound
    {c200 c020 c002 c110 c101 c011 l0 l1 l2 m : ℝ}
    (hc200 : m ≤ c200) (hc020 : m ≤ c020) (hc002 : m ≤ c002)
    (hc110 : m ≤ c110) (hc101 : m ≤ c101) (hc011 : m ≤ c011)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (hsum : l0 + l1 + l2 = 1) :
    m ≤ quadraticBernstein c200 c020 c002 c110 c101 c011 l0 l1 l2 := by
  have hbasis := quadraticBernstein_basis_sum hsum
  have h200 : 0 ≤ (c200 - m) * l0^2 := mul_nonneg (sub_nonneg.mpr hc200) (sq_nonneg l0)
  have h020 : 0 ≤ (c020 - m) * l1^2 := mul_nonneg (sub_nonneg.mpr hc020) (sq_nonneg l1)
  have h002 : 0 ≤ (c002 - m) * l2^2 := mul_nonneg (sub_nonneg.mpr hc002) (sq_nonneg l2)
  have h110 : 0 ≤ 2 * (c110 - m) * l0 * l1 := by positivity
  have h101 : 0 ≤ 2 * (c101 - m) * l0 * l2 := by positivity
  have h011 : 0 ≤ 2 * (c011 - m) * l1 * l2 := by positivity
  unfold quadraticBernstein
  nlinarith

end Checkerboard
