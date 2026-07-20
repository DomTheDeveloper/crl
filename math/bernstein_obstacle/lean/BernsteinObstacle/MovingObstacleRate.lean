import BernsteinObstacle.MovingObstacleConvergence
import BernsteinObstacle.MinkowskiRate
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Moving-obstacle, vanishing-order, and codimension rate law

The exact-obstacle `h^r + h_Gamma^(3/2)` theorem is one specialization of a
three-scale estimate.  If the obstacle itself is approximated with order `s`,
the smooth bulk field has order `r`, and the active-set repair has vanishing
order `q` near a codimension-`c` defect set, then the natural norm scale is

`h^s + h^r + h_Gamma^(q-1) * sqrt (h_Gamma^c)`.

For an exact obstacle the first term vanishes.  For quadratic contact across a
hypersurface, `q = 2` and `c = 1`, recovering `h^r + h_Gamma^(3/2)`.
-/

section MovingObstacleRate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translating a zero-obstacle recovery by an approximated obstacle adds only
the obstacle approximation error. -/
theorem movingObstacleRecoveryRate
    (psi psi_h z z_h : E)
    (P A B h g : ℝ) (s r q c : ℕ)
    (hpsi : ‖psi - psi_h‖ ≤ P * h ^ s)
    (hzero :
      ‖z - z_h‖ ≤
        A * h ^ r + B * vanishingCodimensionScale g q c) :
    ‖(psi + z) - (psi_h + z_h)‖ ≤
      P * h ^ s + A * h ^ r +
        B * vanishingCodimensionScale g q c := by
  have htriangle :
      ‖(psi + z) - (psi_h + z_h)‖ ≤
        ‖psi - psi_h‖ + ‖z - z_h‖ := by
    calc
      ‖(psi + z) - (psi_h + z_h)‖ =
          ‖(psi - psi_h) + (z - z_h)‖ := by
            congr 1
            abel
      _ ≤ ‖psi - psi_h‖ + ‖z - z_h‖ := norm_add_le _ _
  calc
    ‖(psi + z) - (psi_h + z_h)‖ ≤
        ‖psi - psi_h‖ + ‖z - z_h‖ := htriangle
    _ ≤ P * h ^ s +
        (A * h ^ r + B * vanishingCodimensionScale g q c) :=
      add_le_add hpsi hzero
    _ = P * h ^ s + A * h ^ r +
        B * vanishingCodimensionScale g q c := by ring

/-- Abstract coercive three-component square-root transfer. -/
theorem sharpRate_of_three_components
    (e alpha P A B a b d : ℝ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (henergy :
      alpha * e ^ 2 ≤ P * a ^ 2 + A * b ^ 2 + B * d ^ 2) :
    e ≤ Real.sqrt (max P (max A B) / alpha) * (a + b + d) := by
  let M : ℝ := max P (max A B)
  have hPM : P ≤ M := by
    exact le_max_left P (max A B)
  have hAM : A ≤ M := by
    exact (le_max_left A B).trans (le_max_right P (max A B))
  have hBM : B ≤ M := by
    exact (le_max_right A B).trans (le_max_right P (max A B))
  have hM : 0 ≤ M := hP.trans hPM
  have hweighted :
      P * a ^ 2 + A * b ^ 2 + B * d ^ 2 ≤
        M * (a ^ 2 + b ^ 2 + d ^ 2) := by
    calc
      P * a ^ 2 + A * b ^ 2 + B * d ^ 2 ≤
          M * a ^ 2 + M * b ^ 2 + M * d ^ 2 := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hPM (sq_nonneg a))
            (mul_le_mul_of_nonneg_right hAM (sq_nonneg b)))
          (mul_le_mul_of_nonneg_right hBM (sq_nonneg d))
      _ = M * (a ^ 2 + b ^ 2 + d ^ 2) := by ring
  have hsquares :
      a ^ 2 + b ^ 2 + d ^ 2 ≤ (a + b + d) ^ 2 := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hd, mul_nonneg hb hd]
  have hcoercive :
      alpha * e ^ 2 ≤ M * (a + b + d) ^ 2 := by
    calc
      alpha * e ^ 2 ≤ P * a ^ 2 + A * b ^ 2 + B * d ^ 2 := henergy
      _ ≤ M * (a ^ 2 + b ^ 2 + d ^ 2) := hweighted
      _ ≤ M * (a + b + d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquares hM
  have hdiv :
      e ^ 2 ≤ (M / alpha) * (a + b + d) ^ 2 := by
    have htmp : e ^ 2 ≤ (M * (a + b + d) ^ 2) / alpha := by
      apply (le_div_iff₀ halpha).2
      simpa [mul_comm] using hcoercive
    calc
      e ^ 2 ≤ (M * (a + b + d) ^ 2) / alpha := htmp
      _ = (M / alpha) * (a + b + d) ^ 2 := by ring
  have hratio : 0 ≤ M / alpha := div_nonneg hM (le_of_lt halpha)
  have hsqrtSq : (Real.sqrt (M / alpha)) ^ 2 = M / alpha :=
    Real.sq_sqrt hratio
  have hrhsNonneg :
      0 ≤ Real.sqrt (M / alpha) * (a + b + d) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg ha hb) hd)
  have hsquareBound :
      e ^ 2 ≤ (Real.sqrt (M / alpha) * (a + b + d)) ^ 2 := by
    calc
      e ^ 2 ≤ (M / alpha) * (a + b + d) ^ 2 := hdiv
      _ = (Real.sqrt (M / alpha) * (a + b + d)) ^ 2 := by
        rw [mul_pow, hsqrtSq]
  have hfinal : e ≤ Real.sqrt (M / alpha) * (a + b + d) := by
    nlinarith
  simpa [M] using hfinal

/-- Grand sharp-rate law with obstacle approximation, bulk approximation, and a
vanishing-order/codimension defect repair. -/
theorem grandSharpRate_of_movingObstacle_components
    (e alpha P A B h g : ℝ) (s r q c : ℕ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * g ^ (2 * (q - 1) + c)) :
    e ≤ Real.sqrt (max P (max A B) / alpha) *
      (h ^ s + h ^ r + vanishingCodimensionScale g q c) := by
  have hs : h ^ (2 * s) = (h ^ s) ^ 2 :=
    (bulkScale_sq h s).symm
  have hr : h ^ (2 * r) = (h ^ r) ^ 2 :=
    (bulkScale_sq h r).symm
  have hdefect :
      g ^ (2 * (q - 1) + c) =
        (vanishingCodimensionScale g q c) ^ 2 :=
    (vanishingCodimensionScale_sq g q c hg).symm
  apply sharpRate_of_three_components
    e alpha P A B (h ^ s) (h ^ r)
      (vanishingCodimensionScale g q c)
      he halpha hP hA hB
  · exact pow_nonneg hh _
  · exact pow_nonneg hh _
  · exact vanishingCodimensionScale_nonneg g q c hg
  · simpa [hs, hr, hdefect] using henergy

/-- Exact obstacle and a quadratic codimension-one contact interface recover the
original two-term Bernstein obstacle rate exactly. -/
theorem grandSharpRate_exactObstacle_quadratic_codimOne
    (e alpha A B h g : ℝ) (r : ℕ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤ A * h ^ (2 * r) + B * g ^ 3) :
    e ≤ Real.sqrt (max A B / alpha) *
      (h ^ r + g * Real.sqrt g) := by
  have henergy' :
      alpha * e ^ 2 ≤
        A * h ^ (2 * r) + B * g ^ (2 * (2 - 1) + 1) := by
    simpa using henergy
  simpa [vanishingCodimensionScale_quadratic_codimOne] using
    sharpRate_of_vanishingCodimension_components
      e alpha A B h g r 2 1
      he halpha hA hB hh hg henergy'

end MovingObstacleRate

end BernsteinObstacle
