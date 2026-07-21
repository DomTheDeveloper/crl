import BernsteinObstacle.MinkowskiRate
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Consistency-limited vanishing order and quadratic-contact saturation

The coefficient repair amplitude is controlled by both coefficient consistency
order `m` and physical gap vanishing order `q`; the effective order is `min m q`.
-/

def consistencyLimitedOrder (m q : ℕ) : ℕ := min m q

theorem consistencyLimitedOrder_eq_vanishingOrder
    (m q : ℕ) (hqm : q ≤ m) :
    consistencyLimitedOrder m q = q := by
  simp [consistencyLimitedOrder, Nat.min_eq_right hqm]

def consistencyVanishingCodimensionScale
    (h : ℝ) (m q c : ℕ) : ℝ :=
  vanishingCodimensionScale h (consistencyLimitedOrder m q) c

theorem consistencyVanishingCodimensionScale_of_q_le_m
    (h : ℝ) (m q c : ℕ) (hqm : q ≤ m) :
    consistencyVanishingCodimensionScale h m q c =
      vanishingCodimensionScale h q c := by
  simp [consistencyVanishingCodimensionScale,
    consistencyLimitedOrder_eq_vanishingOrder m q hqm]

theorem quadraticContact_codimOne_saturation
    (h : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    consistencyVanishingCodimensionScale h m 2 1 =
      h * Real.sqrt h := by
  rw [consistencyVanishingCodimensionScale_of_q_le_m h m 2 1 hm]
  exact vanishingCodimensionScale_quadratic_codimOne h

def phaseLockedQuadraticMiddleCoefficient (h theta : ℝ) : ℝ :=
  -((1 : ℝ) / 2) * (1 - theta) ^ 2 * h ^ 2

theorem phaseLockedQuadraticMiddleCoefficient_neg
    (h theta : ℝ) (hh : 0 < h) (htheta : theta < 1) :
    phaseLockedQuadraticMiddleCoefficient h theta < 0 := by
  have hgap : 0 < 1 - theta := sub_pos.mpr htheta
  have hgapSq : 0 < (1 - theta) ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt hgap)
  have hhSq : 0 < h ^ 2 := sq_pos_of_ne_zero (ne_of_gt hh)
  have hprod : 0 < (1 - theta) ^ 2 * h ^ 2 := mul_pos hgapSq hhSq
  unfold phaseLockedQuadraticMiddleCoefficient
  nlinarith

def phaseLockedQuadraticCorrection (h theta x : ℝ) : ℝ :=
  (1 - theta) ^ 2 * x * (h - x)

theorem phaseLockedQuadraticCorrection_slope_identity
    (h theta x : ℝ) :
    (1 - theta) ^ 2 * (h - 2 * x) =
      (1 - theta) ^ 2 * (h - x) - (1 - theta) ^ 2 * x := by
  ring

end

end BernsteinObstacle
