import BernsteinObstacle.MovingObstacleRate
import BernsteinObstacle.MinkowskiSaturation

namespace BernsteinObstacle

/-!
# Grand consistency-limited Bernstein obstacle rate

The nominal coefficient-consistency order `m` and the physical gap-vanishing
order `q` compete.  The effective repair order is `min m q`; therefore the full
moving-obstacle estimate has the scale

`h^s + h^r + h_Gamma^(min(m,q)-1) * sqrt(h_Gamma^c)`.

This exposes a structural saturation law.  For quadratic contact (`q = 2`)
across a codimension-one interface, every method with `m >= 2` has the same
unfitted positive-basis repair barrier `h_Gamma^(3/2)`, regardless of higher
bulk polynomial order.
-/

/-- Grand rate with obstacle approximation order, bulk order, coefficient
consistency order, physical vanishing order, and defect codimension. -/
theorem grandSharpRate_of_consistencyLimitedComponents
    (e alpha P A B h g : ℝ) (s r m q c : ℕ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * g ^ (2 * (consistencyLimitedOrder m q - 1) + c)) :
    e ≤ Real.sqrt (max P (max A B) / alpha) *
      (h ^ s + h ^ r +
        consistencyVanishingCodimensionScale g m q c) := by
  simpa [consistencyVanishingCodimensionScale] using
    grandSharpRate_of_movingObstacle_components
      e alpha P A B h g s r (consistencyLimitedOrder m q) c
      he halpha hP hA hB hh hg henergy

/-- Quadratic-contact saturation inside the full moving-obstacle estimate.
Once coefficient consistency reaches order two, the codimension-one defect term
is exactly `g * sqrt g`; increasing `m` cannot improve this unfitted clipping
exponent. -/
theorem grandSharpRate_quadraticContact_saturation
    (e alpha P A B h g : ℝ) (s r m : ℕ)
    (hm : 2 ≤ m)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) + B * g ^ 3) :
    e ≤ Real.sqrt (max P (max A B) / alpha) *
      (h ^ s + h ^ r + g * Real.sqrt g) := by
  have henergy' :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * g ^ (2 * (consistencyLimitedOrder m 2 - 1) + 1) := by
    rw [consistencyLimitedOrder_eq_vanishingOrder m 2 hm]
    simpa using henergy
  have hbase :=
    grandSharpRate_of_consistencyLimitedComponents
      e alpha P A B h g s r m 2 1
      he halpha hP hA hB hh hg henergy'
  rw [consistencyVanishingCodimensionScale_of_q_le_m g m 2 1 hm,
    vanishingCodimensionScale_quadratic_codimOne] at hbase
  exact hbase

end BernsteinObstacle
