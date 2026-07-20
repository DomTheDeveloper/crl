import BernsteinObstacle.MovingObstacleRate
import BernsteinObstacle.MinkowskiSaturation

namespace BernsteinObstacle

/-!
# Grand Bernstein obstacle rate in the saturation regime

The same mesh scale may be used for repair amplitude and patch thickness when
coefficient consistency reaches the physical vanishing order, `q ≤ m`.
-/

theorem grandSharpRate_of_consistencyLimitedComponents
    (e alpha P A B h g : ℝ) (s r m q c : ℕ)
    (hqm : q ≤ m)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * g ^ (2 * (q - 1) + c)) :
    e ≤ Real.sqrt (max P (max A B) / alpha) *
      (h ^ s + h ^ r +
        consistencyVanishingCodimensionScale g m q c) := by
  have hbase :=
    grandSharpRate_of_movingObstacle_components
      e alpha P A B h g s r q c
      he halpha hP hA hB hh hg henergy
  rw [consistencyVanishingCodimensionScale_of_q_le_m g m q c hqm]
  exact hbase

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
          B * g ^ (2 * (2 - 1) + 1) := by
    simpa using henergy
  have hbase :=
    grandSharpRate_of_consistencyLimitedComponents
      e alpha P A B h g s r m 2 1 hm
      he halpha hP hA hB hh hg henergy'
  rw [consistencyVanishingCodimensionScale_of_q_le_m g m 2 1 hm,
    vanishingCodimensionScale_quadratic_codimOne] at hbase
  exact hbase

end BernsteinObstacle
