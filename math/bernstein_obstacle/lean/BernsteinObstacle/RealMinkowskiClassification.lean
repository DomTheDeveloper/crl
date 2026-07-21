import BernsteinObstacle.MinkowskiSaturation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Real-power consistency–vanishing–codimension classification

The integer-power saturation theorem covers the regime in which the coefficient
consistency order `m` is at least the physical gap-vanishing order `q`. When
`m < q`, the risky layer has fractional thickness `h^(m/q)`, so a complete
classification requires real powers.
-/

noncomputable def realConsistencyLimitedOrder (m q : ℝ) : ℝ := min m q

noncomputable def realRiskThickness (h m q : ℝ) : ℝ :=
  h ^ (realConsistencyLimitedOrder m q / q)

noncomputable def realRepairExponent (m q c : ℝ) : ℝ :=
  realConsistencyLimitedOrder m q - 1 +
    c * realConsistencyLimitedOrder m q / (2 * q)

noncomputable def realMultiplierExponent (m q c : ℝ) : ℝ :=
  realConsistencyLimitedOrder m q / 2 +
    c * realConsistencyLimitedOrder m q / (2 * q)

noncomputable def realVIExponent (m q c : ℝ) : ℝ :=
  min (realRepairExponent m q c) (realMultiplierExponent m q c)

noncomputable def realVIRateScale (h m q c : ℝ) : ℝ :=
  h ^ realVIExponent m q c

@[simp] theorem realConsistencyLimitedOrder_eq_consistency
    (m q : ℝ) (hmq : m ≤ q) :
    realConsistencyLimitedOrder m q = m := by
  simp [realConsistencyLimitedOrder, min_eq_left hmq]

@[simp] theorem realConsistencyLimitedOrder_eq_vanishing
    (m q : ℝ) (hqm : q ≤ m) :
    realConsistencyLimitedOrder m q = q := by
  simp [realConsistencyLimitedOrder, min_eq_right hqm]

theorem realRiskThickness_of_q_le_m
    (h m q : ℝ) (hqm : q ≤ m) (hq : q ≠ 0) :
    realRiskThickness h m q = h := by
  simp [realRiskThickness,
    realConsistencyLimitedOrder_eq_vanishing m q hqm, hq]

theorem realRiskThickness_of_m_le_q
    (h m q : ℝ) (hmq : m ≤ q) :
    realRiskThickness h m q = h ^ (m / q) := by
  simp [realRiskThickness,
    realConsistencyLimitedOrder_eq_consistency m q hmq]

theorem realVIExponent_eq_classification
    (m q c : ℝ) :
    realVIExponent m q c =
      c * realConsistencyLimitedOrder m q / (2 * q) +
        min (realConsistencyLimitedOrder m q - 1)
          (realConsistencyLimitedOrder m q / 2) := by
  let a := realConsistencyLimitedOrder m q
  let t := c * a / (2 * q)
  have hmin : min (a - 1 + t) (a / 2 + t) =
      min (a - 1) (a / 2) + t := by
    by_cases h : a - 1 ≤ a / 2
    · have ht : a - 1 + t ≤ a / 2 + t := add_le_add_right h t
      rw [min_eq_left ht, min_eq_left h]
    · have hrev : a / 2 ≤ a - 1 := le_of_not_ge h
      have ht : a / 2 + t ≤ a - 1 + t := add_le_add_right hrev t
      rw [min_eq_right ht, min_eq_right hrev]
  unfold realVIExponent realRepairExponent realMultiplierExponent
  change min (a - 1 + t) (a / 2 + t) = t + min (a - 1) (a / 2)
  rw [hmin]
  ring

theorem realVIExponent_of_effectiveOrder_ge_two
    (m q c : ℝ)
    (ha : 2 ≤ realConsistencyLimitedOrder m q) :
    realVIExponent m q c =
      realConsistencyLimitedOrder m q / 2 +
        c * realConsistencyLimitedOrder m q / (2 * q) := by
  have hbase : realConsistencyLimitedOrder m q / 2 ≤
      realConsistencyLimitedOrder m q - 1 := by linarith
  have ht := add_le_add_right hbase
    (c * realConsistencyLimitedOrder m q / (2 * q))
  unfold realVIExponent realRepairExponent realMultiplierExponent
  exact min_eq_right ht

theorem realVIExponent_of_q_le_m
    (m q c : ℝ) (hqm : q ≤ m) (hq : 0 < q) (hq2 : 2 ≤ q) :
    realVIExponent m q c = (q + c) / 2 := by
  have ha : 2 ≤ realConsistencyLimitedOrder m q := by
    simpa [realConsistencyLimitedOrder_eq_vanishing m q hqm] using hq2
  rw [realVIExponent_of_effectiveOrder_ge_two m q c ha]
  rw [realConsistencyLimitedOrder_eq_vanishing m q hqm]
  field_simp [ne_of_gt hq]
  ring

theorem realVIExponent_of_m_le_q
    (m q c : ℝ) (hmq : m ≤ q) (hq : 0 < q) (hm2 : 2 ≤ m) :
    realVIExponent m q c = m / 2 * (1 + c / q) := by
  have ha : 2 ≤ realConsistencyLimitedOrder m q := by
    simpa [realConsistencyLimitedOrder_eq_consistency m q hmq] using hm2
  rw [realVIExponent_of_effectiveOrder_ge_two m q c ha]
  rw [realConsistencyLimitedOrder_eq_consistency m q hmq]
  field_simp [ne_of_gt hq]
  ring

theorem realVIRateScale_of_q_le_m
    (h m q c : ℝ) (hqm : q ≤ m) (hq : 0 < q) (hq2 : 2 ≤ q) :
    realVIRateScale h m q c = h ^ ((q + c) / 2) := by
  rw [realVIRateScale, realVIExponent_of_q_le_m m q c hqm hq hq2]

theorem realVIRateScale_of_m_le_q
    (h m q c : ℝ) (hmq : m ≤ q) (hq : 0 < q) (hm2 : 2 ≤ m) :
    realVIRateScale h m q c = h ^ (m / 2 * (1 + c / q)) := by
  rw [realVIRateScale, realVIExponent_of_m_le_q m q c hmq hq hm2]

theorem realVIExponent_quadratic_codimOne
    (m : ℝ) (hm : 2 ≤ m) :
    realVIExponent m 2 1 = (3 : ℝ) / 2 := by
  simpa using realVIExponent_of_q_le_m m 2 1 hm (by norm_num) (by norm_num)

theorem realVIRateScale_quadratic_codimOne
    (h m : ℝ) (hm : 2 ≤ m) :
    realVIRateScale h m 2 1 = h ^ ((3 : ℝ) / 2) := by
  rw [realVIRateScale, realVIExponent_quadratic_codimOne m hm]

end BernsteinObstacle
