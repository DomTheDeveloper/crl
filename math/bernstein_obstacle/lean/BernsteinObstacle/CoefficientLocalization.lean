import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Coefficient-error localization and stable inversion

These elementary but decisive estimates isolate the exact analytical input of
the free-boundary argument.  An `O(h^2)` coefficient-to-value error prevents a
negative coefficient wherever the true lattice value dominates that error.
A uniformly bounded inverse collocation operator transfers `O(h^2)` lattice
values to `O(h^2)` Bernstein coefficients on interface elements.
-/

/-- If a coefficient differs from a nonnegative lattice value by at most
`err`, and the value is at least `err`, then the coefficient is nonnegative. -/
theorem coefficient_nonneg_of_abs_sub_le
    (b v err : ℝ) (herror : |b - v| ≤ err) (hvalue : err ≤ v) :
    0 ≤ b := by
  have hlower : -err ≤ b - v := (abs_le.mp herror).1
  linarith

/-- Contrapositive localization form: a negative coefficient can occur only
where the true lattice value is smaller than the coefficient error. -/
theorem value_lt_error_of_coefficient_neg
    (b v err : ℝ) (herror : |b - v| ≤ err) (hb : b < 0) :
    v < err := by
  have hlower : -err ≤ b - v := (abs_le.mp herror).1
  linarith

/-- A two-sided value bound plus a coefficient-to-value error bound gives a
two-sided coefficient bound. -/
theorem abs_coefficient_le_valueBound_add_error
    (b v valueBound err : ℝ)
    (herror : |b - v| ≤ err) (hvalue : |v| ≤ valueBound) :
    |b| ≤ valueBound + err := by
  calc
    |b| = |(b - v) + v| := by ring_nf
    _ ≤ |b - v| + |v| := abs_add _ _
    _ ≤ err + valueBound := add_le_add herror hvalue
    _ = valueBound + err := by ring

/-- If both the nodal value and coefficient error are `O(h^2)`, then the
coefficient is `O(h^2)` with the sum of the constants. -/
theorem abs_coefficient_le_quadratic_scale
    (b v valueConstant errorConstant h : ℝ)
    (hvalueConstant : 0 ≤ valueConstant)
    (herrorConstant : 0 ≤ errorConstant)
    (hh : 0 ≤ h)
    (herror : |b - v| ≤ errorConstant * h ^ 2)
    (hvalue : |v| ≤ valueConstant * h ^ 2) :
    |b| ≤ (valueConstant + errorConstant) * h ^ 2 := by
  have hbase := abs_coefficient_le_valueBound_add_error
    b v (valueConstant * h ^ 2) (errorConstant * h ^ 2)
    herror hvalue
  calc
    |b| ≤ valueConstant * h ^ 2 + errorConstant * h ^ 2 := hbase
    _ = (valueConstant + errorConstant) * h ^ 2 := by ring

section StableInverse

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A bounded inverse collocation operator transfers a quadratic-scale bound
on lattice data to the same quadratic scale on Bernstein coefficients. -/
theorem stableInverse_quadratic_norm_bound
    (L : V →L[ℝ] W) (v : V) (M h : ℝ)
    (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hv : ‖v‖ ≤ M * h ^ 2) :
    ‖L v‖ ≤ ‖L‖ * M * h ^ 2 := by
  calc
    ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
    _ ≤ ‖L‖ * (M * h ^ 2) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg L)
    _ = ‖L‖ * M * h ^ 2 := by ring

end StableInverse

end BernsteinObstacle
