import BernsteinObstacle.Core
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Smooth quadratic contact: fixed-degree Bernstein-cone saturation

This file begins the formal core of the smooth-contact counterexample.  Unlike the
half-quadratic hinge, the target `(x - 1/2)^2` is an analytic polynomial and is
represented exactly by the unconstrained cubic space.  Its canonical cubic
Bernstein coefficients nevertheless contain two negative entries.

The file is intentionally not imported by `BernsteinObstacle.lean` until it has
passed the pinned project checker and an axiom audit.
-/

/-- Canonical cubic Bernstein coefficients of `(x - 1/2)^2`. -/
def centeredQuadraticCubicCoeff : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => -(1 / 12)
  | 2 => -(1 / 12)
  | 3 => 1 / 4
  | _ => 0

@[simp] theorem centeredQuadraticCubicCoeff_zero :
    centeredQuadraticCubicCoeff 0 = 1 / 4 := rfl

@[simp] theorem centeredQuadraticCubicCoeff_one :
    centeredQuadraticCubicCoeff 1 = -(1 / 12) := rfl

@[simp] theorem centeredQuadraticCubicCoeff_two :
    centeredQuadraticCubicCoeff 2 = -(1 / 12) := rfl

@[simp] theorem centeredQuadraticCubicCoeff_three :
    centeredQuadraticCubicCoeff 3 = 1 / 4 := rfl

/-- Exact cubic Bernstein representation of the centered quadratic. -/
theorem centeredQuadratic_eq_cubicBernsteinCurve (x : ℝ) :
    curve 3 centeredQuadraticCubicCoeff x = (x - 1 / 2) ^ 2 := by
  simp [curve, basis, centeredQuadraticCubicCoeff, Finset.sum_range_succ]
  ring

/-- The first interior cubic coefficient is strictly negative. -/
theorem centeredQuadraticCubicCoeff_one_neg :
    centeredQuadraticCubicCoeff 1 < 0 := by
  norm_num [centeredQuadraticCubicCoeff]

/-- The second interior cubic coefficient is strictly negative. -/
theorem centeredQuadraticCubicCoeff_two_neg :
    centeredQuadraticCubicCoeff 2 < 0 := by
  norm_num [centeredQuadraticCubicCoeff]

/-- The canonical coefficient vector cannot satisfy coefficient nonnegativity. -/
theorem centeredQuadraticCubicCoeff_not_nonnegative :
    ¬ (∀ k ∈ Finset.range 4, 0 ≤ centeredQuadraticCubicCoeff k) := by
  intro h
  have h1 := h 1 (by norm_num)
  linarith [centeredQuadraticCubicCoeff_one_neg]

/-- The physical central-cell scaling. -/
def cubicCenteredDefect (h : ℝ) : ℝ := h ^ 2 / 12

/-- Convex inward-repair weight for a coefficient defect `d`. -/
def inwardRepairWeight (d : ℝ) : ℝ := d / (1 + d)

/-- The inward convex blend sends the worst coefficient `-d` exactly to zero. -/
theorem inwardRepairWeight_repairs_minimum
    (d : ℝ) (hd : 0 ≤ d) :
    (1 - inwardRepairWeight d) * (-d) + inwardRepairWeight d = 0 := by
  have hden : 1 + d ≠ 0 := by positivity
  unfold inwardRepairWeight
  field_simp [hden]
  ring

/-- For a physical cell of width `h`, the cubic coefficient defect is nonnegative. -/
theorem cubicCenteredDefect_nonneg (h : ℝ) :
    0 ≤ cubicCenteredDefect h := by
  positivity

/-- The explicit repair weight cancels the negative physical cubic coefficient. -/
theorem cubicCenteredRepair_exact (h : ℝ) :
    (1 - inwardRepairWeight (cubicCenteredDefect h)) *
          (-cubicCenteredDefect h) +
        inwardRepairWeight (cubicCenteredDefect h) = 0 := by
  exact inwardRepairWeight_repairs_minimum
    (cubicCenteredDefect h) (cubicCenteredDefect_nonneg h)

end

end BernsteinObstacle
