import BernsteinObstacle.QuadraticIntegral
import BernsteinObstacle.QuadraticHingeProjection
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

noncomputable section

/-!
# Explicit flat-interface benchmark

This file formalizes the exact geometry and scalar calculations for the manufactured
obstacle solution `u(x,y) = a * (y₊)^2` on the half-cell-shifted diagonal grid.
The Euclidean element assembly is intentionally separated from these reusable facts:

* two quarter-width product prisms are contained in the two cut triangles;
* the comparison-field energy and obstacle-multiplier integrals have exact constants;
* squared lower/upper bounds imply the advertised two-sided `h^(3/2)` sandwich.
-/

/-- The upper-left triangle in the reference interface square
`[0,h] × [-h/2,h/2]`, cut by the southwest-to-northeast diagonal. -/
def flatUpperCutTriangle (h : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ h ∧ z.1 - h / 2 ≤ z.2 ∧ z.2 ≤ h / 2}

/-- The lower-right triangle in the same reference interface square. -/
def flatLowerCutTriangle (h : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ h ∧ -h / 2 ≤ z.2 ∧ z.2 ≤ z.1 - h / 2}

/-- Quarter-width prism retained in the upper-left cut triangle. -/
def flatLeftPrism (h : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ h / 4 ∧ -h / 4 ≤ z.2 ∧ z.2 ≤ h / 4}

/-- Quarter-width prism retained in the lower-right cut triangle. -/
def flatRightPrism (h : ℝ) : Set (ℝ × ℝ) :=
  {z | 3 * h / 4 ≤ z.1 ∧ z.1 ≤ h ∧ -h / 4 ≤ z.2 ∧ z.2 ≤ h / 4}

/-- The left retained product prism lies in the upper cut triangle. -/
theorem flatLeftPrism_subset_upperCutTriangle
    (h : ℝ) (hh : 0 ≤ h) :
    flatLeftPrism h ⊆ flatUpperCutTriangle h := by
  intro z hz
  rcases hz with ⟨hx0, hxh, hy0, hyh⟩
  change 0 ≤ z.1 ∧ z.1 ≤ h ∧ z.1 - h / 2 ≤ z.2 ∧ z.2 ≤ h / 2
  constructor
  · exact hx0
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The right retained product prism lies in the lower cut triangle. -/
theorem flatRightPrism_subset_lowerCutTriangle
    (h : ℝ) (hh : 0 ≤ h) :
    flatRightPrism h ⊆ flatLowerCutTriangle h := by
  intro z hz
  rcases hz with ⟨hx0, hxh, hy0, hyh⟩
  change 0 ≤ z.1 ∧ z.1 ≤ h ∧ -h / 2 ≤ z.2 ∧ z.2 ≤ z.1 - h / 2
  constructor
  · nlinarith
  constructor
  · exact hxh
  constructor <;> nlinarith

/-- Value of the explicit feasible quadratic comparison on the interface strip. -/
def flatComparisonValue (a h y : ℝ) : ℝ :=
  (a / 4) * (y + h / 2) ^ 2

/-- Derivative of the explicit strip comparison. -/
def flatComparisonDerivative (a h y : ℝ) : ℝ :=
  (a / 2) * (y + h / 2)

/-- Derivative of the exact noncontact quadratic profile. -/
def flatExactDerivative (a y : ℝ) : ℝ :=
  2 * a * y

/-- Exact comparison energy on the contact half of the strip. -/
theorem flatComparison_contact_energy (a h : ℝ) :
    (∫ y in -h / 2..0, (flatComparisonDerivative a h y) ^ 2) =
      a ^ 2 * h ^ 3 / 96 := by
  rw [show
    (fun y : ℝ => (flatComparisonDerivative a h y) ^ 2) =
      (fun y : ℝ =>
        (a ^ 2 / 4) * y ^ 2 + (a ^ 2 * h / 4) * y + a ^ 2 * h ^ 2 / 16) by
      funext y
      simp [flatComparisonDerivative]
      ring]
  rw [intervalIntegral_quadraticPolynomial]
  ring

/-- Exact comparison energy on the noncontact half of the strip. -/
theorem flatComparison_noncontact_energy (a h : ℝ) :
    (∫ y in 0..h / 2,
      (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) =
      a ^ 2 * h ^ 3 / 32 := by
  rw [show
    (fun y : ℝ =>
      (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) =
      (fun y : ℝ =>
        (9 * a ^ 2 / 4) * y ^ 2 + (-(3 * a ^ 2 * h / 4)) * y +
          a ^ 2 * h ^ 2 / 16) by
      funext y
      simp [flatExactDerivative, flatComparisonDerivative]
      ring]
  rw [intervalIntegral_quadraticPolynomial]
  ring

/-- Exact obstacle-multiplier contribution on the contact half-strip. -/
theorem flatComparison_multiplier_term (a h : ℝ) :
    (∫ y in -h / 2..0, 2 * a * flatComparisonValue a h y) =
      a ^ 2 * h ^ 3 / 48 := by
  rw [show
    (fun y : ℝ => 2 * a * flatComparisonValue a h y) =
      (fun y : ℝ =>
        (a ^ 2 / 2) * y ^ 2 + (a ^ 2 * h / 2) * y +
          a ^ 2 * h ^ 2 / 8) by
      funext y
      simp [flatComparisonValue]
      ring]
  rw [intervalIntegral_quadraticPolynomial]
  ring

/-- Exact per-unit-tangential-length comparison energy. -/
theorem flatComparison_total_energy (a h : ℝ) :
    (∫ y in -h / 2..0, (flatComparisonDerivative a h y) ^ 2) +
      (∫ y in 0..h / 2,
        (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) =
      a ^ 2 * h ^ 3 / 24 := by
  rw [flatComparison_contact_energy, flatComparison_noncontact_energy]
  ring

/-- Exact right-hand side obtained from the standard Falk comparison estimate. -/
theorem flatComparison_falk_total_per_unitWidth (a h : ℝ) :
    (∫ y in -h / 2..0, (flatComparisonDerivative a h y) ^ 2) +
      (∫ y in 0..h / 2,
        (flatExactDerivative a y - flatComparisonDerivative a h y) ^ 2) +
      2 * (∫ y in -h / 2..0, 2 * a * flatComparisonValue a h y) =
      a ^ 2 * h ^ 3 / 12 := by
  rw [flatComparison_contact_energy, flatComparison_noncontact_energy,
    flatComparison_multiplier_term]
  ring

/-- Exact sharp one-dimensional fiber constant for a centered interval of length
`h/2`. -/
theorem flatPrism_centeredFiber_constant (a h : ℝ) :
    ((4 : ℝ) / 3) * a ^ 2 * ((1 : ℝ) / 2) ^ 3 *
        (1 - (1 : ℝ) / 2) ^ 3 * (h / 2) ^ 3 =
      a ^ 2 * h ^ 3 / 384 := by
  ring

/-- The two quarter-width prisms in one interface square contribute the exact
lower constant `a² h⁴ / 768`. -/
theorem flatPrism_pair_squareContribution (a h : ℝ) :
    (h / 2) * (a ^ 2 * h ^ 3 / 384) = a ^ 2 * h ^ 4 / 768 := by
  ring

/-- Square-root transfer for the explicit deterministic benchmark constants. -/
theorem flatBenchmark_sharp_sandwich
    (a W h error : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 ≤ h) (herror : 0 ≤ error)
    (hlowerSq : a ^ 2 * W * h ^ 3 / 768 ≤ error ^ 2)
    (hupperSq : error ^ 2 ≤ a ^ 2 * W * h ^ 3 / 12) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ error ∧
      error ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hW768 : 0 ≤ W / 768 := by positivity
  have hW12 : 0 ≤ W / 12 := by positivity
  have hlowerNonneg :
      0 ≤ (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) := by
    positivity
  have hupperNonneg :
      0 ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
    positivity
  have hlowerTargetSq :
      ((a * Real.sqrt (W / 768)) * (h * Real.sqrt h)) ^ 2 =
        a ^ 2 * W * h ^ 3 / 768 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hW768, threeHalvesScale_sq h hh]
    ring
  have hupperTargetSq :
      ((a * Real.sqrt (W / 12)) * (h * Real.sqrt h)) ^ 2 =
        a ^ 2 * W * h ^ 3 / 12 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hW12, threeHalvesScale_sq h hh]
    ring
  constructor
  · nlinarith [hlowerSq]
  · nlinarith [hupperSq]

end

end BernsteinObstacle
