import BernsteinObstacle.SmoothQuadraticSaturation
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Corrected recovery and contact-aware alignment

This file supplies the abstract rate-transfer theorem behind the corrected
estimate `h^p + η_h`, together with an exact aligned-contact construction.
The construction uses the canonical Bernstein coefficients of `t^2`, which are
nonnegative in every degree `p ≥ 2`.
-/

section AbstractRepair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convex repair of an unconstrained approximation `v` toward a feasible
anchor `z`. -/
def convexRepair (ε : ℝ) (v z : E) : E :=
  (1 - ε) • v + ε • z

/-- The repair is the base approximation plus a scaled correction. -/
theorem convexRepair_eq_base_add (ε : ℝ) (v z : E) :
    convexRepair ε v z = v + ε • (z - v) := by
  unfold convexRepair
  module

/-- Abstract corrected recovery estimate. -/
theorem convexRepair_error_bound
    (u v z : E) (ε : ℝ) :
    ‖u - convexRepair ε v z‖ ≤
      ‖u - v‖ + |ε| * ‖z - v‖ := by
  rw [convexRepair_eq_base_add]
  have hid : u - (v + ε • (z - v)) = (u - v) - ε • (z - v) := by
    module
  rw [hid]
  calc
    ‖(u - v) - ε • (z - v)‖ ≤ ‖u - v‖ + ‖ε • (z - v)‖ := norm_sub_le _ _
    _ = ‖u - v‖ + |ε| * ‖z - v‖ := by
      rw [norm_smul, Real.norm_eq_abs]

/-- If interpolation contributes `A h^p` and coefficient repair contributes
`η D`, then the repaired approximation has the sum of those errors. -/
theorem correctedRecovery_error_bound
    (u v z : E) (ε A h η D : ℝ) (p : ℕ)
    (hInterp : ‖u - v‖ ≤ A * h ^ p)
    (hWeight : |ε| ≤ η)
    (hAnchor : ‖z - v‖ ≤ D)
    (hη : 0 ≤ η) :
    ‖u - convexRepair ε v z‖ ≤ A * h ^ p + η * D := by
  have hprod : |ε| * ‖z - v‖ ≤ η * D :=
    mul_le_mul hWeight hAnchor (norm_nonneg _) hη
  calc
    ‖u - convexRepair ε v z‖ ≤ ‖u - v‖ + |ε| * ‖z - v‖ :=
      convexRepair_error_bound u v z ε
    _ ≤ A * h ^ p + η * D := add_le_add hInterp hprod

/-- Second-order coefficient repair yields the corrected `h^p + h^2` bound. -/
theorem correctedRecovery_secondOrder_bound
    (u v z : E) (ε A B D h : ℝ) (p : ℕ)
    (hInterp : ‖u - v‖ ≤ A * h ^ p)
    (hWeight : |ε| ≤ B * h ^ 2)
    (hAnchor : ‖z - v‖ ≤ D)
    (hB : 0 ≤ B) (hh : 0 ≤ h) :
    ‖u - convexRepair ε v z‖ ≤ A * h ^ p + (B * D) * h ^ 2 := by
  have hη : 0 ≤ B * h ^ 2 := mul_nonneg hB (sq_nonneg h)
  have hbase := correctedRecovery_error_bound
    u v z ε A h (B * h ^ 2) D p hInterp hWeight hAnchor hη
  calc
    ‖u - convexRepair ε v z‖ ≤ A * h ^ p + (B * h ^ 2) * D := hbase
    _ = A * h ^ p + (B * D) * h ^ 2 := by ring

end AbstractRepair

section CoefficientRepair

variable {ι : Type*}

/-- Apply the scalar inward repair coefficientwise. -/
def inwardRepairCoefficients (d : ℝ) (c : ι → ℝ) : ι → ℝ :=
  fun i => inwardBlend d (c i)

/-- Coefficientwise repair maps the enlarged box `[-d,1]` into `[0,1]`. -/
theorem inwardRepairCoefficients_mem_Icc
    (d : ℝ) (c : ι → ℝ) (hd : 0 ≤ d)
    (hc : ∀ i, c i ∈ Set.Icc (-d) 1) :
    ∀ i, inwardRepairCoefficients d c i ∈ Set.Icc 0 1 := by
  intro i
  exact inwardBlend_mem_Icc d (c i) hd (hc i)

/-- Coefficients already equal to the feasible anchor `1` are fixed exactly. -/
theorem inwardRepairCoefficients_eq_one
    (d : ℝ) (c : ι → ℝ) (i : ι) (hi : c i = 1) :
    inwardRepairCoefficients d c i = 1 := by
  simp [inwardRepairCoefficients, inwardBlend, inwardRepairWeight, hi]

end CoefficientRepair

section AlignedContact

/-- Canonical coefficients of the aligned quadratic profile `a h² t²`. -/
def alignedQuadraticCoeff (p : ℕ) (a h : ℝ) (k : ℕ) : ℝ :=
  a * h ^ 2 * quadraticMonomialCoeff p k

/-- The monomial coefficients are nonnegative in every degree `p ≥ 2`. -/
theorem quadraticMonomialCoeff_nonneg
    (p k : ℕ) (hp : 2 ≤ p) :
    0 ≤ quadraticMonomialCoeff p k := by
  unfold quadraticMonomialCoeff
  exact div_nonneg (by positivity) (quadraticMomentDenominator_pos p hp).le

/-- Aligned quadratic-contact coefficients are nonnegative. -/
theorem alignedQuadraticCoeff_nonneg
    (p k : ℕ) (a h : ℝ) (hp : 2 ≤ p) (ha : 0 ≤ a) :
    0 ≤ alignedQuadraticCoeff p a h k := by
  unfold alignedQuadraticCoeff
  exact mul_nonneg (mul_nonneg ha (sq_nonneg h))
    (quadraticMonomialCoeff_nonneg p k hp)

/-- Exact representation of an aligned quadratic contact profile. -/
theorem alignedQuadraticContact_exact
    (p : ℕ) (hp : 2 ≤ p) (a h t : ℝ) :
    curve p (alignedQuadraticCoeff p a h) t = a * (h * t) ^ 2 := by
  unfold curve alignedQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        (a * h ^ 2 * quadraticMonomialCoeff p k) * basis p k t) =
        (a * h ^ 2) *
          ∑ k ∈ Finset.range (p + 1),
            quadraticMonomialCoeff p k * basis p k t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (a * h ^ 2) * t ^ 2 := by
      rw [quadraticMonomial_eq_bernsteinCurve p hp t]
    _ = a * (h * t) ^ 2 := by ring

/-- Inserting the contact point as a vertex eliminates the quadratic
coefficient obstruction on each adjacent element: the exact target is already
coefficient-feasible. -/
theorem alignedQuadraticContact_exact_and_nonnegative
    (p : ℕ) (hp : 2 ≤ p) (a h : ℝ) (ha : 0 ≤ a) :
    (∀ k, 0 ≤ alignedQuadraticCoeff p a h k) ∧
      (∀ t, curve p (alignedQuadraticCoeff p a h) t = a * (h * t) ^ 2) := by
  constructor
  · intro k
    exact alignedQuadraticCoeff_nonneg p k a h hp ha
  · intro t
    exact alignedQuadraticContact_exact p hp a h t

end AlignedContact

end

end BernsteinObstacle
