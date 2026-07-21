import BernsteinObstacle.Core
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Smooth quadratic contact: fixed-degree Bernstein-cone saturation

The target `(x - 1/2)^2` is analytic and belongs exactly to every polynomial
space of degree at least two.  Nevertheless, its degree-`p` Bernstein
coefficient vector has a strictly negative central entry.  This file isolates
that coefficient-cone obstruction from the lower-regularity half-quadratic
hinge obstruction.
-/

/-- Casted falling-factorial identity used by the Bernstein second moment. -/
@[simp] theorem natCast_mul_pred (n : ℕ) :
    (((n * (n - 1) : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n with
  | zero => norm_num
  | succ n => simp [Nat.cast_succ]

/-- The denominator in the degree-`p` quadratic Bernstein coefficients. -/
def quadraticMomentDenominator (p : ℕ) : ℝ :=
  ((p * (p - 1) : ℕ) : ℝ)

/-- The degree-`p` Bernstein coefficient of the monomial `x^2`. -/
def quadraticMonomialCoeff (p k : ℕ) : ℝ :=
  ((k * (k - 1) : ℕ) : ℝ) / quadraticMomentDenominator p

/-- The degree-`p` Bernstein coefficient of `(x - 1/2)^2`. -/
def centeredQuadraticCoeff (p k : ℕ) : ℝ :=
  quadraticMonomialCoeff p k - (k : ℝ) / (p : ℝ) + 1 / 4

/-- For `p ≥ 2`, the quadratic moment denominator is positive. -/
theorem quadraticMomentDenominator_pos (p : ℕ) (hp : 2 ≤ p) :
    0 < quadraticMomentDenominator p := by
  unfold quadraticMomentDenominator
  exact_mod_cast Nat.mul_pos (by omega : 0 < p) (by omega : 0 < p - 1)

/-- First Bernstein moment on the unit interval. -/
theorem basis_firstMoment (p : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (p + 1), (k : ℝ) * basis p k x) = (p : ℝ) * x := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ p)
  rw [Polynomial.eval_finsetSum] at h
  simpa [basis_eq_eval, nsmul_eq_mul] using h

/-- Second factorial Bernstein moment on the unit interval. -/
theorem basis_secondFactorialMoment (p : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (p + 1),
        ((k * (k - 1) : ℕ) : ℝ) * basis p k x) =
      quadraticMomentDenominator p * x ^ 2 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_mul_smul ℝ p)
  rw [Polynomial.eval_finsetSum] at h
  simpa [basis_eq_eval, nsmul_eq_mul, quadraticMomentDenominator] using h

/-- Every degree at least two reproduces the monomial `x^2` with the canonical
quadratic Bernstein coefficients. -/
theorem quadraticMonomial_eq_bernsteinCurve
    (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    curve p (quadraticMonomialCoeff p) x = x ^ 2 := by
  have hDpos := quadraticMomentDenominator_pos p hp
  have hD : quadraticMomentDenominator p ≠ 0 := ne_of_gt hDpos
  have h2 := basis_secondFactorialMoment p x
  unfold curve quadraticMonomialCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        (((k * (k - 1) : ℕ) : ℝ) / quadraticMomentDenominator p) * basis p k x) =
        (1 / quadraticMomentDenominator p) *
          ∑ k ∈ Finset.range (p + 1),
            ((k * (k - 1) : ℕ) : ℝ) * basis p k x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (1 / quadraticMomentDenominator p) *
          (quadraticMomentDenominator p * x ^ 2) := by rw [h2]
    _ = x ^ 2 := by field_simp [hD]

/-- Every degree at least two reproduces the analytic centered quadratic. -/
theorem centeredQuadratic_eq_bernsteinCurve
    (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    curve p (centeredQuadraticCoeff p) x = (x - 1 / 2) ^ 2 := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hDpos := quadraticMomentDenominator_pos p hp
  have hD : quadraticMomentDenominator p ≠ 0 := ne_of_gt hDpos
  have h0 := basis_sum_eq_one p x
  have h1 := basis_firstMoment p x
  have h2 := basis_secondFactorialMoment p x
  unfold curve centeredQuadraticCoeff quadraticMonomialCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        ((((k * (k - 1) : ℕ) : ℝ) / quadraticMomentDenominator p -
          (k : ℝ) / (p : ℝ) + 1 / 4) * basis p k x)) =
        (1 / quadraticMomentDenominator p) *
            ∑ k ∈ Finset.range (p + 1),
              ((k * (k - 1) : ℕ) : ℝ) * basis p k x -
          (1 / (p : ℝ)) *
            ∑ k ∈ Finset.range (p + 1), (k : ℝ) * basis p k x +
          (1 / 4) *
            ∑ k ∈ Finset.range (p + 1), basis p k x := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (1 / quadraticMomentDenominator p) *
          (quadraticMomentDenominator p * x ^ 2) -
          (1 / (p : ℝ)) * ((p : ℝ) * x) + (1 / 4) * 1 := by
      rw [h2, h1, h0]
    _ = (x - 1 / 2) ^ 2 := by
      field_simp [hD, hpR]
      ring

/-- Exact central coefficient for an even degree `p = 2m`. -/
theorem centeredQuadraticCoeff_even_center
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m) m =
      -1 / (4 * (((2 * m : ℕ) : ℝ) - 1)) := by
  have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have htwoM : 2 * (m : ℝ) ≠ 0 := by positivity
  have hpred : 2 * (m : ℝ) - 1 ≠ 0 := by nlinarith
  unfold centeredQuadraticCoeff quadraticMonomialCoeff quadraticMomentDenominator
  rw [natCast_mul_pred m, natCast_mul_pred (2 * m)]
  push_cast
  field_simp [htwoM, hpred]
  ring

/-- The even-degree central coefficient is strictly negative. -/
theorem centeredQuadraticCoeff_even_center_neg
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m) m < 0 := by
  rw [centeredQuadraticCoeff_even_center m hm]
  have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 4 * (((2 * m : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- Exact central coefficient for an odd degree `p = 2m+1`. -/
theorem centeredQuadraticCoeff_odd_center
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m + 1) m =
      -1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  have hpred : 2 * (m : ℝ) ≠ 0 := by positivity
  unfold centeredQuadraticCoeff quadraticMonomialCoeff quadraticMomentDenominator
  rw [natCast_mul_pred m, natCast_mul_pred (2 * m + 1)]
  push_cast
  field_simp [hp, hpred]
  ring

/-- The odd-degree central coefficient is strictly negative. -/
theorem centeredQuadraticCoeff_odd_center_neg
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m + 1) m < 0 := by
  rw [centeredQuadraticCoeff_odd_center m hm]
  have hden : 0 < 4 * ((2 * m + 1 : ℕ) : ℝ) := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) hden

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

/-- The canonical coefficient vector cannot satisfy coefficient nonnegativity. -/
theorem centeredQuadraticCubicCoeff_not_nonnegative :
    ¬ (∀ k ∈ Finset.range 4, 0 ≤ centeredQuadraticCubicCoeff k) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num [centeredQuadraticCubicCoeff] at h1

/-- A coefficient defect forces a norm error through any bounded coefficient
functional. -/
theorem coefficientDefect_le_opNorm_mul_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (e : E) (d : ℝ)
    (hdefect : d ≤ |L e|) :
    d ≤ ‖L‖ * ‖e‖ := by
  calc
    d ≤ |L e| := hdefect
    _ = ‖L e‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖e‖ := L.le_opNorm e

/-- Division form of the coefficient-functional lower bound. -/
theorem coefficientDefect_div_opNorm_le_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (e : E) (d : ℝ)
    (hL : 0 < ‖L‖) (hdefect : d ≤ |L e|) :
    d / ‖L‖ ≤ ‖e‖ := by
  apply (div_le_iff₀ hL).2
  simpa [mul_comm] using coefficientDefect_le_opNorm_mul_norm L e d hdefect

/-- Convex inward-repair weight for a coefficient defect `d`. -/
def inwardRepairWeight (d : ℝ) : ℝ := d / (1 + d)

/-- Scalar inward blend toward the feasible anchor `1`. -/
def inwardBlend (d a : ℝ) : ℝ :=
  (1 - inwardRepairWeight d) * a + inwardRepairWeight d

/-- The inward blend has a useful closed form. -/
theorem inwardBlend_eq (d a : ℝ) (hd : 0 ≤ d) :
    inwardBlend d a = (a + d) / (1 + d) := by
  have hden : 1 + d ≠ 0 := by positivity
  unfold inwardBlend inwardRepairWeight
  field_simp [hden]
  ring

/-- Blending every coefficient in `[-d,1]` toward `1` repairs the lower bound
without violating the upper bound. -/
theorem inwardBlend_mem_Icc
    (d a : ℝ) (hd : 0 ≤ d) (ha : a ∈ Set.Icc (-d) 1) :
    inwardBlend d a ∈ Set.Icc 0 1 := by
  rw [inwardBlend_eq d a hd]
  have hden : 0 < 1 + d := by positivity
  constructor
  · exact div_nonneg (by linarith [ha.1]) hden.le
  · apply (div_le_iff₀ hden).2
    linarith [ha.2]

/-- The blend changes a scalar coefficient by exactly the repair weight times
its distance from the anchor. -/
theorem inwardBlend_sub (d a : ℝ) :
    inwardBlend d a - a = inwardRepairWeight d * (1 - a) := by
  unfold inwardBlend
  ring

/-- The repair weight is bounded by the raw defect. -/
theorem inwardRepairWeight_le_defect (d : ℝ) (hd : 0 ≤ d) :
    inwardRepairWeight d ≤ d := by
  have hden : 0 < 1 + d := by positivity
  unfold inwardRepairWeight
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The physical central-cell cubic defect. -/
def cubicCenteredDefect (h : ℝ) : ℝ := h ^ 2 / 12

/-- The explicit repair weight cancels the negative physical cubic coefficient. -/
theorem cubicCenteredRepair_exact (h : ℝ) :
    inwardBlend (cubicCenteredDefect h) (-cubicCenteredDefect h) = 0 := by
  have hd : 0 ≤ cubicCenteredDefect h := by
    unfold cubicCenteredDefect
    positivity
  rw [inwardBlend_eq _ _ hd]
  simp

end

end BernsteinObstacle
