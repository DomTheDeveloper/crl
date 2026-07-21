import BernsteinObstacle.Core
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Smooth quadratic contact: fixed-degree Bernstein-cone saturation

The target `(x - 1/2)^2` is analytic and belongs exactly to every polynomial
space of degree at least two. Nevertheless, its degree-`p` Bernstein
coefficient vector has a strictly negative central entry.
-/

@[simp] theorem natCast_mul_pred (n : ℕ) :
    (((n * (n - 1) : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n with
  | zero => norm_num
  | succ n => simp [Nat.cast_succ]

def quadraticMomentDenominator (p : ℕ) : ℝ :=
  ((p * (p - 1) : ℕ) : ℝ)

def quadraticMonomialCoeff (p k : ℕ) : ℝ :=
  ((k * (k - 1) : ℕ) : ℝ) / quadraticMomentDenominator p

def centeredQuadraticCoeff (p k : ℕ) : ℝ :=
  quadraticMonomialCoeff p k - (k : ℝ) / (p : ℝ) + 1 / 4

theorem quadraticMomentDenominator_pos (p : ℕ) (hp : 2 ≤ p) :
    0 < quadraticMomentDenominator p := by
  unfold quadraticMomentDenominator
  exact_mod_cast Nat.mul_pos (by omega : 0 < p) (by omega : 0 < p - 1)

theorem basis_firstMoment (p : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (p + 1), (k : ℝ) * basis p k x) = (p : ℝ) * x := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ p)
  rw [Polynomial.eval_finsetSum] at h
  simpa [basis_eq_eval, nsmul_eq_mul] using h

theorem basis_secondFactorialMoment (p : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (p + 1),
        ((k * (k - 1) : ℕ) : ℝ) * basis p k x) =
      quadraticMomentDenominator p * x ^ 2 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_mul_smul ℝ p)
  rw [Polynomial.eval_finsetSum] at h
  simpa [basis_eq_eval, nsmul_eq_mul, quadraticMomentDenominator] using h

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

/-- Pure field identity behind the even-degree central coefficient. -/
theorem evenCenterRationalIdentity
    (x : ℝ) (hx : x ≠ 0) (hpred : 2 * x - 1 ≠ 0) :
    x * (x - 1) / ((2 * x) * (2 * x - 1)) - x / (2 * x) + 1 / 4 =
      -1 / (4 * (2 * x - 1)) := by
  field_simp [hx, hpred]
  ring

/-- Pure field identity behind the odd-degree central coefficient. -/
theorem oddCenterRationalIdentity
    (x : ℝ) (hx : x ≠ 0) (hodd : 2 * x + 1 ≠ 0) :
    x * (x - 1) / ((2 * x + 1) * (2 * x)) - x / (2 * x + 1) + 1 / 4 =
      -1 / (4 * (2 * x + 1)) := by
  field_simp [hx, hodd]
  ring

theorem centeredQuadraticCoeff_even_center
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m) m =
      -1 / (4 * (((2 * m : ℕ) : ℝ) - 1)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hpred : 2 * (m : ℝ) - 1 ≠ 0 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  unfold centeredQuadraticCoeff quadraticMonomialCoeff quadraticMomentDenominator
  rw [natCast_mul_pred m, natCast_mul_pred (2 * m)]
  push_cast
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    evenCenterRationalIdentity (m : ℝ) hm0 hpred

theorem centeredQuadraticCoeff_even_center_neg
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m) m < 0 := by
  rw [centeredQuadraticCoeff_even_center m hm]
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 4 * (((2 * m : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  exact div_neg_of_neg_of_pos (by norm_num) hden

theorem centeredQuadraticCoeff_odd_center
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m + 1) m =
      -1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hodd : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  unfold centeredQuadraticCoeff quadraticMonomialCoeff quadraticMomentDenominator
  rw [natCast_mul_pred m, natCast_mul_pred (2 * m + 1)]
  push_cast
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    oddCenterRationalIdentity (m : ℝ) hm0 hodd

theorem centeredQuadraticCoeff_odd_center_neg
    (m : ℕ) (hm : 1 ≤ m) :
    centeredQuadraticCoeff (2 * m + 1) m < 0 := by
  rw [centeredQuadraticCoeff_odd_center m hm]
  have hden : 0 < 4 * ((2 * m + 1 : ℕ) : ℝ) := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- Cubic specialization retained as an executable check. -/
def centeredQuadraticCubicCoeff : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => -(1 / 12)
  | 2 => -(1 / 12)
  | 3 => 1 / 4
  | _ => 0

theorem centeredQuadratic_eq_cubicBernsteinCurve (x : ℝ) :
    curve 3 centeredQuadraticCubicCoeff x = (x - 1 / 2) ^ 2 := by
  simp [curve, basis, centeredQuadraticCubicCoeff, Finset.sum_range_succ]
  ring

theorem centeredQuadraticCubicCoeff_not_nonnegative :
    ¬ (∀ k ∈ Finset.range 4, 0 ≤ centeredQuadraticCubicCoeff k) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num [centeredQuadraticCubicCoeff] at h1

theorem coefficientDefect_le_opNorm_mul_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (e : E) (d : ℝ)
    (hdefect : d ≤ |L e|) :
    d ≤ ‖L‖ * ‖e‖ := by
  calc
    d ≤ |L e| := hdefect
    _ = ‖L e‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖e‖ := L.le_opNorm e

theorem coefficientDefect_div_opNorm_le_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (e : E) (d : ℝ)
    (hL : 0 < ‖L‖) (hdefect : d ≤ |L e|) :
    d / ‖L‖ ≤ ‖e‖ := by
  apply (div_le_iff₀ hL).2
  simpa [mul_comm] using coefficientDefect_le_opNorm_mul_norm L e d hdefect

def inwardRepairWeight (d : ℝ) : ℝ := d / (1 + d)

def inwardBlend (d a : ℝ) : ℝ :=
  (1 - inwardRepairWeight d) * a + inwardRepairWeight d

theorem inwardBlend_eq (d a : ℝ) (hd : 0 ≤ d) :
    inwardBlend d a = (a + d) / (1 + d) := by
  have hden : 1 + d ≠ 0 := by positivity
  unfold inwardBlend inwardRepairWeight
  field_simp [hden]
  ring

theorem inwardBlend_mem_Icc
    (d a : ℝ) (hd : 0 ≤ d) (ha : a ∈ Set.Icc (-d) 1) :
    inwardBlend d a ∈ Set.Icc 0 1 := by
  rw [inwardBlend_eq d a hd]
  have hden : 0 < 1 + d := by positivity
  constructor
  · exact div_nonneg (by linarith [ha.1]) hden.le
  · apply (div_le_iff₀ hden).2
    linarith [ha.2]

theorem inwardBlend_sub (d a : ℝ) :
    inwardBlend d a - a = inwardRepairWeight d * (1 - a) := by
  unfold inwardBlend
  ring

theorem inwardRepairWeight_le_defect (d : ℝ) (hd : 0 ≤ d) :
    inwardRepairWeight d ≤ d := by
  have hden : 0 < 1 + d := by positivity
  unfold inwardRepairWeight
  apply (div_le_iff₀ hden).2
  nlinarith

def cubicCenteredDefect (h : ℝ) : ℝ := h ^ 2 / 12

theorem cubicCenteredRepair_exact (h : ℝ) :
    inwardBlend (cubicCenteredDefect h) (-cubicCenteredDefect h) = 0 := by
  have hd : 0 ≤ cubicCenteredDefect h := by
    unfold cubicCenteredDefect
    positivity
  rw [inwardBlend_eq _ _ hd]
  simp

end

end BernsteinObstacle
