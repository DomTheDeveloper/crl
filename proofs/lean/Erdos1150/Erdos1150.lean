import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Polynomial.Eval.Degree

open Complex Finset MeasureTheory
open scoped BigOperators ComplexConjugate Polynomial ZMod

namespace Erdos1150Proof

variable {N : ℕ} [NeZero N]

/-- Orthogonality of the standard additive characters on `ZMod N`. -/
lemma sum_stdAddChar_mul (t : ZMod N) :
    ∑ i : ZMod N, ZMod.stdAddChar (t * i) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst t
    simp
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- Complex conjugation reverses the standard additive character. -/
lemma conj_stdAddChar (x : ZMod N) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv,
    Circle.coe_inv]

/-- Conjugating the DFT reverses its character sign. -/
lemma conj_dft (Φ : ZMod N → ℂ) (k : ZMod N) :
    conj (ZMod.dft Φ k) =
      ∑ j : ZMod N, ZMod.stdAddChar (j * k) * conj (Φ j) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar, neg_neg]

/-- The unnormalised inverse DFT, extracted from Fourier inversion. -/
lemma dft_inverse_sum (Φ : ZMod N → ℂ) (x : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (x * k) * ZMod.dft Φ k = (N : ℂ) * Φ x := by
  have h := congrFun (ZMod.dft_dft Φ) (-x)
  rw [ZMod.dft_apply] at h
  simpa only [smul_eq_mul, mul_neg, neg_neg, mul_comm] using h

/-- Discrete Parseval identity for the unnormalised DFT, in conjugate-product form. -/
lemma dft_parseval_conj (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, conj (ZMod.dft Φ k) * ZMod.dft Φ k =
      (N : ℂ) * ∑ j : ZMod N, conj (Φ j) * Φ j := by
  calc
    ∑ k : ZMod N, conj (ZMod.dft Φ k) * ZMod.dft Φ k =
        ∑ k : ZMod N,
          (∑ j : ZMod N, ZMod.stdAddChar (j * k) * conj (Φ j)) * ZMod.dft Φ k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [conj_dft]
    _ = ∑ k : ZMod N, ∑ j : ZMod N,
          (ZMod.stdAddChar (j * k) * conj (Φ j)) * ZMod.dft Φ k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ j : ZMod N, ∑ k : ZMod N,
          (ZMod.stdAddChar (j * k) * conj (Φ j)) * ZMod.dft Φ k := by
            rw [Finset.sum_comm]
    _ = ∑ j : ZMod N,
          conj (Φ j) * (∑ k : ZMod N, ZMod.stdAddChar (j * k) * ZMod.dft Φ k) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ j : ZMod N, conj (Φ j) * ((N : ℂ) * Φ j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [dft_inverse_sum]
    _ = (N : ℂ) * ∑ j : ZMod N, conj (Φ j) * Φ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Real norm-square form of discrete Parseval. -/
lemma dft_parseval_norm_sq (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2 =
      (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h := dft_parseval_conj Φ
  simp_rw [Complex.conj_mul'] at h
  exact_mod_cast h

/-- A unit-modulus input vector has a Fourier coefficient of size at least `sqrt N`. -/
lemma exists_sqrt_le_norm_dft (Φ : ZMod N → ℂ) (hunit : ∀ j, ‖Φ j‖ = 1) :
    ∃ k : ZMod N, Real.sqrt N ≤ ‖ZMod.dft Φ k‖ := by
  by_contra h
  push_neg at h
  have hterm : ∀ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2 < (N : ℝ) := by
    intro k
    have hsqrt : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsq := (sq_lt_sq₀ (norm_nonneg (ZMod.dft Φ k)) (Real.sqrt_nonneg _)).2 (h k)
    simpa only [hsqrt] using hsq
  have hsum_lt :
      (∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2) < ∑ _k : ZMod N, (N : ℝ) := by
    refine Finset.sum_lt_sum (fun k _ => (hterm k).le) ?_
    exact ⟨0, Finset.mem_univ _, hterm 0⟩
  have hparseval := dft_parseval_norm_sq Φ
  have hinput : (∑ j : ZMod N, ‖Φ j‖ ^ 2) = (N : ℝ) := by
    simp [hunit]
  rw [hinput] at hparseval
  have hconstant : (∑ _k : ZMod N, (N : ℝ)) = (N : ℝ) * N := by
    simp
  rw [hconstant] at hsum_lt
  linarith

/-- Every character appearing in the DFT is a natural power of one root of unity. -/
lemma stdAddChar_neg_mul_eq_pow (j k : ZMod N) :
    (ZMod.stdAddChar (-(j * k)) : ℂ) =
      (ZMod.stdAddChar (-k) : ℂ) ^ j.val := by
  have hj : -(j * k) = j.val • (-k) := by
    rw [← ZMod.natCast_zmod_val j]
    simp [nsmul_eq_mul]
  rw [hj, AddChar.map_nsmul_eq_pow]

/-- The coefficient vector's DFT is evaluation at the corresponding root of unity. -/
lemma dft_coeff_eq_eval (P : ℂ[X]) (n : ℕ) (hdeg : P.natDegree = n)
    (k : ZMod (n + 1)) :
    ZMod.dft (fun j : ZMod (n + 1) => P.coeff j.val) k =
      P.eval (ZMod.stdAddChar (-k) : ℂ) := by
  rw [ZMod.dft_apply, Polynomial.eval_eq_sum_range, hdeg]
  simp only [smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [stdAddChar_neg_mul_eq_pow]
  exact mul_comm _ _

#print axioms dft_coeff_eq_eval

end Erdos1150Proof
