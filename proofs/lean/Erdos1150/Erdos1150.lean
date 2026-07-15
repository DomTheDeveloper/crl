import FormalConjectures.ErdosProblems.«1150»
import Mathlib.Analysis.Fourier.ZMod

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
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

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

#print axioms dft_parseval_conj

end Erdos1150Proof
