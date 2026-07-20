import A387471IntResidue
import A387471MannFinal

/-!
# The six labeled roots attached to the A387471 sine equation

The labels are essential: equal roots still occur with their full multiplicity.
The first three labels are `exp(iα), exp(iβ), exp(iγ)` and the last three are
`-exp(-iα), -exp(-iβ), -exp(-iγ)`.
-/

open Complex Finset
open scoped BigOperators Real

namespace A387471

/-- The six signed roots written directly in angular form. -/
noncomputable def sixRoot (n : ℕ) (A B C : ℤ) : Fin 6 → ℂ
  | ⟨0, _⟩ => Complex.exp ((latticeAngle n A : ℂ) * Complex.I)
  | ⟨1, _⟩ => Complex.exp ((latticeAngle n B : ℂ) * Complex.I)
  | ⟨2, _⟩ => Complex.exp ((latticeAngle n C : ℂ) * Complex.I)
  | ⟨3, _⟩ => -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I)
  | ⟨4, _⟩ => -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I)
  | ⟨5, _⟩ => -Complex.exp (-(latticeAngle n C : ℂ) * Complex.I)
  | ⟨k + 6, h⟩ => by omega

/-- The six exponents as canonical residues modulo `12n`. -/
def sixExponent (n : ℕ) [NeZero n] (A B C : ℤ) : Fin 6 → Fin (12 * n)
  | ⟨0, _⟩ => intResidue (12 * n) A
  | ⟨1, _⟩ => intResidue (12 * n) B
  | ⟨2, _⟩ => intResidue (12 * n) C
  | ⟨3, _⟩ => intResidue (12 * n) (6 * (n : ℤ) - A)
  | ⟨4, _⟩ => intResidue (12 * n) (6 * (n : ℤ) - B)
  | ⟨5, _⟩ => intResidue (12 * n) (6 * (n : ℤ) - C)
  | ⟨k + 6, h⟩ => by omega

/-- Euler's sine numerator identity in the orientation used here. -/
lemma exp_sub_exp_neg_eq_two_sin_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I) =
      2 * (Real.sin x : ℂ) * Complex.I := by
  have hsin := Complex.two_sin (x : ℂ)
  rw [← Complex.ofReal_sin] at hsin
  calc
    Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I) =
        -(Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)) := by
          ring
    _ = ((Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)) *
          Complex.I) * Complex.I := by
          rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
    _ = (2 * (Real.sin x : ℂ)) * Complex.I := by rw [← hsin]
    _ = 2 * (Real.sin x : ℂ) * Complex.I := rfl

/-- The six-root sum is exactly `2i` times the reduced three-sine sum. -/
lemma sum_sixRoot (n : ℕ) (A B C : ℤ) :
    ∑ r : Fin 6, sixRoot n A B C r =
      2 * ((Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
        Real.sin (latticeAngle n C) : ℝ) : ℂ) * Complex.I := by
  have hA := exp_sub_exp_neg_eq_two_sin_mul_I (latticeAngle n A)
  have hB := exp_sub_exp_neg_eq_two_sin_mul_I (latticeAngle n B)
  have hC := exp_sub_exp_neg_eq_two_sin_mul_I (latticeAngle n C)
  calc
    (∑ r : Fin 6, sixRoot n A B C r) =
        (Complex.exp ((latticeAngle n A : ℂ) * Complex.I) -
          Complex.exp (-(latticeAngle n A : ℂ) * Complex.I)) +
        (Complex.exp ((latticeAngle n B : ℂ) * Complex.I) -
          Complex.exp (-(latticeAngle n B : ℂ) * Complex.I)) +
        (Complex.exp ((latticeAngle n C : ℂ) * Complex.I) -
          Complex.exp (-(latticeAngle n C : ℂ) * Complex.I)) := by
            norm_num [Fin.sum_univ_succ, sixRoot]
            ring
    _ = 2 * ((Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
          Real.sin (latticeAngle n C) : ℝ) : ℂ) * Complex.I := by
            rw [hA, hB, hC]
            push_cast
            ring

/-- A reduced sine equation is a vanishing sum of the six labeled roots. -/
lemma sixRoot_vanishes_of_sines {n : ℕ} {A B C : ℤ}
    (h : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    Vanishes Finset.univ (sixRoot n A B C) := by
  simp [Vanishes, sum_sixRoot, h]

/-- Positive labels are the expected powers of the canonical `12n`-th root. -/
lemma canonical_positive_root {n : ℕ} [NeZero n] (A : ℤ) :
    canonicalRoot (12 * n) ^ (intResidue (12 * n) A).val =
      Complex.exp ((latticeAngle n A : ℂ) * Complex.I) := by
  rw [canonicalRoot_pow_intResidue]
  congr 1
  simp [latticeAngle]
  field_simp [NeZero.ne n]
  ring

/-- Negative labels are obtained by the half-turn exponent `6n`. -/
lemma canonical_negative_root {n : ℕ} [NeZero n] (A : ℤ) :
    canonicalRoot (12 * n) ^
        (intResidue (12 * n) (6 * (n : ℤ) - A)).val =
      -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) := by
  rw [canonicalRoot_pow_intResidue]
  calc
    Complex.exp (2 * Real.pi * Complex.I *
        (((6 * (n : ℤ) - A : ℤ) : ℂ)) / (((12 * n : ℕ) : ℂ))) =
        Complex.exp ((Real.pi : ℂ) * Complex.I +
          (-(latticeAngle n A : ℂ)) * Complex.I) := by
          congr 1
          simp [latticeAngle]
          field_simp [NeZero.ne n]
          ring
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I) *
          Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) := by
          rw [Complex.exp_add]
    _ = -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) := by
          rw [Complex.exp_pi_mul_I]
          ring

/-- Every labeled angular root is the corresponding canonical-root power. -/
lemma sixRoot_eq_canonical {n : ℕ} [NeZero n] (A B C : ℤ) (r : Fin 6) :
    sixRoot n A B C r =
      canonicalRoot (12 * n) ^ (sixExponent n A B C r).val := by
  fin_cases r <;>
    simp only [sixRoot, sixExponent] <;>
    first | exact (canonical_positive_root A).symm
          | exact (canonical_positive_root B).symm
          | exact (canonical_positive_root C).symm
          | exact (canonical_negative_root A).symm
          | exact (canonical_negative_root B).symm
          | exact (canonical_negative_root C).symm

/-- The canonical-power version of the six-root relation. -/
lemma canonical_six_vanishes_of_sines {n : ℕ} [NeZero n] {A B C : ℤ}
    (h : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    Vanishes Finset.univ
      (fun r : Fin 6 ↦ canonicalRoot (12 * n) ^ (sixExponent n A B C r).val) := by
  have hv := sixRoot_vanishes_of_sines h
  rw [Vanishes] at hv ⊢
  calc
    (∑ r ∈ Finset.univ,
        canonicalRoot (12 * n) ^ (sixExponent n A B C r).val) =
        ∑ r ∈ Finset.univ, sixRoot n A B C r := by
          apply Finset.sum_congr rfl
          intro r _
          exact (sixRoot_eq_canonical A B C r).symm
    _ = 0 := hv

#print axioms sum_sixRoot
#print axioms sixRoot_eq_canonical
#print axioms canonical_six_vanishes_of_sines

end A387471
