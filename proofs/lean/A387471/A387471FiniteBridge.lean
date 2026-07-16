import A387471Finite60

/-!
# Analytic bridge to the finite 60th-root certificate

This module proves that a bounded integral sine relation is exactly an integer
polynomial relation at the canonical primitive 60th root.  Cyclotomic
minimal-polynomial divisibility then feeds the kernel-decided finite table in
`A387471Finite60`.
-/

open Complex Polynomial
open scoped Real

namespace A387471

/-- Negation on the encoded interval `{-14, …, 14}`. -/
def negAngleFin (a : Fin 29) : Fin 29 := ⟨28 - a.val, by omega⟩

@[simp] lemma angleInt_negAngleFin (a : Fin 29) :
    angleInt (negAngleFin a) = -angleInt a := by
  simp [angleInt, negAngleFin]
  omega

/-- The real angle represented by one finite grid coordinate. -/
noncomputable def angleReal (a : Fin 29) : ℝ :=
  (angleInt a : ℝ) * Real.pi / 30

/-- The chosen natural residue represents the original integer in `ZMod 60`. -/
lemma intResidue60_angleInt_cast (a : Fin 29) :
    ((intResidue60 (angleInt a)).val : ZMod 60) = (angleInt a : ZMod 60) := by
  fin_cases a <;> norm_num [angleInt, intResidue60]

/-- Evaluating the root polynomial gives the corresponding complex exponential. -/
lemma aeval_rootPolynomial60_angleInt (a : Fin 29) :
    Polynomial.aeval (canonicalRoot 60) (rootPolynomial60 (angleInt a)) =
      Complex.exp (2 * Real.pi * Complex.I * (angleInt a : ℤ) / 60) := by
  rw [rootPolynomial60]
  simp only [map_pow, aeval_X]
  rw [canonicalRoot_pow_eq_stdAddChar]
  rw [intResidue60_angleInt_cast]
  exact ZMod.stdAddChar_coe (N := 60) (angleInt a)

/-- The same evaluation in the more convenient `exp(angle * I)` form. -/
lemma aeval_rootPolynomial60_angleInt' (a : Fin 29) :
    Polynomial.aeval (canonicalRoot 60) (rootPolynomial60 (angleInt a)) =
      Complex.exp ((angleReal a : ℂ) * Complex.I) := by
  rw [aeval_rootPolynomial60_angleInt]
  congr 1
  simp [angleReal]
  push_cast
  ring

/-- Evaluation of one sine numerator is `2 i sin(angle)`. -/
lemma aeval_sinePolynomial60_angleInt (a : Fin 29) :
    Polynomial.aeval (canonicalRoot 60) (sinePolynomial60 (angleInt a)) =
      2 * (Real.sin (angleReal a) : ℂ) * Complex.I := by
  rw [sinePolynomial60, map_sub, aeval_rootPolynomial60_angleInt']
  have hneg :
      Polynomial.aeval (canonicalRoot 60) (rootPolynomial60 (-angleInt a)) =
        Complex.exp (-(angleReal a : ℂ) * Complex.I) := by
    rw [← angleInt_negAngleFin a, aeval_rootPolynomial60_angleInt']
    congr 1
    simp [angleReal]
  rw [hneg]
  have hsin := Complex.two_sin (angleReal a : ℂ)
  rw [← Complex.ofReal_sin] at hsin
  calc
    Complex.exp ((angleReal a : ℂ) * Complex.I) -
        Complex.exp (-(angleReal a : ℂ) * Complex.I) =
        - (Complex.exp (-(angleReal a : ℂ) * Complex.I) -
          Complex.exp ((angleReal a : ℂ) * Complex.I)) := by ring
    _ = ((Complex.exp (-(angleReal a : ℂ) * Complex.I) -
          Complex.exp ((angleReal a : ℂ) * Complex.I)) * Complex.I) * Complex.I := by
          rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
    _ = (2 * (Real.sin (angleReal a) : ℂ)) * Complex.I := by rw [← hsin]
    _ = 2 * (Real.sin (angleReal a) : ℂ) * Complex.I := rfl

/-- A three-sine relation evaluates to zero as an integer polynomial relation. -/
lemma aeval_relationPolynomial60_eq_zero {a b c : Fin 29}
    (h : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0) :
    Polynomial.aeval (canonicalRoot 60)
      (relationPolynomial60 (angleInt a) (angleInt b) (angleInt c)) = 0 := by
  simp only [relationPolynomial60, map_add, aeval_sinePolynomial60_angleInt]
  push_cast at h
  rw [h]
  ring

/-- A zero bounded sine sum forces the corresponding polynomial remainder
modulo `Φ₆₀` to vanish. -/
lemma relationPolynomial60_mod_eq_zero_of_sines {a b c : Fin 29}
    (h : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0) :
    relationPolynomial60 (angleInt a) (angleInt b) (angleInt c) %ₘ phi60 = 0 := by
  have hprim : IsPrimitiveRoot (canonicalRoot 60) 60 :=
    canonicalRoot_isPrimitive (by norm_num)
  have hroot := aeval_relationPolynomial60_eq_zero h
  have hdvd : minpoly ℤ (canonicalRoot 60) ∣
      relationPolynomial60 (angleInt a) (angleInt b) (angleInt c) :=
    minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (by norm_num)) hroot
  rw [← Polynomial.cyclotomic_eq_minpoly hprim (by norm_num), cyclotomic_sixty] at hdvd
  exact (Polynomial.modByMonic_eq_zero_iff_dvd phi60_monic).2 hdvd

/-- Complete classification of bounded integral three-sine relations. -/
theorem bounded_grid_sine_classification (a b c : Fin 29)
    (hadm : admissibleGrid a b c)
    (h : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0) :
    classifiedGrid (angleInt a) (angleInt b) (angleInt c) :=
  relation_mod_zero_implies_classified_grid a b c hadm
    (relationPolynomial60_mod_eq_zero_of_sines h)

#print axioms aeval_sinePolynomial60_angleInt
#print axioms relationPolynomial60_mod_eq_zero_of_sines
#print axioms bounded_grid_sine_classification

end A387471
