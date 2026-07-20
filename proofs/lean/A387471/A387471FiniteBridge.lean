import A387471Finite60

/-!
# Analytic bridge to the finite 60th-root certificate

A bounded integral sine relation is evaluated directly in the sixteen-dimensional
coefficient model from `A387471Finite60`. The primitive 60th root satisfies the
recurrence encoded by `stepVec60`, and its rational minimal polynomial has degree
16. Consequently a represented polynomial of degree at most 15 evaluates to zero
only when every coefficient is zero.
-/

open Complex Polynomial
open scoped Real BigOperators

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

/-- The explicit recurrence polynomial vanishes at the canonical primitive
60th root. -/
lemma canonicalRoot60_phi_relation :
    canonicalRoot 60 ^ 16 + canonicalRoot 60 ^ 14 - canonicalRoot 60 ^ 10 -
      canonicalRoot 60 ^ 8 - canonicalRoot 60 ^ 6 + canonicalRoot 60 ^ 2 + 1 = 0 := by
  have hprim : IsPrimitiveRoot (canonicalRoot 60) 60 :=
    canonicalRoot_isPrimitive (by norm_num)
  have hroot : IsRoot (cyclotomic 60 ℂ) (canonicalRoot 60) :=
    hprim.isRoot_cyclotomic (by norm_num)
  have hcyc : Polynomial.map (Int.castRingHom ℂ) phi60 = cyclotomic 60 ℂ := by
    rw [← cyclotomic_sixty, Polynomial.map_cyclotomic]
  rw [← hcyc] at hroot
  simpa [Polynomial.IsRoot.def, phi60] using hroot

lemma evalVec60_base (z : ℂ) : evalVec60 z baseVec60 = 1 := by
  norm_num [evalVec60, baseVec60, Fin.sum_univ_succ]

/-- `stepVec60` is multiplication by the primitive root in the represented
basis. -/
lemma evalVec60_step (v : Fin 16 → ℤ) :
    evalVec60 (canonicalRoot 60) (stepVec60 v) =
      canonicalRoot 60 * evalVec60 (canonicalRoot 60) v := by
  simp [evalVec60, stepVec60, Fin.sum_univ_succ]
  linear_combination -(v 15 : ℂ) * canonicalRoot60_phi_relation

/-- The recurrence vector for the `k`th power evaluates to the actual `k`th
power of the primitive root. -/
lemma evalVec60_powVecNat60 (k : ℕ) :
    evalVec60 (canonicalRoot 60) (powVecNat60 k) = canonicalRoot 60 ^ k := by
  induction k with
  | zero =>
      simpa [powVecNat60] using evalVec60_base (canonicalRoot 60)
  | succ k ih =>
      rw [powVecNat60, evalVec60_step, ih, pow_succ]
      ring

lemma evalVec60_powVec60 (k : Fin 60) :
    evalVec60 (canonicalRoot 60) (powVec60 k) = canonicalRoot 60 ^ k.val := by
  exact evalVec60_powVecNat60 k.val

/-- Evaluation at a primitive 60th root is injective on the represented
sixteen-dimensional rational coefficient space. -/
lemma evalVec60_eq_zero_iff (v : Fin 16 → ℤ) :
    evalVec60 (canonicalRoot 60) v = 0 ↔ v = 0 := by
  constructor
  · intro heval
    have hpolyEval : Polynomial.aeval (canonicalRoot 60) (vecPoly60Q v) = 0 := by
      simpa [aeval_vecPoly60Q] using heval
    have hprim : IsPrimitiveRoot (canonicalRoot 60) 60 :=
      canonicalRoot_isPrimitive (by norm_num)
    have hpoly : vecPoly60Q v = 0 := by
      by_contra hne
      have hdeg := minpoly.degree_le_of_ne_zero ℚ (canonicalRoot 60) hne hpolyEval
      have hnat := Polynomial.natDegree_le_natDegree hdeg
      rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim (by norm_num),
        Polynomial.natDegree_cyclotomic] at hnat
      have hupper := natDegree_vecPoly60Q_le v
      norm_num at hnat
      omega
    exact (vecPoly60Q_eq_zero_iff v).mp hpoly
  · rintro rfl
    exact evalVec60_zero _

/-- A residue power is the complex exponential of the represented angle. -/
lemma canonicalRoot60_pow_angleInt (a : Fin 29) :
    canonicalRoot 60 ^ (intResidue60 (angleInt a)).val =
      Complex.exp (2 * Real.pi * Complex.I * (angleInt a : ℤ) / 60) := by
  rw [canonicalRoot_pow_eq_stdAddChar]
  rw [intResidue60_angleInt_cast]
  exact ZMod.stdAddChar_coe (N := 60) (angleInt a)

lemma canonicalRoot60_pow_angleInt' (a : Fin 29) :
    canonicalRoot 60 ^ (intResidue60 (angleInt a)).val =
      Complex.exp ((angleReal a : ℂ) * Complex.I) := by
  rw [canonicalRoot60_pow_angleInt]
  congr 1
  simp [angleReal]
  push_cast
  ring

/-- Evaluation of one represented sine numerator is `2 i sin(angle)`. -/
lemma evalVec60_sine_angleInt (a : Fin 29) :
    evalVec60 (canonicalRoot 60) (sineVec60 (angleInt a)) =
      2 * (Real.sin (angleReal a) : ℂ) * Complex.I := by
  change evalVec60 (canonicalRoot 60)
      (powVec60 (intResidue60 (angleInt a)) -
        powVec60 (intResidue60 (-angleInt a))) = _
  rw [evalVec60_sub, evalVec60_powVec60, evalVec60_powVec60,
    canonicalRoot60_pow_angleInt']
  have hneg :
      canonicalRoot 60 ^ (intResidue60 (-angleInt a)).val =
        Complex.exp (-(angleReal a : ℂ) * Complex.I) := by
    rw [← angleInt_negAngleFin a, canonicalRoot60_pow_angleInt']
    congr 1
    simp [angleReal]
    ring
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

/-- A three-sine relation makes the represented relation vector evaluate to
zero. -/
lemma evalVec60_relation_eq_zero {a b c : Fin 29}
    (h : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0) :
    evalVec60 (canonicalRoot 60)
      (relationVec60 (angleInt a) (angleInt b) (angleInt c)) = 0 := by
  change evalVec60 (canonicalRoot 60)
    ((sineVec60 (angleInt a) + sineVec60 (angleInt b)) +
      sineVec60 (angleInt c)) = 0
  rw [evalVec60_add, evalVec60_add, evalVec60_sine_angleInt,
    evalVec60_sine_angleInt, evalVec60_sine_angleInt]
  have hc :
      ((Real.sin (angleReal a) + Real.sin (angleReal b) +
        Real.sin (angleReal c) : ℝ) : ℂ) = 0 := by
    exact_mod_cast h
  push_cast at hc
  linear_combination (2 * Complex.I) * hc

/-- Complete classification of bounded integral three-sine relations. -/
theorem bounded_grid_sine_classification (a b c : Fin 29)
    (hadm : admissibleGrid a b c)
    (h : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0) :
    classifiedGrid (angleInt a) (angleInt b) (angleInt c) := by
  apply finite60_grid_certificate a b c hadm
  have hvec : relationVec60 (angleInt a) (angleInt b) (angleInt c) = 0 :=
    (evalVec60_eq_zero_iff _).mp (evalVec60_relation_eq_zero h)
  intro i
  exact congrFun hvec i

#print axioms canonicalRoot60_phi_relation
#print axioms evalVec60_powVecNat60
#print axioms evalVec60_eq_zero_iff
#print axioms bounded_grid_sine_classification

end A387471
