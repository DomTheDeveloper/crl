import Mathlib
import A387471MannFinal

/-!
# Exact finite 60th-root certificate for A387471

After the weight-six Mann reduction, every relevant sine angle is an integral
multiple of `π / 30`. This module checks the remaining bounded classification
inside Lean's kernel. The certificate is purely integral: powers of a primitive
60th root are reduced modulo the explicit cyclotomic polynomial `Φ₆₀`, and the
resulting sixteen-dimensional coefficient vectors are compared by `decide`.
-/

open Polynomial
open scoped BigOperators Matrix

namespace A387471

/-- The explicit 30th cyclotomic polynomial. -/
def phi30 : ℤ[X] := X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- The explicit 60th cyclotomic polynomial. -/
def phi60 : ℤ[X] := X ^ 16 + X ^ 14 - X ^ 10 - X ^ 8 - X ^ 6 + X ^ 2 + 1

lemma cyclotomic_thirty : cyclotomic 30 ℤ = phi30 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 6 ℤ)
  rw [show 30 = 6 * 5 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_five (by norm_num) ℤ]
  simp [phi30]
  ring

lemma cyclotomic_sixty : cyclotomic 60 ℤ = phi60 := by
  rw [show 60 = 30 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
    cyclotomic_thirty]
  simp [phi30, phi60]
  ring

lemma phi60_monic : phi60.Monic := by
  rw [← cyclotomic_sixty]
  exact cyclotomic.monic 60 ℤ

/-- Convert an integer exponent to its canonical residue modulo 60. -/
def intResidue60 (a : ℤ) : Fin 60 := ⟨(a % 60).toNat, by omega⟩

/-- Polynomial representing a 60th root with integer exponent. -/
def rootPolynomial60 (a : ℤ) : ℤ[X] := X ^ (intResidue60 a).val

/-- Polynomial representing `ζ^a - ζ^(-a)`, proportional to `sin(aπ/30)`. -/
def sinePolynomial60 (a : ℤ) : ℤ[X] := rootPolynomial60 a - rootPolynomial60 (-a)

/-- Polynomial representing a sum of three sine numerators. -/
def relationPolynomial60 (a b c : ℤ) : ℤ[X] :=
  sinePolynomial60 a + sinePolynomial60 b + sinePolynomial60 c

/-- Exact coefficient vectors for `X^k mod Φ₆₀`, for `0 ≤ k < 60`. -/
def powVec60 (k : Fin 60) : Fin 16 → ℤ :=
  match k.val with
  | 0 => ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  | 9 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  | 10 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
  | 11 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
  | 12 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
  | 13 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  | 14 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  | 15 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  | 16 => ![-1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, -1, 0]
  | 17 => ![0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, -1]
  | 18 => ![0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0]
  | 19 => ![0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0]
  | 20 => ![0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0]
  | 21 => ![0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1]
  | 22 => ![-1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 23 => ![0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 24 => ![0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 25 => ![0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 26 => ![0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 27 => ![0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 28 => ![0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0]
  | 29 => ![0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0]
  | 30 => ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 31 => ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 32 => ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 33 => ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 34 => ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 35 => ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 36 => ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 37 => ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 38 => ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0]
  | 39 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]
  | 40 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]
  | 41 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]
  | 42 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]
  | 43 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0]
  | 44 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0]
  | 45 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  | 46 => ![1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0]
  | 47 => ![0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1]
  | 48 => ![0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0]
  | 49 => ![0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0]
  | 50 => ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0]
  | 51 => ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1]
  | 52 => ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 53 => ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 54 => ![0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 55 => ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 56 => ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 57 => ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 58 => ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  | 59 => ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]
  | _ => 0

/-- Turn a sixteen-dimensional coefficient vector into a polynomial. -/
def vecPoly60 (v : Fin 16 → ℤ) : ℤ[X] := ∑ i : Fin 16, monomial i.val (v i)

/-- Vector numerator for one sine. -/
def sineVec60 (a : ℤ) : Fin 16 → ℤ :=
  fun i ↦ powVec60 (intResidue60 a) i - powVec60 (intResidue60 (-a)) i

/-- Vector numerator for a sum of three sines. -/
def relationVec60 (a b c : ℤ) : Fin 16 → ℤ :=
  fun i ↦ sineVec60 a i + sineVec60 b i + sineVec60 c i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem powVec60_correct :
    ∀ k : Fin 60, X ^ k.val %ₘ phi60 = vecPoly60 (powVec60 k) := by
  decide

lemma vecPoly60_eq_zero_iff (v : Fin 16 → ℤ) : vecPoly60 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun p : ℤ[X] ↦ p.coeff i.val) h
    simpa [vecPoly60] using hi
  · rintro rfl
    simp [vecPoly60]

lemma relationPolynomial60_mod_eq_vec (a b c : ℤ) :
    relationPolynomial60 a b c %ₘ phi60 = vecPoly60 (relationVec60 a b c) := by
  change (Polynomial.modByMonicHom phi60) (relationPolynomial60 a b c) = _
  simp only [relationPolynomial60, sinePolynomial60, rootPolynomial60,
    map_add, map_sub, powVec60_correct]
  ext i
  simp [vecPoly60, relationVec60, sineVec60]
  ring

/-- The bounded integer coordinate represented by `Fin 29`: values `-14,…,14`. -/
def angleInt (a : Fin 29) : ℤ := a.val - 14

/-- Strict pair-sum bounds `|a+b| < 10`, corresponding to `|α+β| < π/3`. -/
def admissibleGrid (a b c : Fin 29) : Prop :=
  |angleInt a + angleInt b| < 10 ∧
  |angleInt a + angleInt c| < 10 ∧
  |angleInt b + angleInt c| < 10

/-- The ordinary cancellation family, without an unbounded existential. -/
def ordinaryGrid (a b c : ℤ) : Prop :=
  (a = 0 ∧ b = -c) ∨ (b = 0 ∧ a = -c) ∨ (c = 0 ∧ a = -b)

/-- The two exceptional fifth-root patterns and all their orderings. -/
def exceptionalGrid (a b c : ℤ) : Prop :=
  Perm3 a b c (-5) (-3) 9 ∨ Perm3 a b c (-9) 3 5

/-- Complete target classification on the bounded grid. -/
def classifiedGrid (a b c : ℤ) : Prop := ordinaryGrid a b c ∨ exceptionalGrid a b c

/-- Exact coefficient-vector vanishing predicate. -/
def vectorRelationGrid (a b c : Fin 29) : Prop :=
  relationVec60 (angleInt a) (angleInt b) (angleInt c) = 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finite60_grid_certificate :
    ∀ a b c : Fin 29,
      admissibleGrid a b c → vectorRelationGrid a b c →
        classifiedGrid (angleInt a) (angleInt b) (angleInt c) := by
  decide

/-- Polynomial divisibility by `Φ₆₀` plus the angle bounds yields exactly the
ordinary and two exceptional patterns. -/
theorem relation_mod_zero_implies_classified_grid (a b c : Fin 29)
    (hadm : admissibleGrid a b c)
    (hmod : relationPolynomial60 (angleInt a) (angleInt b) (angleInt c) %ₘ phi60 = 0) :
    classifiedGrid (angleInt a) (angleInt b) (angleInt c) := by
  apply finite60_grid_certificate a b c hadm
  rw [vectorRelationGrid]
  rw [relationPolynomial60_mod_eq_vec] at hmod
  exact (vecPoly60_eq_zero_iff _).mp hmod

#print axioms cyclotomic_sixty
#print axioms powVec60_correct
#print axioms finite60_grid_certificate
#print axioms relation_mod_zero_implies_classified_grid

end A387471
