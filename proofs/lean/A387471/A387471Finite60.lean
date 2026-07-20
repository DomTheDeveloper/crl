import Mathlib
import A387471MannFinal

/-!
# Exact finite 60th-root certificate for A387471

After the weight-six Mann reduction, every relevant sine angle is an integral
multiple of `π / 30`. The finite certificate is purely integral: powers of a
primitive 60th root are represented by sixteen coefficient coordinates using
the recurrence from `Φ₆₀`. The bounded `29^3` classification itself is checked
by kernel `decide`.
-/

open Polynomial
open scoped BigOperators Matrix

namespace A387471

/-- The explicit 30th cyclotomic polynomial. -/
noncomputable def phi30 : ℤ[X] := X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- The explicit 60th cyclotomic polynomial. -/
noncomputable def phi60 : ℤ[X] := X ^ 16 + X ^ 14 - X ^ 10 - X ^ 8 - X ^ 6 + X ^ 2 + 1

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

/-- Convert an integer exponent to its canonical residue modulo 60. -/
def intResidue60 (a : ℤ) : Fin 60 := ⟨(a % 60).toNat, by omega⟩

/-- Coefficient vector of the constant polynomial `1`. -/
def baseVec60 : Fin 16 → ℤ :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Multiplication by `X`, reduced using
`X^16 = -X^14 + X^10 + X^8 + X^6 - X^2 - 1`. -/
def stepVec60 (v : Fin 16 → ℤ) : Fin 16 → ℤ :=
  ![-v 15,
    v 0,
    v 1 - v 15,
    v 2,
    v 3,
    v 4,
    v 5 + v 15,
    v 6,
    v 7 + v 15,
    v 8,
    v 9 + v 15,
    v 10,
    v 11,
    v 12,
    v 13 - v 15,
    v 14]

/-- Exact coefficient vectors for successive powers of a primitive 60th root. -/
def powVecNat60 : ℕ → Fin 16 → ℤ
  | 0 => baseVec60
  | k + 1 => stepVec60 (powVecNat60 k)

/-- Exact coefficient vector for a residue exponent `0 ≤ k < 60`. -/
def powVec60 (k : Fin 60) : Fin 16 → ℤ := powVecNat60 k.val

/-- Vector numerator for one sine. -/
def sineVec60 (a : ℤ) : Fin 16 → ℤ :=
  fun i ↦ powVec60 (intResidue60 a) i - powVec60 (intResidue60 (-a)) i

/-- Vector numerator for a sum of three sines. -/
def relationVec60 (a b c : ℤ) : Fin 16 → ℤ :=
  fun i ↦ sineVec60 a i + sineVec60 b i + sineVec60 c i

/-- Evaluate an integer coefficient vector at a complex number. -/
noncomputable def evalVec60 (z : ℂ) (v : Fin 16 → ℤ) : ℂ :=
  ∑ i : Fin 16, (v i : ℂ) * z ^ i.val

/-- The rational polynomial represented by a coefficient vector. -/
noncomputable def vecPoly60Q (v : Fin 16 → ℤ) : ℚ[X] :=
  ∑ i : Fin 16, C (v i : ℚ) * X ^ i.val

lemma evalVec60_zero (z : ℂ) : evalVec60 z 0 = 0 := by
  simp [evalVec60]

lemma evalVec60_add (z : ℂ) (v w : Fin 16 → ℤ) :
    evalVec60 z (v + w) = evalVec60 z v + evalVec60 z w := by
  simp only [evalVec60, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib]

lemma evalVec60_sub (z : ℂ) (v w : Fin 16 → ℤ) :
    evalVec60 z (v - w) = evalVec60 z v - evalVec60 z w := by
  simp only [evalVec60, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]

lemma aeval_vecPoly60Q (z : ℂ) (v : Fin 16 → ℤ) :
    Polynomial.aeval z (vecPoly60Q v) = evalVec60 z v := by
  simp [vecPoly60Q, evalVec60]

lemma coeff_vecPoly60Q (v : Fin 16 → ℤ) (i : Fin 16) :
    (vecPoly60Q v).coeff i.val = (v i : ℚ) := by
  classical
  unfold vecPoly60Q
  change (∑ j in Finset.univ,
      (C (v j : ℚ) * X ^ j.val).coeff i.val) = (v i : ℚ)
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
    simp [hval]
  · intro hi
    simp at hi
  · simp

lemma vecPoly60Q_eq_zero_iff (v : Fin 16 → ℤ) : vecPoly60Q v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hiQ : (v i : ℚ) = 0 := by
      rw [← coeff_vecPoly60Q v i, h]
      simp
    have hiZ : v i = 0 := by exact_mod_cast hiQ
    simpa using hiZ
  · rintro rfl
    simp [vecPoly60Q]

lemma natDegree_vecPoly60Q_le (v : Fin 16 → ℤ) :
    (vecPoly60Q v).natDegree ≤ 15 := by
  rw [vecPoly60Q]
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro i _
  by_cases hi : v i = 0
  · simp [hi]
  · simp [hi]
    omega

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

/-- Exact coefficient-vector vanishing predicate, stated pointwise so its
finite decision procedure is fully kernel-reducible. -/
def vectorRelationGrid (a b c : Fin 29) : Prop :=
  ∀ i : Fin 16, relationVec60 (angleInt a) (angleInt b) (angleInt c) i = 0

instance perm3IntDecidable (x y z a b c : ℤ) : Decidable (Perm3 x y z a b c) := by
  unfold Perm3
  infer_instance

instance admissibleGridDecidable (a b c : Fin 29) : Decidable (admissibleGrid a b c) := by
  unfold admissibleGrid
  infer_instance

instance ordinaryGridDecidable (a b c : ℤ) : Decidable (ordinaryGrid a b c) := by
  unfold ordinaryGrid
  infer_instance

instance exceptionalGridDecidable (a b c : ℤ) : Decidable (exceptionalGrid a b c) := by
  unfold exceptionalGrid
  infer_instance

instance classifiedGridDecidable (a b c : ℤ) : Decidable (classifiedGrid a b c) := by
  unfold classifiedGrid
  infer_instance

instance vectorRelationGridDecidable (a b c : Fin 29) :
    Decidable (vectorRelationGrid a b c) := by
  unfold vectorRelationGrid
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finite60_grid_certificate :
    ∀ a b c : Fin 29,
      admissibleGrid a b c → vectorRelationGrid a b c →
        classifiedGrid (angleInt a) (angleInt b) (angleInt c) := by
  decide

#print axioms cyclotomic_sixty
#print axioms coeff_vecPoly60Q
#print axioms natDegree_vecPoly60Q_le
#print axioms finite60_grid_certificate

end A387471
