import Checkerboard.N21Profiles

/-!
# Finite Boolean closure of the 21×21 upper bounds

The dual profiles leave 136 and 132 candidate points. Lean computes the
collinear triples among those candidates and bit-blasts the two remaining
finite statements. The resulting SAT proof is checked by `bv_decide`.
-/

namespace Checkerboard

/-- An ordered candidate-index triple. -/
structure IndexTriple (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  deriving DecidableEq, Fintype

/-- Selected indices of a Boolean assignment. -/
def selectedIndices {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

/-- Selected board points of a Boolean assignment. -/
def selectedPoints {n : ℕ} (point : Fin n → Point 21)
    (x : Fin n → Bool) : Finset (Point 21) :=
  (selectedIndices x).image point

/-- All increasing collinear triples in an indexed candidate set. -/
def collinearTriples {n : ℕ} (point : Fin n → Point 21) :
    Finset (IndexTriple n) :=
  Finset.univ.filter fun t =>
    t.a.1 < t.b.1 ∧ t.b.1 < t.c.1 ∧
      determinant (point t.a) (point t.b) (point t.c) = 0

/-- Boolean assignment avoids every generated collinear triple. -/
def avoidsCollinearTriples {n : ℕ} (point : Fin n → Point 21)
    (x : Fin n → Bool) : Prop :=
  ∀ t ∈ collinearTriples point,
    x t.a ≠ true ∨ x t.b ≠ true ∨ x t.c ≠ true

/-- Independent fingerprint of the generated fat all-slope constraints. -/
theorem n21p0_collinearTriple_count :
    (collinearTriples n21p0Point).card = 5084 := by decide

/-- Independent fingerprint of the generated thin all-slope constraints. -/
theorem n21p1_collinearTriple_count :
    (collinearTriples n21p1Point).card = 4796 := by decide

set_option maxHeartbeats 0 in
/-- No 33-point assignment survives the fat-profile budget and all collinear
triple clauses. -/
theorem n21p0_boolean_bound :
    ∀ x : Fin 136 → Bool,
      avoidsCollinearTriples n21p0Point x →
      natCertificateBudget n21p0Weight (selectedPoints n21p0Point x) = 1 →
      (selectedIndices x).card ≤ 32 := by
  bv_decide

set_option maxHeartbeats 0 in
/-- No 33-point assignment survives the thin-profile zero budget and all
collinear triple clauses. -/
theorem n21p1_boolean_bound :
    ∀ x : Fin 132 → Bool,
      avoidsCollinearTriples n21p1Point x →
      natCertificateBudget n21p1Weight (selectedPoints n21p1Point x) = 0 →
      (selectedIndices x).card ≤ 32 := by
  bv_decide

end Checkerboard
