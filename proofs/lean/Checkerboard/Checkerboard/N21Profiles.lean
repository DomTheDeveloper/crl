import Checkerboard.NatCertificateBudget

/-!
# Exact 21×21 integer dual profiles

This file replays the two rational line covers after clearing denominators and
computes the resulting zero/one-slack candidate sets inside Lean.
-/

namespace Checkerboard

private def profileAxisWeight (n : ℕ) (axis : List ℕ) (index : ℕ) : ℕ :=
  if index < n then axis.getD (min index (n - 1 - index)) 0 else 0

private def profileDiagonalWeight (n parity : ℕ) (diagonal : List ℕ)
    (family : LineFamily) (index : ℕ) : ℕ :=
  let middle := (n - 1) / 2
  match family with
  | .sum =>
      let folded := min index (2 * n - 2 - index)
      if index % 2 = parity % 2 then
        diagonal.getD ((folded - parity % 2) / 2) 0
      else 0
  | .difference =>
      let distance := Nat.dist index (n - 1)
      if distance % 2 = parity % 2 then
        diagonal.getD (middle - (distance + parity % 2) / 2) 0
      else 0
  | _ => 0

private def integerProfileWeight (n parity : ℕ) (axis diagonal : List ℕ)
    (line : PrincipalLine n) : ℕ :=
  match line.1 with
  | .row => profileAxisWeight n axis line.2.1
  | .column => profileAxisWeight n axis line.2.1
  | .sum => profileDiagonalWeight n parity diagonal .sum line.2.1
  | .difference => profileDiagonalWeight n parity diagonal .difference line.2.1

/-- Cleared-denominator four-direction profile for the fat 21-board. -/
def n21p0Weight : PrincipalLine 21 → ℕ :=
  integerProfileWeight 21 0
    [28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0]
    [0, 0, 0, 10, 18, 24, 30, 36, 41, 44, 45]

/-- Cleared-denominator four-direction profile for the thin 21-board. -/
def n21p1Weight : PrincipalLine 21 → ℕ :=
  integerProfileWeight 21 1
    [15, 12, 8, 6, 3, 2, 0, 0, 0, 0, 0]
    [0, 0, 6, 11, 15, 18, 22, 25, 27, 28]

/-- Every fat-color point receives coverage at least 75. -/
theorem n21p0_cover :
    ∀ p : Point 21, InColor 0 p → 75 ≤ coverage n21p0Weight p := by
  decide

/-- Every thin-color point receives coverage at least 48. -/
theorem n21p1_cover :
    ∀ p : Point 21, InColor 1 p → 48 ≤ coverage n21p1Weight p := by
  decide

/-- Exact cleared objective `33·75+1`. -/
theorem n21p0_cost : certificateCost n21p0Weight = 2476 := by decide

/-- Exact cleared objective `33·48`. -/
theorem n21p1_cost : certificateCost n21p1Weight = 1584 := by decide

/-- The 136 points whose fat-profile slack is at most one. -/
def n21p0Candidates : Finset (Point 21) :=
  Finset.univ.filter fun p =>
    InColor 0 p ∧ coverage n21p0Weight p - 75 ≤ 1

/-- The 132 zero-slack points of the thin profile. -/
def n21p1Candidates : Finset (Point 21) :=
  Finset.univ.filter fun p =>
    InColor 1 p ∧ coverage n21p1Weight p - 48 ≤ 0

private def n21p0CandidateList : List (Point 21) := n21p0Candidates.toList
private def n21p1CandidateList : List (Point 21) := n21p1Candidates.toList

private theorem n21p0CandidateList_length : n21p0CandidateList.length = 136 := by
  decide

private theorem n21p1CandidateList_length : n21p1CandidateList.length = 132 := by
  decide

/-- Deterministic enumeration of the 136 fat-profile candidates. -/
def n21p0Point (i : Fin 136) : Point 21 :=
  n21p0CandidateList.get
    ⟨i.1, by rw [n21p0CandidateList_length]; exact i.2⟩

/-- Deterministic enumeration of the 132 thin-profile candidates. -/
def n21p1Point (i : Fin 132) : Point 21 :=
  n21p1CandidateList.get
    ⟨i.1, by rw [n21p1CandidateList_length]; exact i.2⟩

/-- The fat candidate enumeration has no repetitions. -/
theorem n21p0Point_injective : Function.Injective n21p0Point := by decide

/-- The thin candidate enumeration has no repetitions. -/
theorem n21p1Point_injective : Function.Injective n21p1Point := by decide

/-- Every fat point of slack at most one occurs in the enumeration. -/
theorem n21p0Point_surjective :
    ∀ p : Point 21,
      InColor 0 p → coverage n21p0Weight p - 75 ≤ 1 →
      ∃ i, n21p0Point i = p := by
  decide

/-- Every thin zero-slack point occurs in the enumeration. -/
theorem n21p1Point_surjective :
    ∀ p : Point 21,
      InColor 1 p → coverage n21p1Weight p - 48 ≤ 0 →
      ∃ i, n21p1Point i = p := by
  decide

end Checkerboard
