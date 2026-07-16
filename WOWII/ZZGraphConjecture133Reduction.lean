import WOWII.ZZGraphConjecture133SmallL

/-!
An exact Lean reduction for the remaining C4-free branch of WOWII Graph
Conjecture 133.  All graph theory is isolated in the integer inequality

  radius.toNat + floor(l G) ≤ path G.

Once that inequality is supplied, the repository theorem follows by normalization.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The exact C4-free correctness gate for Conjecture 133. -/
theorem conjecture133_of_noC4_of_radius_floor_l_le_path
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hNoC4 : ¬ ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    (hGap : (G.radius.toNat : ℤ) + ⌊l G⌋ ≤ (path G : ℤ)) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  dsimp only
  rw [if_neg hNoC4]
  norm_num
  exact_mod_cast hGap

/-- Thus the entire conjecture is reduced to the gap inequality only in the
C4-free branch; the C4-present branch is already unconditional. -/
theorem conjecture133_of_C4_or_radius_floor_l_le_path
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (h : (∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) ∨
      (G.radius.toNat : ℤ) + ⌊l G⌋ ≤ (path G : ℤ)) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  rcases h with hC4 | hGap
  · exact conjecture133_of_hasC4 G hG hC4
  · by_cases hC4 : ∃ a b c d : α,
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    · exact conjecture133_of_hasC4 G hG hC4
    · exact conjecture133_of_noC4_of_radius_floor_l_le_path G hC4 hGap

end WrittenOnTheWallII.GraphConjecture133
