import WOWII.ZZGraphConjecture133C4

/-!
A second clean branch of WOWII Graph Conjecture 133: when the graph is C4-free
but the floored average neighborhood-independence invariant is at most one.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Conjecture 133 holds in the C4-free branch whenever `⌊l(G)⌋ ≤ 1`. -/
theorem conjecture133_of_noC4_of_floor_l_le_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hNoC4 : ¬ ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    (hFloor : ⌊l G⌋ ≤ (1 : ℤ)) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  dsimp only
  rw [if_neg hNoC4]
  norm_num
  have hRadius : (G.radius.toNat : ℝ) + 1 ≤ (path G : ℝ) := by
    exact_mod_cast radius_toNat_add_one_le_path G hG
  have hFloorReal : (⌊l G⌋ : ℝ) ≤ 1 := by
    exact_mod_cast hFloor
  linarith

/-- Combined elementary resolution of the two branches already formalized:
`G` either contains a C4, or it is C4-free with `⌊l(G)⌋ ≤ 1`. -/
theorem conjecture133_of_hasC4_or_floor_l_le_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (h : (∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) ∨
      ⌊l G⌋ ≤ (1 : ℤ)) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  rcases h with hC4 | hFloor
  · exact conjecture133_of_hasC4 G hG hC4
  · by_cases hC4 : ∃ a b c d : α,
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    · exact conjecture133_of_hasC4 G hG hC4
    · exact conjecture133_of_noC4_of_floor_l_le_one G hG hC4 hFloor

end WrittenOnTheWallII.GraphConjecture133
