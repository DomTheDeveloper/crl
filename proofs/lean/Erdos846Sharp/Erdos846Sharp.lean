import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

open Finset Fintype

namespace Erdos846Sharp

open SimpleGraph

/-- Mantel's extremal comparison in the exact form needed by the Erdős 846 construction. -/
theorem triangleFree_card_edges_le_turan
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    #G.edgeFinset ≤ #(turanGraph n 2).edgeFinset := by
  have hT := isTuranMaximal_turanGraph (n := n) (r := 2) (by omega)
  exact hT.2 (by simpa using hG)

/-- The familiar numerical Mantel bound: a triangle-free graph has at most `n²/4` edges. -/
theorem four_mul_triangleFree_card_edges_le_sq
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    4 * #G.edgeFinset ≤ n ^ 2 := by
  have hle := triangleFree_card_edges_le_turan G hG
  have hT : 4 * #(turanGraph n 2).edgeFinset ≤ n ^ 2 := by
    rw [card_edgeFinset_turanGraph]
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases hm with hm | hm <;> simp [hm] <;> omega
  exact (Nat.mul_le_mul_left 4 hle).trans hT

/-- The bound is attained by the complete bipartite Turán graph. -/
theorem exists_triangleFree_extremizer (n : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧
      #G.edgeFinset = #(turanGraph n 2).edgeFinset := by
  refine ⟨turanGraph n 2, ?_, rfl⟩
  simpa using turanGraph_cliqueFree (n := n) (r := 2) (by omega)

#print axioms Erdos846Sharp.four_mul_triangleFree_card_edges_le_sq
#print axioms Erdos846Sharp.exists_triangleFree_extremizer

end Erdos846Sharp
