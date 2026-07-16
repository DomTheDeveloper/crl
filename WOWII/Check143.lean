import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-! API and helper checks for the WOWII 143 proof. -/

open Classical SimpleGraph

#check Multiset.sort_eq
#check Multiset.mem_sort
#check Multiset.pairwise_sort
#check Multiset.count_eq_card_filter_eq
#check Multiset.count_map
#check List.count_eq_countP
#check List.Pairwise.rel_get_of_lt
#check Nat.sSup_mem
#check Nat.le_sSup
#check SimpleGraph.three_le_girth
#check SimpleGraph.exists_girth_eq_length
#check SimpleGraph.girth_eq_zero
#check SimpleGraph.Walk.connected_induce_support
#check SimpleGraph.Walk.IsPath.length_support
#check SimpleGraph.Walk.IsPath.support_nodup
#check SimpleGraph.Walk.IsCycle.three_le_length
#check SimpleGraph.Walk.IsCycle.length_ge_girth

namespace WrittenOnTheWallII.GraphConjecture143

example {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    (degreeSequence G).count k = countDegreeK G k := by
  classical
  unfold degreeSequence countDegreeK
  rw [← Multiset.count_coe]
  rw [Multiset.sort_eq]
  simp [Multiset.count_map, eq_comm]

example {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    (degreeSequence G).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort

end WrittenOnTheWallII.GraphConjecture143
