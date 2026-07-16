import WOWII.ZZGraphConjecture314CycleDichotomy

/-!
An indexed form of the induced five-cycle witness used in the nonbipartite
classification for WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An injective copy of the five-cycle whose induced adjacency agrees exactly
with `cycleGraph 5`. -/
def IsInducedC5Embedding (G : SimpleGraph α) (c : Fin 5 → α) : Prop :=
  Function.Injective c ∧
  ∀ i j : Fin 5, G.Adj (c i) (c j) ↔ (cycleGraph 5).Adj i j

/-- The explicit ordered witness predicate packages into an indexed induced
copy of `C₅`. -/
lemma exists_inducedC5Embedding_of_FormsInducedC5
    (G : SimpleGraph α) {x0 x1 x2 x3 x4 : α}
    (hC : FormsInducedC5 G x0 x1 x2 x3 x4) :
    ∃ c : Fin 5 → α, IsInducedC5Embedding G c := by
  rcases hC with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    ha01, ha12, ha23, ha34, ha40, hn02, hn03, hn13, hn14, hn24⟩
  let c : Fin 5 → α := ![x0, x1, x2, x3, x4]
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [c]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [c, cycleGraph, Fin.ext_iff]

/-- Every indexed cycle vertex has its two expected cycle neighbors. -/
lemma inducedC5Embedding_adj_pred_succ
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    G.Adj (c i) (c (i + 1)) ∧ G.Adj (c i) (c (i - 1)) := by
  constructor
  · exact (hc.2 i (i + 1)).mpr (by simp [cycleGraph_adj])
  · exact (hc.2 i (i - 1)).mpr (by simp [cycleGraph_adj])

/-- Cycle indices are adjacent exactly when their images are adjacent. -/
lemma inducedC5Embedding_adj_iff
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i j : Fin 5) :
    G.Adj (c i) (c j) ↔ (cycleGraph 5).Adj i j :=
  hc.2 i j

end WrittenOnTheWallII.GraphConjecture314
