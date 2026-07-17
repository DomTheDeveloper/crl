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
  have ha10 : G.Adj x1 x0 := ha01.symm
  have ha21 : G.Adj x2 x1 := ha12.symm
  have ha32 : G.Adj x3 x2 := ha23.symm
  have ha43 : G.Adj x4 x3 := ha34.symm
  have ha04 : G.Adj x0 x4 := ha40.symm
  have hn20 : ¬G.Adj x2 x0 := fun h => hn02 h.symm
  have hn30 : ¬G.Adj x3 x0 := fun h => hn03 h.symm
  have hn31 : ¬G.Adj x3 x1 := fun h => hn13 h.symm
  have hn41 : ¬G.Adj x4 x1 := fun h => hn14 h.symm
  have hn42 : ¬G.Adj x4 x2 := fun h => hn24 h.symm
  have hcycleTable : ∀ i j : Fin 5, (cycleGraph 5).Adj i j ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 4 ∧ j = 0) ∨ (i = 0 ∧ j = 4) := by
    decide
  let c : Fin 5 → α := fun i =>
    match i.1 with
    | 0 => x0
    | 1 => x1
    | 2 => x2
    | 3 => x3
    | _ => x4
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [c]
  · intro i j
    rw [hcycleTable i j]
    fin_cases i <;> fin_cases j <;> simp_all [c]

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
