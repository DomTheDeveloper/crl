import WOWII.ZZGraphConjecture314C5Dominates

/-!
Classification of every vertex by its neighborhood on a dominating induced
five-cycle. This produces the five bags used in the nonbipartite branch of
WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The cycle-neighborhood of `x` is exactly the neighborhood of index `i` in
`cycleGraph 5`. -/
def C5BagSpec (G : SimpleGraph α) (c : Fin 5 → α) (x : α) (i : Fin 5) : Prop :=
  ∀ j : Fin 5, G.Adj x (c j) ↔ (cycleGraph 5).Adj i j

/-- A finite truth-table lemma: a nonempty subset of `C₅` containing no
adjacent pair and having no isolated chosen element is the neighborhood of a
unique cycle vertex. -/
lemma fin5_existsUnique_neighbor_pattern
    (P : Fin 5 → Bool)
    (hne : ∃ i, P i = true)
    (hind : ∀ i j, (cycleGraph 5).Adj i j → ¬(P i = true ∧ P j = true))
    (htwo : ∀ i, P i = true → ∃ j, j ≠ i ∧ P j = true) :
    ∃! k : Fin 5, ∀ j : Fin 5, P j = true ↔ (cycleGraph 5).Adj k j := by
  revert P
  decide

private lemma cycle_adj_plus
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    G.Adj (c i) (c (i + 1)) :=
  (hc.2 i (i + 1)).mpr (by simp [cycleGraph_adj])

private lemma cycle_adj_minus
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    G.Adj (c i) (c (i - 1)) :=
  (hc.2 i (i - 1)).mpr (by simp [cycleGraph_adj])

/-- A cycle neighbor of `x` cannot be its only cycle neighbor. -/
lemma exists_second_cycle_neighbor
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (c : Fin 5 → α) (hc : IsInducedC5Embedding G c)
    (x : α) {i : Fin 5} (hxi : G.Adj x (c i)) :
    ∃ j : Fin 5, j ≠ i ∧ G.Adj x (c j) := by
  by_contra h
  push_neg at h
  have honly : ∀ j : Fin 5, G.Adj x (c j) → j = i := by
    intro j hxj
    by_contra hji
    exact h j hji hxj
  have hx_not_cycle : ∀ k : Fin 5, x ≠ c k := by
    intro k hxk
    have hpX : G.Adj x (c (k + 1)) := by simpa [hxk] using cycle_adj_plus hc k
    have hmX : G.Adj x (c (k - 1)) := by simpa [hxk] using cycle_adj_minus hc k
    have hpi : k + 1 = i := honly (k + 1) hpX
    have hmi : k - 1 = i := honly (k - 1) hmX
    have : k + 1 = k - 1 := hpi.trans hmi.symm
    fin_cases k <;> simp_all
  have hx1 : ¬G.Adj x (c (i + 1)) := by
    intro h1
    have := honly (i + 1) h1
    fin_cases i <;> simp_all
  have hx2 : ¬G.Adj x (c (i + 2)) := by
    intro h2
    have := honly (i + 2) h2
    fin_cases i <;> simp_all
  have hx3 : ¬G.Adj x (c (i + 3)) := by
    intro h3
    have := honly (i + 3) h3
    fin_cases i <;> simp_all
  have hc02 : ¬G.Adj (c i) (c (i + 2)) := by
    rw [hc.2 i (i + 2)]
    fin_cases i <;> decide
  have hc03 : ¬G.Adj (c i) (c (i + 3)) := by
    rw [hc.2 i (i + 3)]
    fin_cases i <;> decide
  have hc13 : ¬G.Adj (c (i + 1)) (c (i + 3)) := by
    rw [hc.2 (i + 1) (i + 3)]
    fin_cases i <;> decide
  have h01ne : c i ≠ c (i + 1) := by
    intro hEq
    exact (by fin_cases i <;> decide : i ≠ i + 1) (hc.1 hEq)
  have h02ne : c i ≠ c (i + 2) := by
    intro hEq
    exact (by fin_cases i <;> decide : i ≠ i + 2) (hc.1 hEq)
  have h03ne : c i ≠ c (i + 3) := by
    intro hEq
    exact (by fin_cases i <;> decide : i ≠ i + 3) (hc.1 hEq)
  have h12ne : c (i + 1) ≠ c (i + 2) := by
    intro hEq
    exact (by fin_cases i <;> decide : i + 1 ≠ i + 2) (hc.1 hEq)
  have h13ne : c (i + 1) ≠ c (i + 3) := by
    intro hEq
    exact (by fin_cases i <;> decide : i + 1 ≠ i + 3) (hc.1 hEq)
  have h23ne : c (i + 2) ≠ c (i + 3) := by
    intro hEq
    exact (by fin_cases i <;> decide : i + 2 ≠ i + 3) (hc.1 hEq)
  have hc12 : G.Adj (c (i + 1)) (c (i + 2)) := by
    convert cycle_adj_plus hc (i + 1) using 1 <;>
      fin_cases i <;> decide
  have hc23 : G.Adj (c (i + 2)) (c (i + 3)) := by
    convert cycle_adj_plus hc (i + 2) using 1 <;>
      fin_cases i <;> decide
  apply hNoP5 x (c i) (c (i + 1)) (c (i + 2)) (c (i + 3))
  unfold FormsInducedP5
  exact ⟨hxi.ne, hx_not_cycle (i + 1), hx_not_cycle (i + 2), hx_not_cycle (i + 3),
    h01ne, h02ne, h03ne, h12ne, h13ne, h23ne,
    hxi, cycle_adj_plus hc i, hc12, hc23,
    hx1, hx2, hx3, hc02, hc03, hc13⟩

/-- Every vertex belongs to a unique cycle bag. -/
lemma existsUnique_C5BagSpec
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (c : Fin 5 → α) (hc : IsInducedC5Embedding G c)
    (x : α) :
    ∃! i : Fin 5, C5BagSpec G c x i := by
  let P : Fin 5 → Bool := fun j => decide (G.Adj x (c j))
  have hne : ∃ i, P i = true := by
    obtain ⟨i, hi⟩ := exists_adj_cycleVertex_of_inducedC5 G hG hTriFree hNoP5 c hc x
    exact ⟨i, by simp [P, hi]⟩
  have hind : ∀ i j, (cycleGraph 5).Adj i j → ¬(P i = true ∧ P j = true) := by
    intro i j hij hp
    have hxi : G.Adj x (c i) := by simpa [P] using hp.1
    have hxj : G.Adj x (c j) := by simpa [P] using hp.2
    have hcij : G.Adj (c i) (c j) := (hc.2 i j).mpr hij
    exact hTriFree x (c i) (c j) hxi hcij hxj.symm
  have htwo : ∀ i, P i = true → ∃ j, j ≠ i ∧ P j = true := by
    intro i hi
    have hxi : G.Adj x (c i) := by simpa [P] using hi
    obtain ⟨j, hji, hxj⟩ := exists_second_cycle_neighbor G hNoP5 c hc x hxi
    exact ⟨j, hji, by simp [P, hxj]⟩
  obtain ⟨i, hi, huniq⟩ := fin5_existsUnique_neighbor_pattern P hne hind htwo
  refine ⟨i, ?_, ?_⟩
  · intro j
    simpa [C5BagSpec, P] using hi j
  · intro k hk
    apply huniq k
    intro j
    simpa [C5BagSpec, P] using hk j

/-- A cycle vertex belongs to the correspondingly indexed bag. -/
lemma C5BagSpec_cycleVertex
    (G : SimpleGraph α) (c : Fin 5 → α)
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    C5BagSpec G c (c i) i := by
  intro j
  exact hc.2 i j

end WrittenOnTheWallII.GraphConjecture314
