import WOWII.ZZGraphConjecture314BipartiteCommon

/-!
The complete bipartite/chain-graph half of the classification proof for
WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma bool_eq_of_ne_same'' {a b s : Bool} (ha : a ≠ s) (hb : b ≠ s) : a = b := by
  cases a <;> cases b <;> cases s <;> simp_all

private lemma bool_eq_false_of_true_ne'' {a : Bool} (h : true ≠ a) : a = false := by
  cases a <;> simp_all

private lemma bool_eq_true_of_false_ne'' {a : Bool} (h : false ≠ a) : a = true := by
  cases a <;> simp_all

private lemma exists_neighbor_of_connected
    (G : SimpleGraph α) (hG : G.Connected) (x : α) :
    ∃ y : α, G.Adj x y := by
  obtain ⟨z, hzx⟩ := exists_ne x
  obtain ⟨p⟩ := hG x z
  cases p with
  | nil => exact (hzx rfl).elim
  | cons h p => exact ⟨_, h⟩

/-- Nested neighborhoods on each side of a bipartition exclude an induced P5. -/
lemma no_FormsInducedP5_of_bipartite_nested_neighborhoods
    (G : SimpleGraph α)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNested : ∀ a b : α, side a = side b →
      (∀ x : α, G.Adj a x → G.Adj b x) ∨
      (∀ x : α, G.Adj b x → G.Adj a x)) :
    ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 hP5
  rcases hP5 with ⟨-, -, -, -, -, -, -, -, -, -,
    ha01, ha12, ha23, ha34, -, hn03, -, -, hn14, -⟩
  have hx0x2 : side x0 = side x2 :=
    bool_eq_of_ne_same'' (hpart x0 x1 ha01) (hpart x2 x1 ha12.symm)
  have hx2x4 : side x2 = side x4 :=
    bool_eq_of_ne_same'' (hpart x2 x3 ha23) (hpart x4 x3 ha34.symm)
  rcases hNested x0 x4 (hx0x2.trans hx2x4) with h04 | h40
  · exact hn14 (h04 x1 ha01).symm
  · exact hn03 (h40 x3 ha34.symm)

/-- A connected bipartite graph with nested neighborhoods on each side is well
 totally dominated. This is precisely the connected chain-graph family. -/
lemma isWellTotallyDominated_of_connected_chain_graph
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNested : ∀ a b : α, side a = side b →
      (∀ x : α, G.Adj a x → G.Adj b x) ∨
      (∀ x : α, G.Adj b x → G.Adj a x)) :
    IsWellTotallyDominated G := by
  have hNoP5 := no_FormsInducedP5_of_bipartite_nested_neighborhoods G side hpart hNested
  have hcommon (s : Bool) (a₁ a₂ : α)
      (ha₁ : side a₁ = s) (ha₂ : side a₂ = s) (_ha₁₂ : a₁ ≠ a₂) :
      ∃ c : α, side c ≠ s ∧ G.Adj c a₁ ∧ G.Adj c a₂ := by
    rcases hNested a₁ a₂ (ha₁.trans ha₂.symm) with h12 | h21
    · obtain ⟨c, ha₁c⟩ := exists_neighbor_of_connected G hG a₁
      have ha₂c : G.Adj a₂ c := h12 c ha₁c
      refine ⟨c, ?_, ha₁c.symm, ha₂c.symm⟩
      intro hc
      exact hpart a₁ c ha₁c (ha₁.trans hc.symm)
    · obtain ⟨c, ha₂c⟩ := exists_neighbor_of_connected G hG a₂
      have ha₁c : G.Adj a₁ c := h21 c ha₂c
      refine ⟨c, ?_, ha₁c.symm, ha₂c.symm⟩
      intro hc
      exact hpart a₁ c ha₁c (ha₁.trans hc.symm)
  let u : α := Classical.ofNonempty
  obtain ⟨v, huv⟩ := exists_neighbor_of_connected G hG u
  cases hu : side u with
  | false =>
      have hv : side v = true := by
        apply bool_eq_true_of_false_ne''
        simpa [hu] using hpart u v huv
      exact isWellTotallyDominated_of_bipartite_common_neighbors
        G side u v hu hv hpart hcommon hNoP5
  | true =>
      have hv : side v = false := by
        apply bool_eq_false_of_true_ne''
        simpa [hu] using hpart u v huv
      exact isWellTotallyDominated_of_bipartite_common_neighbors
        G side v u hv hu hpart hcommon hNoP5

end WrittenOnTheWallII.GraphConjecture314
