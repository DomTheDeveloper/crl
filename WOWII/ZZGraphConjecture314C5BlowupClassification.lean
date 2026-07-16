import WOWII.ZZGraphConjecture314C5Bags
import WOWII.ZZGraphConjecture314ConditionalFinal

/-!
Completion of the nonbipartite structural branch: a dominating induced
five-cycle forces the entire graph to be a nonempty complete blow-up of `C₅`.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Two nonadjacent vertices of `C₅` have a common neighbor. -/
lemma fin5_common_neighbor_of_not_adj :
    ∀ i j : Fin 5, ¬(cycleGraph 5).Adj i j →
      ∃ k : Fin 5, (cycleGraph 5).Adj i k ∧ (cycleGraph 5).Adj j k := by
  decide

/-- Finite index certificate for the induced-`P₅` created by a missing edge
between two consecutive bags. -/
lemma fin5_missing_blowup_edge_pattern :
    ∀ i j : Fin 5, (cycleGraph 5).Adj i j →
      ∃ a b d : Fin 5,
        (cycleGraph 5).Adj i a ∧
        (cycleGraph 5).Adj i b ∧
        (cycleGraph 5).Adj b d ∧
        (cycleGraph 5).Adj j d ∧
        ¬(cycleGraph 5).Adj a b ∧
        ¬(cycleGraph 5).Adj a d ∧
        ¬(cycleGraph 5).Adj j a ∧
        ¬(cycleGraph 5).Adj i d ∧
        ¬(cycleGraph 5).Adj j b ∧
        a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        i ≠ d ∧ j ≠ a ∧ j ≠ b := by
  decide

/-- An indexed induced five-cycle forces the complete `C₅`-blow-up
classification. -/
lemma hasWOWII314StructuralClassification_of_inducedC5Embedding
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (c : Fin 5 → α) (hc : IsInducedC5Embedding G c) :
    HasWOWII314StructuralClassification G := by
  let bag : α → Fin 5 := fun x => Classical.choose
    (existsUnique_C5BagSpec G hG hTriFree hNoP5 c hc x)
  have hbagSpec : ∀ x : α, C5BagSpec G c x (bag x) := by
    intro x
    exact (Classical.choose_spec
      (existsUnique_C5BagSpec G hG hTriFree hNoP5 c hc x)).1
  have hbagUnique : ∀ x : α, ∀ i : Fin 5, C5BagSpec G c x i → bag x = i := by
    intro x i hi
    exact (Classical.choose_spec
      (existsUnique_C5BagSpec G hG hTriFree hNoP5 c hc x)).2 i hi
  have hcycleBag : ∀ i : Fin 5, bag (c i) = i := by
    intro i
    exact hbagUnique (c i) i (C5BagSpec_cycleVertex G c hc i)
  have hsurj : Function.Surjective bag := by
    intro i
    exact ⟨c i, hcycleBag i⟩
  have hadj : ∀ x y : α, G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y) := by
    intro x y
    constructor
    · intro hxy
      by_contra hn
      obtain ⟨k, hik, hjk⟩ := fin5_common_neighbor_of_not_adj (bag x) (bag y) hn
      have hxk : G.Adj x (c k) := (hbagSpec x k).mpr hik
      have hyk : G.Adj y (c k) := (hbagSpec y k).mpr hjk
      exact hTriFree x y (c k) hxy hyk hxk.symm
    · intro hij
      by_contra hnxy
      obtain ⟨a, b, d, hia, hib, hbd, hjd,
        hnab, hnad, hnja, hnid, hnjb,
        hab, had, hbdne, hid, hja, hjb⟩ :=
        fin5_missing_blowup_edge_pattern (bag x) (bag y) hij
      have hax : G.Adj (c a) x := ((hbagSpec x a).mpr hia).symm
      have hxb : G.Adj x (c b) := (hbagSpec x b).mpr hib
      have hbdG : G.Adj (c b) (c d) := (hc.2 b d).mpr hbd
      have hdy : G.Adj (c d) y := ((hbagSpec y d).mpr hjd).symm
      have hnabG : ¬G.Adj (c a) (c b) := by rw [hc.2 a b]; exact hnab
      have hnadG : ¬G.Adj (c a) (c d) := by rw [hc.2 a d]; exact hnad
      have hnay : ¬G.Adj (c a) y := by
        intro h
        exact hnja ((hbagSpec y a).mp h.symm)
      have hnxd : ¬G.Adj x (c d) := by
        intro h
        exact hnid ((hbagSpec x d).mp h)
      have hnby : ¬G.Adj (c b) y := by
        intro h
        exact hnjb ((hbagSpec y b).mp h.symm)
      have hca_cb : c a ≠ c b := fun h => hab (hc.1 h)
      have hca_cd : c a ≠ c d := fun h => had (hc.1 h)
      have hcb_cd : c b ≠ c d := fun h => hbdne (hc.1 h)
      have hca_y : c a ≠ y := by
        intro h
        subst y
        have hEq : bag (c a) = bag x := by
          simpa [hcycleBag a] using hja.symm
        exact hnxy (hEq ▸ hax.symm)
      have hx_cd : x ≠ c d := by
        intro h
        subst x
        exact hid (hcycleBag d)
      have hx_y : x ≠ y := by
        intro h
        subst y
        exact hij (by simpa using rfl)
      have hcb_y : c b ≠ y := by
        intro h
        subst y
        exact hjb (hcycleBag b)
      apply hNoP5 (c a) x (c b) (c d) y
      unfold FormsInducedP5
      exact ⟨hax.ne, hca_cb, hca_cd, hca_y,
        hxb.ne, hx_cd, hx_y,
        hcb_cd, hcb_y, hdy.ne,
        hax, hxb, hbdG, hdy,
        hnabG, hnadG, hnay, hnxd, hnxy, hnby⟩
  exact Or.inr ⟨bag, hsurj, hadj⟩

/-- The same classification, starting from the explicit ordered cycle witness. -/
lemma hasWOWII314StructuralClassification_of_FormsInducedC5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {x0 x1 x2 x3 x4 : α}
    (hC : FormsInducedC5 G x0 x1 x2 x3 x4) :
    HasWOWII314StructuralClassification G := by
  obtain ⟨c, hc⟩ := exists_inducedC5Embedding_of_FormsInducedC5 G hC
  exact hasWOWII314StructuralClassification_of_inducedC5Embedding
    G hG hTriFree hNoP5 c hc

end WrittenOnTheWallII.GraphConjecture314
