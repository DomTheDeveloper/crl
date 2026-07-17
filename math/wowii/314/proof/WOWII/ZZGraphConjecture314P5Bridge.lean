import WOWII.ZZGraphConjecture314PathTree

/-!
An explicit induced `P₅` supplies the five-vertex witness in the official
`largestInducedPathSize` invariant used by WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma largestInducedPathSize_ge_five_of_FormsInducedP5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x0 x1 x2 x3 x4 : α}
    (h : FormsInducedP5 G x0 x1 x2 x3 x4) :
    5 ≤ largestInducedPathSize G := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    ha01, ha12, ha23, ha34, hn02, hn03, hn04, hn13, hn14, hn24⟩
  have ha10 : G.Adj x1 x0 := ha01.symm
  have ha21 : G.Adj x2 x1 := ha12.symm
  have ha32 : G.Adj x3 x2 := ha23.symm
  have ha43 : G.Adj x4 x3 := ha34.symm
  have hn20 : ¬G.Adj x2 x0 := fun h => hn02 h.symm
  have hn30 : ¬G.Adj x3 x0 := fun h => hn03 h.symm
  have hn40 : ¬G.Adj x4 x0 := fun h => hn04 h.symm
  have hn31 : ¬G.Adj x3 x1 := fun h => hn13 h.symm
  have hn41 : ¬G.Adj x4 x1 := fun h => hn14 h.symm
  have hn42 : ¬G.Adj x4 x2 := fun h => hn24 h.symm
  let S : Finset α := {x0, x1, x2, x3, x4}
  let p : G.Walk x0 x4 :=
    .cons ha01 (.cons ha12 (.cons ha23 (.cons ha34 .nil)))
  have hp : p.IsPath := by
    simp [p, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hScard : S.card = 5 := by
    simp [S, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hsupp : p.support.toFinset = S := by
    simp [p, S]
  let hiso : G.induce (S : Set α) ≃g p.toSubgraph.coe :=
    { toFun := fun a => ⟨a, by
          have haFin : (a : α) ∈ p.support.toFinset := by
            rw [hsupp]
            simpa using a.property
          exact p.mem_verts_toSubgraph.mpr (by simpa using haFin)⟩
      invFun := fun a => ⟨a, by
          have haSupp : (a : α) ∈ p.support := p.mem_verts_toSubgraph.mp a.property
          have haFin : (a : α) ∈ p.support.toFinset := by simpa using haSupp
          rw [hsupp] at haFin
          simpa using haFin⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl
      map_rel_iff' := by
        intro a b
        rcases a with ⟨a, ha⟩
        rcases b with ⟨b, hb⟩
        change p.toSubgraph.Adj a b ↔ G.Adj a b
        constructor
        · exact p.toSubgraph.adj_sub
        · intro hab
          rw [Walk.adj_toSubgraph_iff_mem_edges]
          simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
            rcases hb with rfl | rfl | rfl | rfl | rfl <;>
            simp_all [p, Sym2.eq, Sym2.rel_iff'] <;> grind }
  have htree : (G.induce (S : Set α)).IsTree := by
    exact hiso.isTree_iff.mpr (path_toSubgraph_isTree hp)
  let X0 : (S : Set α) := ⟨x0, by simp [S]⟩
  let X1 : (S : Set α) := ⟨x1, by simp [S]⟩
  let X2 : (S : Set α) := ⟨x2, by simp [S]⟩
  let X3 : (S : Set α) := ⟨x3, by simp [S]⟩
  let X4 : (S : Set α) := ⟨x4, by simp [S]⟩
  have hmem (w : (S : Set α)) :
      (w : α) = x0 ∨ (w : α) = x1 ∨ (w : α) = x2 ∨
      (w : α) = x3 ∨ (w : α) = x4 := by
    simpa [S] using w.property
  have degree_le_two_of_pair
      (v a b : (S : Set α))
      (hv : ∀ w : (S : Set α), (G.induce (S : Set α)).Adj v w → w = a ∨ w = b) :
      (G.induce (S : Set α)).degree v ≤ 2 := by
    rw [← card_neighborFinset_eq_degree]
    calc
      ((G.induce (S : Set α)).neighborFinset v).card ≤ ({a, b} : Finset (S : Set α)).card := by
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton]
        apply hv w
        simpa only [mem_neighborFinset] using hw
      _ ≤ 2 := Finset.card_le_two
  have hdeg : ∀ v : (S : Set α), (G.induce (S : Set α)).degree v ≤ 2 := by
    intro v
    rcases hmem v with hv0 | hv1 | hv2 | hv3 | hv4
    · have hv : v = X0 := by apply Subtype.ext; exact hv0
      subst v
      apply degree_le_two_of_pair X0 X1 X1
      intro w hw
      change G.Adj x0 (w : α) at hw
      rcases hmem w with hw0 | hw1 | hw2 | hw3 | hw4
      · exact (G.loopless x0 (by simpa [hw0] using hw)).elim
      · left; apply Subtype.ext; exact hw1
      · exact (hn02 (by simpa [hw2] using hw)).elim
      · exact (hn03 (by simpa [hw3] using hw)).elim
      · exact (hn04 (by simpa [hw4] using hw)).elim
    · have hv : v = X1 := by apply Subtype.ext; exact hv1
      subst v
      apply degree_le_two_of_pair X1 X0 X2
      intro w hw
      change G.Adj x1 (w : α) at hw
      rcases hmem w with hw0 | hw1 | hw2 | hw3 | hw4
      · left; apply Subtype.ext; exact hw0
      · exact (G.loopless x1 (by simpa [hw1] using hw)).elim
      · right; apply Subtype.ext; exact hw2
      · exact (hn13 (by simpa [hw3] using hw)).elim
      · exact (hn14 (by simpa [hw4] using hw)).elim
    · have hv : v = X2 := by apply Subtype.ext; exact hv2
      subst v
      apply degree_le_two_of_pair X2 X1 X3
      intro w hw
      change G.Adj x2 (w : α) at hw
      rcases hmem w with hw0 | hw1 | hw2 | hw3 | hw4
      · exact (hn20 (by simpa [hw0] using hw)).elim
      · left; apply Subtype.ext; exact hw1
      · exact (G.loopless x2 (by simpa [hw2] using hw)).elim
      · right; apply Subtype.ext; exact hw3
      · exact (hn24 (by simpa [hw4] using hw)).elim
    · have hv : v = X3 := by apply Subtype.ext; exact hv3
      subst v
      apply degree_le_two_of_pair X3 X2 X4
      intro w hw
      change G.Adj x3 (w : α) at hw
      rcases hmem w with hw0 | hw1 | hw2 | hw3 | hw4
      · exact (hn30 (by simpa [hw0] using hw)).elim
      · exact (hn31 (by simpa [hw1] using hw)).elim
      · left; apply Subtype.ext; exact hw2
      · exact (G.loopless x3 (by simpa [hw3] using hw)).elim
      · right; apply Subtype.ext; exact hw4
    · have hv : v = X4 := by apply Subtype.ext; exact hv4
      subst v
      apply degree_le_two_of_pair X4 X3 X3
      intro w hw
      change G.Adj x4 (w : α) at hw
      rcases hmem w with hw0 | hw1 | hw2 | hw3 | hw4
      · exact (hn40 (by simpa [hw0] using hw)).elim
      · exact (hn41 (by simpa [hw1] using hw)).elim
      · exact (hn42 (by simpa [hw2] using hw)).elim
      · left; apply Subtype.ext; exact hw3
      · exact (G.loopless x4 (by simpa [hw4] using hw)).elim
  unfold largestInducedPathSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨T, rfl, -, -⟩
      exact T.card_le_univ⟩
  · exact ⟨S, hScard, htree, hdeg⟩

lemma no_FormsInducedP5_of_largestInducedPathSize_le_four
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hPath : largestInducedPathSize G ≤ 4) :
    ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 hP5
  have hfive := largestInducedPathSize_ge_five_of_FormsInducedP5 G hP5
  omega

end WrittenOnTheWallII.GraphConjecture314
