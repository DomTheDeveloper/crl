import WOWII.ZZGraphConjecture314MinimalTDSStructure

/-!
In a triangle-free induced-P5-free graph, the graph induced by a minimal total
dominating set has every degree between one and two.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma one_le_induced_minimalTDS_degree
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    (r : (S : Set α)) :
    1 ≤ (G.induce (S : Set α)).degree r := by
  rw [← card_neighborFinset_eq_degree, Finset.one_le_card]
  obtain ⟨y, hyS, hry⟩ := hS.1 (r : α)
  refine ⟨⟨y, by simpa using hyS⟩, ?_⟩
  simpa only [mem_neighborFinset] using hry

lemma induced_minimalTDS_degree_le_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    (r : (S : Set α)) :
    (G.induce (S : Set α)).degree r ≤ 2 := by
  rw [← card_neighborFinset_eq_degree]
  by_contra h
  have hthree : 2 < ((G.induce (S : Set α)).neighborFinset r).card := by omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hthree
  have hraInd : (G.induce (S : Set α)).Adj r a :=
    (mem_neighborFinset _ _ _).mp ha
  have hrbInd : (G.induce (S : Set α)).Adj r b :=
    (mem_neighborFinset _ _ _).mp hb
  have hrcInd : (G.induce (S : Set α)).Adj r c :=
    (mem_neighborFinset _ _ _).mp hc
  have hra : G.Adj (r : α) (a : α) := hraInd
  have hrb : G.Adj (r : α) (b : α) := hrbInd
  have hrc : G.Adj (r : α) (c : α) := hrcInd
  have hab' : (a : α) ≠ b := by
    intro hEq
    exact hab (Subtype.ext hEq)
  have hac' : (a : α) ≠ c := by
    intro hEq
    exact hac (Subtype.ext hEq)
  have hbc' : (b : α) ≠ c := by
    intro hEq
    exact hbc (Subtype.ext hEq)
  exact no_three_mem_minimalTDS_adj_common_center G hTriFree hNoP5 hS
    (by simpa using a.property) (by simpa using b.property) (by simpa using c.property)
    hab' hac' hbc' hra hrb hrc

end WrittenOnTheWallII.GraphConjecture314
