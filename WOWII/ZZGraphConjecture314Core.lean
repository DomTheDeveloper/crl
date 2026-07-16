import FormalConjectures.WrittenOnTheWallII.GraphConjecture314

/-!
Reusable total-domination lemmas for WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every vertex of a minimal total dominating set has a private neighbor:
a vertex whose unique neighbor in the dominating set is that selected vertex. -/
lemma exists_private_neighbor_of_mem_minimalTDS
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {v : α} (hv : v ∈ S) :
    ∃ x : α, G.Adj x v ∧ ∀ w ∈ S, G.Adj x w → w = v := by
  have hproper : S.erase v ⊂ S := Finset.erase_ssubset hv
  have hnot : ¬IsTotalDominatingSet G (S.erase v) := hS.2 _ hproper
  unfold IsTotalDominatingSet at hnot
  push_neg at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨w, hwS, hxw⟩ := hS.1 x
  have hw : w = v := by
    by_contra hwv
    exact hx w (Finset.mem_erase.mpr ⟨hwv, hwS⟩) hxw
  subst w
  refine ⟨x, hxw, ?_⟩
  intro y hyS hxy
  by_contra hyv
  exact hx y (Finset.mem_erase.mpr ⟨hyv, hyS⟩) hxy

/-- Every total dominating set in a nonempty graph is nonempty. -/
lemma totalDominatingSet_nonempty [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : IsTotalDominatingSet G S) : S.Nonempty := by
  obtain ⟨w, hw, -⟩ := hS Classical.ofNonempty
  exact ⟨w, hw⟩

/-- A minimal total dominating set has no redundant false-twin pair: if two
selected vertices have identical adjacency to every vertex, one can be removed. -/
lemma not_both_mem_minimalTDS_of_false_twins
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {u v : α} (huv : u ≠ v)
    (htwin : ∀ x : α, G.Adj x u ↔ G.Adj x v) :
    ¬(u ∈ S ∧ v ∈ S) := by
  rintro ⟨huS, hvS⟩
  have hproper : S.erase u ⊂ S := Finset.erase_ssubset huS
  apply hS.2 _ hproper
  intro x
  obtain ⟨w, hwS, hxw⟩ := hS.1 x
  by_cases hwu : w = u
  · subst w
    refine ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hvS⟩, ?_⟩
    exact (htwin x).mp hxw
  · exact ⟨w, Finset.mem_erase.mpr ⟨hwu, hwS⟩, hxw⟩

end WrittenOnTheWallII.GraphConjecture314
