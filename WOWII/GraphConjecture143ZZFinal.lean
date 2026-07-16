import WOWII.GraphConjecture143Proof
import WOWII.GraphConjecture143Next
import WOWII.GraphConjecture143Leaves
import WOWII.GraphConjecture143Boundary
import WOWII.GraphConjecture143CycleAttach

/-!
A complete modular, sorry-free proof of WOWII Graph Conjecture 143,
assembled from independently verified graph-theoretic lemmas.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma finset_card_le_largestInducedTreeSize
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hT : (G.induce (S : Set α)).IsTree) :
    S.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨T, rfl, _⟩
      exact T.card_le_univ⟩
  · exact ⟨S, rfl, hT⟩

lemma conjecture143_of_sigma_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hcyc : ¬G.IsAcyclic)
    (hσ : secondSmallestDegree G = 1) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  obtain ⟨x, y, hxy, hdx, hdy⟩ :=
    exists_two_degree_one_of_secondSmallestDegree_eq_one G hG hσ
  obtain ⟨S, hxS, hyS, hT, hmax⟩ :=
    exists_max_induced_tree_containing G hG x y
  obtain ⟨z, hzS, a, haS, b, hbS, hab, hza, hzb⟩ :=
    exists_external_vertex_with_two_tree_neighbors G hG hcyc hxS hyS hT hmax
  have hcard : G.girth + 1 ≤ S.card :=
    girth_add_one_le_card_of_tree_with_two_leaves_and_external_chord
      G hT hxS hyS hxy hdx hdy hzS haS hbS hab hza hzb
  have htree : S.card ≤ largestInducedTreeSize G :=
    finset_card_le_largestInducedTreeSize G hT
  have hNat : G.girth + 1 ≤ largestInducedTreeSize G := hcard.trans htree
  have hReal : (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast hNat
  simpa [hσ] using hReal

/-- WOWII Graph Conjecture 143. -/
theorem conjecture143_proved
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hσ : 0 < secondSmallestDegree G) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  by_cases hacyc : G.IsAcyclic
  · exact conjecture143_of_girth_zero G hG hσ hacyc.girth_eq_zero
  · by_cases hσone : secondSmallestDegree G = 1
    · exact conjecture143_of_sigma_one G hG hacyc hσone
    · have hσtwo : 2 ≤ secondSmallestDegree G := by omega
      exact conjecture143_of_cyclic_sigma_ge_two G hacyc hσtwo

end WrittenOnTheWallII.GraphConjecture143
