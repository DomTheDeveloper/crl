import WotW316Clique2
import WotW316Clique3
import WotW316StructureExtra

/-!
# Complete proof of Written on the Wall II, Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The exact research-open theorem from `GraphConjecture316.lean`. -/
theorem conjecture316_solved (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    G.IsWellTotallyDominated := by
  classical
  by_cases hP : (pendantVertices G).Nonempty
  · by_cases hadjP : ∃ l ∈ pendantVertices G, ∃ c ∈ pendantVertices G, G.Adj l c
    · rcases hadjP with ⟨l, hl, c, hc, hlc⟩
      exact wellTotallyDominated_of_all_pendant G
        (all_pendant_of_adjacent_pendants G hG hl hc hlc)
    · have hleaf_core :
          ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G := by
        intro l hl c hlc
        have hcnot : c ∉ pendantVertices G := by
          intro hc
          exact hadjP ⟨l, hl, c, hc, hlc⟩
        simp [coreVertices, hcnot]
      have hqle : (coreVertices G).card ≤ 3 :=
        core_card_le_three G hG hP hleaf_core h
      have hFne := forcedVertices_nonempty G hP hleaf_core
      have hqpos : 0 < (coreVertices G).card := by
        have hsub : forcedVertices G ⊆ coreVertices G := by
          intro c hc
          exact ((mem_forcedVertices_iff G).1 hc).1
        exact Finset.card_pos.mpr ⟨hFne.some, hsub hFne.some_mem⟩
      have hqcases :
          (coreVertices G).card = 1 ∨ (coreVertices G).card = 2 ∨
            (coreVertices G).card = 3 := by
        omega
      have hclique :
          ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v := by
        rcases hqcases with hq1 | hq2 | hq3
        · intro u hu v hv huv
          have hpairSub : ({u, v} : Finset α) ⊆ coreVertices G := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hu
            · exact hv
          have hpairCard : ({u, v} : Finset α).card = 2 := by simp [huv]
          have hle := Finset.card_le_card hpairSub
          rw [hpairCard, hq1] at hle
          omega
        · exact core_clique_of_card_eq_two G hG hleaf_core hq2
        · exact core_clique_of_card_eq_three G hG hP hleaf_core h hq3
      exact wellTotallyDominated_of_clique_core G hP hleaf_core hclique
  · have hPempty : pendantVertices G = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hP
    have hupper := upper_bound_sum_compl_degrees_of_average G hG h
    have hsum0 : (∑ v, Gᶜ.degree v) = 0 := by
      rw [hPempty] at hupper
      simp at hupper
      omega
    letI : Nonempty α := hG.nonempty
    apply wellTotallyDominated_of_complete G
    intro u v huv
    by_contra hnot
    have hcomp : Gᶜ.Adj u v := by simp [huv, hnot]
    have hdegpos : 0 < Gᶜ.degree u := by
      rw [(Gᶜ).degree_pos_iff_exists_adj]
      exact ⟨v, hcomp⟩
    have hle : Gᶜ.degree u ≤ ∑ x, Gᶜ.degree x := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    omega

#print axioms conjecture316_solved

end

end WrittenOnTheWallII.GraphConjecture316
