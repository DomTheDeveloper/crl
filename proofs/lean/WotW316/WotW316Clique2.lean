import WotW316Partitions
import WotW316Bounds

/-!
# The two-vertex core case for Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

lemma sum_degrees_on_pendants :
    (∑ l ∈ pendantVertices G, G.degree l) = (pendantVertices G).card := by
  classical
  calc
    (∑ l ∈ pendantVertices G, G.degree l) =
        ∑ _l ∈ pendantVertices G, 1 := by
          apply Finset.sum_congr rfl
          intro l hl
          simpa [pendantVertices] using hl
    _ = (pendantVertices G).card := by simp

lemma sum_degrees_exact
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ v, G.degree v) =
      (pendantVertices G).card + (pendantVertices G).card +
        ∑ c ∈ coreVertices G, (coreNeighbors G c).card := by
  have hcoreSum :
      (∑ c ∈ coreVertices G, G.degree c) =
        (pendantVertices G).card +
          ∑ c ∈ coreVertices G, (coreNeighbors G c).card := by
    calc
      (∑ c ∈ coreVertices G, G.degree c) =
          ∑ c ∈ coreVertices G,
            ((pendantNeighbors G c).card + (coreNeighbors G c).card) := by
              apply Finset.sum_congr rfl
              intro c _
              rw [degree_eq_pendantNeighbors_add_coreNeighbors G c]
      _ = (∑ c ∈ coreVertices G, (pendantNeighbors G c).card) +
          ∑ c ∈ coreVertices G, (coreNeighbors G c).card := by
              rw [Finset.sum_add_distrib]
      _ = (pendantVertices G).card +
          ∑ c ∈ coreVertices G, (coreNeighbors G c).card := by
              rw [sum_card_pendantNeighbors G hleaf_core]
  calc
    (∑ v, G.degree v) =
        (∑ l ∈ pendantVertices G, G.degree l) +
          ∑ c ∈ coreVertices G, G.degree c := sum_degrees_split G G
    _ = (pendantVertices G).card +
          ((pendantVertices G).card +
            ∑ c ∈ coreVertices G, (coreNeighbors G c).card) := by
          rw [sum_degrees_on_pendants G, hcoreSum]
    _ = (pendantVertices G).card + (pendantVertices G).card +
          ∑ c ∈ coreVertices G, (coreNeighbors G c).card := by omega

/-- If the core has two vertices in a connected graph, they must be adjacent. -/
theorem core_clique_of_card_eq_two
    (hG : G.Connected)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcard : (coreVertices G).card = 2) :
    ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v := by
  classical
  intro u hu v hv huv
  by_contra hnot
  have hpairSub : ({u, v} : Finset α) ⊆ coreVertices G := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  have hpairCard : ({u, v} : Finset α).card = 2 := by simp [huv]
  have hcore : coreVertices G = {u, v} :=
    Finset.eq_of_subset_of_card_le hpairSub (by simpa [hcard, hpairCard]) |>.symm
  have huempty : coreNeighbors G u = ∅ := by
    ext x
    simp only [Finset.mem_empty, iff_false]
    intro hx
    change x ∈ (coreVertices G).filter (fun c => G.Adj u c) at hx
    rcases Finset.mem_filter.mp hx with ⟨hxCore, hux⟩
    rw [hcore] at hxCore
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxCore
    rcases hxCore with rfl | rfl
    · exact G.loopless u hux
    · exact hnot hux
  have hvempty : coreNeighbors G v = ∅ := by
    ext x
    simp only [Finset.mem_empty, iff_false]
    intro hx
    change x ∈ (coreVertices G).filter (fun c => G.Adj v c) at hx
    rcases Finset.mem_filter.mp hx with ⟨hxCore, hvx⟩
    rw [hcore] at hxCore
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxCore
    rcases hxCore with rfl | rfl
    · exact hnot hvx.symm
    · exact G.loopless v hvx
  have hsumCore :
      (∑ c ∈ coreVertices G, (coreNeighbors G c).card) = 0 := by
    rw [hcore]
    simp [huv, huempty, hvempty]
  have hsum := sum_degrees_exact G hleaf_core
  rw [hsumCore] at hsum
  have hhand := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  have hedge : G.edgeFinset.card = (pendantVertices G).card := by
    omega
  have hpart := pendant_card_add_core_card G
  have hconn := hG.card_vert_le_card_edgeSet_add_one
  have hedgeSet : Nat.card G.edgeSet = G.edgeFinset.card := by
    simpa [Nat.card_eq_fintype_card, edgeFinset] using Set.ncard_eq_toFinset_card G.edgeSet
  rw [hedgeSet, hedge] at hconn
  rw [hcard] at hpart
  have hn : Fintype.card α = (pendantVertices G).card + 2 := by omega
  rw [Nat.card_eq_fintype_card, hn] at hconn
  omega

#print axioms core_clique_of_card_eq_two

end

end WrittenOnTheWallII.GraphConjecture316
