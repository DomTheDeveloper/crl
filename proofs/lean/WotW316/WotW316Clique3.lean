import WotW316Bounds
import WotW316Partitions

/-!
# The three-vertex core case for Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

lemma sum_compl_degrees_exact
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ v, Gᶜ.degree v) =
      (pendantVertices G).card * (Fintype.card α - 2) +
        (pendantVertices G).card * ((coreVertices G).card - 1) +
          ∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card := by
  rw [sum_degrees_split G Gᶜ, sum_compl_degrees_on_pendants G,
    sum_core_compl_degrees G hleaf_core]
  omega

/-- If the core has three vertices, the degree hypothesis forces it to be a clique. -/
theorem core_clique_of_card_eq_three
    (hG : G.Connected)
    (hP : (pendantVertices G).Nonempty)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (havg : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card)
    (hcard : (coreVertices G).card = 3) :
    ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v := by
  classical
  have hexact := sum_compl_degrees_exact G hleaf_core
  have hupper := upper_bound_sum_compl_degrees_of_average G hG havg
  have hpart := pendant_card_add_core_card G
  have hn : Fintype.card α = (pendantVertices G).card + 3 := by omega
  have hsub : Fintype.card α - 2 = (pendantVertices G).card + 1 := by omega
  have hbase :
      (pendantVertices G).card * (Fintype.card α - 2) +
          (pendantVertices G).card * ((coreVertices G).card - 1) =
        (pendantVertices G).card * Fintype.card α := by
    rw [hsub, hcard, hn]
    norm_num
    ring
  have hleZero :
      ((pendantVertices G).card * (Fintype.card α - 2) +
          (pendantVertices G).card * ((coreVertices G).card - 1)) +
          (∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card) ≤
        (pendantVertices G).card * (Fintype.card α - 2) +
          (pendantVertices G).card * ((coreVertices G).card - 1) := by
    calc
      _ = ∑ v, Gᶜ.degree v := hexact.symm
      _ ≤ (pendantVertices G).card * Fintype.card α := hupper
      _ = _ := hbase.symm
  have hzero :
      (∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card) = 0 := by
    omega
  intro u hu v hv huv
  by_contra hnot
  have hcomp : Gᶜ.Adj u v := by
    simp [huv, hnot]
  have hmem : v ∈ coreComplementNeighbors G u := by
    exact Finset.mem_filter.mpr ⟨hv, hcomp⟩
  have hpos : 0 < (coreComplementNeighbors G u).card :=
    Finset.card_pos.mpr ⟨v, hmem⟩
  have hle :
      (coreComplementNeighbors G u).card ≤
        ∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card := by
    exact Finset.single_le_sum
      (s := coreVertices G)
      (f := fun c => (coreComplementNeighbors G c).card)
      (fun _ _ => Nat.zero_le _) hu
  omega

#print axioms core_clique_of_card_eq_three

end

end WrittenOnTheWallII.GraphConjecture316
