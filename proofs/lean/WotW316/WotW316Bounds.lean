import WotW316Count
import WotW316StructureExtra

/-!
# Complement-degree bounds for Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

lemma degree_compl_of_pendant {l : α} (hl : l ∈ pendantVertices G) :
    Gᶜ.degree l = Fintype.card α - 2 := by
  rw [G.degree_compl]
  have hdeg : G.degree l = 1 := by simpa [pendantVertices] using hl
  rw [hdeg]
  omega

lemma missingPendantNeighbors_subset_compl_neighborFinset
    {c : α} (hc : c ∈ coreVertices G) :
    missingPendantNeighbors G c ⊆ Gᶜ.neighborFinset c := by
  classical
  intro l hl
  have hlP : l ∈ pendantVertices G := (Finset.mem_filter.mp hl).1
  have hnot : ¬G.Adj c l := (Finset.mem_filter.mp hl).2
  have hdeg : G.degree l = 1 := by simpa [pendantVertices] using hlP
  have hne : c ≠ l := by
    intro hcl
    subst c
    exact ((mem_coreVertices_iff G).1 hc) hdeg
  have hadj : Gᶜ.Adj c l := by
    simp [hne, hnot]
  simpa only [(Gᶜ).mem_neighborFinset] using hadj

lemma card_missingPendantNeighbors_le_degree_compl
    {c : α} (hc : c ∈ coreVertices G) :
    (missingPendantNeighbors G c).card ≤ Gᶜ.degree c := by
  rw [← (Gᶜ).card_neighborFinset_eq_degree]
  exact Finset.card_le_card (missingPendantNeighbors_subset_compl_neighborFinset G hc)

lemma pendant_card_add_core_card :
    (pendantVertices G).card + (coreVertices G).card = Fintype.card α := by
  classical
  have hle : (pendantVertices G).card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ (pendantVertices G))
  rw [coreVertices, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ]
  omega

lemma sum_degrees_split (H : SimpleGraph α) [DecidableRel H.Adj] :
    (∑ v, H.degree v) =
      (∑ v ∈ pendantVertices G, H.degree v) +
        ∑ v ∈ coreVertices G, H.degree v := by
  classical
  have hdisj : Disjoint (pendantVertices G) (coreVertices G) := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxC
    exact (Finset.mem_sdiff.mp hxC).2 hxP
  have hunion : pendantVertices G ∪ coreVertices G = Finset.univ := by
    ext v
    simp [coreVertices]
  calc
    (∑ v, H.degree v) = ∑ v ∈ pendantVertices G ∪ coreVertices G, H.degree v := by
      rw [hunion]
    _ = (∑ v ∈ pendantVertices G, H.degree v) +
        ∑ v ∈ coreVertices G, H.degree v := by
      rw [Finset.sum_union hdisj]

lemma sum_compl_degrees_on_pendants :
    (∑ l ∈ pendantVertices G, Gᶜ.degree l) =
      (pendantVertices G).card * (Fintype.card α - 2) := by
  classical
  calc
    (∑ l ∈ pendantVertices G, Gᶜ.degree l) =
        ∑ _l ∈ pendantVertices G, (Fintype.card α - 2) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [degree_compl_of_pendant G hl]
    _ = (pendantVertices G).card * (Fintype.card α - 2) := by simp

lemma lower_bound_sum_compl_degrees
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (pendantVertices G).card * (Fintype.card α - 2) +
        (pendantVertices G).card * ((coreVertices G).card - 1) ≤
      ∑ v, Gᶜ.degree v := by
  classical
  rw [sum_degrees_split G Gᶜ, sum_compl_degrees_on_pendants G,
    ← sum_card_missingPendantNeighbors G hleaf_core]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum fun c hc => card_missingPendantNeighbors_le_degree_compl G hc) _

lemma upper_bound_sum_compl_degrees_of_average
    (hG : G.Connected)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    (∑ v, Gᶜ.degree v) ≤ (pendantVertices G).card * Fintype.card α := by
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hG.nonempty
  have hnq : (0 : ℚ) < (Fintype.card α : ℚ) := by exact_mod_cast hn
  unfold averageDegree at h
  have hq := (div_le_iff₀ hnq).mp h
  exact_mod_cast hq

lemma core_card_le_three
    (hG : G.Connected)
    (hP : (pendantVertices G).Nonempty)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    (coreVertices G).card ≤ 3 := by
  let p := (pendantVertices G).card
  let q := (coreVertices G).card
  let n := Fintype.card α
  have hp : 0 < p := by simpa [p] using Finset.card_pos.mpr hP
  have hCne := forcedVertices_nonempty G hP hleaf_core
  have hq : 0 < q := by
    have hsub : forcedVertices G ⊆ coreVertices G := by
      intro c hc
      exact ((mem_forcedVertices_iff G).1 hc).1
    rcases hCne with ⟨c, hcF⟩
    have : 0 < (coreVertices G).card :=
      Finset.card_pos.mpr ⟨c, hsub hcF⟩
    simpa [q] using this
  have hpart : p + q = n := by
    simpa [p, q, n] using pendant_card_add_core_card G
  have hlower := lower_bound_sum_compl_degrees G hleaf_core
  have hupper := upper_bound_sum_compl_degrees_of_average G hG h
  have hineq : p * (n - 2) + p * (q - 1) ≤ p * n := by
    simpa [p, q, n] using le_trans hlower hupper
  have hn2 : 2 ≤ n := by omega
  have hmul : p * ((n - 2) + (q - 1)) ≤ p * n := by
    simpa [Nat.mul_add] using hineq
  have hcancel : (n - 2) + (q - 1) ≤ n :=
    Nat.le_of_mul_le_mul_left hmul hp
  omega

#print axioms core_card_le_three

end

end WrittenOnTheWallII.GraphConjecture316
