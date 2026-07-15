import WotW316Count

/-!
# Exact neighborhood decompositions for Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Pendant neighbors of a vertex. -/
def pendantNeighbors (v : α) : Finset α :=
  (pendantVertices G).filter fun l => G.Adj v l

/-- Core neighbors in the complement graph. -/
def coreComplementNeighbors (v : α) : Finset α :=
  (coreVertices G).filter fun c => Gᶜ.Adj v c

lemma pendant_core_partition :
    pendantVertices G ∪ coreVertices G = Finset.univ := by
  classical
  ext v
  simp [coreVertices]

lemma pendant_core_disjoint :
    Disjoint (pendantVertices G) (coreVertices G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxC
  have hxnot : x ∉ pendantVertices G := by
    simpa [coreVertices] using hxC
  exact hxnot hxP

lemma neighborFinset_eq_pendant_union_core (v : α) :
    G.neighborFinset v = pendantNeighbors G v ∪ coreNeighbors G v := by
  classical
  ext x
  by_cases hx : x ∈ pendantVertices G
  · have hxnot : x ∉ coreVertices G := by
      simpa [coreVertices] using hx
    simp [pendantNeighbors, coreNeighbors, hx, hxnot, G.mem_neighborFinset]
  · have hxcore : x ∈ coreVertices G := by
      simp [coreVertices, hx]
    simp [pendantNeighbors, coreNeighbors, hx, hxcore, G.mem_neighborFinset]

lemma pendantNeighbors_disjoint_coreNeighbors (v : α) :
    Disjoint (pendantNeighbors G v) (coreNeighbors G v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxC
  have hxP' := (Finset.mem_filter.mp hxP).1
  have hxC' := (Finset.mem_filter.mp hxC).1
  exact (Finset.disjoint_left.mp (pendant_core_disjoint G)) hxP' hxC'

lemma degree_eq_pendantNeighbors_add_coreNeighbors (v : α) :
    G.degree v = (pendantNeighbors G v).card + (coreNeighbors G v).card := by
  rw [← G.card_neighborFinset_eq_degree, neighborFinset_eq_pendant_union_core]
  exact Finset.card_union_of_disjoint (pendantNeighbors_disjoint_coreNeighbors G v)

lemma card_filter_rel_eq_sum_ite
    (s : Finset α) (r : α → Prop) [DecidablePred r] :
    (s.filter r).card = ∑ x ∈ s, if r x then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.filter_insert]
      by_cases hra : r a
      · rw [if_pos hra]
        have haf : a ∉ s.filter r := by
          simp [ha]
        rw [Finset.card_insert_of_notMem haf, Finset.sum_insert ha, if_pos hra, ih]
        omega
      · rw [if_neg hra, Finset.sum_insert ha, if_neg hra, ih]
        simp

lemma sum_card_pendantNeighbors
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ c ∈ coreVertices G, (pendantNeighbors G c).card) =
      (pendantVertices G).card := by
  classical
  calc
    (∑ c ∈ coreVertices G, (pendantNeighbors G c).card) =
        ∑ c ∈ coreVertices G,
          ∑ l ∈ pendantVertices G, if G.Adj c l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            exact card_filter_rel_eq_sum_ite (pendantVertices G) (fun l => G.Adj c l)
    _ = ∑ l ∈ pendantVertices G,
          ∑ c ∈ coreVertices G, if G.Adj l c then 1 else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _
            apply Finset.sum_congr rfl
            intro c _
            simpa only [G.adj_comm]
    _ = ∑ l ∈ pendantVertices G, (coreNeighbors G l).card := by
            apply Finset.sum_congr rfl
            intro l _
            unfold coreNeighbors
            exact (card_filter_rel_eq_sum_ite
              (coreVertices G) (fun c => G.Adj l c)).symm
    _ = ∑ _l ∈ pendantVertices G, 1 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [card_coreNeighbors_of_pendant G hl hleaf_core]
    _ = (pendantVertices G).card := by simp

lemma complementNeighborFinset_eq_missingPendant_union_core
    {c : α} (hc : c ∈ coreVertices G) :
    Gᶜ.neighborFinset c =
      missingPendantNeighbors G c ∪ coreComplementNeighbors G c := by
  classical
  ext x
  by_cases hx : x ∈ pendantVertices G
  · have hxcore : x ∉ coreVertices G := by
      simpa [coreVertices] using hx
    have hne : c ≠ x := by
      intro h
      subst c
      exact hxcore hc
    simp [missingPendantNeighbors, coreComplementNeighbors, hx, hxcore,
      (Gᶜ).mem_neighborFinset, hne]
  · have hxcore : x ∈ coreVertices G := by
      simp [coreVertices, hx]
    simp [missingPendantNeighbors, coreComplementNeighbors, hx, hxcore,
      (Gᶜ).mem_neighborFinset]

lemma missingPendant_disjoint_coreComplement (c : α) :
    Disjoint (missingPendantNeighbors G c) (coreComplementNeighbors G c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxC
  have hxP' := (Finset.mem_filter.mp hxP).1
  have hxC' := (Finset.mem_filter.mp hxC).1
  exact (Finset.disjoint_left.mp (pendant_core_disjoint G)) hxP' hxC'

lemma degree_compl_eq_missingPendant_add_core
    {c : α} (hc : c ∈ coreVertices G) :
    Gᶜ.degree c =
      (missingPendantNeighbors G c).card + (coreComplementNeighbors G c).card := by
  rw [← (Gᶜ).card_neighborFinset_eq_degree,
    complementNeighborFinset_eq_missingPendant_union_core G hc]
  exact Finset.card_union_of_disjoint (missingPendant_disjoint_coreComplement G c)

lemma sum_core_compl_degrees
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ c ∈ coreVertices G, Gᶜ.degree c) =
      (pendantVertices G).card * ((coreVertices G).card - 1) +
        ∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card := by
  calc
    (∑ c ∈ coreVertices G, Gᶜ.degree c) =
        ∑ c ∈ coreVertices G,
          ((missingPendantNeighbors G c).card + (coreComplementNeighbors G c).card) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [degree_compl_eq_missingPendant_add_core G hc]
    _ = (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) +
        ∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card := by
            rw [Finset.sum_add_distrib]
    _ = (pendantVertices G).card * ((coreVertices G).card - 1) +
        ∑ c ∈ coreVertices G, (coreComplementNeighbors G c).card := by
            rw [sum_card_missingPendantNeighbors G hleaf_core]

#print axioms sum_card_pendantNeighbors
#print axioms sum_core_compl_degrees

end

end WrittenOnTheWallII.GraphConjecture316
