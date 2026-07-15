import WotW316
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Counting reduction for Conjecture 316

The average-degree hypothesis forces the non-pendant core to have at most
three vertices. This file develops the required pendant/core incidence count.
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Core neighbors of a vertex. -/
def coreNeighbors (v : α) : Finset α :=
  (coreVertices G).filter fun c => G.Adj v c

/-- Core vertices not adjacent to a given pendant vertex. -/
def missingCoreNeighbors (l : α) : Finset α :=
  (coreVertices G).filter fun c => ¬ G.Adj l c

/-- Pendant vertices not adjacent to a given core vertex. -/
def missingPendantNeighbors (c : α) : Finset α :=
  (pendantVertices G).filter fun l => ¬ G.Adj c l

lemma coreNeighbors_eq_neighborFinset_of_pendant
    {l : α} (hl : l ∈ pendantVertices G)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    coreNeighbors G l = G.neighborFinset l := by
  classical
  ext c
  simp only [coreNeighbors, Finset.mem_filter, G.mem_neighborFinset]
  constructor
  · exact fun h => h.2
  · intro hlc
    exact ⟨hleaf_core l hl c hlc, hlc⟩

lemma card_coreNeighbors_of_pendant
    {l : α} (hl : l ∈ pendantVertices G)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (coreNeighbors G l).card = 1 := by
  rw [coreNeighbors_eq_neighborFinset_of_pendant G hl hleaf_core,
    G.card_neighborFinset_eq_degree]
  simpa [pendantVertices] using hl

lemma missingCoreNeighbors_eq_sdiff (l : α) :
    missingCoreNeighbors G l = coreVertices G \ coreNeighbors G l := by
  classical
  ext c
  constructor
  · intro hc
    have hcCore : c ∈ coreVertices G := (Finset.mem_filter.mp hc).1
    have hnot : ¬G.Adj l c := (Finset.mem_filter.mp hc).2
    refine Finset.mem_sdiff.mpr ⟨hcCore, ?_⟩
    intro hcN
    exact hnot (Finset.mem_filter.mp hcN).2
  · intro hc
    rcases Finset.mem_sdiff.mp hc with ⟨hcCore, hcN⟩
    refine Finset.mem_filter.mpr ⟨hcCore, ?_⟩
    intro hlc
    exact hcN (Finset.mem_filter.mpr ⟨hcCore, hlc⟩)

lemma card_missingCoreNeighbors_of_pendant
    {l : α} (hl : l ∈ pendantVertices G)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (missingCoreNeighbors G l).card = (coreVertices G).card - 1 := by
  rw [missingCoreNeighbors_eq_sdiff]
  have hsub : coreNeighbors G l ⊆ coreVertices G := by
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    card_coreNeighbors_of_pendant G hl hleaf_core]

lemma sum_card_missingPendantNeighbors
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) =
      (pendantVertices G).card * ((coreVertices G).card - 1) := by
  classical
  have hdouble :
      (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) =
        ∑ l ∈ pendantVertices G, (missingCoreNeighbors G l).card := by
    calc
      (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) =
          ∑ c ∈ coreVertices G,
            ∑ l ∈ pendantVertices G, if ¬G.Adj c l then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro c _
              simp [missingPendantNeighbors]
      _ = ∑ l ∈ pendantVertices G,
            ∑ c ∈ coreVertices G, if ¬G.Adj c l then 1 else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ l ∈ pendantVertices G, (missingCoreNeighbors G l).card := by
              apply Finset.sum_congr rfl
              intro l _
              simp [missingCoreNeighbors, G.adj_comm]
  rw [hdouble]
  calc
    (∑ l ∈ pendantVertices G, (missingCoreNeighbors G l).card) =
        ∑ _l ∈ pendantVertices G, ((coreVertices G).card - 1) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [card_missingCoreNeighbors_of_pendant G hl hleaf_core]
    _ = (pendantVertices G).card * ((coreVertices G).card - 1) := by
          simp

#print axioms sum_card_missingPendantNeighbors

end

end WrittenOnTheWallII.GraphConjecture316
