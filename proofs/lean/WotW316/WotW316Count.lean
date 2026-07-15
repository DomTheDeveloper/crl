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
  simp [missingCoreNeighbors, coreNeighbors]

lemma card_missingCoreNeighbors_of_pendant
    {l : α} (hl : l ∈ pendantVertices G)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (missingCoreNeighbors G l).card = (coreVertices G).card - 1 := by
  rw [missingCoreNeighbors_eq_sdiff]
  have hsub : coreNeighbors G l ⊆ coreVertices G := by
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  rw [Finset.card_sdiff hsub, card_coreNeighbors_of_pendant G hl hleaf_core]

lemma sum_card_missingPendantNeighbors
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) =
      (pendantVertices G).card * ((coreVertices G).card - 1) := by
  classical
  calc
    (∑ c ∈ coreVertices G, (missingPendantNeighbors G c).card) =
        ∑ l ∈ pendantVertices G, (missingCoreNeighbors G l).card := by
          simp [missingPendantNeighbors, missingCoreNeighbors, Finset.sum_comm, G.adj_comm]
    _ = ∑ _l ∈ pendantVertices G, ((coreVertices G).card - 1) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [card_missingCoreNeighbors_of_pendant G hl hleaf_core]
    _ = (pendantVertices G).card * ((coreVertices G).card - 1) := by
          simp [mul_comm]

#print axioms sum_card_missingPendantNeighbors

end

end WrittenOnTheWallII.GraphConjecture316
