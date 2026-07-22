import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations

open Classical
open SimpleGraph

namespace C217

universe u

namespace SimpleGraph.Walk

variable {V : Type u}
variable {G H K : SimpleGraph V}
variable {a b u v : V}

/-- Transport a walk across equality of its ambient graphs. -/
def castGraph (h : H = K) (p : H.Walk a b) : K.Walk a b := h ▸ p

@[simp]
theorem support_castGraph (h : H = K) (p : H.Walk a b) :
    (castGraph h p).support = p.support := by
  subst K
  rfl

@[simp]
theorem length_castGraph (h : H = K) (p : H.Walk a b) :
    (castGraph h p).length = p.length := by
  rw [← length_support, support_castGraph, length_support]

lemma isHamiltonian_castGraph (h : H = K) (p : H.Walk a b)
    (hp : p.IsHamiltonian) :
    (castGraph h p).IsHamiltonian := by
  intro x
  simpa only [support_castGraph] using hp x

/-- Transfer a walk to another graph when every edge used by the walk is
an edge of the target graph. -/
def transferEdges (p : H.Walk a b)
    (h : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y) : G.Walk a b :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ x y z hxy q =>
      .cons (h (by simp))
        (transferEdges q (fun {_ _} hmem => h (by simp [hmem])))

@[simp]
theorem support_transferEdges (p : H.Walk a b)
    (h : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y) :
    (transferEdges p h).support = p.support := by
  induction p with
  | nil => rfl
  | cons hadj q ih =>
      simp only [transferEdges, support_cons]
      rw [ih]

@[simp]
theorem length_transferEdges (p : H.Walk a b)
    (h : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y) :
    (transferEdges p h).length = p.length := by
  rw [← length_support, support_transferEdges, length_support]

lemma isHamiltonian_transferEdges (p : H.Walk a b)
    (h : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y)
    (hp : p.IsHamiltonian) :
    (transferEdges p h).IsHamiltonian := by
  intro x
  simpa only [support_transferEdges] using hp x

/-- Every occurrence of an edge in a walk is represented by two
consecutive indexed vertices.  This pinned-version lemma replaces a later
Mathlib convenience theorem. -/
lemma exists_index_of_mem_edges (p : H.Walk a b) {x y : V}
    (hxy : s(x, y) ∈ p.edges) :
    ∃ i < p.length,
      s(p.getVert i, p.getVert (i + 1)) = s(x, y) := by
  induction p with
  | nil => simp at hxy
  | cons hadj q ih =>
      simp only [edges_cons, List.mem_cons] at hxy
      rcases hxy with hhead | htail
      · refine ⟨0, by simp, ?_⟩
        simpa using hhead.symm
      · obtain ⟨i, hi, heq⟩ := ih htail
        refine ⟨i + 1, by simpa using hi, ?_⟩
        simpa using heq

lemma edges_in_base_of_avoid_right
    [DecidableEq V] (p : (G ⊔ edge u v).Walk a b)
    (hv : v ∉ p.support) :
    ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y := by
  intro x y hxy
  have hAdj : (G ⊔ edge u v).Adj x y := p.adj_of_mem_edges hxy
  rw [SimpleGraph.sup_adj] at hAdj
  rcases hAdj with hG | hedge
  · exact hG
  · rw [SimpleGraph.edge_adj] at hedge
    rcases hedge.1 with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact (hv (p.snd_mem_support_of_mem_edges hxy)).elim
    · rcases h with ⟨rfl, rfl⟩
      exact (hv (p.fst_mem_support_of_mem_edges hxy)).elim

lemma edges_in_base_of_avoid_left
    [DecidableEq V] (p : (G ⊔ edge u v).Walk a b)
    (hu : u ∉ p.support) :
    ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y := by
  intro x y hxy
  have hAdj : (G ⊔ edge u v).Adj x y := p.adj_of_mem_edges hxy
  rw [SimpleGraph.sup_adj] at hAdj
  rcases hAdj with hG | hedge
  · exact hG
  · rw [SimpleGraph.edge_adj] at hedge
    rcases hedge.1 with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact (hu (p.fst_mem_support_of_mem_edges hxy)).elim
    · rcases h with ⟨rfl, rfl⟩
      exact (hu (p.snd_mem_support_of_mem_edges hxy)).elim

end SimpleGraph.Walk

end C217
