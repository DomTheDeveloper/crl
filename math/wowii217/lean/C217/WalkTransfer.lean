import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations

open Classical
open SimpleGraph

namespace C217

universe u

namespace SimpleGraph.Walk

variable {V : Type u}
variable {G H : SimpleGraph V}
variable {a b u v : V}

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
