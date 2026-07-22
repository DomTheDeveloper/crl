import C217.CastGraphExtra
import Mathlib.Tactic

open Classical
open SimpleGraph

namespace C217

universe u

namespace SimpleGraph

variable {V : Type u}
variable [Fintype V] [DecidableEq V]

/-- Oriented form of the one-edge Hamilton-path closure argument. -/
lemma traceable_of_oriented_added_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b u v : V}
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {i : ℕ} (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hdeg : p.length ≤ G.degree u + G.degree v) :
    ∃ c d : V, ∃ q : G.Walk c d, q.IsHamiltonian := by
  by_cases hub : G.Adj u b
  · exact Walk.exists_hamiltonianPath_of_right_endpoint p hp hi hui hvi hub
  by_cases hva : G.Adj v a
  · exact Walk.exists_hamiltonianPath_of_left_endpoint p hp hi hui hvi hva
  obtain ⟨t, ht, hti, hut, hvs⟩ :=
    Walk.exists_closure_crossing_index p hp hi hui hvi hub hva hdeg
  rcases Nat.lt_or_gt_of_ne hti with hlt | hgt
  · obtain ⟨q, hq⟩ :=
      Walk.exists_hamiltonianPath_of_left_crossing p hp hlt hi hui hvi hut hvs
    exact ⟨a, b, q, hq⟩
  · obtain ⟨q, hq⟩ :=
      Walk.exists_hamiltonianPath_of_right_crossing p hp hgt ht hui hvi hut hvs
    exact ⟨a, b, q, hq⟩

/-- Bondy--Chvátal closure for Hamilton paths. Adding a nonedge whose
degree sum is at least `|V|-1` cannot create traceability from nothing. -/
theorem traceable_of_sup_edge_traceable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (_huv : ¬ G.Adj u v)
    (hdeg : Fintype.card V - 1 ≤ G.degree u + G.degree v)
    (htrace : ∃ a b : V, ∃ p : (G ⊔ edge u v).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  obtain ⟨a, b, p, hp⟩ := htrace
  by_cases hbase : ∀ x y : V, s(x, y) ∈ p.edges → G.Adj x y
  · let q : G.Walk a b :=
      Walk.transferEdges p (fun {_ _} hmem => hbase _ _ hmem)
    exact ⟨a, b, q, Walk.isHamiltonian_transferEdges p _ hp⟩

  push_neg at hbase
  obtain ⟨x, y, hxy, hnxy⟩ := hbase
  obtain ⟨i, hi, hsym⟩ := Walk.exists_index_of_mem_edges p hxy

  have hnindex : ¬ G.Adj (p.getVert i) (p.getVert (i + 1)) := by
    intro hadj
    apply hnxy
    have hmem : s(p.getVert i, p.getVert (i + 1)) ∈ G.edgeSet := hadj
    have hmemxy : s(x, y) ∈ G.edgeSet := hsym ▸ hmem
    exact hmemxy

  have haug : (G ⊔ edge u v).Adj (p.getVert i) (p.getVert (i + 1)) :=
    p.adj_getVert_succ hi
  rw [SimpleGraph.sup_adj] at haug
  have hedge : (edge u v).Adj (p.getVert i) (p.getVert (i + 1)) :=
    haug.resolve_left hnindex
  rw [SimpleGraph.edge_adj] at hedge

  have hdegP : p.length ≤ G.degree u + G.degree v := by
    rw [hp.length_eq]
    exact hdeg

  rcases hedge.1 with horient | horient
  · exact traceable_of_oriented_added_edge G p hp hi horient.1 horient.2 hdegP
  · have hcomm : G ⊔ edge u v = G ⊔ edge v u :=
      congrArg (fun E : SimpleGraph V => G ⊔ E)
        (SimpleGraph.edge_comm (s := u) (t := v))
    let p' : (G ⊔ edge v u).Walk a b := Walk.castGraph hcomm p
    have hp' : p'.IsHamiltonian := by
      simpa [p'] using Walk.isHamiltonian_castGraph hcomm p hp
    have hi' : i < p'.length := by
      simpa [p'] using hi
    have hvi' : p'.getVert i = v := by
      simpa [p'] using horient.1
    have hui' : p'.getVert (i + 1) = u := by
      simpa [p'] using horient.2
    have hdegP' : p'.length ≤ G.degree v + G.degree u := by
      simpa [p', Nat.add_comm] using hdegP
    exact traceable_of_oriented_added_edge G p' hp' hi' hvi' hui' hdegP'

end SimpleGraph

end C217
