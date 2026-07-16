import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Vertices on a cycle have degree at least two.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma two_le_degree_of_cycle_root {G : SimpleGraph α} [DecidableRel G.Adj]
    {v : α} {c : G.Walk v v} (hc : c.IsCycle) : 2 ≤ G.degree v := by
  have hs : c.snd ∈ G.neighborFinset v := by
    simpa using c.adj_snd hc.not_nil
  have hp : c.penultimate ∈ G.neighborFinset v := by
    simpa using (c.adj_penultimate hc.not_nil).symm
  have hne : c.snd ≠ c.penultimate := hc.snd_ne_penultimate
  have hsub : ({c.snd, c.penultimate} : Finset α) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hs
    · exact hp
  calc
    2 = ({c.snd, c.penultimate} : Finset α).card := by simp [hne]
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
    _ = G.degree v := rfl

lemma two_le_degree_of_mem_cycle {G : SimpleGraph α} [DecidableRel G.Adj]
    {u x : α} {c : G.Walk u u} (hc : c.IsCycle) (hx : x ∈ c.support) :
    2 ≤ G.degree x := by
  exact two_le_degree_of_cycle_root (hc.rotate hx)

end WrittenOnTheWallII.GraphConjecture143
