import FormalConjectures.WrittenOnTheWallII.GraphConjecture133

/-!
The first structural reduction in the C4-free branch of WOWII Graph Conjecture 133:
every neighborhood induces a matching together with isolated vertices.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A vertex with two distinct neighbors inside one open neighborhood creates a 4-cycle. -/
lemma hasC4_of_two_neighbors_inside_neighborhood
    (G : SimpleGraph α) {v x y z : α}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  exact ⟨v, y, x, z,
    hvy.ne, hvx.ne, hvz.ne, hxy.ne.symm, hyz, hxz.ne,
    hvy, hxy.symm, hxz, hvz.symm⟩

/-- In a C4-free graph, a vertex in `N(v)` has at most one neighbor inside `N(v)`. -/
lemma neighbors_inside_neighborhood_unique_of_noC4
    (G : SimpleGraph α)
    (hNoC4 : ¬ ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    {v x y z : α}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  by_contra hyz
  exact hNoC4 (hasC4_of_two_neighbors_inside_neighborhood G hvx hvy hvz hxy hxz hyz)

/-- Equivalently, every graph induced by an open neighborhood has maximum degree at most one. -/
lemma neighborhood_induced_degree_le_one_of_noC4
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hNoC4 : ¬ ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    (v : α) (x : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree x ≤ 1 := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro y hy z hz
  apply Subtype.ext
  have hxyInd : (G.induce (G.neighborSet v)).Adj x y := by
    simpa only [mem_neighborFinset] using hy
  have hxzInd : (G.induce (G.neighborSet v)).Adj x z := by
    simpa only [mem_neighborFinset] using hz
  exact neighbors_inside_neighborhood_unique_of_noC4 G hNoC4
    x.property y.property z.property hxyInd hxzInd

end WrittenOnTheWallII.GraphConjecture133
