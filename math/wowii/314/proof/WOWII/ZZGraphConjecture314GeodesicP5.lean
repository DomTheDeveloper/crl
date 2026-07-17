import WOWII.ZZGraphConjecture314P5Bridge

/-!
Geodesic infrastructure for the structural classification in WOWII Graph
Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The first five vertices of any geodesic of length at least four form an
induced `P₅`. -/
lemma formsInducedP5_of_geodesic_length_ge_four
    {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hgeo : p.length = G.dist u v) (hfour : 4 ≤ p.length) :
    FormsInducedP5 G
      (p.getVert 0) (p.getVert 1) (p.getVert 2) (p.getVert 3) (p.getVert 4) := by
  have hp : p.IsPath := p.isPath_of_length_eq_dist hgeo
  have hne : ∀ i j : ℕ, i ≤ 4 → j ≤ 4 → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij heq
    have hie : i ≤ p.length := by omega
    have hje : j ≤ p.length := by omega
    have hij' : i = j := hp.getVert_injOn (by simpa using hie) (by simpa using hje) heq
    exact hij hij'
  have hnonadj : ∀ i j : ℕ, i ≤ 4 → j ≤ 4 → i + 2 ≤ j →
      ¬G.Adj (p.getVert i) (p.getVert j) := by
    intro i j hi hj hgap hadj
    have hie : i ≤ p.length := by omega
    have hje : j ≤ p.length := by omega
    let q := (p.drop i).take (j - i)
    have hqsub : q.IsSubwalk p :=
      (Walk.isSubwalk_take (p.drop i) (j - i)).trans (Walk.isSubwalk_drop p i)
    have hseg := length_eq_dist_of_subwalk hgeo hqsub
    have hmin : j - i ≤ p.length - i := by omega
    have hseg' : j - i = G.dist (p.getVert i) (p.getVert j) := by
      simpa [q, Nat.min_eq_left hmin, Nat.add_sub_of_le (by omega : i ≤ j)] using hseg
    rw [dist_eq_one_iff_adj.mpr hadj] at hseg'
    omega
  unfold FormsInducedP5
  exact ⟨
    hne 0 1 (by omega) (by omega) (by omega),
    hne 0 2 (by omega) (by omega) (by omega),
    hne 0 3 (by omega) (by omega) (by omega),
    hne 0 4 (by omega) (by omega) (by omega),
    hne 1 2 (by omega) (by omega) (by omega),
    hne 1 3 (by omega) (by omega) (by omega),
    hne 1 4 (by omega) (by omega) (by omega),
    hne 2 3 (by omega) (by omega) (by omega),
    hne 2 4 (by omega) (by omega) (by omega),
    hne 3 4 (by omega) (by omega) (by omega),
    p.adj_getVert_succ (i := 0) (by omega),
    p.adj_getVert_succ (i := 1) (by omega),
    p.adj_getVert_succ (i := 2) (by omega),
    p.adj_getVert_succ (i := 3) (by omega),
    hnonadj 0 2 (by omega) (by omega) (by omega),
    hnonadj 0 3 (by omega) (by omega) (by omega),
    hnonadj 0 4 (by omega) (by omega) (by omega),
    hnonadj 1 3 (by omega) (by omega) (by omega),
    hnonadj 1 4 (by omega) (by omega) (by omega),
    hnonadj 2 4 (by omega) (by omega) (by omega)⟩

/-- In an induced-`P₅`-free connected graph, every pair of vertices is at
distance at most three. -/
lemma dist_le_three_of_no_FormsInducedP5
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (u v : α) :
    G.dist u v ≤ 3 := by
  obtain ⟨p, -, hgeo⟩ := hG.exists_path_of_dist u v
  by_contra h
  have hfour : 4 ≤ p.length := by omega
  exact hNoP5 _ _ _ _ _ (formsInducedP5_of_geodesic_length_ge_four hgeo hfour)

end WrittenOnTheWallII.GraphConjecture314
