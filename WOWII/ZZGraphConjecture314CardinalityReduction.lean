import WOWII.ZZGraphConjecture314DominatingEdge

/-!
A direct route to WOWII Graph Conjecture 314 that bypasses the full structural
classification.  In a triangle-free induced-P5-free graph, the existence of a
two-vertex total dominating set already forces the graph into the compiled
bipartite dominating-edge family.  Consequently, the entire conjecture reduces
to proving that every minimal total dominating set has at most three vertices.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every total dominating set in a nonempty graph contains at least two vertices. -/
lemma two_le_card_of_totalDominatingSet
    [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : IsTotalDominatingSet G S) :
    2 ≤ S.card := by
  let x : α := Classical.ofNonempty
  obtain ⟨y, hyS, hxy⟩ := hS x
  obtain ⟨z, hzS, hyz⟩ := hS y
  exact Finset.two_le_card.mpr ⟨y, hyS, z, hzS, hyz.ne⟩

/-- A triangle-free graph with a two-vertex total dominating set is bipartite,
with the two vertices forming the dominating edge.  If the graph is also
induced-P5-free, the existing family theorem makes it well totally dominated. -/
lemma isWellTotallyDominated_of_totalDominating_pair
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (u v : α)
    (hTD : IsTotalDominatingSet G {u, v})
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    IsWellTotallyDominated G := by
  have huv : G.Adj u v := by
    obtain ⟨w, hw, huw⟩ := hTD u
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.loopless u huw).elim
    · exact huw
  let side : α → Bool := fun x => if G.Adj u x then true else false
  have hu : side u = false := by
    simp [side]
  have hv : side v = true := by
    simp [side, huv]
  have huDom : ∀ x : α, side x = true → G.Adj u x := by
    intro x hx
    simpa [side] using hx
  have hvDom : ∀ x : α, side x = false → G.Adj v x := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hTD x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · have hnot : ¬G.Adj u x := by simpa [side] using hx
      exact (hnot hxw.symm).elim
    · exact hxw.symm
  have hpart : ∀ x y : α, G.Adj x y → side x ≠ side y := by
    intro x y hxy hsame
    cases hxs : side x with
    | false =>
        have hys : side y = false := by
          calc
            side y = side x := hsame.symm
            _ = false := hxs
        exact hTriFree v x y (hvDom x hxs) hxy (hvDom y hys).symm
    | true =>
        have hys : side y = true := by
          calc
            side y = side x := hsame.symm
            _ = true := hxs
        exact hTriFree u x y (huDom x hxs) hxy (huDom y hys).symm
  exact isWellTotallyDominated_of_bipartite_dominating_edge
    G side u v hu hv hpart huDom hvDom hNoP5

/-- If one minimal total dominating set has cardinality two, the whole graph is
well totally dominated. -/
lemma isWellTotallyDominated_of_exists_minimalTDS_card_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (hTwo : ∃ S : Finset α, IsMinimalTotalDominatingSet G S ∧ S.card = 2) :
    IsWellTotallyDominated G := by
  obtain ⟨S, hS, hScard⟩ := hTwo
  obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp hScard
  subst S
  exact isWellTotallyDominated_of_totalDominating_pair G u v hS.1 hTriFree hNoP5

/-- Direct cardinality reduction: the only remaining graph-theoretic lemma needed
for Conjecture 314 is that every minimal total dominating set has order at most
three.  If a set of order two exists, the preceding theorem handles the graph;
otherwise every minimal set has order exactly three. -/
theorem isWellTotallyDominated_of_minimalTDS_card_le_three
    [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (hUpper : ∀ S : Finset α, IsMinimalTotalDominatingSet G S → S.card ≤ 3) :
    IsWellTotallyDominated G := by
  by_cases hTwo : ∃ S : Finset α, IsMinimalTotalDominatingSet G S ∧ S.card = 2
  · exact isWellTotallyDominated_of_exists_minimalTDS_card_eq_two
      G hTriFree hNoP5 hTwo
  · intro S T hS hT
    have hSlo : 2 ≤ S.card := two_le_card_of_totalDominatingSet G hS.1
    have hTlo : 2 ≤ T.card := two_le_card_of_totalDominatingSet G hT.1
    have hShi : S.card ≤ 3 := hUpper S hS
    have hThi : T.card ≤ 3 := hUpper T hT
    have hSne : S.card ≠ 2 := fun h => hTwo ⟨S, hS, h⟩
    have hTne : T.card ≠ 2 := fun h => hTwo ⟨T, hT, h⟩
    omega

end WrittenOnTheWallII.GraphConjecture314
