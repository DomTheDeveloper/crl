import WOWII.ZZGraphConjecture314GeodesicP5
import WOWII.ZZGraphConjecture314ChainGraph

/-!
The bipartite half of the structural classification for WOWII Graph Conjecture
314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma bool_eq_of_ne_same_bip {a b s : Bool} (ha : a ≠ s) (hb : b ≠ s) : a = b := by
  cases a <;> cases b <;> cases s <;> simp_all

/-- In a connected bipartite induced-`P₅`-free graph, two distinct vertices on
one side have a common neighbor on the other side. -/
lemma exists_common_neighbor_of_bipartite_noP5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {a b : α} (hsame : side a = side b) (hab : a ≠ b) :
    ∃ c : α, side c ≠ side a ∧ G.Adj c a ∧ G.Adj c b := by
  have hdist : G.dist a b ≤ 3 := dist_le_three_of_no_FormsInducedP5 G hG hNoP5 a b
  obtain ⟨p, hp, hgeo⟩ := hG.exists_path_of_dist a b
  have hzero : G.dist a b ≠ 0 := by
    intro h
    exact hab ((hG.dist_eq_zero_iff).mp h)
  have hone : G.dist a b ≠ 1 := by
    intro h
    have hadj : G.Adj a b := dist_eq_one_iff_adj.mp h
    exact hpart a b hadj hsame
  have hthree : G.dist a b ≠ 3 := by
    intro h
    have hlen : p.length = 3 := hgeo.trans h
    have h01 : G.Adj a (p.getVert 1) := by
      simpa using p.adj_getVert_succ (i := 0) (by omega)
    have h12 : G.Adj (p.getVert 1) (p.getVert 2) :=
      p.adj_getVert_succ (i := 1) (by omega)
    have h23 : G.Adj (p.getVert 2) b := by
      have h' := p.adj_getVert_succ (i := 2) (by omega)
      have hend : p.getVert 3 = b := by simpa [hlen] using p.getVert_length
      simpa [hend] using h'
    have hs01 := hpart a (p.getVert 1) h01
    have hs12 := hpart (p.getVert 1) (p.getVert 2) h12
    have hs23 := hpart (p.getVert 2) b h23
    cases ha : side a <;>
      cases h1 : side (p.getVert 1) <;>
      cases h2 : side (p.getVert 2) <;>
      cases hb : side b <;> simp_all
  have htwo : G.dist a b = 2 := by omega
  have hlen : p.length = 2 := hgeo.trans htwo
  let c := p.getVert 1
  have hac : G.Adj a c := by
    exact p.adj_getVert_succ (i := 0) (by omega)
  have hcb : G.Adj c b := by
    have h' := p.adj_getVert_succ (i := 1) (by omega)
    have hend : p.getVert 2 = b := by simpa [hlen] using p.getVert_length
    simpa [c, hend] using h'
  refine ⟨c, (hpart a c hac).symm, hac.symm, hcb⟩

/-- Connected bipartite induced-`P₅`-free graphs are chain graphs: the open
neighborhoods of vertices on either fixed side are linearly ordered by
inclusion. -/
lemma nested_neighborhoods_of_bipartite_noP5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    ∀ a b : α, side a = side b →
      (∀ x : α, G.Adj a x → G.Adj b x) ∨
      (∀ x : α, G.Adj b x → G.Adj a x) := by
  intro a b hsame
  by_cases hab : a = b
  · subst b
    exact Or.inl (by aesop)
  by_cases hAB : ∀ x : α, G.Adj a x → G.Adj b x
  · exact Or.inl hAB
  right
  push_neg at hAB
  obtain ⟨x, hax, hnxb⟩ := hAB
  intro y hby
  by_contra hnay
  obtain ⟨c, hcside, hca, hcb⟩ :=
    exists_common_neighbor_of_bipartite_noP5 G hG side hpart hNoP5 hsame hab
  have hxside_ne : side x ≠ side a := hpart a x hax
  have hyside_ne : side y ≠ side b := hpart b y hby
  have hxcy : side x = side c ∧ side c = side y := by
    constructor
    · exact bool_eq_of_ne_same_bip hxside_ne hcside
    · have hy_ne_a : side y ≠ side a := by simpa [hsame] using hyside_ne
      exact bool_eq_of_ne_same_bip hcside hy_ne_a
  have hn_xc : ¬G.Adj x c := fun h => hpart x c h hxcy.1
  have hn_xy : ¬G.Adj x y := fun h => hpart x y h (hxcy.1.trans hxcy.2)
  have hn_cy : ¬G.Adj c y := fun h => hpart c y h hxcy.2
  have hn_ab : ¬G.Adj a b := fun h => hpart a b h hsame
  have hxa : G.Adj x a := hax.symm
  have hx_ne_a : x ≠ a := hxa.ne
  have hx_ne_c : x ≠ c := by
    intro h
    subst c
    exact hnxb hcb.symm
  have hx_ne_b : x ≠ b := by
    intro h
    subst x
    exact hn_ab hax
  have hx_ne_y : x ≠ y := by
    intro h
    subst y
    exact hnxb hby
  have ha_ne_c : a ≠ c := hca.ne.symm
  have ha_ne_b : a ≠ b := hab
  have ha_ne_y : a ≠ y := by
    intro h
    subst y
    exact hn_ab hby.symm
  have hc_ne_b : c ≠ b := hcb.ne
  have hc_ne_y : c ≠ y := by
    intro h
    subst y
    exact hnay hca.symm
  have hb_ne_y : b ≠ y := hby.ne
  apply hNoP5 x a c b y
  unfold FormsInducedP5
  exact ⟨hx_ne_a, hx_ne_c, hx_ne_b, hx_ne_y,
    ha_ne_c, ha_ne_b, ha_ne_y,
    hc_ne_b, hc_ne_y, hb_ne_y,
    hxa, hca.symm, hcb, hby,
    hn_xc, (fun h => hnxb h.symm), hn_xy,
    hn_ab, hnay, hn_cy⟩

/-- The exact structural-classification branch in the bipartite case. -/
lemma hasWOWII314StructuralClassification_of_bipartite_side
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    HasWOWII314StructuralClassification G := by
  left
  exact ⟨side, hpart,
    nested_neighborhoods_of_bipartite_noP5 G hG side hpart hNoP5⟩

/-- Hence the exact WOWII 314 conclusion is complete whenever a bipartition is
supplied. -/
lemma isWellTotallyDominated_of_bipartite_noP5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (side : α → Bool)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    IsWellTotallyDominated G := by
  exact isWellTotallyDominated_of_connected_chain_graph G hG side hpart
    (nested_neighborhoods_of_bipartite_noP5 G hG side hpart hNoP5)

end WrittenOnTheWallII.GraphConjecture314
