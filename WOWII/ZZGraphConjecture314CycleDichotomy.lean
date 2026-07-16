import WOWII.ZZGraphConjecture314BipartiteClassification

/-!
A root-distance proof of the bipartite-or-`C₅` dichotomy needed for WOWII
Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Five ordered vertices form an induced five-cycle. -/
def FormsInducedC5 (G : SimpleGraph α) (x0 x1 x2 x3 x4 : α) : Prop :=
  x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x0 ≠ x4 ∧
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧
  x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
  G.Adj x0 x1 ∧ G.Adj x1 x2 ∧ G.Adj x2 x3 ∧ G.Adj x3 x4 ∧ G.Adj x4 x0 ∧
  ¬G.Adj x0 x2 ∧ ¬G.Adj x0 x3 ∧ ¬G.Adj x1 x3 ∧ ¬G.Adj x1 x4 ∧ ¬G.Adj x2 x4

private lemma dist_eq_of_adj_same_distance_parity
    (G : SimpleGraph α) (r x y : α) (hxy : G.Adj x y)
    (hpar : (G.dist r x % 2 = 0) ↔ (G.dist r y % 2 = 0)) :
    G.dist r x = G.dist r y := by
  rcases hxy.diff_dist_adj (u := r) with h | h | h
  · exact h.symm
  · by_cases hx : G.dist r x % 2 = 0
    · have hy := hpar.mp hx
      omega
    · have hy : G.dist r y % 2 ≠ 0 := by
        intro hy
        exact hx (hpar.mpr hy)
      omega
  · by_cases hx : G.dist r x % 2 = 0
    · have hy := hpar.mp hx
      omega
    · have hy : G.dist r y % 2 ≠ 0 := by
        intro hy
        exact hx (hpar.mpr hy)
      omega

/-- If there is no induced five-cycle, parity of distance from a fixed root is
a bipartition. The proof uses only the exact forbidden configurations needed by
WOWII 314. -/
lemma exists_bipartite_side_of_no_inducedC5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (hNoC5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedC5 G x0 x1 x2 x3 x4) :
    ∃ side : α → Bool, ∀ x y : α, G.Adj x y → side x ≠ side y := by
  let r : α := Classical.ofNonempty
  let side : α → Bool := fun x => if G.dist r x % 2 = 0 then false else true
  refine ⟨side, ?_⟩
  intro x y hxy
  intro hside
  have hpar : (G.dist r x % 2 = 0) ↔ (G.dist r y % 2 = 0) := by
    constructor
    · intro hx
      by_contra hy
      simp [side, hx, hy] at hside
    · intro hy
      by_contra hx
      simp [side, hx, hy] at hside
  have heq : G.dist r x = G.dist r y :=
    dist_eq_of_adj_same_distance_parity G r x y hxy hpar
  have hle : G.dist r x ≤ 3 := dist_le_three_of_no_FormsInducedP5 G hG hNoP5 r x
  interval_cases hd : G.dist r x
  · have hx : x = r := (hG.dist_eq_zero_iff).mp hd
    have hy0 : G.dist r y = 0 := by simpa [← heq] using hd
    have hy : y = r := (hG.dist_eq_zero_iff).mp hy0
    subst x
    subst y
    exact G.loopless r hxy
  · have hrx : G.Adj r x := dist_eq_one_iff_adj.mp hd
    have hrydist : G.dist r y = 1 := by omega
    have hry : G.Adj r y := dist_eq_one_iff_adj.mp hrydist
    exact hTriFree r x y hrx hxy hry.symm
  · have hdy : G.dist r y = 2 := by omega
    obtain ⟨p, hp, hpgeo⟩ := hG.exists_path_of_dist r x
    obtain ⟨q, hq, hqgeo⟩ := hG.exists_path_of_dist r y
    have hplen : p.length = 2 := hpgeo.trans hd
    have hqlen : q.length = 2 := hqgeo.trans hdy
    let a := p.getVert 1
    let b := q.getVert 1
    have hra : G.Adj r a := by
      simpa [a] using p.adj_getVert_succ (i := 0) (by omega)
    have hax : G.Adj a x := by
      have h := p.adj_getVert_succ (i := 1) (by omega)
      have hend : p.getVert 2 = x := by simpa [hplen] using p.getVert_length
      simpa [a, hend] using h
    have hrb : G.Adj r b := by
      simpa [b] using q.adj_getVert_succ (i := 0) (by omega)
    have hby : G.Adj b y := by
      have h := q.adj_getVert_succ (i := 1) (by omega)
      have hend : q.getVert 2 = y := by simpa [hqlen] using q.getVert_length
      simpa [b, hend] using h
    by_cases hab : a = b
    · subst b
      exact hTriFree a x y hax hxy hby.symm
    · have hrx : ¬G.Adj r x := by
        intro h
        have := dist_eq_one_iff_adj.mpr h
        omega
      have hry : ¬G.Adj r y := by
        intro h
        have := dist_eq_one_iff_adj.mpr h
        omega
      have hay : ¬G.Adj a y := by
        intro h
        exact hTriFree a x y hax hxy h.symm
      have habn : ¬G.Adj a b := by
        intro h
        exact hTriFree a r b hra.symm hrb h.symm
      have hxb : ¬G.Adj x b := by
        intro h
        exact hTriFree x y b hxy hby.symm h.symm
      have hr_ne_a : r ≠ a := hra.ne
      have hr_ne_x : r ≠ x := by
        intro h
        subst x
        exact hrx (by simpa using hra)
      have hr_ne_y : r ≠ y := by
        intro h
        subst y
        exact hry (by simpa using hrb)
      have hr_ne_b : r ≠ b := hrb.ne
      have ha_ne_x : a ≠ x := hax.ne
      have ha_ne_y : a ≠ y := by
        intro h
        subst y
        exact hry (by simpa using hra)
      have hx_ne_y : x ≠ y := hxy.ne
      have hx_ne_b : x ≠ b := by
        intro h
        subst x
        exact hrx (by simpa using hrb)
      have hy_ne_b : y ≠ b := hby.ne.symm
      apply hNoC5 r a x y b
      unfold FormsInducedC5
      exact ⟨hr_ne_a, hr_ne_x, hr_ne_y, hr_ne_b,
        ha_ne_x, ha_ne_y, hab,
        hx_ne_y, hx_ne_b, hy_ne_b,
        hra, hax, hxy, hby.symm, hrb.symm,
        hrx, hry, hay, habn, hxb⟩
  · have hdy : G.dist r y = 3 := by omega
    obtain ⟨p, hp, hpgeo⟩ := hG.exists_path_of_dist r x
    have hplen : p.length = 3 := hpgeo.trans hd
    let a := p.getVert 1
    let b := p.getVert 2
    have hra : G.Adj r a := by
      simpa [a] using p.adj_getVert_succ (i := 0) (by omega)
    have hab : G.Adj a b := by
      simpa [a, b] using p.adj_getVert_succ (i := 1) (by omega)
    have hbx : G.Adj b x := by
      have h := p.adj_getVert_succ (i := 2) (by omega)
      have hend : p.getVert 3 = x := by simpa [hplen] using p.getVert_length
      simpa [b, hend] using h
    have hrb : ¬G.Adj r b := by
      intro h
      exact hTriFree r a b hra hab h.symm
    have hrx : ¬G.Adj r x := by
      intro h
      have := dist_eq_one_iff_adj.mpr h
      omega
    have hax : ¬G.Adj a x := by
      intro h
      exact hTriFree a b x hab hbx h.symm
    have hry : ¬G.Adj r y := by
      intro h
      have := dist_eq_one_iff_adj.mpr h
      omega
    have hay : ¬G.Adj a y := by
      intro h
      have hw : G.Walk r y := .cons hra (.cons h .nil)
      have hle2 : G.dist r y ≤ 2 := by simpa using G.dist_le hw
      omega
    have hby : ¬G.Adj b y := by
      intro h
      exact hTriFree b x y hbx hxy h.symm
    have hr_ne_a : r ≠ a := hra.ne
    have hr_ne_b : r ≠ b := by
      intro h
      subst b
      exact hrb (by simpa using hra)
    have hr_ne_x : r ≠ x := by
      intro h
      subst x
      exact hrx (by simpa using hra)
    have hr_ne_y : r ≠ y := by
      intro h
      subst y
      exact hry (by simpa using hra)
    have ha_ne_b : a ≠ b := hab.ne
    have ha_ne_x : a ≠ x := by
      intro h
      subst x
      have hdist1 : G.dist r a = 1 := dist_eq_one_iff_adj.mpr hra
      omega
    have ha_ne_y : a ≠ y := by
      intro h
      subst y
      have hdist1 : G.dist r a = 1 := dist_eq_one_iff_adj.mpr hra
      omega
    have hb_ne_x : b ≠ x := hbx.ne
    have hb_ne_y : b ≠ y := by
      intro h
      subst y
      have w : G.Walk r b := .cons hra (.cons hab .nil)
      have hdist2 : G.dist r b ≤ 2 := by simpa using G.dist_le w
      omega
    have hx_ne_y : x ≠ y := hxy.ne
    apply hNoP5 r a b x y
    unfold FormsInducedP5
    exact ⟨hr_ne_a, hr_ne_b, hr_ne_x, hr_ne_y,
      ha_ne_b, ha_ne_x, ha_ne_y,
      hb_ne_x, hb_ne_y, hx_ne_y,
      hra, hab, hbx, hxy,
      hrb, hrx, hry, hax, hay, hby⟩

/-- Under the exact WOWII 314 hypotheses, either the graph has an induced
five-cycle or it has a Boolean bipartition. -/
lemma inducedC5_or_bipartite_side
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    (∃ x0 x1 x2 x3 x4 : α, FormsInducedC5 G x0 x1 x2 x3 x4) ∨
    (∃ side : α → Bool, ∀ x y : α, G.Adj x y → side x ≠ side y) := by
  by_cases hC5 : ∃ x0 x1 x2 x3 x4 : α, FormsInducedC5 G x0 x1 x2 x3 x4
  · exact Or.inl hC5
  · right
    push_neg at hC5
    exact exists_bipartite_side_of_no_inducedC5 G hG hTriFree hNoP5 hC5

end WrittenOnTheWallII.GraphConjecture314
