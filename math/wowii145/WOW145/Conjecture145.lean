import WOW146.ExceptionalTheorem
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

/-!
# WOWII Graph Conjecture 145

A proof of the exact Formal Conjectures statement.
-/

open Classical SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma exists_localIndependenceMin_eq (H : SimpleGraph α) :
    ∃ v : α, indepNeighborsCard H v = localIndependenceMin H := by
  obtain ⟨v, _, hv⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (indepNeighborsCard H)
  exact ⟨v, hv.symm⟩

private lemma nonadjacent_nonneighbors_of_indepNeighborsCard_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] {v : α}
    (hv : indepNeighborsCard Gᶜ v = 1) :
    ∀ ⦃x y : α⦄, Gᶜ.Adj v x → Gᶜ.Adj v y → ¬G.Adj x y := by
  intro x y hvx hvy hxy
  let x' : (Gᶜ).neighborSet v := ⟨x, hvx⟩
  let y' : (Gᶜ).neighborSet v := ⟨y, hvy⟩
  have hxy' : x' ≠ y' := by
    intro h
    apply hxy.ne
    exact congrArg Subtype.val h
  have hind : ((Gᶜ).induce ((Gᶜ).neighborSet v)).IsIndepSet
      ({x', y'} : Finset ((Gᶜ).neighborSet v)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · simp [x', y', hxy]
    · simp [x', y', hxy.symm]
    · exact (hab rfl).elim
  have hle := hind.card_le_indepNum
  have htwo : 2 ≤ indepNeighborsCard Gᶜ v := by
    simpa [indepNeighborsCard, Finset.card_pair hxy'] using hle
  omega

private lemma exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hm : localIndependenceMin Gᶜ = 1) :
    ∃ v : α, ∀ x : α, G.dist v x ≤ 2 := by
  obtain ⟨v, hv⟩ := exists_localIndependenceMin_eq (Gᶜ)
  have hvone : indepNeighborsCard Gᶜ v = 1 := hv.trans hm
  have hnon := nonadjacent_nonneighbors_of_indepNeighborsCard_compl_eq_one G hvone
  refine ⟨v, fun x => ?_⟩
  by_cases hxv : x = v
  · subst x
    simp
  by_cases hvx : G.Adj v x
  · exact (G.dist_le hvx.toWalk).trans (by norm_num)
  have hvne : v ≠ x := Ne.symm hxv
  have hcvx : Gᶜ.Adj v x := by
    simp [hvne, hvx]
  have hxs : x ∈ G.support := by
    rw [hG.preconnected.support_eq_univ]
    simp
  obtain ⟨z, hxz⟩ := (mem_support G).mp hxs
  have hvz : G.Adj v z := by
    by_contra hn
    have hzv : z ≠ v := by
      intro hzv
      subst z
      exact hvx hxz.symm
    have hvz_ne : v ≠ z := Ne.symm hzv
    have hcvz : Gᶜ.Adj v z := by
      simp [hvz_ne, hn]
    exact (hnon hcvx hcvz) hxz
  exact WOW146.dist_le_two_of_adj_adj G hvz hxz.symm

private lemma radius_toNat_le_two_of_localIndependenceMin_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hm : localIndependenceMin Gᶜ = 1) :
    G.radius.toNat ≤ 2 := by
  obtain ⟨v, hv⟩ := exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one G hG hm
  have hecc : G.eccent v ≤ (2 : ℕ∞) := by
    rw [eccent_le_iff]
    intro x
    rw [← (hG v x).coe_dist_eq_edist]
    exact_mod_cast hv x
  have hr : G.radius ≤ (2 : ℕ∞) := radius_le_eccent.trans hecc
  simpa using ENat.toNat_le_toNat hr (by simp)

private lemma diam_le_four_of_localIndependenceMin_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hm : localIndependenceMin Gᶜ = 1) :
    G.diam ≤ 4 := by
  obtain ⟨c, hc⟩ := exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one G hG hm
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  rw [← huv]
  calc
    G.dist u v ≤ G.dist u c + G.dist c v := hG.dist_triangle
    _ ≤ 2 + 2 := Nat.add_le_add (by simpa [dist_comm] using hc u) (hc v)
    _ = 4 := by norm_num

/-- Exact Lean proof of WOWII Graph Conjecture 145. -/
theorem conjecture145_proved (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  let p := eccSet G (maxEccentricityVertices G : Set α)
  let t := largestInducedTreeSize G
  let m := localIndependenceMin Gᶜ
  have hpdiam : p + 1 ≤ G.diam := by
    simpa [p] using eccSet_periphery_add_one_le_diam hG
  have hdtree : G.diam + 1 ≤ t := by
    simpa [t] using diam_succ_le_largestInducedTreeSize hG
  by_cases hmge : 2 ≤ m
  · have hpt : p ≤ t := by omega
    change 2 * p ≤ t * m
    nlinarith
  have hm : m = 1 := by
    have hmpos : 0 < m := by simpa [m] using hlMin
    omega
  have hmraw : localIndependenceMin Gᶜ = 1 := by simpa [m] using hm
  have hdle : G.diam ≤ 4 :=
    diam_le_four_of_localIndependenceMin_compl_eq_one G hG hmraw
  have hple : p ≤ 3 := by omega
  have hgoal : 2 * p ≤ t := by
    by_cases hp : p ≤ 2
    · omega
    · have hp3 : p = 3 := by omega
      have hd4 : G.diam = 4 := by omega
      have hrle : G.radius.toNat ≤ 2 :=
        radius_toNat_le_two_of_localIndependenceMin_compl_eq_one G hG hmraw
      have hdlower : G.diam ≤ 2 * G.radius.toNat := diam_le_two_mul_radius_toNat hG
      have hr2 : G.radius.toNat = 2 := by omega
      have hsix : 6 ≤ t := by
        have hpraw : eccSet G (maxEccentricityVertices G : Set α) = 3 := by
          simpa [p] using hp3
        simpa [t] using WOW146.exceptional_case G hG hr2 hd4 hpraw
      omega
  change 2 * p ≤ t * m
  simpa [hm] using hgoal

#print axioms WOW145.conjecture145_proved

end WOW145
