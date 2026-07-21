/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

open Classical

namespace WrittenOnTheWallII.GraphConjecture322

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

@[category research solved, AMS 5]
theorem conjecture322 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 5 ≤ Fintype.card α)
    (h : ∀ v : α, indepNeighborsCard G v ≤ 1) :
    IsWellTotallyDominated G := by
  have adjacent_of_two_neighbors {u v w : α} (hvu : G.Adj v u) (hvw : G.Adj v w)
      (huw : u ≠ w) : G.Adj u w := by
    by_contra hnuw
    let u' : G.neighborSet v := ⟨u, hvu⟩
    let w' : G.neighborSet v := ⟨w, hvw⟩
    have hu'w' : u' ≠ w' := by
      intro heq
      exact huw (congrArg Subtype.val heq)
    have hs :
        (G.induce (G.neighborSet v)).IsIndepSet
          ({u', w'} : Finset (G.neighborSet v)) := by
      rw [isIndepSet_iff]
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · change ¬G.Adj u w
          exact hnuw
      · rcases hy with rfl | rfl
        · change ¬G.Adj w u
          exact fun hwu => hnuw hwu.symm
        · exact (hxy rfl).elim
    have htwo : 2 ≤ (G.induce (G.neighborSet v)).indepNum := by
      have hcard := hs.card_le_indepNum
      simpa [u', w', hu'w'] using hcard
    have hone := h v
    unfold indepNeighborsCard at hone
    omega
  have transGen_adj : ∀ {u w : α}, Relation.TransGen G.Adj u w → u ≠ w → G.Adj u w := by
    intro u w huw
    induction huw with
    | single hadj =>
        intro _
        exact hadj
    | @tail v w _ hvw ih =>
        intro huw_ne
        by_cases huv : u = v
        · subst v
          exact hvw
        · exact adjacent_of_two_neighbors (ih huv).symm hvw huw_ne
  have hcomplete : ∀ {u w : α}, u ≠ w → G.Adj u w := by
    intro u w huw
    have hreach : Relation.ReflTransGen G.Adj u w :=
      (reachable_iff_reflTransGen u w).mp (hG u w)
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hreach with hwu | htrans
    · exact (huw hwu.symm).elim
    · exact transGen_adj htrans huw
  intro S T hS hT
  have minimal_card_two (U : Finset α) (hU : IsMinimalTotalDominatingSet G U) :
      U.card = 2 := by
    let v : α := Classical.choice hG.nonempty
    obtain ⟨a, haU, hva⟩ := hU.1 v
    obtain ⟨b, hbU, hab⟩ := hU.1 a
    have hab_ne : a ≠ b := hab.ne
    have hpair_subset : ({a, b} : Finset α) ⊆ U := by
      simp [haU, hbU]
    have hge : 2 ≤ U.card := by
      calc
        2 = ({a, b} : Finset α).card := by simp [hab_ne]
        _ ≤ U.card := Finset.card_le_card hpair_subset
    have hle : U.card ≤ 2 := by
      by_contra hnot
      have hgt : 2 < U.card := by omega
      have hpair_ne : ({a, b} : Finset α) ≠ U := by
        intro heq
        have heq_card := congrArg Finset.card heq
        simp [hab_ne] at heq_card
        omega
      have hproper : ({a, b} : Finset α) ⊂ U :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hpair_subset, hpair_ne⟩
      have hpair_dom : IsTotalDominatingSet G ({a, b} : Finset α) := by
        intro x
        by_cases hxa : x = a
        · exact ⟨b, by simp, hcomplete (hxa.trans_ne hab_ne)⟩
        · exact ⟨a, by simp, hcomplete hxa⟩
      exact hU.2 _ hproper hpair_dom
    omega
  rw [minimal_card_two S hS, minimal_card_two T hT]

end WrittenOnTheWallII.GraphConjecture322
