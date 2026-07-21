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

import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 322

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture322

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 322](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph on `n ≥ 5` vertices. If the maximum over all
vertices `v` of `l(v)` — the independence number of the neighborhood `N(v)` of `v`
— is at most 1, then `G` is well totally dominated.

Here `l(v) = α(G[N(v)])` is the independence number of the subgraph induced by the
open neighborhood of `v`.
-/
@[category research solved, AMS 5]
theorem conjecture322 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 5 ≤ Fintype.card α)
    (h : ∀ v : α, indepNeighborsCard G v ≤ 1) :
    IsWellTotallyDominated G := by
  have hcomp : ∀ {u v : α}, u ≠ v → G.Adj u v := by
    have hloc : ∀ (x u v : α), G.Adj x u → G.Adj x v → u ≠ v → G.Adj u v := by
      intro x u v hxu hxv huv
      by_contra hnadj
      have hu : u ∈ G.neighborSet x := hxu
      have hv : v ∈ G.neighborSet x := hxv
      have hne : (⟨u, hu⟩ : G.neighborSet x) ≠ ⟨v, hv⟩ := by
        simp [Subtype.ext_iff, huv]
      have hindep : (G.induce (G.neighborSet x)).IsIndepSet
          ({⟨u, hu⟩, ⟨v, hv⟩} : Finset (G.neighborSet x)) := by
        rw [isIndepSet_iff]
        have hcoe : ((({⟨u, hu⟩, ⟨v, hv⟩} : Finset (G.neighborSet x))) :
            Set (G.neighborSet x)) = {⟨u, hu⟩, ⟨v, hv⟩} := by simp
        rw [hcoe]
        refine Set.pairwise_pair.mpr fun _ => ⟨?_, ?_⟩
        · exact fun hadj => hnadj (induce_adj.mp hadj)
        · exact fun hadj => hnadj (induce_adj.mp hadj).symm
      have h2 : 2 ≤ (G.induce (G.neighborSet x)).indepNum := by
        have hcard := hindep.card_le_indepNum
        rwa [Finset.card_pair hne] at hcard
      have hle : (2 : ℕ) ≤ 1 := le_trans h2 (h x)
      omega
    have hwalk : ∀ {u v : α}, G.Walk u v → u ≠ v → G.Adj u v := by
      intro u v p
      induction p with
      | nil => intro hne; exact absurd rfl hne
      | @cons a b c hab q ih =>
        intro huv
        by_cases hbc : b = c
        · subst hbc; exact hab
        · exact hloc b a c hab.symm (ih hbc) huv
    intro u v huv
    obtain ⟨p⟩ := hG.preconnected u v
    exact hwalk p huv
  have hα : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hTDS_ge : ∀ S : Finset α, IsTotalDominatingSet G S → 2 ≤ S.card := by
    intro S hS
    obtain ⟨v⟩ := hα
    obtain ⟨w, hwS, _⟩ := hS v
    obtain ⟨w', hw'S, hww'⟩ := hS w
    exact Finset.one_lt_card.mpr ⟨w, hwS, w', hw'S, hww'.ne⟩
  have hTDS_of_two : ∀ S : Finset α, 2 ≤ S.card → IsTotalDominatingSet G S := by
    intro S hS v
    obtain ⟨a, haS, b, hbS, hab⟩ := Finset.one_lt_card.mp hS
    by_cases hva : v = a
    · have hvb : v ≠ b := by rw [hva]; exact hab
      exact ⟨b, hbS, hcomp hvb⟩
    · exact ⟨a, haS, hcomp hva⟩
  have hmin : ∀ S : Finset α, IsMinimalTotalDominatingSet G S → S.card = 2 := by
    rintro S ⟨hS, hSmin⟩
    have h2 := hTDS_ge S hS
    rcases eq_or_lt_of_le h2 with heq | hlt
    · omega
    · exfalso
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq h2
      have hTne : T ≠ S := by
        intro hEq
        rw [hEq] at hTcard
        omega
      have hTproper : T ⊂ S := hTS.ssubset_of_ne hTne
      exact hSmin T hTproper (hTDS_of_two T (le_of_eq hTcard.symm))
  intro S T hS hT
  rw [hmin S hS, hmin T hT]

-- Sanity checks

/-- In `K₄`, all vertices have degree 3. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 4)).maxDegree = 3 := by decide +native

/-- In the edgeless graph `⊥` on 5 vertices, the minimum degree is 0. -/
@[category test, AMS 5]
example : (⊥ : SimpleGraph (Fin 5)).minDegree = 0 := by decide +native

end WrittenOnTheWallII.GraphConjecture322
