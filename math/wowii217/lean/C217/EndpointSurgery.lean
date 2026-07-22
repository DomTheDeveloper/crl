import C217.ClosureSurgery
import Mathlib.Tactic

open Classical
open SimpleGraph

namespace C217

universe u

lemma closure_right_endpoint_support_perm {α : Type u} (l : List α) (i : ℕ) :
    l.take (i + 1) ++ (l.drop (i + 1)).reverse ~ l := by
  exact (List.Perm.append_right (List.reverse_perm _) _).trans
    (List.Perm.refl.trans (List.take_append_drop (i + 1) l))

lemma closure_left_endpoint_support_perm {α : Type u} (l : List α) (i : ℕ) :
    (l.take (i + 1)).reverse ++ l.drop (i + 1) ~ l := by
  exact (List.Perm.append_left (List.reverse_perm _) _).trans
    (List.Perm.refl.trans (List.take_append_drop (i + 1) l))

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V}
variable {a b u v : V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the first endpoint of the added edge is adjacent to the terminal
endpoint of the augmented Hamilton path, rotate the suffix and eliminate
the added edge. -/
lemma exists_hamiltonianPath_of_right_endpoint
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {i : ℕ} (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hub : G.Adj u b) :
    ∃ c d : V, ∃ q : G.Walk c d, q.IsHamiltonian := by
  let AH := p.take i
  have hvAH : v ∉ AH.support := by
    rw [← hvi]
    exact hp.isPath.getVert_not_mem_support_take_of_lt (by omega) (by omega)
  let A0 : G.Walk a (p.getVert i) :=
    AH.transferEdges (AH.edges_in_base_of_avoid_right hvAH)
  let A : G.Walk a u := A0.copy rfl hui

  let BH := p.drop (i + 1)
  have huBH : u ∉ BH.support := by
    rw [← hui]
    exact hp.isPath.getVert_not_mem_support_drop_of_lt (by omega) (by omega)
  let B0 : G.Walk (p.getVert (i + 1)) b :=
    BH.transferEdges (BH.edges_in_base_of_avoid_left huBH)
  let B : G.Walk v b := B0.copy hvi rfl

  let q : G.Walk a v := (A.concat hub).append B.reverse
  refine ⟨a, v, q, ?_⟩
  have hAsupp : A.support = p.support.take (i + 1) := by
    simp [A, A0, AH, Walk.support_take]
  have hBsupp : B.support = p.support.drop (i + 1) := by
    simp only [B, B0, Walk.support_copy, Walk.support_transferEdges, BH,
      Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]
  have hqsupp : q.support =
      p.support.take (i + 1) ++ (p.support.drop (i + 1)).reverse := by
    dsimp [q]
    rw [Walk.support_append_eq_support_dropLast_append, Walk.support_concat,
      Walk.support_reverse, hAsupp, hBsupp]
    simp
  have hperm : q.support ~ p.support := by
    rw [hqsupp]
    exact closure_right_endpoint_support_perm p.support i
  intro x
  rw [hperm.count_eq x]
  exact hp x

/-- If the second endpoint of the added edge is adjacent to the initial
endpoint of the augmented Hamilton path, rotate the prefix and eliminate
the added edge. -/
lemma exists_hamiltonianPath_of_left_endpoint
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {i : ℕ} (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hva : G.Adj v a) :
    ∃ c d : V, ∃ q : G.Walk c d, q.IsHamiltonian := by
  let AH := p.take i
  have hvAH : v ∉ AH.support := by
    rw [← hvi]
    exact hp.isPath.getVert_not_mem_support_take_of_lt (by omega) (by omega)
  let A0 : G.Walk a (p.getVert i) :=
    AH.transferEdges (AH.edges_in_base_of_avoid_right hvAH)
  let A : G.Walk a u := A0.copy rfl hui

  let BH := p.drop (i + 1)
  have huBH : u ∉ BH.support := by
    rw [← hui]
    exact hp.isPath.getVert_not_mem_support_drop_of_lt (by omega) (by omega)
  let B0 : G.Walk (p.getVert (i + 1)) b :=
    BH.transferEdges (BH.edges_in_base_of_avoid_left huBH)
  let B : G.Walk v b := B0.copy hvi rfl

  let q : G.Walk u b := (A.reverse.concat hva.symm).append B
  refine ⟨u, b, q, ?_⟩
  have hAsupp : A.support = p.support.take (i + 1) := by
    simp [A, A0, AH, Walk.support_take]
  have hBsupp : B.support = p.support.drop (i + 1) := by
    simp only [B, B0, Walk.support_copy, Walk.support_transferEdges, BH,
      Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]
  have hqsupp : q.support =
      (p.support.take (i + 1)).reverse ++ p.support.drop (i + 1) := by
    dsimp [q]
    rw [Walk.support_append_eq_support_dropLast_append, Walk.support_concat,
      Walk.support_reverse, hAsupp, hBsupp]
    simp
  have hperm : q.support ~ p.support := by
    rw [hqsupp]
    exact closure_left_endpoint_support_perm p.support i
  intro x
  rw [hperm.count_eq x]
  exact hp x

end SimpleGraph.Walk

end C217
