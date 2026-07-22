import C217.PathSegments
import Mathlib.Tactic

open Classical
open SimpleGraph

namespace C217

universe u

private lemma tail_reverse_take_succ {α : Type u} (l : List α) {n : ℕ}
    (hn : n < l.length) :
    (l.take (n + 1)).reverse.tail = (l.take n).reverse := by
  rw [← List.take_concat_get' l n hn]
  simp

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V}
variable {a b u v : V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Perform the Hamilton-path rotation when the crossing index lies before
an oriented occurrence of the added edge. -/
lemma exists_hamiltonianPath_of_left_crossing
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {t i : ℕ} (hti : t < i) (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hut : G.Adj u (p.getVert t))
    (hvs : G.Adj v (p.getVert (t + 1))) :
    ∃ q : G.Walk a b, q.IsHamiltonian := by
  let PH := p.take t
  have hvPH : v ∉ PH.support := by
    rw [← hvi]
    exact hp.isPath.getVert_not_mem_support_take_of_lt (by omega) (by omega)
  let P : G.Walk a (p.getVert t) :=
    PH.transferEdges (PH.edges_in_base_of_avoid_right hvPH)

  let DH := p.drop (t + 1)
  let MH := DH.take (i - t - 1)
  have hDpath : DH.IsPath := hp.isPath.drop _
  have hDv : DH.getVert (i - t) = v := by
    dsimp [DH]
    rw [p.drop_getVert]
    convert hvi using 1 <;> omega
  have hvMH : v ∉ MH.support := by
    rw [← hDv]
    exact hDpath.getVert_not_mem_support_take_of_lt (by omega) (by
      dsimp [DH]
      rw [p.drop_length]
      omega)
  let M0 : G.Walk (p.getVert (t + 1)) (DH.getVert (i - t - 1)) :=
    MH.transferEdges (MH.edges_in_base_of_avoid_right hvMH)
  have hMend : DH.getVert (i - t - 1) = u := by
    dsimp [DH]
    rw [p.drop_getVert]
    convert hui using 1 <;> omega
  let M : G.Walk (p.getVert (t + 1)) u := M0.copy rfl hMend

  let BH := p.drop (i + 1)
  have huBH : u ∉ BH.support := by
    rw [← hui]
    exact hp.isPath.getVert_not_mem_support_drop_of_lt (by omega) (by omega)
  let B0 : G.Walk (p.getVert (i + 1)) b :=
    BH.transferEdges (BH.edges_in_base_of_avoid_left huBH)
  let B : G.Walk v b := B0.copy hvi rfl

  let q : G.Walk a b :=
    (((P.concat hut.symm).append M.reverse).concat hvs.symm).append B
  refine ⟨q, ?_⟩

  have hPsupp : P.support = p.support.take (t + 1) := by
    simp [P, PH, Walk.take_support_eq_support_take_succ]
  have hMsupp : M.support = (p.support.drop (t + 1)).take (i - t) := by
    simp only [M, M0, Walk.support_copy, Walk.support_transferEdges, MH,
      Walk.take_support_eq_support_take_succ, DH, Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]
    congr 2
    omega
  have hBsupp : B.support = p.support.drop (i + 1) := by
    simp only [B, B0, Walk.support_copy, Walk.support_transferEdges, BH,
      Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]

  have hmidlen : i - t - 1 < (p.support.drop (t + 1)).length := by
    rw [List.length_drop, p.length_support]
    omega
  have htail :
      ((p.support.drop (t + 1)).take (i - t)).reverse.tail =
        ((p.support.drop (t + 1)).take (i - t - 1)).reverse := by
    convert tail_reverse_take_succ (p.support.drop (t + 1)) hmidlen using 1 <;> omega

  have hviList : p.support[i + 1] = v := by
    rw [p.support_getElem_eq_getVert]
    exact hvi
  have hdropv : p.support.drop (i + 1) = v :: p.support.drop (i + 2) := by
    rw [List.drop_eq_getElem_cons (by rw [p.length_support]; omega), hviList]

  have hqsupp : q.support =
      p.support.take (t + 1) ++ [u] ++
        ((p.support.drop (t + 1)).take (i - t - 1)).reverse ++
          p.support.drop (i + 1) := by
    dsimp [q]
    rw [Walk.support_append, Walk.support_concat, Walk.support_append,
      Walk.support_concat, Walk.support_reverse, hPsupp, hMsupp, hBsupp, htail]
    simp [hdropv, List.append_assoc]

  have huiList : p.support[i] = u := by
    rw [p.support_getElem_eq_getVert]
    exact hui
  have hperm : q.support ~ p.support := by
    rw [hqsupp]
    exact closure_left_support_perm p.support hti (by rw [p.length_support]; omega) u huiList
  intro x
  rw [hperm.count_eq x]
  exact hp x

/-- Perform the Hamilton-path rotation when the crossing index lies after
an oriented occurrence of the added edge. -/
lemma exists_hamiltonianPath_of_right_crossing
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {i t : ℕ} (hit : i < t) (ht : t < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hut : G.Adj u (p.getVert t))
    (hvs : G.Adj v (p.getVert (t + 1))) :
    ∃ q : G.Walk a b, q.IsHamiltonian := by
  let AH := p.take i
  have hvAH : v ∉ AH.support := by
    rw [← hvi]
    exact hp.isPath.getVert_not_mem_support_take_of_lt (by omega) (by omega)
  let A0 : G.Walk a (p.getVert i) :=
    AH.transferEdges (AH.edges_in_base_of_avoid_right hvAH)
  let A : G.Walk a u := A0.copy rfl hui

  let DH := p.drop (i + 1)
  have huDH : u ∉ DH.support := by
    rw [← hui]
    exact hp.isPath.getVert_not_mem_support_drop_of_lt (by omega) (by omega)
  let MH := DH.take (t - i - 1)
  have huMH : u ∉ MH.support :=
    not_mem_support_take_of_not_mem_support huDH _
  let M0 : G.Walk (p.getVert (i + 1)) (DH.getVert (t - i - 1)) :=
    MH.transferEdges (MH.edges_in_base_of_avoid_left huMH)
  have hMend : DH.getVert (t - i - 1) = p.getVert t := by
    dsimp [DH]
    rw [p.drop_getVert]
    congr 1
    omega
  let M : G.Walk v (p.getVert t) := M0.copy hvi hMend

  let RH := p.drop (t + 1)
  have huRH : u ∉ RH.support := by
    rw [← hui]
    exact hp.isPath.getVert_not_mem_support_drop_of_lt (by omega) (by omega)
  let R : G.Walk (p.getVert (t + 1)) b :=
    RH.transferEdges (RH.edges_in_base_of_avoid_left huRH)

  let q : G.Walk a b :=
    (((A.concat hut).append M.reverse).concat hvs).append R
  refine ⟨q, ?_⟩

  have hAsupp : A.support = p.support.take (i + 1) := by
    simp [A, A0, AH, Walk.take_support_eq_support_take_succ]
  have hMsupp : M.support = (p.support.drop (i + 1)).take (t - i) := by
    simp only [M, M0, Walk.support_copy, Walk.support_transferEdges, MH,
      Walk.take_support_eq_support_take_succ, DH, Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]
    congr 2
    omega
  have hRsupp : R.support = p.support.drop (t + 1) := by
    simp only [R, Walk.support_transferEdges, RH,
      Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by omega)]

  have hmidlen : t - i - 1 < (p.support.drop (i + 1)).length := by
    rw [List.length_drop, p.length_support]
    omega
  have hlast : (p.support.drop (i + 1))[t - i - 1] = p.getVert t := by
    rw [List.getElem_drop, p.support_getElem_eq_getVert]
    congr 1
    omega
  have htake :
      (p.support.drop (i + 1)).take (t - i) =
        (p.support.drop (i + 1)).take (t - i - 1) ++ [p.getVert t] := by
    convert List.take_concat_get' (p.support.drop (i + 1)) (t - i - 1) hmidlen using 1
    · omega
    · exact hlast
  have hMrev :
      p.getVert t :: ((p.support.drop (i + 1)).take (t - i)).reverse.tail =
        ((p.support.drop (i + 1)).take (t - i)).reverse := by
    rw [htake]
    simp

  have htsList : p.support[t + 1] = p.getVert (t + 1) := by
    exact p.support_getElem_eq_getVert
  have hdropS : p.support.drop (t + 1) =
      p.getVert (t + 1) :: p.support.drop (t + 2) := by
    rw [List.drop_eq_getElem_cons (by rw [p.length_support]; omega), htsList]

  have hqsupp : q.support =
      p.support.take (i + 1) ++
        ((p.support.drop (i + 1)).take (t - i)).reverse ++
          p.support.drop (t + 1) := by
    dsimp [q]
    rw [Walk.support_append, Walk.support_concat, Walk.support_append,
      Walk.support_concat, Walk.support_reverse, hAsupp, hMsupp, hRsupp]
    simp [hMrev, hdropS, List.append_assoc]

  have hperm : q.support ~ p.support := by
    rw [hqsupp]
    exact closure_right_support_perm p.support hit (by rw [p.length_support]; omega)
  intro x
  rw [hperm.count_eq x]
  exact hp x

end SimpleGraph.Walk

end C217
