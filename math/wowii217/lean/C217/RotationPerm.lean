import C217.ClosureIndex
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace C217

open List

universe u

/-- Support permutation for the rotation used when the crossing index is
strictly before the added edge. -/
lemma closure_left_support_perm {α : Type u} (l : List α) {t i : ℕ}
    (hti : t < i) (hi : i < l.length) (u : α) (hu : l[i] = u) :
    l.take (t + 1) ++ [u] ++
        ((l.drop (t + 1)).take (i - t - 1)).reverse ++ l.drop (i + 1) ~ l := by
  let A := l.take (t + 1)
  let M := (l.drop (t + 1)).take (i - t - 1)
  let R := l.drop (i + 1)
  have hdrop : M ++ l.drop i = l.drop (t + 1) := by
    dsimp [M]
    convert List.drop_take_append_drop l (t + 1) (i - t - 1) using 1 <;> omega
  have hcons : l[i] :: R = l.drop i := by
    dsimp [R]
    exact List.cons_getElem_drop_succ (l := l) (n := i)
  have hdecomp : A ++ M ++ [l[i]] ++ R = l := by
    calc
      A ++ M ++ [l[i]] ++ R = A ++ (M ++ (l[i] :: R)) := by simp [List.append_assoc]
      _ = A ++ (M ++ l.drop i) := by rw [hcons]
      _ = A ++ l.drop (t + 1) := by rw [hdrop]
      _ = l := by simpa [A] using List.take_append_drop (t + 1) l
  have hmid : [l[i]] ++ M.reverse ~ M ++ [l[i]] := by
    exact (List.perm_append_comm [l[i]] M.reverse).trans
      ((List.reverse_perm M).append_right [l[i]])
  rw [← hdecomp]
  rw [← hu]
  simpa [A, M, R, List.append_assoc] using
    (hmid.append_left A).append_right R

/-- Support permutation for the rotation used when the crossing index is
strictly after the added edge. -/
lemma closure_right_support_perm {α : Type u} (l : List α) {i t : ℕ}
    (hit : i < t) (ht : t < l.length) :
    l.take (i + 1) ++
        ((l.drop (i + 1)).take (t - i)).reverse ++ l.drop (t + 1) ~ l := by
  let A := l.take (i + 1)
  let M := (l.drop (i + 1)).take (t - i)
  let R := l.drop (t + 1)
  have hdrop : M ++ R = l.drop (i + 1) := by
    dsimp [M, R]
    convert List.drop_take_append_drop l (i + 1) (t - i) using 1 <;> omega
  have hdecomp : A ++ M ++ R = l := by
    calc
      A ++ M ++ R = A ++ (M ++ R) := by simp [List.append_assoc]
      _ = A ++ l.drop (i + 1) := by rw [hdrop]
      _ = l := by simpa [A] using List.take_append_drop (i + 1) l
  have hrev : M.reverse ~ M := List.reverse_perm M
  rw [← hdecomp]
  simpa [A, M, R, List.append_assoc] using
    (hrev.append_left A).append_right R

end C217
