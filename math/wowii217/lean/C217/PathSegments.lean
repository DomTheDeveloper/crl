import C217.RotationPerm
import Mathlib.Tactic

open Classical
open SimpleGraph

namespace C217

universe u

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V}
variable {a b : V}

/-- Pinned compatibility lemma: a suffix of a path is a path. -/
protected lemma IsPath.drop {p : G.Walk a b} (hp : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath :=
  isPath_of_isSubwalk (p.isSubwalk_drop n) hp

/-- A vertex occurring strictly later on a path cannot occur in an earlier
prefix. -/
lemma IsPath.getVert_not_mem_support_take_of_lt {p : G.Walk a b}
    (hp : p.IsPath) {m n : ℕ} (hmn : m < n) (hn : n ≤ p.length) :
    p.getVert n ∉ (p.take m).support := by
  intro hmem
  rcases (p.take m).mem_support_iff_exists_getVert.mp hmem with ⟨k, hk, hklen⟩
  have hEq : p.getVert (m ⊓ k) = p.getVert n := by
    simpa using hk
  have hminle : m ⊓ k ≤ p.length := by omega
  have hidx : m ⊓ k = n := hp.getVert_injective_on hminle hn hEq
  omega

/-- A vertex occurring strictly earlier on a path cannot occur in a later
suffix. -/
lemma IsPath.getVert_not_mem_support_drop_of_lt {p : G.Walk a b}
    (hp : p.IsPath) {n m : ℕ} (hnm : n < m) (hm : m ≤ p.length) :
    p.getVert n ∉ (p.drop m).support := by
  intro hmem
  rcases (p.drop m).mem_support_iff_exists_getVert.mp hmem with ⟨k, hk, hklen⟩
  have hEq : p.getVert (m + k) = p.getVert n := by
    simpa using hk
  have hmk : m + k ≤ p.length := by
    rw [p.drop_length] at hklen
    omega
  have hidx : m + k = n := hp.getVert_injective_on hmk n.le hEq
  omega

/-- Taking a prefix preserves non-membership. -/
lemma not_mem_support_take_of_not_mem_support {p : G.Walk a b}
    {x : V} (hx : x ∉ p.support) (n : ℕ) :
    x ∉ (p.take n).support := by
  intro h
  exact hx (p.isSubwalk_take n).support_subset h

/-- Dropping a prefix preserves non-membership. -/
lemma not_mem_support_drop_of_not_mem_support {p : G.Walk a b}
    {x : V} (hx : x ∉ p.support) (n : ℕ) :
    x ∉ (p.drop n).support := by
  intro h
  exact hx (p.isSubwalk_drop n).support_subset h

end SimpleGraph.Walk

end C217
