import Mathlib
import A387471Families

/-!
# Weight-six roots-of-unity classification for OEIS A387471

This module is the proof boundary that was missing from the original draft.
It will contain a self-contained specialization of Mann's theorem to minimal
vanishing sums of at most six roots of unity, the finite order-30
classification, and the grid-level sine classification used by the exact
sequence theorem.
-/

namespace A387471

/-- A finite vanishing sum indexed by a finite set. -/
def Vanishes {ι : Type*} (s : Finset ι) (z : ι → ℂ) : Prop :=
  ∑ i ∈ s, z i = 0

/-- Minimality means that no nonempty proper subcollection vanishes. -/
def MinimallyVanishes {ι : Type*} (s : Finset ι) (z : ι → ℂ) : Prop :=
  Vanishes s z ∧ ∀ t : Finset ι, t ⊂ s → t.Nonempty → ¬ Vanishes t z

@[simp] theorem vanishes_empty {ι : Type*} (z : ι → ℂ) : Vanishes ∅ z := by
  simp [Vanishes]

#print axioms vanishes_empty

end A387471
