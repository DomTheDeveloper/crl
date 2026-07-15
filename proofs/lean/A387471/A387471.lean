import Mathlib

/-!
# A387471: equal-angle cevian concurrencies

This file does two separate things.

1. It gives an exact Lean statement of the OEIS conjecture using the
   trigonometric-Ceva sine-product equation.
2. It kernel-checks the algebraic reduction from the proposed classification
   of the three sine arguments to the ordinary and exceptional index triples.

The remaining research-level dependency is deliberately exposed as
`ABCClassified`: proving that every rational-angle sine solution satisfies
that classification requires the short vanishing-sum-of-roots-of-unity
classification. It is not assumed as an axiom in this file.
-/

open Finset

namespace A387471

/-- An ordered triple encoded without introducing a bespoke structure. -/
abbrev Triple := ℕ × (ℕ × ℕ)

/-- The allowed cevian indices for the OEIS parameter `m = 2n - 1`. -/
def indices (n : ℕ) : Finset ℕ := Finset.Icc 1 (2 * n - 1)

/-- Every ordered index triple in the allowed range. -/
def allTriples (n : ℕ) : Finset Triple :=
  (indices n).product ((indices n).product (indices n))

/-- The angle of the cevian with index `i`; here `θ = π/(6n)`. -/
def cevianAngle (n i : ℕ) : ℝ :=
  (i : ℝ) * (Real.pi / (6 * (n : ℝ)))

/-- The denominator-free trigonometric-Ceva equation.

For indices in `1, …, 2n-1`, this says
`sin x sin y sin z = sin (π/3-x) sin (π/3-y) sin (π/3-z)`.
-/
def CevianConcurrent (n i j k : ℕ) : Prop :=
  Real.sin (cevianAngle n i) * Real.sin (cevianAngle n j) * Real.sin (cevianAngle n k) =
    Real.sin (Real.pi / 3 - cevianAngle n i) *
      Real.sin (Real.pi / 3 - cevianAngle n j) *
      Real.sin (Real.pi / 3 - cevianAngle n k)

/-- The finite set whose cardinality is A387471(n). -/
noncomputable def solutionTriples (n : ℕ) : Finset Triple := by
  classical
  exact (allTriples n).filter fun t ↦ CevianConcurrent n t.1 t.2.1 t.2.2

/-- The conjectured closed form. -/
def closedForm (n : ℕ) : ℕ :=
  if 5 ∣ n then 6 * n + 7 else 6 * n - 5

/-- Exact formal statement of the A387471 conjecture.

This is a definition of a proposition, not a claimed proof.
-/
def ExactStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (solutionTriples n).card = closedForm n

/-- The six ordered permutations of three entries. -/
def Perm3 {α : Type*} (x y z a b c : α) : Prop :=
  (x = a ∧ y = b ∧ z = c) ∨
  (x = a ∧ y = c ∧ z = b) ∨
  (x = b ∧ y = a ∧ z = c) ∨
  (x = b ∧ y = c ∧ z = a) ∨
  (x = c ∧ y = a ∧ z = b) ∨
  (x = c ∧ y = b ∧ z = a)

/-- Integer form of the inverse linear change of variables

`A = i+j-k-n`, `B = i+k-j-n`, `C = j+k-i-n`.

Writing it without division avoids parity side conditions.
-/
def Reconstruct (n A B C i j k : ℤ) : Prop :=
  2 * i = 2 * n + A + B ∧
  2 * j = 2 * n + A + C ∧
  2 * k = 2 * n + B + C

/-- The ordinary family: one index is `n` and the other two sum to `2n`. -/
def OrdinaryIndices (n i j k : ℤ) : Prop :=
  (i = n ∧ j + k = 2 * n) ∨
  (j = n ∧ i + k = 2 * n) ∨
  (k = n ∧ i + j = 2 * n)

/-- The two exceptional families, including every ordering. -/
def ExceptionalIndices (n i j k : ℤ) : Prop :=
  ∃ q : ℤ, n = 5 * q ∧
    (Perm3 i j k q (7 * q) (8 * q) ∨
      Perm3 i j k (2 * q) (3 * q) (9 * q))

/-- The exceptional patterns on the three sine arguments. -/
def ExceptionalABC (n A B C : ℤ) : Prop :=
  ∃ q : ℤ, n = 5 * q ∧
    (Perm3 A B C (-5 * q) (-3 * q) (9 * q) ∨
      Perm3 A B C (-9 * q) (3 * q) (5 * q))

/-- The exact missing classification lemma after the trigonometric reduction.

The ordinary pattern is a permutation of `(0,s,-s)`. The only other patterns
are the two fifth-root families, which force `5 ∣ n`.
-/
def ABCClassified (n A B C : ℤ) : Prop :=
  (∃ s : ℤ, Perm3 A B C 0 s (-s)) ∨ ExceptionalABC n A B C

/-- Corresponding classification of the original cevian indices. -/
def IndexClassified (n i j k : ℤ) : Prop :=
  OrdinaryIndices n i j k ∨ ExceptionalIndices n i j k

/-- A permutation of `(0,s,-s)` reconstructs to the ordinary family. -/
theorem reconstruct_ordinary {n A B C i j k s : ℤ}
    (hrec : Reconstruct n A B C i j k)
    (hpat : Perm3 A B C 0 s (-s)) :
    OrdinaryIndices n i j k := by
  rcases hrec with ⟨hi, hj, hk⟩
  rcases hpat with h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl, rfl⟩
  all_goals simp [OrdinaryIndices] at *
  all_goals omega

/-- Either exceptional sine pattern reconstructs to its claimed index family. -/
theorem reconstruct_exceptional {n A B C i j k : ℤ}
    (hrec : Reconstruct n A B C i j k)
    (hpat : ExceptionalABC n A B C) :
    ExceptionalIndices n i j k := by
  rcases hrec with ⟨hi, hj, hk⟩
  rcases hpat with ⟨q, hn, hpat⟩
  subst n
  refine ⟨q, rfl, ?_⟩
  rcases hpat with hpat | hpat
  · left
    rcases hpat with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals simp only [Perm3]
    all_goals omega
  · right
    rcases hpat with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals simp only [Perm3]
    all_goals omega

/-- Kernel-checked transfer of the entire hard classification to the claimed
index classification. -/
theorem classification_transfer {n A B C i j k : ℤ}
    (hrec : Reconstruct n A B C i j k)
    (hclass : ABCClassified n A B C) :
    IndexClassified n i j k := by
  rcases hclass with ⟨s, hs⟩ | hexc
  · exact Or.inl (reconstruct_ordinary hrec hs)
  · exact Or.inr (reconstruct_exceptional hrec hexc)

/-- Exceptional triples can occur only when five divides the parameter. -/
theorem five_dvd_of_exceptional {n i j k : ℤ}
    (h : ExceptionalIndices n i j k) : (5 : ℤ) ∣ n := by
  rcases h with ⟨q, hn, _⟩
  exact ⟨q, hn⟩

/-- Arithmetic assembly of the predicted counts: `6(n-1)+1` ordinary
ordered triples and twelve exceptional ordered triples exactly when `5 ∣ n`. -/
theorem closedForm_eq_family_count (n : ℕ) (hn : 1 ≤ n) :
    closedForm n = 6 * (n - 1) + 1 + (if 5 ∣ n then 12 else 0) := by
  by_cases h : 5 ∣ n
  · simp [closedForm, h]
    omega
  · simp [closedForm, h]
    omega

#print axioms reconstruct_ordinary
#print axioms reconstruct_exceptional
#print axioms classification_transfer
#print axioms closedForm_eq_family_count

end A387471
