import Mathlib

/-!
# A387471: equal-angle cevian concurrencies

This file does two separate things.

1. It gives an exact Lean statement of the OEIS conjecture using the
   trigonometric-Ceva sine-product equation.
2. It kernel-checks the trigonometric and algebraic reductions from the
   concurrence equation to the ordinary and exceptional index triples.

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
noncomputable def cevianAngle (n i : ℕ) : ℝ :=
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

/-! ## Trigonometric reduction -/

/-- The exact product-to-sum identity behind the reduction to three sines. -/
theorem product_difference_identity (x y z : ℝ) :
    Real.sin x * Real.sin y * Real.sin z -
        Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) *
          Real.sin (Real.pi / 3 - z) =
      Real.sqrt 3 / 4 *
        (Real.sin (x + y - z - Real.pi / 6) +
          Real.sin (x + z - y - Real.pi / 6) +
          Real.sin (y + z - x - Real.pi / 6)) := by
  have hsqrt : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by norm_num
  simp only [Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add,
    Real.sin_pi_div_three, Real.cos_pi_div_three,
    Real.sin_pi_div_six, Real.cos_pi_div_six]
  ring_nf at *
  nlinarith

/-- The trigonometric-Ceva product equation is equivalent to a three-sine
vanishing relation. -/
theorem product_concurrent_iff_three_sines (x y z : ℝ) :
    (Real.sin x * Real.sin y * Real.sin z =
      Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) *
        Real.sin (Real.pi / 3 - z)) ↔
      Real.sin (x + y - z - Real.pi / 6) +
        Real.sin (x + z - y - Real.pi / 6) +
        Real.sin (y + z - x - Real.pi / 6) = 0 := by
  constructor
  · intro h
    have hz :
        Real.sin x * Real.sin y * Real.sin z -
            Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) *
              Real.sin (Real.pi / 3 - z) = 0 := sub_eq_zero.mpr h
    rw [product_difference_identity] at hz
    have hc : Real.sqrt 3 / 4 ≠ 0 := by positivity
    exact (mul_eq_zero.mp hz).resolve_left hc
  · intro h
    apply sub_eq_zero.mp
    rw [product_difference_identity, h, mul_zero]

/-- The lattice angle `a*π/(6n)` for an integer coefficient `a`. -/
noncomputable def latticeAngle (n : ℕ) (a : ℤ) : ℝ :=
  (a : ℝ) * (Real.pi / (6 * (n : ℝ)))

/-- The three integer coefficients produced by the linear change of variables. -/
def reducedA (n i j k : ℕ) : ℤ := (i : ℤ) + j - k - n
def reducedB (n i j k : ℕ) : ℤ := (i : ℤ) + k - j - n
def reducedC (n i j k : ℕ) : ℤ := (j : ℤ) + k - i - n

/-- First reduced angle. -/
theorem latticeAngle_reducedA (n i j k : ℕ) (hn : 0 < n) :
    latticeAngle n (reducedA n i j k) =
      cevianAngle n i + cevianAngle n j - cevianAngle n k - Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [latticeAngle, reducedA, cevianAngle]
  field_simp [hn0]
  ring

/-- Second reduced angle. -/
theorem latticeAngle_reducedB (n i j k : ℕ) (hn : 0 < n) :
    latticeAngle n (reducedB n i j k) =
      cevianAngle n i + cevianAngle n k - cevianAngle n j - Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [latticeAngle, reducedB, cevianAngle]
  field_simp [hn0]
  ring

/-- Third reduced angle. -/
theorem latticeAngle_reducedC (n i j k : ℕ) (hn : 0 < n) :
    latticeAngle n (reducedC n i j k) =
      cevianAngle n j + cevianAngle n k - cevianAngle n i - Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [latticeAngle, reducedC, cevianAngle]
  field_simp [hn0]
  ring

/-- The reduced three-sine equation attached to a cevian index triple. -/
def ReducedSineEquation (n i j k : ℕ) : Prop :=
  Real.sin (latticeAngle n (reducedA n i j k)) +
    Real.sin (latticeAngle n (reducedB n i j k)) +
    Real.sin (latticeAngle n (reducedC n i j k)) = 0

/-- Fully formalized bridge from trigonometric Ceva to the integer-lattice
three-sine equation. -/
theorem cevianConcurrent_iff_reduced (n i j k : ℕ) (hn : 0 < n) :
    CevianConcurrent n i j k ↔ ReducedSineEquation n i j k := by
  unfold CevianConcurrent ReducedSineEquation
  rw [product_concurrent_iff_three_sines]
  rw [← latticeAngle_reducedA n i j k hn,
    ← latticeAngle_reducedB n i j k hn,
    ← latticeAngle_reducedC n i j k hn]

/-! ## Algebraic reconstruction -/

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

#print axioms product_difference_identity
#print axioms product_concurrent_iff_three_sines
#print axioms cevianConcurrent_iff_reduced
#print axioms reconstruct_ordinary
#print axioms reconstruct_exceptional
#print axioms classification_transfer
#print axioms closedForm_eq_family_count

end A387471
