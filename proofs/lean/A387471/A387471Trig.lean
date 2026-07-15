import A387471

/-!
# Trigonometric reduction for A387471

This module kernel-checks the bridge from the trigonometric-Ceva product
condition to the three-sine lattice equation. It also proves that the reduced
integer coefficients reconstruct the original cevian indices exactly.
-/

namespace A387471

/-- The exact product-to-sum identity behind the reduction to three sines. -/
theorem product_difference_identity (x y z : ℝ) :
    Real.sin x * Real.sin y * Real.sin z -
        Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) *
          Real.sin (Real.pi / 3 - z) =
      Real.sqrt 3 / 4 *
        (Real.sin (x + y - z - Real.pi / 6) +
          Real.sin (x + z - y - Real.pi / 6) +
          Real.sin (y + z - x - Real.pi / 6)) := by
  have hsqrt2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by norm_num
  have hsqrt3 : (Real.sqrt 3 : ℝ) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt2]
  simp only [Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add,
    Real.sin_pi_div_three, Real.cos_pi_div_three,
    Real.sin_pi_div_six, Real.cos_pi_div_six]
  ring_nf
  rw [hsqrt2, hsqrt3]
  ring

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

/-- The lattice angle `a * π/(6n)` for an integer coefficient `a`. -/
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

/-- Second reduced angle. -/
theorem latticeAngle_reducedB (n i j k : ℕ) (hn : 0 < n) :
    latticeAngle n (reducedB n i j k) =
      cevianAngle n i + cevianAngle n k - cevianAngle n j - Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [latticeAngle, reducedB, cevianAngle]
  field_simp [hn0]

/-- Third reduced angle. -/
theorem latticeAngle_reducedC (n i j k : ℕ) (hn : 0 < n) :
    latticeAngle n (reducedC n i j k) =
      cevianAngle n j + cevianAngle n k - cevianAngle n i - Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [latticeAngle, reducedC, cevianAngle]
  field_simp [hn0]

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

/-- The reduced coefficients satisfy the inverse reconstruction equations
identically. -/
theorem reconstruct_reduced (n i j k : ℕ) :
    Reconstruct (n : ℤ) (reducedA n i j k) (reducedB n i j k)
      (reducedC n i j k) (i : ℤ) (j : ℤ) (k : ℤ) := by
  unfold Reconstruct reducedA reducedB reducedC
  constructor
  · ring
  constructor <;> ring

/-- The one remaining mathematical input, stated exactly on the finite cevian
grid. A proof follows from the classification of vanishing sums of six roots
of unity together with the admissible-angle bounds. -/
def GridSineClassification : Prop :=
  ∀ n i j k : ℕ, 0 < n →
    i ∈ indices n → j ∈ indices n → k ∈ indices n →
    ReducedSineEquation n i j k →
    ABCClassified (n : ℤ) (reducedA n i j k) (reducedB n i j k)
      (reducedC n i j k)

/-- Once the six-root classification is supplied, every concurrent cevian
triple belongs to the ordinary or exceptional index families. -/
theorem indexClassified_of_gridSineClassification
    (H : GridSineClassification) (n i j k : ℕ) (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (hcon : CevianConcurrent n i j k) :
    IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ) := by
  apply classification_transfer (reconstruct_reduced n i j k)
  exact H n i j k hn hi hj hk ((cevianConcurrent_iff_reduced n i j k hn).mp hcon)

#print axioms product_difference_identity
#print axioms product_concurrent_iff_three_sines
#print axioms cevianConcurrent_iff_reduced
#print axioms reconstruct_reduced
#print axioms indexClassified_of_gridSineClassification

end A387471
