import A387471Bounds

/-!
# Analytic consequences of the exact reduced coefficient bounds
-/

open Set

namespace A387471

lemma latticeAngle_mem_Icc {n : ℕ} (hn : 0 < n) {A : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ)) :
    latticeAngle n A ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (6 : ℝ) * n := by positivity
  have hloR : -3 * (n : ℝ) < (A : ℝ) := by exact_mod_cast hA.1
  have hhiR : (A : ℝ) < 3 * (n : ℝ) := by exact_mod_cast hA.2
  have hloq : -(1 / 2 : ℝ) < (A : ℝ) / (6 * n) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  have hhiq : (A : ℝ) / (6 * n) < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  constructor
  · have hm := mul_lt_mul_of_pos_right hloq Real.pi_pos
    calc
      -(Real.pi / 2) = -(1 / 2 : ℝ) * Real.pi := by ring
      _ ≤ (A : ℝ) / (6 * n) * Real.pi := le_of_lt hm
      _ = latticeAngle n A := by
        simp only [latticeAngle]
        ring
  · have hm := mul_lt_mul_of_pos_right hhiq Real.pi_pos
    calc
      latticeAngle n A = (A : ℝ) / (6 * n) * Real.pi := by
        simp only [latticeAngle]
        ring
      _ ≤ (1 / 2 : ℝ) * Real.pi := le_of_lt hm
      _ = Real.pi / 2 := by ring

/-- On the admissible interval, a zero sine forces the integer coefficient to
be zero. -/
lemma coefficient_eq_zero_of_sine {n : ℕ} (hn : 0 < n) {A : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) = 0) : A = 0 := by
  have hmem := latticeAngle_mem_Icc hn hA
  have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hangle : latticeAngle n A = 0 :=
    Real.injOn_sin hmem hzero (by simpa using hsin)
  have hn0 : (6 * (n : ℝ)) ≠ 0 := by positivity
  have hpi0 : Real.pi / (6 * (n : ℝ)) ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  have hcast : (A : ℝ) = 0 :=
    (mul_eq_zero.mp (by simpa [latticeAngle] using hangle)).resolve_right hpi0
  exact_mod_cast hcast

#print axioms latticeAngle_mem_Icc
#print axioms coefficient_eq_zero_of_sine

end A387471
