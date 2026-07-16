import A387471AngleBounds
import A387471SixRoots

/-!
# Cancellation consequences inside the admissible sine interval
-/

open Set

namespace A387471

/-- On the admissible interval, `sin B + sin C = 0` forces `B = -C`. -/
lemma coefficients_eq_neg_of_sine_add_eq_zero {n : ℕ} (hn : 0 < n) {B C : ℤ}
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (h : Real.sin (latticeAngle n B) + Real.sin (latticeAngle n C) = 0) :
    B = -C := by
  have hnegC : -3 * (n : ℤ) < -C ∧ -C < 3 * (n : ℤ) := by omega
  have hmemB := latticeAngle_mem_Icc hn hB
  have hmemNegC := latticeAngle_mem_Icc hn hnegC
  have hangNeg : latticeAngle n (-C) = -latticeAngle n C := by simp [latticeAngle]
  have hsine : Real.sin (latticeAngle n B) = Real.sin (latticeAngle n (-C)) := by
    rw [hangNeg, Real.sin_neg]
    linarith
  have hangle : latticeAngle n B = latticeAngle n (-C) :=
    Real.injOn_sin hmemB hmemNegC hsine
  have hn0 : (6 * (n : ℝ)) ≠ 0 := by positivity
  have hfac : Real.pi / (6 * (n : ℝ)) ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  have hcast : (B : ℝ) = (-C : ℤ) := by
    apply mul_right_cancel₀ hfac
    simpa [latticeAngle] using hangle
  exact_mod_cast hcast

/-- Cancellation of a root with its own reflected term forces the corresponding
coefficient to be zero. -/
lemma coefficient_eq_zero_of_self_pair {n : ℕ} (hn : 0 < n) {A : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hpair : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      (-Complex.exp (-(latticeAngle n A : ℂ) * Complex.I)) = 0) : A = 0 := by
  have hnum : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) -
      Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) = 0 := by simpa using hpair
  rw [exp_sub_exp_neg_eq_two_sin_mul_I] at hnum
  have hsin : Real.sin (latticeAngle n A) = 0 := by
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    exact_mod_cast (mul_eq_zero.mp (mul_eq_zero.mp hnum |>.resolve_left htwo) |>.resolve_right hI)
  exact coefficient_eq_zero_of_sine hn hA hsin

#print axioms coefficients_eq_neg_of_sine_add_eq_zero
#print axioms coefficient_eq_zero_of_self_pair

end A387471
