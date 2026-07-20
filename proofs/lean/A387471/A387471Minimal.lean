import A387471Bounds
import A387471GridLift
import A387471SixRoots

/-!
# The minimal six-root branch of the A387471 classification
-/

namespace A387471

/-- A minimal six-term root relation satisfying the admissible bounds is either
ordinary or one of the two fifth-root exceptional patterns. -/
theorem minimal_six_root_classification {n : ℕ} (hn : 0 < n)
    {A B C : ℤ}
    (hAb : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hBb : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hCb : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hAB : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (hAC : -2 * (n : ℤ) < A + C ∧ A + C < 2 * (n : ℤ))
    (hBC : -2 * (n : ℤ) < B + C ∧ B + C < 2 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    letI : NeZero n := ⟨hn.ne'⟩
    MinimallyVanishes Finset.univ
      (fun r : Fin 6 ↦ canonicalRoot (12 * n) ^ (sixExponent n A B C r).val) →
      ABCClassified (n : ℤ) A B C := by
  letI : NeZero n := ⟨hn.ne'⟩
  intro hmin
  have hcard : (Finset.univ : Finset (Fin 6)).card ≤ 6 := by simp
  have hratioA := mann_weight_six_canonical (N := 12 * n)
    (mul_ne_zero (by norm_num) hn.ne') Finset.univ (sixExponent n A B C)
    hcard hmin (0 : Fin 6) (by simp) (3 : Fin 6) (by simp)
  have hratioB := mann_weight_six_canonical (N := 12 * n)
    (mul_ne_zero (by norm_num) hn.ne') Finset.univ (sixExponent n A B C)
    hcard hmin (1 : Fin 6) (by simp) (4 : Fin 6) (by simp)
  have hratioC := mann_weight_six_canonical (N := 12 * n)
    (mul_ne_zero (by norm_num) hn.ne') Finset.univ (sixExponent n A B C)
    hcard hmin (2 : Fin 6) (by simp) (5 : Fin 6) (by simp)
  have hdA : (n : ℤ) ∣ 5 * A :=
    n_dvd_five_mul_of_paired_ratio hn A (by simpa [sixExponent] using hratioA)
  have hdB : (n : ℤ) ∣ 5 * B :=
    n_dvd_five_mul_of_paired_ratio hn B (by simpa [sixExponent] using hratioB)
  have hdC : (n : ℤ) ∣ 5 * C :=
    n_dvd_five_mul_of_paired_ratio hn C (by simpa [sixExponent] using hratioC)
  rcases hdA with ⟨qA, hA⟩
  rcases hdB with ⟨qB, hB⟩
  rcases hdC with ⟨qC, hC⟩
  have hqAb := quotient_bounds hn hAb.1 hAb.2 hA
  have hqBb := quotient_bounds hn hBb.1 hBb.2 hB
  have hqCb := quotient_bounds hn hCb.1 hCb.2 hC
  let a : Fin 29 := fin29OfInt qA hqAb.1 hqAb.2
  let b : Fin 29 := fin29OfInt qB hqBb.1 hqBb.2
  let c : Fin 29 := fin29OfInt qC hqCb.1 hqCb.2
  have ha : angleInt a = qA := by simp [a]
  have hb : angleInt b = qB := by simp [b]
  have hc : angleInt c = qC := by simp [c]
  have hadm : admissibleGrid a b c := by
    rw [admissibleGrid, ha, hb, hc]
    exact ⟨quotient_pair_bound hn hAB.1 hAB.2 hA hB,
      quotient_pair_bound hn hAC.1 hAC.2 hA hC,
      quotient_pair_bound hn hBC.1 hBC.2 hB hC⟩
  have hangleA : latticeAngle n A = angleReal a := by
    simpa [a] using latticeAngle_eq_angleReal hn hA hqAb.1 hqAb.2
  have hangleB : latticeAngle n B = angleReal b := by
    simpa [b] using latticeAngle_eq_angleReal hn hB hqBb.1 hqBb.2
  have hangleC : latticeAngle n C = angleReal c := by
    simpa [c] using latticeAngle_eq_angleReal hn hC hqCb.1 hqCb.2
  have hgridSine : Real.sin (angleReal a) + Real.sin (angleReal b) +
      Real.sin (angleReal c) = 0 := by
    rwa [← hangleA, ← hangleB, ← hangleC]
  have hclass := bounded_grid_sine_classification a b c hadm hgridSine
  rw [ha, hb, hc] at hclass
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  exact classifiedGrid_to_ABC hnZ hA hB hC hclass

/-- Specialization to the reduced coefficients of an admissible cevian triple. -/
theorem minimal_reduced_classification {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (hsin : ReducedSineEquation n i j k) :
    letI : NeZero n := ⟨hn.ne'⟩
    MinimallyVanishes Finset.univ
      (fun r : Fin 6 ↦ canonicalRoot (12 * n) ^
        (sixExponent n (reducedA n i j k) (reducedB n i j k)
          (reducedC n i j k) r).val) →
      ABCClassified (n : ℤ) (reducedA n i j k) (reducedB n i j k)
        (reducedC n i j k) := by
  letI : NeZero n := ⟨hn.ne'⟩
  intro hmin
  apply minimal_six_root_classification hn
    (reducedA_bounds hn hi hj hk)
    (reducedB_bounds hn hi hj hk)
    (reducedC_bounds hn hi hj hk)
    (reducedAB_bounds hn hi)
    (reducedAC_bounds hn hj)
    (reducedBC_bounds hn hk)
    hsin hmin

#print axioms minimal_six_root_classification
#print axioms minimal_reduced_classification

end A387471