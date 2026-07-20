import BernsteinObstacle.Energy
import BernsteinObstacle.MinimizerConvergence
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

noncomputable section

/-!
# Coefficient squared norm and strong convergence

The finite coefficient energy uses the sum of coordinate squares, whereas the
ambient finite product carries the sup norm.  This file proves that the squared
sup norm is bounded by the coefficient squared norm.  Consequently, convergence
of the coefficient squared norm to zero implies strong convergence in the
ambient norm.  This removes the need to assume a separate norm-error majorant
when the coercive VI estimate already controls `coefficientNormSq`.
-/

section CoefficientNorm

variable {ι : Type*} [Fintype ι]

/-- The squared sup norm of a finite real coefficient vector is bounded by the
sum of its coordinate squares. -/
theorem norm_sq_le_coefficientNormSq (w : ι → ℝ) :
    ‖w‖ ^ 2 ≤ coefficientNormSq w := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      have hw : w = 0 := Subsingleton.elim w 0
      rw [hw]
      simp [coefficientNormSq]
  | inr h =>
      letI := h
      obtain ⟨i, hi⟩ := (IsGreatest.pi_norm w).1
      have hterm : (w i) ^ 2 ≤ coefficientNormSq w := by
        unfold coefficientNormSq
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      calc
        ‖w‖ ^ 2 = ‖w i‖ ^ 2 := by rw [← hi]
        _ = (w i) ^ 2 := by simp [Real.norm_eq_abs]
        _ ≤ coefficientNormSq w := hterm

/-- The ambient finite-product norm is bounded by the square root of the
coefficient squared norm. -/
theorem norm_le_sqrt_coefficientNormSq (w : ι → ℝ) :
    ‖w‖ ≤ Real.sqrt (coefficientNormSq w) := by
  exact Real.le_sqrt_of_sq_le (norm_sq_le_coefficientNormSq w)

/-- If the coefficient squared norm of a sequence tends to zero, the sequence
converges strongly to zero in the finite-product norm. -/
theorem stronglyConverges_zero_of_coefficientNormSq_tendsto_zero
    (w : ℕ → ι → ℝ)
    (hSq : Tendsto (fun k => coefficientNormSq (w k)) atTop (nhds 0)) :
    StronglyConverges w 0 := by
  have hSqrt :
      Tendsto (fun k => Real.sqrt (coefficientNormSq (w k))) atTop (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hSq
    change Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘ (fun k => coefficientNormSq (w k)))
      atTop (nhds 0)
    exact h
  unfold StronglyConverges
  exact squeeze_zero_norm
    (fun k => norm_le_sqrt_coefficientNormSq (w k)) hSqrt

/-- A recovery sequence converging strongly to `x`, together with a vanishing
coefficient-squared distance from candidates to that recovery, gives strong
convergence of the candidates to `x`. -/
theorem stronglyConverges_of_recovery_coefficientNormSq
    (u r : ℕ → ι → ℝ) (x : ι → ℝ)
    (hr : StronglyConverges r x)
    (hSq : Tendsto (fun k => coefficientNormSq (u k - r k)) atTop (nhds 0)) :
    StronglyConverges u x := by
  have hdiff : StronglyConverges (fun k => u k - r k) 0 :=
    stronglyConverges_zero_of_coefficientNormSq_tendsto_zero
      (fun k => u k - r k) hSq
  unfold StronglyConverges at hdiff hr ⊢
  have hadd := hdiff.add hr
  simpa using hadd

/-- A nonnegative scalar majorant tending to zero is enough to force strong
convergence when it bounds the coefficient squared recovery error. -/
theorem stronglyConverges_of_recovery_coefficientNormSq_bound
    (u r : ℕ → ι → ℝ) (x : ι → ℝ) (sqErr : ℕ → ℝ)
    (hr : StronglyConverges r x)
    (hbound : ∀ k, coefficientNormSq (u k - r k) ≤ sqErr k)
    (hSqErr : Tendsto sqErr atTop (nhds 0)) :
    StronglyConverges u x := by
  have hnonneg : ∀ k, 0 ≤ coefficientNormSq (u k - r k) := by
    intro k
    unfold coefficientNormSq
    positivity
  have hSq : Tendsto (fun k => coefficientNormSq (u k - r k)) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall hnonneg)
      (Eventually.of_forall hbound) hSqErr
  exact stronglyConverges_of_recovery_coefficientNormSq u r x hr hSq

end CoefficientNorm

end

end BernsteinObstacle
