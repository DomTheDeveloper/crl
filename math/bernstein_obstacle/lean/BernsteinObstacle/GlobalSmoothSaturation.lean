import BernsteinObstacle.ContactAwareRecovery
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Global best-approximation saturation bridge

This file turns a local coefficient obstruction and an explicit feasible repair
into a statement about the actual metric distance from a target to a feasible
set.  Unlike a rate lemma with an externally supplied error variable, the
quantity below is the genuine best-approximation error `Metric.infDist u K`.
-/

section BestApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Best approximation error of `u` from the feasible set `K`. -/
def bestApproximationError (u : E) (K : Set E) : ℝ :=
  Metric.infDist u K

/-- A uniformly bounded coefficient functional converts a coefficient defect
on every feasible competitor into a lower bound for the genuine best error. -/
theorem bestApproximationError_lower_of_coefficientDefect
    (u : E) (K : Set E) (L : E →L[ℝ] ℝ) (d A : ℝ)
    (hK : K.Nonempty) (hA : 0 < A) (hL : ‖L‖ ≤ A)
    (hdefect : ∀ v ∈ K, d ≤ |L (u - v)|) :
    d / A ≤ bestApproximationError u K := by
  unfold bestApproximationError
  apply (Metric.le_infDist hK).2
  intro v hv
  apply (div_le_iff₀ hA).2
  calc
    d ≤ |L (u - v)| := hdefect v hv
    _ = ‖L (u - v)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖u - v‖ := L.le_opNorm (u - v)
    _ ≤ A * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = A * dist u v := by rw [dist_eq_norm]

/-- Any explicit feasible witness gives an upper bound for the genuine best
approximation error. -/
theorem bestApproximationError_upper_of_witness
    (u v : E) (K : Set E) (R : ℝ) (hv : v ∈ K)
    (hupper : ‖u - v‖ ≤ R) :
    bestApproximationError u K ≤ R := by
  unfold bestApproximationError
  calc
    Metric.infDist u K ≤ dist u v := Metric.infDist_le_dist_of_mem hv
    _ = ‖u - v‖ := dist_eq_norm
    _ ≤ R := hupper

/-- Exact two-sided second-order saturation template for a feasible cone.

The lower estimate comes from a defect of size `gamma * h^2`; the upper
estimate comes from an explicit feasible recovery of size `C * h^2`. -/
theorem bestApproximationError_secondOrder_sandwich
    (u v : E) (K : Set E) (L : E →L[ℝ] ℝ)
    (gamma A C h : ℝ)
    (hK : K.Nonempty) (hv : v ∈ K)
    (hA : 0 < A) (hL : ‖L‖ ≤ A)
    (hdefect : ∀ w ∈ K, gamma * h ^ 2 ≤ |L (u - w)|)
    (hupper : ‖u - v‖ ≤ C * h ^ 2) :
    (gamma / A) * h ^ 2 ≤ bestApproximationError u K ∧
      bestApproximationError u K ≤ C * h ^ 2 := by
  constructor
  · have hlower := bestApproximationError_lower_of_coefficientDefect
      u K L (gamma * h ^ 2) A hK hA hL hdefect
    calc
      (gamma / A) * h ^ 2 = (gamma * h ^ 2) / A := by ring
      _ ≤ bestApproximationError u K := hlower
  · exact bestApproximationError_upper_of_witness
      u v K (C * h ^ 2) hv hupper

/-- The coefficient-cone saturation theorem in normalized form. -/
theorem normalized_bestApproximationError_mem_Icc
    (u v : E) (K : Set E) (L : E →L[ℝ] ℝ)
    (gamma A C h : ℝ)
    (hK : K.Nonempty) (hv : v ∈ K)
    (hA : 0 < A) (hh : 0 < h) (hL : ‖L‖ ≤ A)
    (hdefect : ∀ w ∈ K, gamma * h ^ 2 ≤ |L (u - w)|)
    (hupper : ‖u - v‖ ≤ C * h ^ 2) :
    bestApproximationError u K / h ^ 2 ∈ Set.Icc (gamma / A) C := by
  have hsandwich := bestApproximationError_secondOrder_sandwich
    u v K L gamma A C h hK hv hA hL hdefect hupper
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · exact (le_div_iff₀ hh2).2 hsandwich.1
  · exact (div_le_iff₀ hh2).2 hsandwich.2

end BestApproximation

end

end BernsteinObstacle
