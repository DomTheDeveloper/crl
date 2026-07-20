import BernsteinObstacle.AssembledObstacle
import BernsteinObstacle.CoefficientNorm
import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

noncomputable section

/-!
# Strong convergence from coercive energy gaps

The discrete variational inequality gives a coercive bound on the coefficient
squared error in terms of the recovery energy gap.  This file converts a
vanishing energy gap into a vanishing coefficient squared error and then invokes
the finite coefficient norm bridge to obtain strong convergence.  Thus the
finite assembled minimizer endgame no longer assumes a separate norm-error
estimate.
-/

section EnergyGapConvergence

variable {ι : Type*} [Fintype ι]

/-- The coefficient squared norm is unchanged when a difference is reversed. -/
theorem coefficientNormSq_sub_comm (u v : ι → ℝ) :
    coefficientNormSq (u - v) = coefficientNormSq (v - u) := by
  unfold coefficientNormSq
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A positive fixed multiple of a nonnegative coefficient squared error cannot
stay away from zero under a scalar majorant tending to zero. -/
theorem coefficientNormSq_tendsto_zero_of_scaled_le
    (w : ℕ → ι → ℝ) (gap : ℕ → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hbound : ∀ k, (μ / 2) * coefficientNormSq (w k) ≤ gap k)
    (hgap : Tendsto gap atTop (nhds 0)) :
    Tendsto (fun k => coefficientNormSq (w k)) atTop (nhds 0) := by
  have hhalf : 0 < μ / 2 := by positivity
  have hupper : ∀ k, coefficientNormSq (w k) ≤ gap k / (μ / 2) := by
    intro k
    apply (le_div_iff₀ hhalf).2
    simpa [mul_comm] using hbound k
  have hdiv : Tendsto (fun k => gap k / (μ / 2)) atTop (nhds 0) := by
    have h := hgap.div_const (μ / 2)
    simpa using h
  have hnonneg : ∀ k, 0 ≤ coefficientNormSq (w k) := by
    intro k
    unfold coefficientNormSq
    positivity
  exact squeeze_zero' (Eventually.of_forall hnonneg)
    (Eventually.of_forall hupper) hdiv

/-- A strongly convergent recovery sequence and a coercive energy-gap estimate
with vanishing gap imply strong convergence of the candidate sequence. -/
theorem stronglyConverges_of_recovery_scaledEnergyGap
    (u r : ℕ → ι → ℝ) (x : ι → ℝ)
    (gap : ℕ → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hr : StronglyConverges r x)
    (hbound : ∀ k, (μ / 2) * coefficientNormSq (r k - u k) ≤ gap k)
    (hgap : Tendsto gap atTop (nhds 0)) :
    StronglyConverges u x := by
  have hSqReverse :
      Tendsto (fun k => coefficientNormSq (r k - u k)) atTop (nhds 0) :=
    coefficientNormSq_tendsto_zero_of_scaled_le
      (fun k => r k - u k) gap μ hμ hbound hgap
  have hSq :
      Tendsto (fun k => coefficientNormSq (u k - r k)) atTop (nhds 0) := by
    simpa only [coefficientNormSq_sub_comm] using hSqReverse
  exact stronglyConverges_of_recovery_coefficientNormSq u r x hr hSq

end EnergyGapConvergence

section AssembledEnergyGapConvergence

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- Complete finite assembled minimizer endgame: if assembled VI solutions have
a strongly convergent feasible recovery sequence, a uniform positive coercivity
constant, and a recovery energy gap tending to zero, then the solutions converge
strongly to the recovery limit. -/
theorem assembledVISolutions_strongConvergence_of_energyGap
    (A : BernsteinAssembly Element Dof d n)
    (a : ℕ → Dof → Dof → ℝ)
    (f u r : ℕ → Dof → ℝ)
    (x : Dof → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hsymm : ∀ k i j, a k i j = a k j i)
    (hu : ∀ k, IsAssembledObstacleSolution A (a k) (f k) (u k))
    (hrFeasible : ∀ k, r k ∈ assemblyFeasibleSet A)
    (hcoercive : ∀ k,
      μ * coefficientNormSq (r k - u k) ≤
        matrixBilin (a k) (r k - u k) (r k - u k))
    (hr : StronglyConverges r x)
    (hgap : Tendsto
      (fun k => discreteEnergy (a k) (f k) (r k) -
        discreteEnergy (a k) (f k) (u k)) atTop (nhds 0)) :
    StronglyConverges u x := by
  apply stronglyConverges_of_recovery_scaledEnergyGap
    u r x
    (fun k => discreteEnergy (a k) (f k) (r k) -
      discreteEnergy (a k) (f k) (u k)) μ hμ hr
  · intro k
    exact assembledSolution_coercive_error_le_energyGap
      A (a k) (f k) (u k) (r k) μ (hsymm k) (hu k)
      (hrFeasible k) (hcoercive k)
  · exact hgap

/-- The same endgame specialized to clipped, boundary-compatible raw recovery
coefficients. -/
theorem assembledVISolutions_strongConvergence_of_clippedRecoveryEnergyGap
    (A : BernsteinAssembly Element Dof d n)
    (a : ℕ → Dof → Dof → ℝ)
    (f u raw : ℕ → Dof → ℝ)
    (x : Dof → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hsymm : ∀ k i j, a k i j = a k j i)
    (hu : ∀ k, IsAssembledObstacleSolution A (a k) (f k) (u k))
    (hboundary : ∀ k i, i ∈ A.boundaryDof → raw k i = 0)
    (hcoercive : ∀ k,
      μ * coefficientNormSq (clipCoefficients (raw k) - u k) ≤
        matrixBilin (a k)
          (clipCoefficients (raw k) - u k)
          (clipCoefficients (raw k) - u k))
    (hr : StronglyConverges (fun k => clipCoefficients (raw k)) x)
    (hgap : Tendsto
      (fun k => discreteEnergy (a k) (f k) (clipCoefficients (raw k)) -
        discreteEnergy (a k) (f k) (u k)) atTop (nhds 0)) :
    StronglyConverges u x := by
  apply assembledVISolutions_strongConvergence_of_energyGap
    A a f u (fun k => clipCoefficients (raw k)) x μ hμ hsymm hu
  · intro k
    exact clipCoefficients_mem_assemblyFeasibleSet A (raw k)
      (fun i hi => hboundary k i hi)
  · exact hcoercive
  · exact hr
  · exact hgap

end AssembledEnergyGapConvergence

end

end BernsteinObstacle
