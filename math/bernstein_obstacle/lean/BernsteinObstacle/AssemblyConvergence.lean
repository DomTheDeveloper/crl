import BernsteinObstacle.AssemblyMosco
import BernsteinObstacle.MinimizerConvergence

open Filter

namespace BernsteinObstacle

noncomputable section

/-!
# Strong convergence from assembled clipped recovery

This file composes the assembled feasible-set theorem with the abstract
recovery-to-minimizer convergence bridge.  It records the exact final interface
used by the finite-element proof: raw recovery coefficients satisfy homogeneous
boundary data, global clipping makes every recovery feasible, the clipped
recovery converges strongly to the target, and the discrete solution approaches
that recovery with a vanishing norm majorant.
-/

section AssemblyConvergence

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- Mosco recovery for the assembled feasible set plus a vanishing
recovery-to-solution bound gives strong convergence. -/
theorem assemblyMosco_recovery_closeness_implies_strongConvergence
    (A : BernsteinAssembly Element Dof d n)
    (x : Dof → ℝ) (hx : x ∈ assemblyFeasibleSet A)
    (u : ℕ → Dof → ℝ) (err : ℕ → ℝ)
    (hclose :
      ∀ r : ℕ → Dof → ℝ,
        (∀ k, r k ∈ assemblyFeasibleSet A) →
        StronglyConverges r x →
        ∀ k, ‖u k - r k‖ ≤ err k)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges u x := by
  exact mosco_recovery_closeness_implies_strong_convergence
    (assemblyFeasibleSet_mosco_const A) x hx u err hclose herr

/-- A boundary-compatible raw recovery sequence becomes feasible after clipping,
and if the clipped sequence converges while the solution-to-recovery error
vanishes, then the assembled solutions converge strongly. -/
theorem assembledClippedRecovery_implies_strongConvergence
    (A : BernsteinAssembly Element Dof d n)
    (raw u : ℕ → Dof → ℝ) (x : Dof → ℝ) (err : ℕ → ℝ)
    (hboundary : ∀ k i, i ∈ A.boundaryDof → raw k i = 0)
    (hrecovery : StronglyConverges (fun k => clipCoefficients (raw k)) x)
    (hclose : ∀ k, ‖u k - clipCoefficients (raw k)‖ ≤ err k)
    (herr : Tendsto err atTop (nhds 0)) :
    (∀ k, clipCoefficients (raw k) ∈ assemblyFeasibleSet A) ∧
      StronglyConverges u x := by
  constructor
  · intro k
    exact clipCoefficients_mem_assemblyFeasibleSet A (raw k)
      (fun i hi => hboundary k i hi)
  · exact stronglyConverges_of_recovery_closeness
      u (fun k => clipCoefficients (raw k)) x err hrecovery hclose herr

/-- Operator form for a chosen assembled recovery construction. -/
theorem assemblyRecoveryOperator_closeness_implies_strongConvergence
    (A : BernsteinAssembly Element Dof d n)
    (R : ℕ → (Dof → ℝ) → (Dof → ℝ))
    (hmap : ∀ k x, x ∈ assemblyFeasibleSet A → R k x ∈ assemblyFeasibleSet A)
    (hR : ∀ x ∈ assemblyFeasibleSet A,
      StronglyConverges (fun k => R k x) x)
    (x : Dof → ℝ) (hx : x ∈ assemblyFeasibleSet A)
    (u : ℕ → Dof → ℝ) (err : ℕ → ℝ)
    (hclose : ∀ k, ‖u k - R k x‖ ≤ err k)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges u x := by
  exact recoveryOperator_closeness_implies_strong_convergence
    R hmap hR x hx u err hclose herr

end AssemblyConvergence

end

end BernsteinObstacle
