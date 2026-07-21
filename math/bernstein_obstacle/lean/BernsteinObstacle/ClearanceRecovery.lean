import BernsteinObstacle.AsymptoticRecovery

open Filter

namespace BernsteinObstacle

/-!
# Positive-clearance recovery for conforming obstacle FEM

For a fixed smooth stage, physical obstacle-FEM arguments commonly prove two
facts:

1. the smooth recovery has a strictly positive feasibility clearance;
2. the finite-element recovery converges to that smooth target.

Once the recovery error is smaller than the clearance, discrete feasibility is
a deterministic consequence.  This file formalizes that standard implication
and packages it into `AsymptoticSobolevFEMRecoveryData`, so eventual feasibility
no longer has to be postulated separately.
-/

section ClearanceRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative recovery data in which eventual feasibility follows from a
strict stagewise clearance and strong convergence of the finite-element
recovery to the smooth target. -/
structure ClearanceSobolevFEMRecoveryData (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  discreteCone : ℕ → Set E
  limitCone : Set E
  smoothApprox : E → ℕ → E
  femRecovery : E → ℕ → ℕ → E
  clearance : E → ℕ → ℝ
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  zero_recovery_mem :
    ∀ x, x ∈ limitCone → ∀ n,
      femRecovery x 0 n ∈ discreteCone n
  zero_recovery_close :
    ∀ x, x ∈ limitCone → ∀ n,
      ‖femRecovery x 0 n - smoothApprox x 0‖ ≤ (1 : ℝ)
  clearance_pos :
    ∀ x, x ∈ limitCone → ∀ m, 0 < clearance x m
  recovery_tendsto :
    ∀ x, x ∈ limitCone → ∀ m,
      Tendsto (fun n => femRecovery x m n - smoothApprox x m)
        atTop (nhds 0)
  recovery_mem_of_norm_lt_clearance :
    ∀ x, x ∈ limitCone → ∀ m n,
      ‖femRecovery x m n - smoothApprox x m‖ < clearance x m →
        femRecovery x m n ∈ discreteCone n
  inner : ∀ n, discreteCone n ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

/-- A positive clearance is eventually larger than any error sequence tending
to zero. -/
theorem eventually_norm_lt_clearance
    (err : ℕ → E) (delta : ℝ)
    (hdelta : 0 < delta)
    (herr : Tendsto err atTop (nhds 0)) :
    ∀ᶠ n in atTop, ‖err n‖ < delta := by
  have hnorm : Tendsto (fun n => ‖err n‖) atTop (nhds 0) :=
    tendsto_norm.comp herr
  exact (tendsto_order.1 hnorm).2 delta hdelta

/-- Strict stagewise clearance converts quantitative FEM convergence into the
ordinary eventual-feasibility recovery interface. -/
def ClearanceSobolevFEMRecoveryData.toAsymptoticData
    (D : ClearanceSobolevFEMRecoveryData E) :
    AsymptoticSobolevFEMRecoveryData E where
  discreteCone := D.discreteCone
  limitCone := D.limitCone
  smoothApprox := D.smoothApprox
  femRecovery := D.femRecovery
  smooth_converges := D.smooth_converges
  zero_recovery_mem := D.zero_recovery_mem
  zero_recovery_close := D.zero_recovery_close
  recovery_eventually_mem := by
    intro x hx m
    have hclose :
        ∀ᶠ n in atTop,
          ‖D.femRecovery x m n - D.smoothApprox x m‖ < D.clearance x m :=
      eventually_norm_lt_clearance
        (fun n => D.femRecovery x m n - D.smoothApprox x m)
        (D.clearance x m) (D.clearance_pos x hx m)
        (D.recovery_tendsto x hx m)
    exact hclose.mono fun n hn =>
      D.recovery_mem_of_norm_lt_clearance x hx m n hn
  recovery_tendsto := D.recovery_tendsto
  inner := D.inner
  limit_convex := D.limit_convex
  limit_closed := D.limit_closed

/-- Positive-clearance FEM recovery implies Mosco convergence of the discrete
obstacle cones. -/
theorem ClearanceSobolevFEMRecoveryData.moscoConverges
    (D : ClearanceSobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone := by
  exact D.toAsymptoticData.moscoConverges

/-- Positive-clearance FEM recovery closes the abstract strong-minimizer
endgame whenever the usual recovery-comparison error tends to zero. -/
theorem ClearanceSobolevFEMRecoveryData.minimizers_strongConvergence
    (D : ClearanceSobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ D.discreteCone n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges D.discreteCone D.limitCone ∧ StronglyConverges u x := by
  exact D.toAsymptoticData.minimizers_strongConvergence
    x hx u solutionErr hsolution hsolutionErr

end ClearanceRecovery

end BernsteinObstacle
