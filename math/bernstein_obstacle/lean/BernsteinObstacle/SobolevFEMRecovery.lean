import BernsteinObstacle.ScheduledRecovery

open Filter

namespace BernsteinObstacle

/-!
# Moving Sobolev/FEM recovery interfaces

These structures package the exact data needed to instantiate the verified
Mosco/minimizer endgame for a moving conforming finite-element family inside one
ambient normed space. They deliberately separate the physical analytical
inputs from the abstract convergence argument.
-/

section SobolevFEMRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SobolevFEMRecoveryData (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  discreteCone : ℕ → Set E
  limitCone : Set E
  smoothApprox : E → ℕ → E
  femRecovery : E → ℕ → ℕ → E
  stage : E → ℕ → ℕ
  error : E → ℕ → ℝ
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  stage_tendsto :
    ∀ x, x ∈ limitCone → Tendsto (stage x) atTop atTop
  recovery_mem :
    ∀ x, x ∈ limitCone → ∀ n,
      femRecovery x (stage x n) n ∈ discreteCone n
  recovery_close :
    ∀ x, x ∈ limitCone → ∀ n,
      ‖femRecovery x (stage x n) n - smoothApprox x (stage x n)‖ ≤ error x n
  error_tendsto :
    ∀ x, x ∈ limitCone → Tendsto (error x) atTop (nhds 0)
  inner : ∀ n, discreteCone n ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

theorem SobolevFEMRecoveryData.diagonalRecovery
    (D : SobolevFEMRecoveryData E) (x : E) (hx : x ∈ D.limitCone) :
    ∃ (w : ℕ → E) (R : ℕ → ℕ → E)
      (stage : ℕ → ℕ) (err : ℕ → ℝ),
      StronglyConverges w x ∧
      Tendsto stage atTop atTop ∧
      (∀ n, R (stage n) n ∈ D.discreteCone n) ∧
      (∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n) ∧
      Tendsto err atTop (nhds 0) := by
  refine ⟨D.smoothApprox x, D.femRecovery x, D.stage x, D.error x, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.smooth_converges x hx
  · exact D.stage_tendsto x hx
  · exact D.recovery_mem x hx
  · exact D.recovery_close x hx
  · exact D.error_tendsto x hx

theorem SobolevFEMRecoveryData.moscoConverges
    (D : SobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone := by
  exact mosco_of_diagonalRecovery_of_subset_closedConvex
    D.discreteCone D.limitCone D.diagonalRecovery
    D.inner D.limit_convex D.limit_closed

theorem SobolevFEMRecoveryData.minimizers_strongConvergence
    (D : SobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ D.discreteCone n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges D.discreteCone D.limitCone ∧ StronglyConverges u x := by
  exact diagonalRecovery_minimizers_strongConvergence
    D.discreteCone D.limitCone D.diagonalRecovery
    D.inner D.limit_convex D.limit_closed
    x hx u solutionErr hsolution hsolutionErr

/-- Moving Sobolev/FEM recovery data in the threshold form produced directly by
local approximation estimates. -/
structure ThresholdSobolevFEMRecoveryData (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  discreteCone : ℕ → Set E
  limitCone : Set E
  smoothApprox : E → ℕ → E
  femRecovery : E → ℕ → ℕ → E
  threshold : E → ℕ → ℕ
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  threshold_zero :
    ∀ x, x ∈ limitCone → threshold x 0 = 0
  threshold_self :
    ∀ x, x ∈ limitCone → ∀ m, m ≤ threshold x m
  recovery_mem :
    ∀ x, x ∈ limitCone → ∀ m n,
      threshold x m ≤ n → femRecovery x m n ∈ discreteCone n
  recovery_close :
    ∀ x, x ∈ limitCone → ∀ m n,
      threshold x m ≤ n →
      ‖femRecovery x m n - smoothApprox x m‖ ≤ (((m : ℝ) + 1)⁻¹)
  inner : ∀ n, discreteCone n ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

theorem ThresholdSobolevFEMRecoveryData.scheduledRecovery
    (D : ThresholdSobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) :
    ∃ (w : ℕ → E) (R : ℕ → ℕ → E)
      (stage : ℕ → ℕ) (err : ℕ → ℝ),
      StronglyConverges w x ∧
      Tendsto stage atTop atTop ∧
      (∀ n, R (stage n) n ∈ D.discreteCone n) ∧
      (∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n) ∧
      Tendsto err atTop (nhds 0) := by
  obtain ⟨stage, err, hw, hstage, hmem, hclose, herr⟩ :=
    exists_scheduledDiagonalRecovery
      D.discreteCone (D.smoothApprox x) (D.femRecovery x) (D.threshold x) x
      (D.smooth_converges x hx) (D.threshold_zero x hx)
      (D.threshold_self x hx) (D.recovery_mem x hx) (D.recovery_close x hx)
  exact ⟨D.smoothApprox x, D.femRecovery x, stage, err,
    hw, hstage, hmem, hclose, herr⟩

theorem ThresholdSobolevFEMRecoveryData.moscoConverges
    (D : ThresholdSobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone := by
  exact mosco_of_diagonalRecovery_of_subset_closedConvex
    D.discreteCone D.limitCone D.scheduledRecovery
    D.inner D.limit_convex D.limit_closed

theorem ThresholdSobolevFEMRecoveryData.minimizers_strongConvergence
    (D : ThresholdSobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ D.discreteCone n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges D.discreteCone D.limitCone ∧ StronglyConverges u x := by
  have hM : MoscoConverges D.discreteCone D.limitCone := D.moscoConverges
  refine ⟨hM, ?_⟩
  exact mosco_recovery_closeness_implies_strong_convergence
    hM x hx u solutionErr hsolution hsolutionErr

end SobolevFEMRecovery

end BernsteinObstacle
