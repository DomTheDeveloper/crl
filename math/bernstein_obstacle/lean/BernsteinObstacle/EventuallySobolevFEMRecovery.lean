import BernsteinObstacle.SobolevFEMRecovery
import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

noncomputable section

/-!
# Constructing FEM recovery thresholds from eventual estimates

Local finite-element analysis normally proves that, for each fixed smooth stage,
feasibility and the desired error bound hold on all sufficiently fine meshes.
This file converts those eventual statements into the explicit threshold data
consumed by `ThresholdSobolevFEMRecoveryData`.
-/

section EventualIndex

variable {P : ℕ → Prop}

/-- A concrete index after which an eventual `atTop` property holds. -/
def eventualIndex (hP : ∀ᶠ n in atTop, P n) : ℕ :=
  Classical.choose (eventually_atTop.1 hP)

/-- The property holds at every index beyond `eventualIndex`. -/
theorem eventualIndex_spec (hP : ∀ᶠ n in atTop, P n)
    {n : ℕ} (hn : eventualIndex hP ≤ n) : P n := by
  exact Classical.choose_spec (eventually_atTop.1 hP) n hn

end EventualIndex

section EventuallySobolevFEMRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving Sobolev/FEM recovery data stated in the form produced directly by
analysis: each fixed smooth stage is eventually feasible and eventually meets
its prescribed accuracy.  Stage zero is required on every mesh to initialize
the constructive scheduler. -/
structure EventuallySobolevFEMRecoveryData (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  discreteCone : ℕ → Set E
  limitCone : Set E
  smoothApprox : E → ℕ → E
  femRecovery : E → ℕ → ℕ → E
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  stageZero_mem :
    ∀ x, x ∈ limitCone → ∀ n, femRecovery x 0 n ∈ discreteCone n
  stageZero_close :
    ∀ x, x ∈ limitCone → ∀ n,
      ‖femRecovery x 0 n - smoothApprox x 0‖ ≤ (((0 : ℝ) + 1)⁻¹)
  recovery_eventually :
    ∀ x, x ∈ limitCone → ∀ m,
      ∀ᶠ n in atTop,
        femRecovery x m n ∈ discreteCone n ∧
          ‖femRecovery x m n - smoothApprox x m‖ ≤ (((m : ℝ) + 1)⁻¹)
  inner : ∀ n, discreteCone n ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

/-- The explicit mesh threshold extracted from the eventual stage estimate. -/
def EventuallySobolevFEMRecoveryData.threshold
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) (m : ℕ) : ℕ :=
  if hm : m = 0 then 0
  else max m (eventualIndex (D.recovery_eventually x hx m))

@[simp]
theorem EventuallySobolevFEMRecoveryData.threshold_zero
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) :
    D.threshold x hx 0 = 0 := by
  simp [EventuallySobolevFEMRecoveryData.threshold]

/-- Every selected threshold is at least its smoothness stage. -/
theorem EventuallySobolevFEMRecoveryData.stage_le_threshold
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) (m : ℕ) :
    m ≤ D.threshold x hx m := by
  by_cases hm : m = 0
  · subst m
    simp
  · simp [EventuallySobolevFEMRecoveryData.threshold, hm]

/-- Feasibility holds on every mesh beyond the extracted threshold. -/
theorem EventuallySobolevFEMRecoveryData.recovery_mem_after_threshold
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) (m n : ℕ)
    (hn : D.threshold x hx m ≤ n) :
    D.femRecovery x m n ∈ D.discreteCone n := by
  by_cases hm : m = 0
  · subst m
    exact D.stageZero_mem x hx n
  · have hindex :
        eventualIndex (D.recovery_eventually x hx m) ≤ n := by
      apply le_trans (le_max_right m _)
      simpa [EventuallySobolevFEMRecoveryData.threshold, hm] using hn
    exact (eventualIndex_spec (D.recovery_eventually x hx m) hindex).1

/-- The stage accuracy holds on every mesh beyond the extracted threshold. -/
theorem EventuallySobolevFEMRecoveryData.recovery_close_after_threshold
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) (m n : ℕ)
    (hn : D.threshold x hx m ≤ n) :
    ‖D.femRecovery x m n - D.smoothApprox x m‖ ≤ (((m : ℝ) + 1)⁻¹) := by
  by_cases hm : m = 0
  · subst m
    exact D.stageZero_close x hx n
  · have hindex :
        eventualIndex (D.recovery_eventually x hx m) ≤ n := by
      apply le_trans (le_max_right m _)
      simpa [EventuallySobolevFEMRecoveryData.threshold, hm] using hn
    exact (eventualIndex_spec (D.recovery_eventually x hx m) hindex).2

/-- Eventual physical recovery estimates canonically produce the threshold-form
package used by the verified scheduled Mosco theorem. -/
def EventuallySobolevFEMRecoveryData.toThresholdData
    (D : EventuallySobolevFEMRecoveryData E) :
    ThresholdSobolevFEMRecoveryData E where
  discreteCone := D.discreteCone
  limitCone := D.limitCone
  smoothApprox := D.smoothApprox
  femRecovery := D.femRecovery
  threshold := fun x m => if hx : x ∈ D.limitCone then D.threshold x hx m else m
  smooth_converges := D.smooth_converges
  threshold_zero := by
    intro x hx
    simp [hx]
  threshold_self := by
    intro x hx m
    simp only [hx, ↓reduceDIte]
    exact D.stage_le_threshold x hx m
  recovery_mem := by
    intro x hx m n hn
    simp only [hx, ↓reduceDIte] at hn
    exact D.recovery_mem_after_threshold x hx m n hn
  recovery_close := by
    intro x hx m n hn
    simp only [hx, ↓reduceDIte] at hn
    exact D.recovery_close_after_threshold x hx m n hn
  inner := D.inner
  limit_convex := D.limit_convex
  limit_closed := D.limit_closed

/-- Eventual meshwise recovery estimates imply Mosco convergence directly. -/
theorem EventuallySobolevFEMRecoveryData.moscoConverges
    (D : EventuallySobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone :=
  D.toThresholdData.moscoConverges

/-- Eventual meshwise recovery estimates feed the complete strong-minimizer
endgame after the usual vanishing solution-to-recovery bound. -/
theorem EventuallySobolevFEMRecoveryData.minimizers_strongConvergence
    (D : EventuallySobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ D.discreteCone n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges D.discreteCone D.limitCone ∧ StronglyConverges u x := by
  exact D.toThresholdData.minimizers_strongConvergence
    x hx u solutionErr hsolution hsolutionErr

end EventuallySobolevFEMRecovery

end

end BernsteinObstacle
