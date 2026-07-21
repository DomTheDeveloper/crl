import BernsteinObstacle.SobolevFEMRecovery

open Filter

namespace BernsteinObstacle

/-!
# From ordinary FEM convergence to constructive recovery thresholds

A physical finite-element proof usually supplies, for each fixed smooth target,
an eventual feasibility statement and an error tending to zero as the mesh is
refined. `ThresholdSobolevFEMRecoveryData` expects explicit mesh thresholds.
This file proves that the thresholds can be extracted from the usual
eventual/tendsto hypotheses, leaving only one base recovery at stage zero.
-/

section ThresholdExtraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_threshold_of_eventually
    (P : ℕ → ℕ → Prop)
    (hzero : ∀ n, P 0 n)
    (hevent : ∀ m, ∀ᶠ n in atTop, P m n) :
    ∃ threshold : ℕ → ℕ,
      threshold 0 = 0 ∧
      (∀ m, m ≤ threshold m) ∧
      (∀ m n, threshold m ≤ n → P m n) := by
  classical
  choose N hN using fun m => (eventually_atTop.1 (hevent m))
  let threshold : ℕ → ℕ := fun m => if m = 0 then 0 else max m (N m)
  refine ⟨threshold, ?_, ?_, ?_⟩
  · simp [threshold]
  · intro m
    by_cases hm : m = 0
    · simp [threshold, hm]
    · simp [threshold, hm]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      exact hzero n
    · apply hN m n
      have hmax : max m (N m) ≤ n := by
        simpa [threshold, hm] using hmn
      exact (le_max_right m (N m)).trans hmax

structure AsymptoticSobolevFEMRecoveryData (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  discreteCone : ℕ → Set E
  limitCone : Set E
  smoothApprox : E → ℕ → E
  femRecovery : E → ℕ → ℕ → E
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  zero_recovery_mem :
    ∀ x, x ∈ limitCone → ∀ n,
      femRecovery x 0 n ∈ discreteCone n
  zero_recovery_close :
    ∀ x, x ∈ limitCone → ∀ n,
      ‖femRecovery x 0 n - smoothApprox x 0‖ ≤ (1 : ℝ)
  recovery_eventually_mem :
    ∀ x, x ∈ limitCone → ∀ m,
      ∀ᶠ n in atTop, femRecovery x m n ∈ discreteCone n
  recovery_tendsto :
    ∀ x, x ∈ limitCone → ∀ m,
      Tendsto (fun n => femRecovery x m n - smoothApprox x m)
        atTop (nhds 0)
  inner : ∀ n, discreteCone n ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

theorem AsymptoticSobolevFEMRecoveryData.exists_threshold
    (D : AsymptoticSobolevFEMRecoveryData E)
    (x : E) (hx : x ∈ D.limitCone) :
    ∃ threshold : ℕ → ℕ,
      threshold 0 = 0 ∧
      (∀ m, m ≤ threshold m) ∧
      (∀ m n, threshold m ≤ n →
        D.femRecovery x m n ∈ D.discreteCone n ∧
        ‖D.femRecovery x m n - D.smoothApprox x m‖ ≤
          (((m : ℝ) + 1)⁻¹)) := by
  let P : ℕ → ℕ → Prop := fun m n =>
    D.femRecovery x m n ∈ D.discreteCone n ∧
      ‖D.femRecovery x m n - D.smoothApprox x m‖ ≤
        (((m : ℝ) + 1)⁻¹)
  have hzero : ∀ n, P 0 n := by
    intro n
    constructor
    · exact D.zero_recovery_mem x hx n
    · simpa [P] using D.zero_recovery_close x hx n
  have hevent : ∀ m, ∀ᶠ n in atTop, P m n := by
    intro m
    have hnormRaw := (D.recovery_tendsto x hx m).norm
    have hnorm :
        Tendsto
          (fun n => ‖D.femRecovery x m n - D.smoothApprox x m‖)
          atTop (nhds 0) := by
      simpa only [norm_zero] using hnormRaw
    have heps : 0 < (((m : ℝ) + 1)⁻¹) := by positivity
    have hclose :
        ∀ᶠ n in atTop,
          ‖D.femRecovery x m n - D.smoothApprox x m‖ ≤
            (((m : ℝ) + 1)⁻¹) := by
      exact ((tendsto_order.1 hnorm).2 _ heps).mono fun _ hn => hn.le
    exact (D.recovery_eventually_mem x hx m).and hclose
  simpa [P] using exists_threshold_of_eventually P hzero hevent

noncomputable def AsymptoticSobolevFEMRecoveryData.toThresholdData
    (D : AsymptoticSobolevFEMRecoveryData E) :
    ThresholdSobolevFEMRecoveryData E := by
  classical
  let threshold : E → ℕ → ℕ := fun x =>
    if hx : x ∈ D.limitCone then
      Classical.choose (D.exists_threshold x hx)
    else 0
  refine
    { discreteCone := D.discreteCone
      limitCone := D.limitCone
      smoothApprox := D.smoothApprox
      femRecovery := D.femRecovery
      threshold := threshold
      smooth_converges := D.smooth_converges
      threshold_zero := ?_
      threshold_self := ?_
      recovery_mem := ?_
      recovery_close := ?_
      inner := D.inner
      limit_convex := D.limit_convex
      limit_closed := D.limit_closed }
  · intro x hx
    simpa [threshold, hx] using (Classical.choose_spec (D.exists_threshold x hx)).1
  · intro x hx m
    simpa [threshold, hx] using (Classical.choose_spec (D.exists_threshold x hx)).2.1 m
  · intro x hx m n hmn
    have hspec := (Classical.choose_spec (D.exists_threshold x hx)).2.2 m n
    simpa [threshold, hx] using (hspec (by simpa [threshold, hx] using hmn)).1
  · intro x hx m n hmn
    have hspec := (Classical.choose_spec (D.exists_threshold x hx)).2.2 m n
    simpa [threshold, hx] using (hspec (by simpa [threshold, hx] using hmn)).2

theorem AsymptoticSobolevFEMRecoveryData.moscoConverges
    (D : AsymptoticSobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone := by
  exact D.toThresholdData.moscoConverges

theorem AsymptoticSobolevFEMRecoveryData.minimizers_strongConvergence
    (D : AsymptoticSobolevFEMRecoveryData E)
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

end ThresholdExtraction

end BernsteinObstacle
