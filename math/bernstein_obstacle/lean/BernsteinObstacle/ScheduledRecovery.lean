import BernsteinObstacle.DiagonalRecovery
import Mathlib.Data.Nat.Find

open Filter

namespace BernsteinObstacle

/-!
# Constructive scheduling for moving recovery

The abstract diagonal theorem accepts a stage map tending to infinity and a
vanishing tracking error. In an actual FEM proof these objects are obtained
from mesh thresholds: for each smooth approximation level `m`, all meshes after
`threshold m` recover that approximation with error at most `1 / (m + 1)`.
-/

section ScheduledRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scheduledStage (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => threshold m ≤ n) n

theorem threshold_scheduledStage_le
    (threshold : ℕ → ℕ) (hzero : threshold 0 = 0) (n : ℕ) :
    threshold (scheduledStage threshold n) ≤ n := by
  unfold scheduledStage
  exact Nat.findGreatest_spec
    (P := fun m => threshold m ≤ n) (m := 0) (Nat.zero_le n) (by
      rw [hzero]
      exact Nat.zero_le n)

theorem scheduledStage_tendsto_atTop
    (threshold : ℕ → ℕ)
    (hself : ∀ m, m ≤ threshold m) :
    Tendsto (scheduledStage threshold) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro m
  refine eventually_atTop.2 ⟨threshold m, ?_⟩
  intro n hn
  unfold scheduledStage
  exact Nat.le_findGreatest (le_trans (hself m) hn) hn

theorem scheduledError_tendsto_zero
    (threshold : ℕ → ℕ)
    (hself : ∀ m, m ≤ threshold m) :
    Tendsto (fun n => (((scheduledStage threshold n : ℝ) + 1)⁻¹))
      atTop (nhds 0) := by
  have hbase :
      Tendsto (fun m : ℕ => (((m : ℝ) + 1)⁻¹)) atTop (nhds (0 : ℝ)) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact hbase.comp (scheduledStage_tendsto_atTop threshold hself)

theorem exists_scheduledDiagonalRecovery
    (K : ℕ → Set E)
    (w : ℕ → E) (R : ℕ → ℕ → E)
    (threshold : ℕ → ℕ) (x : E)
    (hw : StronglyConverges w x)
    (hzero : threshold 0 = 0)
    (hself : ∀ m, m ≤ threshold m)
    (hmem : ∀ m n, threshold m ≤ n → R m n ∈ K n)
    (hclose : ∀ m n, threshold m ≤ n →
      ‖R m n - w m‖ ≤ (((m : ℝ) + 1)⁻¹)) :
    ∃ (stage : ℕ → ℕ) (err : ℕ → ℝ),
      StronglyConverges w x ∧
      Tendsto stage atTop atTop ∧
      (∀ n, R (stage n) n ∈ K n) ∧
      (∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n) ∧
      Tendsto err atTop (nhds 0) := by
  let stage : ℕ → ℕ := scheduledStage threshold
  let err : ℕ → ℝ := fun n => (((stage n : ℝ) + 1)⁻¹)
  refine ⟨stage, err, hw, ?_, ?_, ?_, ?_⟩
  · exact scheduledStage_tendsto_atTop threshold hself
  · intro n
    exact hmem (stage n) n (threshold_scheduledStage_le threshold hzero n)
  · intro n
    exact hclose (stage n) n (threshold_scheduledStage_le threshold hzero n)
  · simpa [stage, err] using scheduledError_tendsto_zero threshold hself

theorem mosco_of_scheduledRecovery_of_subset_closedConvex
    (K : ℕ → Set E) (Klim : Set E)
    (hthreshold :
      ∀ x ∈ Klim,
        ∃ (w : ℕ → E) (R : ℕ → ℕ → E) (threshold : ℕ → ℕ),
          StronglyConverges w x ∧
          threshold 0 = 0 ∧
          (∀ m, m ≤ threshold m) ∧
          (∀ m n, threshold m ≤ n → R m n ∈ K n) ∧
          (∀ m n, threshold m ≤ n →
            ‖R m n - w m‖ ≤ (((m : ℝ) + 1)⁻¹)))
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim) :
    MoscoConverges K Klim := by
  apply mosco_of_diagonalRecovery_of_subset_closedConvex
    K Klim ?_ hsubset hconv hclosed
  intro x hx
  obtain ⟨w, R, threshold, hw, hzero, hself, hmem, hclose⟩ :=
    hthreshold x hx
  obtain ⟨stage, err, hw', hstage, hmem', hclose', herr⟩ :=
    exists_scheduledDiagonalRecovery K w R threshold x
      hw hzero hself hmem hclose
  exact ⟨w, R, stage, err, hw', hstage, hmem', hclose', herr⟩

end ScheduledRecovery

end BernsteinObstacle
