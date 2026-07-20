import BernsteinObstacle.ConvexWeakClosure
import BernsteinObstacle.MinimizerConvergence

open Filter

namespace BernsteinObstacle

/-!
# Diagonal recovery for moving Bernstein cones

The positive-density proof first chooses smooth nonnegative approximants and
then, for progressively finer meshes, applies a positive Bernstein recovery to
a slowly varying approximant.  This file certifies the diagonal argument: if
the smooth stage tends to infinity and the discrete recovery error tends to
zero, the resulting moving feasible sequence converges strongly to the target.
-/

section DiagonalRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convergent approximation sequence remains convergent after composition
with any stage map tending to infinity. -/
theorem stronglyConverges_comp_tendsto_atTop
    (w : ℕ → E) (x : E) (stage : ℕ → ℕ)
    (hw : StronglyConverges w x)
    (hstage : Tendsto stage atTop atTop) :
    StronglyConverges (fun n => w (stage n)) x := by
  unfold StronglyConverges at hw ⊢
  exact hw.comp hstage

/-- A moving recovery tracking a slowly varying smooth approximant with a
vanishing norm error converges strongly to the same target. -/
theorem diagonalRecovery_stronglyConverges
    (w : ℕ → E) (R : ℕ → ℕ → E)
    (stage : ℕ → ℕ) (x : E) (err : ℕ → ℝ)
    (hw : StronglyConverges w x)
    (hstage : Tendsto stage atTop atTop)
    (hclose : ∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges (fun n => R (stage n) n) x := by
  have hwstage : StronglyConverges (fun n => w (stage n)) x :=
    stronglyConverges_comp_tendsto_atTop w x stage hw hstage
  exact stronglyConverges_of_recovery_closeness
    (fun n => R (stage n) n) (fun n => w (stage n)) x err
    hwstage hclose herr

/-- The diagonal positive-recovery data supplies the recovery half of Mosco
convergence; inner inclusion and closed convexity supply the weak-limit half. -/
theorem mosco_of_diagonalRecovery_of_subset_closedConvex
    (K : ℕ → Set E) (Klim : Set E)
    (hdiag :
      ∀ x ∈ Klim,
        ∃ (w : ℕ → E) (R : ℕ → ℕ → E)
          (stage : ℕ → ℕ) (err : ℕ → ℝ),
          StronglyConverges w x ∧
          Tendsto stage atTop atTop ∧
          (∀ n, R (stage n) n ∈ K n) ∧
          (∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n) ∧
          Tendsto err atTop (nhds 0))
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim) :
    MoscoConverges K Klim := by
  apply mosco_of_recovery_of_subset_of_closedConvex
    K Klim ?_ hsubset hconv hclosed
  intro x hx
  obtain ⟨w, R, stage, err, hw, hstage, hmem, hclose, herr⟩ :=
    hdiag x hx
  refine ⟨fun n => R (stage n) n, hmem, ?_⟩
  exact diagonalRecovery_stronglyConverges
    w R stage x err hw hstage hclose herr

/-- Full B4--B6 endgame: diagonal recovery gives Mosco convergence, and a
vanishing solution-to-recovery bound gives strong minimizer convergence. -/
theorem diagonalRecovery_minimizers_strongConvergence
    (K : ℕ → Set E) (Klim : Set E)
    (hdiag :
      ∀ x ∈ Klim,
        ∃ (w : ℕ → E) (R : ℕ → ℕ → E)
          (stage : ℕ → ℕ) (err : ℕ → ℝ),
          StronglyConverges w x ∧
          Tendsto stage atTop atTop ∧
          (∀ n, R (stage n) n ∈ K n) ∧
          (∀ n, ‖R (stage n) n - w (stage n)‖ ≤ err n) ∧
          Tendsto err atTop (nhds 0))
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim)
    (x : E) (hx : x ∈ Klim)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ K n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges K Klim ∧ StronglyConverges u x := by
  have hM : MoscoConverges K Klim :=
    mosco_of_diagonalRecovery_of_subset_closedConvex
      K Klim hdiag hsubset hconv hclosed
  refine ⟨hM, ?_⟩
  exact mosco_recovery_closeness_implies_strong_convergence
    hM x hx u solutionErr hsolution hsolutionErr

end DiagonalRecovery

end BernsteinObstacle
