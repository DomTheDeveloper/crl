import BernsteinObstacle.ConvexWeakClosure
import BernsteinObstacle.MinimizerConvergence

open Filter

namespace BernsteinObstacle

/-!
# Moving closed-convex cones: Mosco and strong minimizer convergence

This file packages the exact B5--B6 endgame of the manuscript.  Once a moving
inner approximation has a positive recovery operator converging strongly to
the identity, norm-closed convexity of the limit set supplies the weak-limit
condition automatically.  A vanishing recovery-to-solution estimate then
gives strong convergence of the discrete minimizers.
-/

section MovingConeConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed-convex moving inner approximations with a convergent recovery
operator Mosco-converge, and any candidate sequence approaching that recovery
strongly converges to the target. -/
theorem movingClosedConvexRecovery_strongConvergence
    (K : ℕ → Set E) (Klim : Set E)
    (R : ℕ → E → E)
    (hmap : ∀ n x, x ∈ Klim → R n x ∈ K n)
    (hR : ∀ x ∈ Klim, StronglyConverges (fun n => R n x) x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim)
    (x : E) (hx : x ∈ Klim)
    (u : ℕ → E) (err : ℕ → ℝ)
    (hclose : ∀ n, ‖u n - R n x‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    MoscoConverges K Klim ∧ StronglyConverges u x := by
  have hM : MoscoConverges K Klim :=
    mosco_of_recovery_operators_of_subset_of_closedConvex
      K Klim R hmap hR hsubset hconv hclosed
  refine ⟨hM, ?_⟩
  exact recoveryOperator_closeness_implies_strong_convergence
    R hmap hR x hx u err hclose herr

/-- Sequence form: if every point of the closed convex limit set has a strong
feasible recovery sequence, then Mosco convergence and the standard
recovery-closeness minimizer conclusion hold. -/
theorem movingClosedConvexRecoverySequence_strongConvergence
    (K : ℕ → Set E) (Klim : Set E)
    (hrecovery :
      ∀ x ∈ Klim, ∃ r : ℕ → E,
        (∀ n, r n ∈ K n) ∧ StronglyConverges r x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim)
    (x : E) (hx : x ∈ Klim)
    (u : ℕ → E) (err : ℕ → ℝ)
    (hclose :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ K n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    MoscoConverges K Klim ∧ StronglyConverges u x := by
  have hM : MoscoConverges K Klim :=
    mosco_of_recovery_of_subset_of_closedConvex
      K Klim hrecovery hsubset hconv hclosed
  refine ⟨hM, ?_⟩
  exact mosco_recovery_closeness_implies_strong_convergence
    hM x hx u err hclose herr

end MovingConeConvergence

end BernsteinObstacle
