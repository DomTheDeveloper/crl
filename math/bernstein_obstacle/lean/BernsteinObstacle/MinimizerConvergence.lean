import BernsteinObstacle.MoscoTools
import Mathlib.Analysis.Normed.Group.Continuity

open Filter

namespace BernsteinObstacle

/-!
# Recovery-to-minimizer strong convergence

Mosco convergence supplies a strongly convergent feasible recovery sequence.
The variational-inequality/energy argument supplies an estimate showing that
the discrete minimizer approaches that recovery sequence.  This file proves the
abstract topological transfer from those two inputs to strong convergence of the
discrete minimizers.

The file intentionally does not assert the still-unformalized Sobolev/FEM
estimate that produces `hclose`; it isolates the exact remaining obligation.
-/

section MinimizerConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `r n → x` strongly and `u n - r n` has a norm majorant tending to zero,
then `u n → x` strongly. -/
theorem stronglyConverges_of_recovery_closeness
    (u r : ℕ → E) (x : E) (err : ℕ → ℝ)
    (hr : StronglyConverges r x)
    (hclose : ∀ n, ‖u n - r n‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges u x := by
  unfold StronglyConverges at hr ⊢
  have hdiff : Tendsto (fun n => u n - r n) atTop (nhds 0) :=
    squeeze_zero_norm hclose herr
  have hadd := hdiff.add hr
  simpa using hadd

/-- A Mosco recovery sequence plus a vanishing recovery-to-solution error bound
implies strong convergence of the candidate discrete solutions. -/
theorem mosco_recovery_closeness_implies_strong_convergence
    {K : ℕ → Set E} {Klim : Set E}
    (hM : MoscoConverges K Klim)
    (x : E) (hx : x ∈ Klim)
    (u : ℕ → E) (err : ℕ → ℝ)
    (hclose :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ K n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges u x := by
  obtain ⟨r, hrK, hr⟩ := hM.recovery x hx
  exact stronglyConverges_of_recovery_closeness
    u r x err hr (hclose r hrK hr) herr

/-- Operator form of the same transfer theorem.  A chosen recovery operator is
often the convenient interface for finite-element interpolation plus clipping. -/
theorem recoveryOperator_closeness_implies_strong_convergence
    {K : ℕ → Set E} {Klim : Set E}
    (R : ℕ → E → E)
    (hmap : ∀ n x, x ∈ Klim → R n x ∈ K n)
    (hR : ∀ x ∈ Klim, StronglyConverges (fun n => R n x) x)
    (x : E) (hx : x ∈ Klim)
    (u : ℕ → E) (err : ℕ → ℝ)
    (hclose : ∀ n, ‖u n - R n x‖ ≤ err n)
    (herr : Tendsto err atTop (nhds 0)) :
    StronglyConverges u x := by
  exact stronglyConverges_of_recovery_closeness
    u (fun n => R n x) x err (hR x hx) hclose herr

end MinimizerConvergence

end BernsteinObstacle
