import BernsteinObstacle.MoscoTools
import Mathlib.Analysis.LocallyConvex.Separation

open Filter

namespace BernsteinObstacle

/-!
# Norm-closed convex sets are weakly sequentially closed

The weak-limit half of the moving Bernstein-cone Mosco proof does not need to
remain an external hypothesis.  A point outside a norm-closed convex set is
strictly separated from it by a continuous linear functional.  Weak
convergence against that functional then contradicts feasibility of the
sequence.
-/

section ConvexWeakClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every norm-closed convex set in a real normed space is weakly sequentially
closed for the project's continuous-dual definition of weak convergence. -/
theorem weaklySequentiallyClosed_of_convex_isClosed
    (K : Set E) (hconv : Convex ℝ K) (hclosed : IsClosed K) :
    WeaklySequentiallyClosed K := by
  intro u x hu hweak
  by_contra hx
  obtain ⟨φ, a, hK, hxa⟩ :=
    geometric_hahn_banach_closed_point hconv hclosed hx
  have hIoi : Set.Ioi a ∈ nhds (φ x) :=
    isOpen_Ioi.mem_nhds hxa
  have hevent : ∀ᶠ n in atTop, a < φ (u n) :=
    (hweak φ) hIoi
  have hfalse : ∀ᶠ _n in atTop, False :=
    hevent.mono fun n hn =>
      (not_lt_of_ge (le_of_lt (hK (u n) (hu n)))) hn
  exact eventually_const.mp hfalse

/-- Inner approximations of a norm-closed convex set Mosco-converge once a
strong feasible recovery sequence is available. -/
theorem mosco_of_recovery_of_subset_of_closedConvex
    (K : ℕ → Set E) (Klim : Set E)
    (hrecovery :
      ∀ x ∈ Klim, ∃ u : ℕ → E,
        (∀ n, u n ∈ K n) ∧ StronglyConverges u x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim) :
    MoscoConverges K Klim := by
  exact mosco_of_recovery_of_subset_of_weaklyClosed K Klim
    hrecovery hsubset
    (weaklySequentiallyClosed_of_convex_isClosed Klim hconv hclosed)

/-- Recovery-operator form of the closed-convex Mosco theorem. -/
theorem mosco_of_recovery_operators_of_subset_of_closedConvex
    (K : ℕ → Set E) (Klim : Set E)
    (R : ℕ → E → E)
    (hmap : ∀ n x, x ∈ Klim → R n x ∈ K n)
    (hconverges : ∀ x ∈ Klim, StronglyConverges (fun n => R n x) x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hconv : Convex ℝ Klim) (hclosed : IsClosed Klim) :
    MoscoConverges K Klim := by
  exact mosco_of_recovery_operators_of_subset_of_weaklyClosed
    K Klim R hmap hconverges hsubset
    (weaklySequentiallyClosed_of_convex_isClosed Klim hconv hclosed)

end ConvexWeakClosure

end BernsteinObstacle
