import BernsteinObstacle.Mosco

namespace BernsteinObstacle

/-!
# Reusable Mosco-convergence proof reductions

For an inner approximation `K n ⊆ Klim`, the weak-limit half of Mosco
convergence follows immediately from weak sequential closedness of `Klim`.
Consequently, the only construction-specific obligation is a strong recovery
sequence.  This is exactly the logical decomposition used by the Bernstein
finite-element proof.
-/

section MoscoTools

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inner approximations of a weakly sequentially closed set Mosco-converge as
soon as every point in the limit set has a strong feasible recovery sequence. -/
theorem mosco_of_recovery_of_subset_of_weaklyClosed
    (K : ℕ → Set E) (Klim : Set E)
    (hrecovery :
      ∀ x ∈ Klim, ∃ u : ℕ → E,
        (∀ n, u n ∈ K n) ∧ StronglyConverges u x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hclosed : WeaklySequentiallyClosed Klim) :
    MoscoConverges K Klim := by
  constructor
  · exact hrecovery
  · intro φ hφ u x hu hweak
    apply hclosed u x
    · intro n
      exact hsubset (φ n) (hu n)
    · exact hweak

/-- A family of explicit recovery operators proves Mosco convergence when each
operator maps the limit set into the inner discrete set and converges strongly
to the identity. -/
theorem mosco_of_recovery_operators_of_subset_of_weaklyClosed
    (K : ℕ → Set E) (Klim : Set E)
    (R : ℕ → E → E)
    (hmap : ∀ n x, x ∈ Klim → R n x ∈ K n)
    (hconverges : ∀ x ∈ Klim, StronglyConverges (fun n => R n x) x)
    (hsubset : ∀ n, K n ⊆ Klim)
    (hclosed : WeaklySequentiallyClosed Klim) :
    MoscoConverges K Klim := by
  apply mosco_of_recovery_of_subset_of_weaklyClosed K Klim
  · intro x hx
    exact ⟨fun n => R n x, fun n => hmap n x hx, hconverges x hx⟩
  · exact hsubset
  · exact hclosed

/-- The constant-family case, stated through the recovery-operator interface. -/
theorem mosco_const_of_weaklyClosed
    (K : Set E) (hclosed : WeaklySequentiallyClosed K) :
    MoscoConverges (fun _ => K) K := by
  exact mosco_of_recovery_operators_of_subset_of_weaklyClosed
    (fun _ => K) K (fun _ x => x)
    (fun _ _ hx => hx)
    (fun _ _ => tendsto_const_nhds)
    (fun _ => Set.Subset.rfl)
    hclosed

end MoscoTools

end BernsteinObstacle
