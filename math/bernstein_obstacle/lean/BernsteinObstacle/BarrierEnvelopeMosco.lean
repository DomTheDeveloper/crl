import BernsteinObstacle.Mosco

open Filter

namespace BernsteinObstacle

/-!
# Bernstein–Bézier barrier-envelope Mosco principle

This file isolates the exact abstract logic needed by the bilateral variable-
obstacle theorem. The analytical work constructs an inner family of computable
Bernstein coefficient sets and a strong recovery sequence. Once those two facts
and weak sequential closedness of the continuous order interval are supplied,
Mosco convergence is a formal consequence.
-/

section BarrierEnvelopeMosco

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Formal data for a computable family of certified inner approximations to a
closed bilateral barrier set. -/
structure BilateralBarrierEnvelopeData where
  discreteSet : ℕ → Set E
  limitSet : Set E
  inner : ∀ n, discreteSet n ⊆ limitSet
  weaklyClosed : WeaklySequentiallyClosed limitSet
  recovery :
    ∀ x ∈ limitSet, ∃ u : ℕ → E,
      (∀ n, u n ∈ discreteSet n) ∧ StronglyConverges u x

/-- **Bernstein–Bézier Barrier Envelope Theorem (abstract form).**
A family of exact certified inner sets Mosco-converges once every continuous
feasible point has a strong discrete recovery sequence. -/
theorem BilateralBarrierEnvelopeData.moscoConverges
    (D : BilateralBarrierEnvelopeData (E := E)) :
    MoscoConverges D.discreteSet D.limitSet := by
  constructor
  · exact D.recovery
  · intro φ hφ u x hu hweak
    apply D.weaklyClosed u x
    · intro n
      exact D.inner (φ n) (hu n)
    · exact hweak

/-- The barrier-envelope theorem simultaneously records exact inner feasibility
and Mosco convergence. -/
theorem BilateralBarrierEnvelopeData.inner_and_mosco
    (D : BilateralBarrierEnvelopeData (E := E)) :
    (∀ n, D.discreteSet n ⊆ D.limitSet) ∧
      MoscoConverges D.discreteSet D.limitSet :=
  ⟨D.inner, D.moscoConverges⟩

end BarrierEnvelopeMosco

end BernsteinObstacle
