import BernsteinObstacle.BarrierEnvelopeMosco
import BernsteinObstacle.MovingHilbertVI
import BernsteinObstacle.UniversalRate
import BernsteinObstacle.GrandRateExponents
import BernsteinObstacle.MonotoneInnerConeAlgebra

open Filter
open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Bernstein–Bézier Grand Barrier Theorem

This file is the canonical formal composition layer. It does not pretend that
the physical `W^{1,p}` recovery construction or free-boundary geometry has
already been internalized. Instead, it states the exact abstract data those
analytical layers must provide and closes the Mosco/Hilbert endgame in Lean.
-/

section GrandBarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Bernstein–Bézier Grand Barrier Theorem (formal Hilbert endgame).**
An exact certified inner family with strong recovery has both Mosco convergence
and strong convergence of its projection-form variational-inequality solutions.
-/
theorem BilateralBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence
    (D : BilateralBarrierEnvelopeData (E := E))
    (z u : E) (udisc : ℕ → E)
    (hu : IsHilbertVISolution D.limitSet z u)
    (hudisc : ∀ n, IsHilbertVISolution (D.discreteSet n) z (udisc n)) :
    MoscoConverges D.discreteSet D.limitSet ∧
      StronglyConverges udisc u := by
  obtain ⟨r, hrmem, hrconv⟩ := D.recovery u hu.1
  constructor
  · exact D.moscoConverges
  · exact nested_hilbert_vi_strongConvergence_of_recovery
      D.discreteSet D.limitSet z u udisc r
      D.inner hu hudisc hrmem hrconv

/-- Extract the strong-convergence conclusion of the Grand Barrier Theorem. -/
theorem BilateralBarrierEnvelopeData.grandBarrier_strongConvergence
    (D : BilateralBarrierEnvelopeData (E := E))
    (z u : E) (udisc : ℕ → E)
    (hu : IsHilbertVISolution D.limitSet z u)
    (hudisc : ∀ n, IsHilbertVISolution (D.discreteSet n) z (udisc n)) :
    StronglyConverges udisc u :=
  (D.grandBarrier_mosco_and_hilbertConvergence z u udisc hu hudisc).2

end GrandBarrier

end

end BernsteinObstacle
