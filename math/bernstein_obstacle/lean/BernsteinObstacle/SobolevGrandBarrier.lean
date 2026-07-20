import BernsteinObstacle.GrandBarrier
import BernsteinObstacle.ConvexWeakClosure
import BernsteinObstacle.SobolevFEMRecovery

open Filter
open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Sobolev/FEM instantiation of the Grand Barrier endgame

This file converts the existing moving Sobolev/FEM recovery interface into the
canonical bilateral barrier-envelope interface. The concrete analytical work is
still exactly the work needed to populate `SobolevFEMRecoveryData`.
-/

section SobolevGrandBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The existing moving Sobolev recovery package canonically produces the
barrier-envelope data used by the Grand Barrier theorem. -/
def SobolevFEMRecoveryData.toBarrierEnvelopeData
    (D : SobolevFEMRecoveryData E) :
    BilateralBarrierEnvelopeData (E := E) where
  discreteSet := D.discreteCone
  limitSet := D.limitCone
  inner := D.inner
  weaklyClosed :=
    weaklySequentiallyClosed_of_convex_isClosed
      D.limitCone D.limit_convex D.limit_closed
  recovery := by
    intro x hx
    obtain ⟨w, R, stage, err, hw, hstage, hmem, hclose, herr⟩ :=
      D.diagonalRecovery x hx
    refine ⟨fun n => R (stage n) n, hmem, ?_⟩
    exact diagonalRecovery_stronglyConverges
      w R stage x err hw hstage hclose herr

/-- The Sobolev/FEM package implies the canonical Barrier Envelope Mosco
Theorem. -/
theorem SobolevFEMRecoveryData.barrierEnvelope_moscoConverges
    (D : SobolevFEMRecoveryData E) :
    MoscoConverges D.discreteCone D.limitCone := by
  exact D.toBarrierEnvelopeData.moscoConverges

end SobolevGrandBarrier

section SobolevGrandBarrierHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A fully populated physical recovery package closes both the Mosco and
projection-form Hilbert VI endgames. -/
theorem SobolevFEMRecoveryData.grandBarrier_hilbertConvergence
    (D : SobolevFEMRecoveryData E)
    (z u : E) (udisc : ℕ → E)
    (hu : IsHilbertVISolution D.limitCone z u)
    (hudisc : ∀ n, IsHilbertVISolution (D.discreteCone n) z (udisc n)) :
    MoscoConverges D.discreteCone D.limitCone ∧
      StronglyConverges udisc u := by
  exact D.toBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence
    z u udisc hu hudisc

end SobolevGrandBarrierHilbert

end

end BernsteinObstacle
