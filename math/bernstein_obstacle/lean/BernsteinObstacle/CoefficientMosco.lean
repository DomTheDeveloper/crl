import BernsteinObstacle.CoefficientCone
import BernsteinObstacle.MoscoTools
import Mathlib.Analysis.Normed.Module.Pi
import Mathlib.Topology.Order.OrderClosed

open Filter

namespace BernsteinObstacle

/-!
# Mosco convergence of the finite coefficient cone

This file gives the first concrete Mosco instance in the project.  Weak
convergence of a finite coefficient vector implies convergence of every
coordinate, so coordinatewise nonnegativity is preserved in the limit.  The
constant family of nonnegative orthants therefore Mosco-converges to itself.

This is a finite-dimensional analytical bridge.  It is not the still-missing
Sobolev finite-element recovery theorem for moving Bernstein mesh cones.
-/

section CoefficientMosco

variable {ι : Type*} [Fintype ι]

/-- The finite nonnegative coefficient cone is weakly sequentially closed. -/
theorem coefficientCone_weaklySequentiallyClosed :
    WeaklySequentiallyClosed (coefficientCone ι) := by
  intro u x hu hweak
  intro i
  have hcoord : Tendsto (fun n => u n i) atTop (nhds (x i)) := by
    simpa using hweak (ContinuousLinearMap.proj (R := ℝ) i)
  exact ge_of_tendsto' hcoord (fun n => hu n i)

/-- The constant family of finite nonnegative coefficient cones
Mosco-converges to the same cone. -/
theorem coefficientCone_mosco_const :
    MoscoConverges (fun _ => coefficientCone ι) (coefficientCone ι) := by
  exact mosco_const_of_weaklyClosed
    (coefficientCone ι) coefficientCone_weaklySequentiallyClosed

/-- The identity sequence is a strong feasible recovery sequence for every
point in the finite coefficient cone. -/
theorem coefficientCone_identity_recovery
    (c : ι → ℝ) (hc : c ∈ coefficientCone ι) :
    (∀ n, c ∈ coefficientCone ι) ∧
      StronglyConverges (fun _ : ℕ => c) c := by
  constructor
  · intro n
    exact hc
  · exact tendsto_const_nhds

end CoefficientMosco

end BernsteinObstacle
