import BernsteinObstacle.AssembledGrandTheorem
import BernsteinObstacle.MovingHilbertVI

open Filter
open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Direct Hilbert-VI transfer for assembled Bernstein cones

The generic assembled theorem previously exposed a comparison-error hypothesis
`hsolution`.  For projection-form obstacle variational inequalities in the
finite global coefficient Hilbert space, that hypothesis is unnecessary:
strong feasible recovery and the Hilbert Pythagorean inequality directly force
strong convergence of the actual discrete VI solutions.
-/

section AssembledHilbertTransfer

variable {Element Dof : Type*} [Fintype Dof] {d p : ℕ}

/-- The assembled free-coefficient recovery package directly implies strong
convergence of the projection-form VI solutions on the actual assembled
Bernstein feasible sets. -/
theorem AssembledFreeCoefficientRecoveryData.hilbertVISolutions_strongConvergence
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (z u : Dof → ℝ) (udisc : ℕ → Dof → ℝ)
    (hu : IsHilbertVISolution D.limitCone z u)
    (hudisc : ∀ n,
      IsHilbertVISolution (assemblyFeasibleSet (D.assembly n)) z (udisc n)) :
    StronglyConverges udisc u := by
  exact
    D.toClearanceData.toAsymptoticData.toThresholdData
      |>.hilbertVISolutions_strongConvergence z u udisc hu hudisc

/-- The same concrete assembled data simultaneously yields Mosco convergence
and direct strong convergence of the actual projection-form VI solutions,
without any separately assumed solution-to-recovery error sequence. -/
theorem AssembledFreeCoefficientRecoveryData.mosco_and_hilbertVISolutions_strongConvergence
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (z u : Dof → ℝ) (udisc : ℕ → Dof → ℝ)
    (hu : IsHilbertVISolution D.limitCone z u)
    (hudisc : ∀ n,
      IsHilbertVISolution (assemblyFeasibleSet (D.assembly n)) z (udisc n)) :
    MoscoConverges
        (fun n => assemblyFeasibleSet (D.assembly n)) D.limitCone ∧
      StronglyConverges udisc u := by
  exact ⟨D.moscoConverges,
    D.hilbertVISolutions_strongConvergence z u udisc hu hudisc⟩

end AssembledHilbertTransfer

end

end BernsteinObstacle
