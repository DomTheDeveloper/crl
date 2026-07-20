import BernsteinObstacle.AssembledObstacle
import BernsteinObstacle.SimplexOrientedFace
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Concrete oriented Bernstein face conformity

The generic face-trace interface is instantiated with the actual
lower-dimensional simplicial Bernstein basis and the concrete oriented face
multi-index embeddings.  Equality of the corresponding shared global degrees
of freedom therefore gives equality of the complete face polynomials.
-/

section ConcreteFaceConformity

variable {Element Dof : Type*} [Fintype Dof]
variable {d n : ℕ}

/-- The complete trace of one element on an oriented codimension-one simplex
face, expressed in the genuine lower-dimensional Bernstein basis. -/
def orientedSimplexFaceTrace
    (A : BernsteinAssembly Element Dof (d + 1) n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : Dof → ℝ) (T : Element) (x : BarycentricPoint d) : ℝ :=
  ∑ β : MultiIndex d n,
    localCoefficients A.localDof c T
      (orientedLastFaceMultiIndex d n e β) *
      simplexBasis d n β x

/-- Two neighboring elements have identical complete face polynomials whenever
their oriented face indices refer to the same shared global DOFs. -/
theorem orientedSimplexFaceTrace_eq_of_sharedDofs
    (A : BernsteinAssembly Element Dof (d + 1) n)
    (eT eU : Fin (d + 2) ≃ Fin (d + 2))
    (c : Dof → ℝ) (T U : Element)
    (hshared : ∀ β : MultiIndex d n,
      A.localDof T (orientedLastFaceMultiIndex d n eT β) =
        A.localDof U (orientedLastFaceMultiIndex d n eU β))
    (x : BarycentricPoint d) :
    orientedSimplexFaceTrace A eT c T x =
      orientedSimplexFaceTrace A eU c U x := by
  unfold orientedSimplexFaceTrace localCoefficients
  apply Finset.sum_congr rfl
  intro β hβ
  rw [hshared β]

/-- Global coefficient clipping preserves the concrete oriented common-face
polynomial identity. -/
theorem clipped_orientedSimplexFaceTrace_eq_of_sharedDofs
    (A : BernsteinAssembly Element Dof (d + 1) n)
    (eT eU : Fin (d + 2) ≃ Fin (d + 2))
    (c : Dof → ℝ) (T U : Element)
    (hshared : ∀ β : MultiIndex d n,
      A.localDof T (orientedLastFaceMultiIndex d n eT β) =
        A.localDof U (orientedLastFaceMultiIndex d n eU β))
    (x : BarycentricPoint d) :
    orientedSimplexFaceTrace A eT (clipCoefficients c) T x =
      orientedSimplexFaceTrace A eU (clipCoefficients c) U x := by
  exact orientedSimplexFaceTrace_eq_of_sharedDofs
    A eT eU (clipCoefficients c) T U hshared x

/-- If every oriented face DOF is designated as a homogeneous boundary DOF,
the complete concrete face trace of every feasible field vanishes. -/
theorem orientedSimplexBoundaryFaceTrace_eq_zero
    (A : BernsteinAssembly Element Dof (d + 1) n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : Dof → ℝ) (hc : c ∈ assemblyFeasibleSet A)
    (T : Element)
    (hboundary : ∀ β : MultiIndex d n,
      A.localDof T (orientedLastFaceMultiIndex d n e β) ∈ A.boundaryDof)
    (x : BarycentricPoint d) :
    orientedSimplexFaceTrace A e c T x = 0 := by
  unfold orientedSimplexFaceTrace localCoefficients
  apply Finset.sum_eq_zero
  intro β hβ
  rw [hc.2 _ (hboundary β)]
  simp

/-- A raw coefficient vector with zero boundary DOFs retains an identically
zero concrete boundary-face polynomial after global clipping. -/
theorem clipped_orientedSimplexBoundaryFaceTrace_eq_zero
    (A : BernsteinAssembly Element Dof (d + 1) n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : Dof → ℝ)
    (hcBoundary : ∀ i ∈ A.boundaryDof, c i = 0)
    (T : Element)
    (hboundary : ∀ β : MultiIndex d n,
      A.localDof T (orientedLastFaceMultiIndex d n e β) ∈ A.boundaryDof)
    (x : BarycentricPoint d) :
    orientedSimplexFaceTrace A e (clipCoefficients c) T x = 0 := by
  apply orientedSimplexBoundaryFaceTrace_eq_zero
    A e (clipCoefficients c)
  · exact clipCoefficients_mem_assemblyFeasibleSet A c hcBoundary
  · exact hboundary

end ConcreteFaceConformity

end

end BernsteinObstacle
