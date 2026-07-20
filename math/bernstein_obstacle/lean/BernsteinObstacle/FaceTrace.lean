import BernsteinObstacle.AssembledObstacle
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Shared Bernstein face traces

A conforming Bernstein--Bézier assembly identifies every control coefficient on
an interior face with one global face degree of freedom.  This file formalizes
the resulting equality of the complete face traces, for an arbitrary finite
face basis.  Because clipping acts on the global coefficient vector, the same
trace equality holds after clipping.  Designated boundary-face degrees of
freedom also give an identically zero face trace.
-/

section FaceTrace

variable {Element Face Dof FaceIndex Y : Type*}
variable [Fintype Dof] [Fintype FaceIndex]
variable {d n : ℕ}

/-- A polynomial trace represented by globally shared face coefficients. -/
def sharedFaceTrace
    (faceDof : Face → FaceIndex → Dof)
    (faceWeight : FaceIndex → Y → ℝ)
    (c : Dof → ℝ) (F : Face) (y : Y) : ℝ :=
  ∑ β, c (faceDof F β) * faceWeight β y

/-- The face trace computed through one element's local Bernstein coefficient
pullback. -/
def localFaceTrace
    (A : BernsteinAssembly Element Dof d n)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (c : Dof → ℝ) (T : Element) (F : Face) (y : Y) : ℝ :=
  ∑ β,
    localCoefficients A.localDof c T (faceEmbed T F β) * faceWeight β y

/-- Compatibility of the local face embedding with globally shared face DOFs. -/
def FaceDofCompatible
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n) : Prop :=
  ∀ T F β, A.localDof T (faceEmbed T F β) = faceDof F β

/-- A compatible local trace is exactly the trace assembled from global face
coefficients. -/
theorem localFaceTrace_eq_sharedFaceTrace
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (hcompat : FaceDofCompatible A faceDof faceEmbed)
    (c : Dof → ℝ) (T : Element) (F : Face) (y : Y) :
    localFaceTrace A faceEmbed faceWeight c T F y =
      sharedFaceTrace faceDof faceWeight c F y := by
  unfold localFaceTrace sharedFaceTrace localCoefficients
  apply Finset.sum_congr rfl
  intro β hβ
  rw [hcompat T F β]

/-- Two elements using the same compatible global face DOFs have identical
traces on their common face. -/
theorem localFaceTrace_eq_of_commonFace
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (hcompat : FaceDofCompatible A faceDof faceEmbed)
    (c : Dof → ℝ) (T U : Element) (F : Face) (y : Y) :
    localFaceTrace A faceEmbed faceWeight c T F y =
      localFaceTrace A faceEmbed faceWeight c U F y := by
  rw [localFaceTrace_eq_sharedFaceTrace A faceDof faceEmbed faceWeight hcompat c T F y]
  rw [localFaceTrace_eq_sharedFaceTrace A faceDof faceEmbed faceWeight hcompat c U F y]

/-- Global clipping preserves equality of the complete traces on a common face. -/
theorem clipped_localFaceTrace_eq_of_commonFace
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (hcompat : FaceDofCompatible A faceDof faceEmbed)
    (c : Dof → ℝ) (T U : Element) (F : Face) (y : Y) :
    localFaceTrace A faceEmbed faceWeight (clipCoefficients c) T F y =
      localFaceTrace A faceEmbed faceWeight (clipCoefficients c) U F y := by
  exact localFaceTrace_eq_of_commonFace
    A faceDof faceEmbed faceWeight hcompat (clipCoefficients c) T U F y

/-- If every global DOF of a face is designated as a boundary DOF, every
assembled feasible coefficient vector has identically zero trace on that face. -/
theorem sharedBoundaryFaceTrace_eq_zero
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceWeight : FaceIndex → Y → ℝ)
    (c : Dof → ℝ) (hc : c ∈ assemblyFeasibleSet A)
    (F : Face) (hboundary : ∀ β, faceDof F β ∈ A.boundaryDof)
    (y : Y) :
    sharedFaceTrace faceDof faceWeight c F y = 0 := by
  unfold sharedFaceTrace
  apply Finset.sum_eq_zero
  intro β hβ
  rw [hc.2 (faceDof F β) (hboundary β)]
  simp

/-- The corresponding element-local boundary trace is also identically zero. -/
theorem localBoundaryFaceTrace_eq_zero
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (hcompat : FaceDofCompatible A faceDof faceEmbed)
    (c : Dof → ℝ) (hc : c ∈ assemblyFeasibleSet A)
    (T : Element) (F : Face)
    (hboundary : ∀ β, faceDof F β ∈ A.boundaryDof)
    (y : Y) :
    localFaceTrace A faceEmbed faceWeight c T F y = 0 := by
  rw [localFaceTrace_eq_sharedFaceTrace A faceDof faceEmbed faceWeight hcompat c T F y]
  exact sharedBoundaryFaceTrace_eq_zero A faceDof faceWeight c hc F hboundary y

/-- A clipped recovery with initially zero boundary coefficients has zero local
trace on every designated boundary face. -/
theorem clippedRecovery_localBoundaryFaceTrace_eq_zero
    (A : BernsteinAssembly Element Dof d n)
    (faceDof : Face → FaceIndex → Dof)
    (faceEmbed : Element → Face → FaceIndex → MultiIndex d n)
    (faceWeight : FaceIndex → Y → ℝ)
    (hcompat : FaceDofCompatible A faceDof faceEmbed)
    (c : Dof → ℝ)
    (hcBoundary : ∀ i ∈ A.boundaryDof, c i = 0)
    (T : Element) (F : Face)
    (hboundary : ∀ β, faceDof F β ∈ A.boundaryDof)
    (y : Y) :
    localFaceTrace A faceEmbed faceWeight (clipCoefficients c) T F y = 0 := by
  apply localBoundaryFaceTrace_eq_zero
    A faceDof faceEmbed faceWeight hcompat (clipCoefficients c)
  · exact clipCoefficients_mem_assemblyFeasibleSet A c hcBoundary
  · exact hboundary

end FaceTrace

end

end BernsteinObstacle
