import BernsteinObstacle.FaceTrace
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Orientation-independent Bernstein face traces

Two neighboring simplices need not enumerate the Bernstein degrees of freedom
of their common face in the same order.  An orientation map is therefore an
equivalence between the two local face-index types.  If corresponding indices
refer to the same global degree of freedom and the face basis weights are
reindexed by that equivalence, the complete traces agree.  The same theorem
holds after global coefficient clipping.
-/

section FaceOrientation

variable {Element Face Dof I J Y : Type*}
variable [Fintype Dof] [Fintype I] [Fintype J]
variable {d n : ℕ}

/-- A finite coefficient trace is invariant under an equivalence of its index
set, provided coefficients and basis weights are transported compatibly. -/
theorem finiteTrace_eq_of_reindex
    (e : I ≃ J)
    (leftDof : I → Dof) (rightDof : J → Dof)
    (leftWeight : I → Y → ℝ) (rightWeight : J → Y → ℝ)
    (hDof : ∀ i, leftDof i = rightDof (e i))
    (hWeight : ∀ i y, leftWeight i y = rightWeight (e i) y)
    (c : Dof → ℝ) (y : Y) :
    (∑ i, c (leftDof i) * leftWeight i y) =
      ∑ j, c (rightDof j) * rightWeight j y := by
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hDof i, hWeight i y]

/-- Complete element-local face traces agree across an orientation equivalence
when corresponding local indices are the same global Bernstein DOF. -/
theorem localFaceTrace_eq_of_orientation
    (A : BernsteinAssembly Element Dof d n)
    (leftEmbed : Element → Face → I → MultiIndex d n)
    (rightEmbed : Element → Face → J → MultiIndex d n)
    (leftWeight : I → Y → ℝ) (rightWeight : J → Y → ℝ)
    (e : I ≃ J)
    (hWeight : ∀ i y, leftWeight i y = rightWeight (e i) y)
    (c : Dof → ℝ)
    (T U : Element) (F : Face) (y : Y)
    (hDofTU : ∀ i,
      A.localDof T (leftEmbed T F i) =
        A.localDof U (rightEmbed U F (e i))) :
    localFaceTrace A leftEmbed leftWeight c T F y =
      localFaceTrace A rightEmbed rightWeight c U F y := by
  unfold localFaceTrace localCoefficients
  exact finiteTrace_eq_of_reindex e
    (fun i => A.localDof T (leftEmbed T F i))
    (fun j => A.localDof U (rightEmbed U F j))
    leftWeight rightWeight hDofTU hWeight c y

/-- Global coefficient clipping preserves orientation-reindexed trace equality. -/
theorem clipped_localFaceTrace_eq_of_orientation
    (A : BernsteinAssembly Element Dof d n)
    (leftEmbed : Element → Face → I → MultiIndex d n)
    (rightEmbed : Element → Face → J → MultiIndex d n)
    (leftWeight : I → Y → ℝ) (rightWeight : J → Y → ℝ)
    (e : I ≃ J)
    (hWeight : ∀ i y, leftWeight i y = rightWeight (e i) y)
    (c : Dof → ℝ)
    (T U : Element) (F : Face) (y : Y)
    (hDofTU : ∀ i,
      A.localDof T (leftEmbed T F i) =
        A.localDof U (rightEmbed U F (e i))) :
    localFaceTrace A leftEmbed leftWeight (clipCoefficients c) T F y =
      localFaceTrace A rightEmbed rightWeight (clipCoefficients c) U F y := by
  unfold localFaceTrace localCoefficients
  exact finiteTrace_eq_of_reindex e
    (fun i => A.localDof T (leftEmbed T F i))
    (fun j => A.localDof U (rightEmbed U F j))
    leftWeight rightWeight hDofTU hWeight (clipCoefficients c) y

end FaceOrientation

end

end BernsteinObstacle
