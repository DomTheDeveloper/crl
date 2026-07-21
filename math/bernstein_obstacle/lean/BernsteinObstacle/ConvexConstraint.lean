import BernsteinObstacle.SimplexPartition
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Convex-target Bernstein certificates

The scalar obstacle certificate is one instance of a more general convex-hull
principle. A complete Bernstein field is a convex combination of its
coefficients at every physical point. Consequently, if all coefficients belong
to a convex target set, then the complete vector-valued field belongs to that
set pointwise.
-/

section ConvexConstraint

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A vector-valued complete simplicial Bernstein field. -/
def simplexVectorFieldNat (d n : ℕ)
    (c : (Fin (d + 1) → ℕ) → E)
    (x : BarycentricPoint d) : E :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
    simplexBasisNat d n α x • c α

/-- The finite coefficient constraint associated with a target set. -/
def convexCoefficientSet (C : Set E) (d n : ℕ) :
    Set ((Fin (d + 1) → ℕ) → E) :=
  {c | ∀ α ∈ Finset.piAntidiag
      (Finset.univ : Finset (Fin (d + 1))) n, c α ∈ C}

/-- The corresponding pointwise target constraint for complete fields. -/
def pointwiseConvexConstraint (C : Set E) (d : ℕ) :
    Set (BarycentricPoint d → E) :=
  {v | ∀ x, v x ∈ C}

/-- Coefficients in a convex set certify pointwise membership of the complete
vector-valued Bernstein field in that same set. -/
theorem simplexVectorFieldNat_mem_convex
    (C : Set E) (hC : Convex ℝ C)
    (d n : ℕ) (c : (Fin (d + 1) → ℕ) → E)
    (hc : c ∈ convexCoefficientSet C d n)
    (x : BarycentricPoint d) :
    simplexVectorFieldNat d n c x ∈ C := by
  unfold simplexVectorFieldNat
  exact hC.sum_mem
    (fun α hα => simplexBasisNat_nonneg d n α x)
    (simplexBasisNat_sum_eq_one d n x)
    (fun α hα => hc α hα)

/-- The coefficient certificate gives an exact inner inclusion into the
pointwise convex constraint. -/
theorem simplexVectorFieldNat_pointwise_feasible
    (C : Set E) (hC : Convex ℝ C)
    (d n : ℕ) (c : (Fin (d + 1) → ℕ) → E)
    (hc : c ∈ convexCoefficientSet C d n) :
    simplexVectorFieldNat d n c ∈ pointwiseConvexConstraint C d := by
  intro x
  exact simplexVectorFieldNat_mem_convex C hC d n c hc x

/-- The finite coefficient-feasible set is itself convex whenever the target
set is convex. -/
theorem convex_convexCoefficientSet
    (C : Set E) (hC : Convex ℝ C) (d n : ℕ) :
    Convex ℝ (convexCoefficientSet C d n) := by
  intro c hc z hz a b ha hb hab
  intro α hα
  change a • c α + b • z α ∈ C
  exact hC (hc α hα) (hz α hα) ha hb hab

/-- Any coefficientwise repair map landing in the target set gives an exactly
feasible complete Bernstein field. The map can later be instantiated by metric
projection onto a nonempty closed convex set. -/
theorem repaired_simplexVectorFieldNat_mem_convex
    (C : Set E) (hC : Convex ℝ C)
    (P : E → E) (hP : ∀ y, P y ∈ C)
    (d n : ℕ) (c : (Fin (d + 1) → ℕ) → E)
    (x : BarycentricPoint d) :
    simplexVectorFieldNat d n (fun α => P (c α)) x ∈ C := by
  apply simplexVectorFieldNat_mem_convex C hC d n
  intro α hα
  exact hP (c α)

/-- Coefficientwise repair gives a pointwise feasible complete field. -/
theorem repaired_simplexVectorFieldNat_pointwise_feasible
    (C : Set E) (hC : Convex ℝ C)
    (P : E → E) (hP : ∀ y, P y ∈ C)
    (d n : ℕ) (c : (Fin (d + 1) → ℕ) → E) :
    simplexVectorFieldNat d n (fun α => P (c α)) ∈
      pointwiseConvexConstraint C d := by
  intro x
  exact repaired_simplexVectorFieldNat_mem_convex C hC P hP d n c x

end ConvexConstraint

end

end BernsteinObstacle
