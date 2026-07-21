import BernsteinObstacle.SimplexIndexBridge
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Affine reproduction of the manuscript sampling recovery

The natural-antidiagonal affine theorem is transported through the exact index
bridge to the `MultiIndex`-based `simplexSamplingRecovery` used by the FEM
formalization.
-/

/-- Transport `MultiIndex` coefficients to natural-valued simplex indices,
using zero outside the degree antidiagonal. -/
def naturalizeSimplexCoefficients (d n : ℕ)
    (c : MultiIndex d n → ℝ) (α : Fin (d + 1) → ℕ) : ℝ :=
  if hα : α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n then
    c (natSimplexIndexToMultiIndex d n ⟨α, hα⟩)
  else 0

@[simp]
theorem naturalizeSimplexCoefficients_on_index
    (d n : ℕ) (c : MultiIndex d n → ℝ) (α : NatSimplexIndex d n) :
    naturalizeSimplexCoefficients d n c α.1 =
      c (natSimplexIndexToMultiIndex d n α) := by
  simp [naturalizeSimplexCoefficients, α.2]

/-- Reindexing by `multiIndexNatEquiv` identifies the complete bounded-index
field with the complete natural-antidiagonal field. -/
theorem simplexField_eq_simplexFieldNat_naturalize
    (d n : ℕ) (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    simplexField d n c x =
      simplexFieldNat d n (naturalizeSimplexCoefficients d n c) x := by
  unfold simplexField simplexFieldNat
  calc
    (∑ α : MultiIndex d n, c α * simplexBasis d n α x) =
      ∑ β : NatSimplexIndex d n,
        c ((multiIndexNatEquiv d n).symm β) *
          simplexBasisNat d n β.1 x := by
        exact Fintype.sum_equiv (multiIndexNatEquiv d n)
          (fun α => c α * simplexBasis d n α x)
          (fun β => c ((multiIndexNatEquiv d n).symm β) *
            simplexBasisNat d n β.1 x)
          (fun α => by
            simp [simplexBasis_eq_simplexBasisNat])
    _ = ∑ β : NatSimplexIndex d n,
        naturalizeSimplexCoefficients d n c β.1 *
          simplexBasisNat d n β.1 x := by
        apply Fintype.sum_congr
        intro β
        rw [naturalizeSimplexCoefficients_on_index]
        rfl
    _ = ∑ α ∈ Finset.piAntidiag
          (Finset.univ : Finset (Fin (d + 1))) n,
        naturalizeSimplexCoefficients d n c α *
          simplexBasisNat d n α x := by
        rw [← Finset.attach_eq_univ, Finset.sum_attach]

/-- Naturalized affine samples are the explicit barycentric lattice samples. -/
theorem naturalize_simplexAffineSamplingCoefficients
    (d n : ℕ) (hn : 0 < n) (a : Fin (d + 1) → ℝ)
    (α : Fin (d + 1) → ℕ)
    (hα : α ∈ Finset.piAntidiag
      (Finset.univ : Finset (Fin (d + 1))) n) :
    naturalizeSimplexCoefficients d n
        (simplexSamplingCoefficients d n hn
          (simplexAffineBarycentricValue d a)) α =
      simplexAffineNaturalSamplingCoefficient d n a α := by
  unfold naturalizeSimplexCoefficients simplexSamplingCoefficients
    simplexAffineBarycentricValue simplexAffineNaturalSamplingCoefficient
  simp only [hα, ↓reduceDIte]
  apply Finset.sum_congr rfl
  intro i hi
  simp [simplexLatticePoint, natSimplexIndexToMultiIndex]

/-- The positive simplex sampling recovery used by the FEM construction exactly
reproduces every affine barycentric function. -/
theorem simplexSamplingRecovery_affine_reproduction
    (d n : ℕ) (hn : 0 < n)
    (a : Fin (d + 1) → ℝ) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn (simplexAffineBarycentricValue d a) x =
      simplexAffineBarycentricValue d a x := by
  unfold simplexSamplingRecovery
  rw [simplexField_eq_simplexFieldNat_naturalize]
  calc
    simplexFieldNat d n
        (naturalizeSimplexCoefficients d n
          (simplexSamplingCoefficients d n hn
            (simplexAffineBarycentricValue d a))) x =
      simplexFieldNat d n
        (simplexAffineNaturalSamplingCoefficient d n a) x := by
        unfold simplexFieldNat
        apply Finset.sum_congr rfl
        intro α hα
        rw [naturalize_simplexAffineSamplingCoefficients d n hn a α hα]
    _ = simplexAffineBarycentricValue d a x :=
      simplexFieldNat_affine_reproduction d n hn a x

end

end BernsteinObstacle
