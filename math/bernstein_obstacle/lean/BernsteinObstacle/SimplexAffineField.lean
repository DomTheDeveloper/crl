import BernsteinObstacle.SimplexAffineReproduction
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Exact reproduction of affine barycentric fields

The normalized first-moment identity implies that the natural-index simplex
Bernstein operator reproduces every affine function exactly.
-/

/-- An affine function written in barycentric coordinates. -/
def simplexAffineBarycentricValue (d : ℕ)
    (a : Fin (d + 1) → ℝ) (x : BarycentricPoint d) : ℝ :=
  ∑ i : Fin (d + 1), a i * x.1 i

/-- Samples of an affine barycentric function on the degree-`n` lattice. -/
def simplexAffineNaturalSamplingCoefficient (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (α : Fin (d + 1) → ℕ) : ℝ :=
  ∑ i : Fin (d + 1), a i * ((α i : ℝ) / (n : ℝ))

/-- The complete natural-index Bernstein field exactly reproduces every affine
barycentric function. -/
theorem simplexFieldNat_affine_reproduction
    (d n : ℕ) (hn : 0 < n)
    (a : Fin (d + 1) → ℝ) (x : BarycentricPoint d) :
    simplexFieldNat d n (simplexAffineNaturalSamplingCoefficient d n a) x =
      simplexAffineBarycentricValue d a x := by
  unfold simplexFieldNat simplexAffineNaturalSamplingCoefficient
    simplexAffineBarycentricValue
  calc
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      (∑ i : Fin (d + 1), a i * ((α i : ℝ) / (n : ℝ))) *
        simplexBasisNat d n α x) =
      ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        ∑ i : Fin (d + 1),
          a i * (((α i : ℝ) / (n : ℝ)) * simplexBasisNat d n α x) := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = ∑ i : Fin (d + 1),
        ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
          a i * (((α i : ℝ) / (n : ℝ)) * simplexBasisNat d n α x) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin (d + 1), a i *
        (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
          ((α i : ℝ) / (n : ℝ)) * simplexBasisNat d n α x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (d + 1), a i * x.1 i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [simplexBasisNat_firstMoment d n hn i x]

end

end BernsteinObstacle