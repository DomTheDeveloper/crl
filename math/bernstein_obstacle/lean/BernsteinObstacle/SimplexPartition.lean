import BernsteinObstacle.Simplex
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-- The simplicial Bernstein basis written with a natural-valued multi-index.
Only multi-indices in `Finset.piAntidiag Finset.univ n` are used in the field. -/
def simplexBasisNat (d _n : ℕ) (α : Fin (d + 1) → ℕ)
    (x : BarycentricPoint d) : ℝ :=
  (Nat.multinomial Finset.univ α : ℝ) *
    ∏ i : Fin (d + 1), (x.1 i) ^ α i

/-- Natural-index simplicial Bernstein basis weights are nonnegative. -/
theorem simplexBasisNat_nonneg (d n : ℕ) (α : Fin (d + 1) → ℕ)
    (x : BarycentricPoint d) :
    0 ≤ simplexBasisNat d n α x := by
  unfold simplexBasisNat
  have hmult : 0 ≤ (Nat.multinomial Finset.univ α : ℝ) := by
    positivity
  have hprod : 0 ≤ ∏ i : Fin (d + 1), (x.1 i) ^ α i := by
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (x.2.1 i) _
  exact mul_nonneg hmult hprod

/-- The simplicial Bernstein basis is a partition of unity. -/
theorem simplexBasisNat_sum_eq_one (d n : ℕ) (x : BarycentricPoint d) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      simplexBasisNat d n α x) = 1 := by
  calc
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      simplexBasisNat d n α x) =
        (∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), x.1 i) ^ n := by
          rw [Finset.sum_pow_eq_sum_piAntidiag]
          apply Finset.sum_congr rfl
          intro α hα
          simp [simplexBasisNat]
    _ = 1 := by
      rw [x.2.2, one_pow]

/-- A simplicial Bernstein field indexed by the complete degree-`n` antidiagonal. -/
def simplexFieldNat (d n : ℕ) (c : (Fin (d + 1) → ℕ) → ℝ)
    (x : BarycentricPoint d) : ℝ :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
    c α * simplexBasisNat d n α x

/-- Nonnegative coefficients certify pointwise nonnegativity for the complete
simplicial Bernstein basis. -/
theorem simplexFieldNat_nonneg (d n : ℕ)
    (c : (Fin (d + 1) → ℕ) → ℝ)
    (hc : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      0 ≤ c α)
    (x : BarycentricPoint d) :
    0 ≤ simplexFieldNat d n c x := by
  unfold simplexFieldNat
  exact Finset.sum_nonneg fun α hα =>
    mul_nonneg (hc α hα) (simplexBasisNat_nonneg d n α x)

/-- A common lower coefficient bound is also a pointwise lower bound. -/
theorem simplexFieldNat_lower_bound (d n : ℕ)
    (c : (Fin (d + 1) → ℕ) → ℝ) (m : ℝ)
    (hc : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      m ≤ c α)
    (x : BarycentricPoint d) :
    m ≤ simplexFieldNat d n c x := by
  have hsum :
      (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        m * simplexBasisNat d n α x) ≤
      (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        c α * simplexBasisNat d n α x) := by
    apply Finset.sum_le_sum
    intro α hα
    exact mul_le_mul_of_nonneg_right (hc α hα)
      (simplexBasisNat_nonneg d n α x)
  calc
    m = m * 1 := by ring
    _ = m * (∑ α ∈ Finset.piAntidiag
        (Finset.univ : Finset (Fin (d + 1))) n,
        simplexBasisNat d n α x) := by
      rw [simplexBasisNat_sum_eq_one]
    _ = ∑ α ∈ Finset.piAntidiag
        (Finset.univ : Finset (Fin (d + 1))) n,
        m * simplexBasisNat d n α x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ α ∈ Finset.piAntidiag
        (Finset.univ : Finset (Fin (d + 1))) n,
        c α * simplexBasisNat d n α x := hsum
    _ = simplexFieldNat d n c x := rfl

/-- A common upper coefficient bound is also a pointwise upper bound. -/
theorem simplexFieldNat_upper_bound (d n : ℕ)
    (c : (Fin (d + 1) → ℕ) → ℝ) (M : ℝ)
    (hc : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      c α ≤ M)
    (x : BarycentricPoint d) :
    simplexFieldNat d n c x ≤ M := by
  have hsum :
      (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        c α * simplexBasisNat d n α x) ≤
      (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        M * simplexBasisNat d n α x) := by
    apply Finset.sum_le_sum
    intro α hα
    exact mul_le_mul_of_nonneg_right (hc α hα)
      (simplexBasisNat_nonneg d n α x)
  calc
    simplexFieldNat d n c x =
        ∑ α ∈ Finset.piAntidiag
          (Finset.univ : Finset (Fin (d + 1))) n,
          c α * simplexBasisNat d n α x := rfl
    _ ≤ ∑ α ∈ Finset.piAntidiag
        (Finset.univ : Finset (Fin (d + 1))) n,
        M * simplexBasisNat d n α x := hsum
    _ = M * (∑ α ∈ Finset.piAntidiag
        (Finset.univ : Finset (Fin (d + 1))) n,
        simplexBasisNat d n α x) := by
      rw [Finset.mul_sum]
    _ = M := by rw [simplexBasisNat_sum_eq_one, mul_one]

/-- Full simplicial Bernstein convex-hull/range certificate. -/
theorem simplexFieldNat_mem_Icc (d n : ℕ)
    (c : (Fin (d + 1) → ℕ) → ℝ) (m M : ℝ)
    (hc : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      c α ∈ Set.Icc m M)
    (x : BarycentricPoint d) :
    simplexFieldNat d n c x ∈ Set.Icc m M := by
  constructor
  · exact simplexFieldNat_lower_bound d n c m
      (fun α hα => (hc α hα).1) x
  · exact simplexFieldNat_upper_bound d n c M
      (fun α hα => (hc α hα).2) x

end

end BernsteinObstacle
