import BernsteinObstacle.SimplexPartition
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Cardinal functions on the barycentric lattice

The general simplex-lattice unisolvence proof uses products of normalized
falling factorials.  At a degree-`r` lattice point indexed by `β`, the cardinal
function indexed by `α` is one when `α = β` and zero otherwise, provided the two
multi-indices have the same total degree.  This file formalizes that Kronecker
delta property in arbitrary finite dimension.

The remaining step to a complete polynomial-space unisolvence theorem is to
package these values as multivariate polynomials of total degree at most `r`
and identify the cardinality with the dimension of that polynomial space.
-/

section LatticeCardinal

variable {ι : Type*} [Fintype ι]

/-- One normalized falling-factorial coordinate factor. -/
def latticeFactor (a b : ℕ) : ℝ :=
  (b.descFactorial a : ℝ) / (a.factorial : ℝ)

/-- A normalized falling-factorial factor equals one on the diagonal. -/
@[simp]
theorem latticeFactor_self (a : ℕ) : latticeFactor a a = 1 := by
  unfold latticeFactor
  rw [Nat.descFactorial_self]
  exact div_self (by positivity)

/-- A normalized falling-factorial factor vanishes when the evaluation index is
strictly below the cardinal index. -/
theorem latticeFactor_eq_zero_of_lt {a b : ℕ} (hba : b < a) :
    latticeFactor a b = 0 := by
  unfold latticeFactor
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hba]
  simp

/-- Product cardinal value indexed by two natural multi-indices. -/
def latticeCardinalValue (α β : ι → ℕ) : ℝ :=
  ∏ i, latticeFactor (α i) (β i)

/-- Every lattice cardinal value is one on its own node. -/
@[simp]
theorem latticeCardinalValue_self (α : ι → ℕ) :
    latticeCardinalValue α α = 1 := by
  simp [latticeCardinalValue]

/-- Two distinct natural multi-indices having the same total degree differ in a
coordinate where the second is strictly smaller than the first. -/
theorem exists_coord_lt_of_sum_eq_of_ne
    (α β : ι → ℕ)
    (hsum : (∑ i, α i) = ∑ i, β i)
    (hne : α ≠ β) :
    ∃ i, β i < α i := by
  by_contra hnone
  push_neg at hnone
  have hle : ∀ i, α i ≤ β i := hnone
  have hexists : ∃ i, α i ≠ β i := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨i, hne_i⟩ := hexists
  have hlt_i : α i < β i := lt_of_le_of_ne (hle i) hne_i
  have hsumlt : (∑ j, α j) < ∑ j, β j := by
    exact Finset.sum_lt_sum (fun j _ => hle j)
      ⟨i, Finset.mem_univ i, hlt_i⟩
  exact (ne_of_lt hsumlt) hsum

/-- Distinct same-degree lattice indices have zero cardinal value. -/
theorem latticeCardinalValue_eq_zero_of_ne
    (α β : ι → ℕ)
    (hsum : (∑ i, α i) = ∑ i, β i)
    (hne : α ≠ β) :
    latticeCardinalValue α β = 0 := by
  obtain ⟨i, hi⟩ := exists_coord_lt_of_sum_eq_of_ne α β hsum hne
  unfold latticeCardinalValue
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact latticeFactor_eq_zero_of_lt hi

/-- Full Kronecker-delta evaluation formula for same-degree lattice indices. -/
theorem latticeCardinalValue_eq_ite
    (α β : ι → ℕ)
    (hsum : (∑ i, α i) = ∑ i, β i) :
    latticeCardinalValue α β = if α = β then 1 else 0 := by
  by_cases h : α = β
  · subst β
    simp
  · simp [h, latticeCardinalValue_eq_zero_of_ne α β hsum h]

end LatticeCardinal

end

end BernsteinObstacle
