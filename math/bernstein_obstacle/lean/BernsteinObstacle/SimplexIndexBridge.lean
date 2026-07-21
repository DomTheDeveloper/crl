import BernsteinObstacle.SimplexAffineField
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Equivalence of bounded simplex multi-indices and natural antidiagonals

The manuscript-facing `MultiIndex d n` uses `Fin (n+1)` coordinates, while the
multinomial theorem uses natural-valued functions in `Finset.piAntidiag`.  This
file proves these are exactly equivalent and identifies their Bernstein basis
formulas.
-/

/-- Natural-valued degree-`n` simplex multi-indices. -/
abbrev NatSimplexIndex (d n : ℕ) :=
  {α : Fin (d + 1) → ℕ //
    α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n}

/-- Forget the automatic coordinate bound in a `MultiIndex`. -/
def multiIndexToNatSimplexIndex (d n : ℕ)
    (α : MultiIndex d n) : NatSimplexIndex d n := by
  refine ⟨fun i => (α.1 i : ℕ), ?_⟩
  rw [Finset.mem_piAntidiag]
  constructor
  · simpa using α.2
  · simp

/-- A natural antidiagonal index automatically has every coordinate at most
`n`, so it determines a `MultiIndex`. -/
def natSimplexIndexToMultiIndex (d n : ℕ)
    (α : NatSimplexIndex d n) : MultiIndex d n := by
  have hsum : (∑ i : Fin (d + 1), α.1 i) = n := by
    have h := (Finset.mem_piAntidiag.mp α.2).1
    simpa using h
  refine ⟨fun i => ⟨α.1 i, ?_⟩, ?_⟩
  · have hi : α.1 i ≤ n := by
      calc
        α.1 i ≤ ∑ j : Fin (d + 1), α.1 j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (α.1 j))
            (Finset.mem_univ i)
        _ = n := hsum
    omega
  · simpa using hsum

@[simp]
theorem natSimplexIndexToMultiIndex_multiIndexToNatSimplexIndex
    (d n : ℕ) (α : MultiIndex d n) :
    natSimplexIndexToMultiIndex d n (multiIndexToNatSimplexIndex d n α) = α := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

@[simp]
theorem multiIndexToNatSimplexIndex_natSimplexIndexToMultiIndex
    (d n : ℕ) (α : NatSimplexIndex d n) :
    multiIndexToNatSimplexIndex d n (natSimplexIndexToMultiIndex d n α) = α := by
  apply Subtype.ext
  funext i
  rfl

/-- Exact equivalence between the two complete simplex index types. -/
def multiIndexNatEquiv (d n : ℕ) : MultiIndex d n ≃ NatSimplexIndex d n where
  toFun := multiIndexToNatSimplexIndex d n
  invFun := natSimplexIndexToMultiIndex d n
  left_inv := natSimplexIndexToMultiIndex_multiIndexToNatSimplexIndex d n
  right_inv := multiIndexToNatSimplexIndex_natSimplexIndexToMultiIndex d n

@[simp]
theorem multiIndexNatEquiv_apply (d n : ℕ) (α : MultiIndex d n)
    (i : Fin (d + 1)) :
    (multiIndexNatEquiv d n α).1 i = (α.1 i : ℕ) := by
  rfl

/-- The factorial-ratio coefficient in `simplexBasis` is exactly the natural
multinomial coefficient. -/
theorem simplexFactorialRatio_eq_multinomial
    (d n : ℕ) (α : MultiIndex d n) :
    ((Nat.factorial n : ℝ) /
        ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ)) =
      (Nat.multinomial Finset.univ
        (fun i : Fin (d + 1) => (α.1 i : ℕ)) : ℝ) := by
  let f : Fin (d + 1) → ℕ := fun i => (α.1 i : ℕ)
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), f i) = n := by
    simpa [f] using α.2
  have hspecN := Nat.multinomial_spec
    (Finset.univ : Finset (Fin (d + 1))) f
  rw [hsum] at hspecN
  have hspecR :
      (∏ i : Fin (d + 1), (Nat.factorial (f i) : ℝ)) *
          (Nat.multinomial Finset.univ f : ℝ) =
        (Nat.factorial n : ℝ) := by
    exact_mod_cast hspecN
  have hprod :
      (∏ i : Fin (d + 1), (Nat.factorial (f i) : ℝ)) ≠ 0 := by
    positivity
  apply (div_eq_iff hprod).2
  simpa [f, mul_comm] using hspecR.symm

/-- The bounded-index and natural-index simplex Bernstein basis definitions are
pointwise identical. -/
theorem simplexBasis_eq_simplexBasisNat
    (d n : ℕ) (α : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis d n α x =
      simplexBasisNat d n (multiIndexToNatSimplexIndex d n α).1 x := by
  unfold simplexBasis simplexBasisNat
  rw [simplexFactorialRatio_eq_multinomial]
  rfl

end

end BernsteinObstacle
