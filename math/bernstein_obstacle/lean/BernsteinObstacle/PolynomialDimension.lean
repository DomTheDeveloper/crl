import BernsteinObstacle.AffineLattice
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Dimension of the simplex polynomial space

The canonical monomial basis of `MvPolynomial.restrictTotalDegree (Fin d) ℝ n`
is indexed by finitely supported exponent vectors having total exponent at most
`n`.  Since `Fin d` is finite, these are exactly the `d` independent
coordinates of a degree-`n` simplex multi-index.
-/

/-- Exponent vectors indexing the monomial basis of the total-degree-`n`
polynomial space in `d` variables. -/
abbrev RestrictedMonomialIndex (d n : ℕ) :=
  {s : Fin d →₀ ℕ // s.sum (fun _ e => e) ≤ n}

/-- Convert independent simplex lattice coordinates to a finitely supported
monomial exponent vector. -/
def affineMultiIndexToMonomial (d n : ℕ) (γ : AffineMultiIndex d n) :
    RestrictedMonomialIndex d n := by
  let s : Fin d →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (γ.1 i : ℕ))
  refine ⟨s, ?_⟩
  rw [Finsupp.sum_fintype s (fun _ e => e) (fun _ => rfl)]
  simpa [s] using γ.2

/-- Recover independent simplex lattice coordinates from a bounded monomial
exponent vector. -/
def monomialToAffineMultiIndex (d n : ℕ)
    (s : RestrictedMonomialIndex d n) : AffineMultiIndex d n := by
  have hsum : (∑ i : Fin d, s.1 i) ≤ n := by
    rw [← Finsupp.sum_fintype s.1 (fun _ e => e) (fun _ => rfl)]
    exact s.2
  refine ⟨fun i => ⟨s.1 i, Nat.lt_succ_iff.mpr ?_⟩, ?_⟩
  · exact (Finset.single_le_sum
      (fun j _ => Nat.zero_le (s.1 j)) (Finset.mem_univ i)).trans hsum
  · simpa using hsum

@[simp]
theorem affineMultiIndexToMonomial_monomialToAffineMultiIndex (d n : ℕ)
    (s : RestrictedMonomialIndex d n) :
    affineMultiIndexToMonomial d n (monomialToAffineMultiIndex d n s) = s := by
  apply Subtype.ext
  ext i
  rfl

@[simp]
theorem monomialToAffineMultiIndex_affineMultiIndexToMonomial (d n : ℕ)
    (γ : AffineMultiIndex d n) :
    monomialToAffineMultiIndex d n (affineMultiIndexToMonomial d n γ) = γ := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

/-- Independent simplex lattice coordinates are equivalent to the canonical
bounded monomial index set. -/
def affineMultiIndexMonomialEquiv (d n : ℕ) :
    AffineMultiIndex d n ≃ RestrictedMonomialIndex d n where
  toFun := affineMultiIndexToMonomial d n
  invFun := monomialToAffineMultiIndex d n
  left_inv := monomialToAffineMultiIndex_affineMultiIndexToMonomial d n
  right_inv := affineMultiIndexToMonomial_monomialToAffineMultiIndex d n

/-- Full simplex multi-indices are equivalent to the canonical monomial basis
index of the affine polynomial space. -/
def multiIndexMonomialEquiv (d n : ℕ) :
    MultiIndex d n ≃ RestrictedMonomialIndex d n :=
  (multiIndexAffineEquiv d n).trans (affineMultiIndexMonomialEquiv d n)

noncomputable instance restrictedMonomialIndexFintype (d n : ℕ) :
    Fintype (RestrictedMonomialIndex d n) :=
  Fintype.ofEquiv (MultiIndex d n) (multiIndexMonomialEquiv d n)

/-- The finite dimension of the total-degree polynomial space equals the
cardinality of its canonical bounded monomial index set. -/
theorem finrank_restrictTotalDegree_eq_card_restrictedMonomialIndex
    (d n : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ n) =
      Fintype.card (RestrictedMonomialIndex d n) := by
  let S : Set (Fin d →₀ ℕ) :=
    {s | s.sum (fun _ e => e) ≤ n}
  have hfinrank :
      Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ n) =
        S.ncard := by
    simpa [MvPolynomial.restrictTotalDegree, S] using
      (Module.finrank_eq_nat_card_basis
        (MvPolynomial.basisRestrictSupport ℝ S))
  calc
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ n)
        = S.ncard := hfinrank
    _ = Fintype.card S := (Set.fintypeCard_eq_ncard S).symm
    _ = Fintype.card (RestrictedMonomialIndex d n) := by rfl

/-- Therefore the dimension of `P_n` in `d` affine coordinates is exactly the
number of degree-`n` simplex lattice points. -/
theorem finrank_restrictTotalDegree_eq_card_multiIndex (d n : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ n) =
      Fintype.card (MultiIndex d n) := by
  rw [finrank_restrictTotalDegree_eq_card_restrictedMonomialIndex]
  exact Fintype.card_congr (multiIndexMonomialEquiv d n).symm

end

end BernsteinObstacle
