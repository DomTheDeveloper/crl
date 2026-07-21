import BernsteinObstacle.CutPatchSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Interface-cover lower bounds for the number of cut elements

A codimension-one interface of uniformly positive measure cannot be covered by
only a few mesh elements when each element contains at most `C h^(d-1)` of the
interface. This file turns that geometric cover estimate into the exact lower
cardinality hypothesis used by `CutPatchSaturation`.
-/

/-- If every summand is at most `q`, then their finite sum is at most
`card(S) * q`. -/
theorem sum_le_card_mul_of_le
    {ι : Type*} (S : Finset ι) (mass : ι → ℝ) (q : ℝ)
    (hmass : ∀ i ∈ S, mass i ≤ q) :
    (∑ i ∈ S, mass i) ≤ (S.card : ℝ) * q := by
  calc
    (∑ i ∈ S, mass i) ≤ ∑ _i ∈ S, q := by
      exact Finset.sum_le_sum fun i hi => hmass i hi
    _ = (S.card : ℝ) * q := by simp

/-- A covered interface mass of at least `C * N`, together with the local upper
bound `C * h^(d-1)` per cut element, forces at least
`N / h^(d-1)` cut elements. Applications may absorb differing geometric
constants into `N`. -/
theorem interfaceCover_card_lowerBound
    {ι : Type*} (S : Finset ι) (interfaceMass : ι → ℝ)
    (totalInterface C N h : ℝ) (d : ℕ)
    (hC : 0 < C) (hh : 0 < h)
    (hcovered : C * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocal : ∀ i ∈ S, interfaceMass i ≤ C * h ^ (d - 1)) :
    N / h ^ (d - 1) ≤ (S.card : ℝ) := by
  have hpow : 0 < h ^ (d - 1) := pow_pos hh _
  have hsum :
      (∑ i ∈ S, interfaceMass i) ≤
        (S.card : ℝ) * (C * h ^ (d - 1)) :=
    sum_le_card_mul_of_le S interfaceMass (C * h ^ (d - 1)) hlocal
  have hscaled :
      C * N ≤ C * ((S.card : ℝ) * h ^ (d - 1)) := by
    calc
      C * N ≤ totalInterface := hcovered
      _ ≤ ∑ i ∈ S, interfaceMass i := hcover
      _ ≤ (S.card : ℝ) * (C * h ^ (d - 1)) := hsum
      _ = C * ((S.card : ℝ) * h ^ (d - 1)) := by ring
  have hcount : N ≤ (S.card : ℝ) * h ^ (d - 1) :=
    (mul_le_mul_left hC).mp hscaled
  exact (div_le_iff₀ hpow).2 hcount

/-- Interface coverage supplies the lower-cardinality premise when the global
squared error merely dominates the retained cut-element energy sum. -/
theorem cutPatch_error_ge_threeHalves_of_interfaceCover_of_sum_le_sq
    {ι : Type*} (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (error localC N totalInterface coverC h : ℝ) (d : ℕ)
    (herror : 0 ≤ error)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hLocalC : 0 ≤ localC)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (henergy : ∀ i ∈ S, localC * h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1)) :
    Real.sqrt (localC * N) * (h * Real.sqrt h) ≤ error := by
  have hcard : N / h ^ (d - 1) ≤ (S.card : ℝ) :=
    interfaceCover_card_lowerBound
      S interfaceMass totalInterface coverC N h d
      hCoverC hh hcovered hcover hlocalInterface
  exact cutPatch_error_ge_threeHalves_of_sum_le_sq
    S energy error localC N h d
    herror hd hh hLocalC hN hsumSq henergy hcard

/-- Equality with the retained energy sum remains available as a corollary. -/
theorem cutPatch_error_ge_threeHalves_of_interfaceCover
    {ι : Type*} (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (error localC N totalInterface coverC h : ℝ) (d : ℕ)
    (herror : 0 ≤ error)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hLocalC : 0 ≤ localC)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (herrorSq : error ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S, localC * h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1)) :
    Real.sqrt (localC * N) * (h * Real.sqrt h) ≤ error := by
  exact cutPatch_error_ge_threeHalves_of_interfaceCover_of_sum_le_sq
    S energy interfaceMass error localC N totalInterface coverC h d
    herror hd hh hLocalC hN hCoverC herrorSq.symm.le henergy
    hcovered hcover hlocalInterface

end BernsteinObstacle
