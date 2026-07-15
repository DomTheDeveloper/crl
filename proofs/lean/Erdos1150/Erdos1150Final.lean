import Erdos1150
import Mathlib.Topology.Algebra.Polynomial

open Complex Finset MeasureTheory
open scoped BigOperators ComplexConjugate Polynomial ZMod

namespace Erdos1150Proof

/-- The exact textbook Parseval lower bound appearing in Formal Conjectures. -/
theorem parseval_lower_bound (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  let Φ : ZMod (n + 1) → ℂ := fun j => P.coeff j.val
  have hunit : ∀ j, ‖Φ j‖ = 1 := by
    intro j
    have hj : j.val ≤ P.natDegree := by
      rw [hdeg]
      exact Nat.le_of_lt_succ j.val_lt
    rcases hcoeff j.val hj with hjc | hjc
    · simp [Φ, hjc]
    · simp [Φ, hjc]
  obtain ⟨k, hk⟩ := exists_sqrt_le_norm_dft Φ hunit
  rw [dft_coeff_eq_eval P n hdeg k] at hk
  let w : ℂ := (ZMod.stdAddChar (-k) : ℂ)
  have hw : w ∈ Metric.sphere (0 : ℂ) 1 := by
    simp [w, Metric.mem_sphere]
  let z : Metric.sphere (0 : ℂ) 1 := ⟨w, hw⟩
  letI : CompactSpace (Metric.sphere (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_sphere
  have hcontinuous : Continuous (fun u : Metric.sphere (0 : ℂ) 1 => ‖P.eval (u : ℂ)‖) :=
    (P.continuous.comp continuous_subtype_val).norm
  have hbounded : BddAbove
      (Set.range (fun u : Metric.sphere (0 : ℂ) 1 => ‖P.eval (u : ℂ)‖)) :=
    (isCompact_range hcontinuous).bddAbove
  exact le_ciSup_of_le hbounded z (by simpa [z, w] using hk)

#print axioms parseval_lower_bound

end Erdos1150Proof
