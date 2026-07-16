import A387471Minimal
import A387471Nonminimal

/-!
# Unconditional grid-level sine classification
-/

namespace A387471

/-- Every admissible reduced sine relation has exactly the ordinary or exceptional
coefficient pattern. -/
theorem grid_sine_classification_proved : GridSineClassification := by
  intro n i j k hn hi hj hk hsin
  letI : NeZero n := ⟨hn.ne'⟩
  let A := reducedA n i j k
  let B := reducedB n i j k
  let C := reducedC n i j k
  by_cases hmin : MinimallyVanishes Finset.univ (sixRoot n A B C)
  · have hminCanonical : MinimallyVanishes Finset.univ
        (fun r : Fin 6 ↦ canonicalRoot (12 * n) ^ (sixExponent n A B C r).val) := by
      simpa only [sixRoot_eq_canonical] using hmin
    exact minimal_reduced_classification hn hi hj hk hsin
      (by simpa [A, B, C] using hminCanonical)
  · exact nonminimal_reduced_classification hn hi hj hk hsin
      (by simpa [A, B, C] using hmin)

/-- Every concurrent admissible cevian triple is ordinary or exceptional. -/
theorem every_solution_indexClassified (n i j k : ℕ) (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (hcon : CevianConcurrent n i j k) :
    IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ) :=
  indexClassified_of_gridSineClassification grid_sine_classification_proved
    n i j k hn hi hj hk hcon

#print axioms grid_sine_classification_proved
#print axioms every_solution_indexClassified

end A387471
