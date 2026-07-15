import Erdos865

open Finset Filter
open scoped Asymptotics

namespace Erdos865

/--
The exact theorem statement currently used by
`google-deepmind/formal-conjectures/FormalConjectures/ErdosProblems/865.lean`.

This wrapper derives the real-valued eventual formulation from the explicit
integer bound `5 * N + 53 < 8 * A.card` proved in `erdos865_contains_triple`.
The witness `C = 7` works for every `N`, not merely for all sufficiently large
`N`, because `8 * 7 = 56 > 53`.
-/
theorem formalConjectures_erdos_865 :
    ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A := by
  refine ⟨7, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro N A hsub hcard
  have hreal : (5 : ℝ) * N + 53 < 8 * A.card := by
    norm_num at hcard ⊢
    nlinarith
  have hnat : 5 * N + 53 < 8 * A.card := by
    exact_mod_cast hreal
  simpa [HasTriple] using erdos865_contains_triple N A hsub hnat

#print axioms formalConjectures_erdos_865

end Erdos865
