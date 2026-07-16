import WOWII.ZZGraphConjecture314CardinalityReduction
import WOWII.ZZGraphConjecture314P5Bridge

/-!
The exact repository statement of WOWII Graph Conjecture 314 is now reduced to
one graph-theoretic lemma: every minimal total dominating set has cardinality at
most three under the original connected, triangle-free, induced-P5-free
hypotheses.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Exact final gate for the repository theorem. -/
theorem conjecture314_of_minimalTDS_card_le_three
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (_hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (hUpper : ∀ S : Finset α, IsMinimalTotalDominatingSet G S → S.card ≤ 3) :
    IsWellTotallyDominated G := by
  apply isWellTotallyDominated_of_minimalTDS_card_le_three G hTriFree
  · exact no_FormsInducedP5_of_largestInducedPathSize_le_four G hPath
  · exact hUpper

end WrittenOnTheWallII.GraphConjecture314
