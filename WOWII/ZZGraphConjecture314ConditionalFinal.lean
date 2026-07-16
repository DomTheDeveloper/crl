import WOWII.ZZGraphConjecture314DominatingEdge
import WOWII.ZZGraphConjecture314Cycle5Blowup

/-!
Assembly theorem for WOWII Graph Conjecture 314 after the structural classification.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The two structural families arising in the classification of connected
triangle-free induced-`P₅`-free graphs. -/
def HasWOWII314Classification (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  (∃ (side : α → Bool) (u v : α),
      side u = false ∧ side v = true ∧
      (∀ x y : α, G.Adj x y → side x ≠ side y) ∧
      (∀ x : α, side x = true → G.Adj u x) ∧
      (∀ x : α, side x = false → G.Adj v x) ∧
      (∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)) ∨
  (∃ (bag : α → Fin 5), Function.Surjective bag ∧
      ∀ x y : α, G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y))

/-- Once the structural classification is supplied, well-total-domination follows
from the two independently formalized family theorems. -/
theorem isWellTotallyDominated_of_WOWII314Classification
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hclass : HasWOWII314Classification G) :
    IsWellTotallyDominated G := by
  rcases hclass with hdom | hcycle
  · obtain ⟨side, u, v, hu, hv, hpart, huDom, hvDom, hNoP5⟩ := hdom
    exact isWellTotallyDominated_of_bipartite_dominating_edge
      G side u v hu hv hpart huDom hvDom hNoP5
  · obtain ⟨bag, hsurj, hAdj⟩ := hcycle
    exact isWellTotallyDominated_of_cycle5_blowup G bag hsurj hAdj

end WrittenOnTheWallII.GraphConjecture314
