import WOWII.ZZGraphConjecture314ChainGraph
import WOWII.ZZGraphConjecture314Cycle5Blowup

/-!
Assembly theorems for WOWII Graph Conjecture 314 after the structural classification.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An earlier, stronger bipartite formulation using a dominating edge. -/
def HasWOWII314Classification (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  (∃ (side : α → Bool) (u v : α),
      side u = false ∧ side v = true ∧
      (∀ x y : α, G.Adj x y → side x ≠ side y) ∧
      (∀ x : α, side x = true → G.Adj u x) ∧
      (∀ x : α, side x = false → G.Adj v x) ∧
      (∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)) ∨
  (∃ (bag : α → Fin 5), Function.Surjective bag ∧
      ∀ x y : α, G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y))

/-- The exact two families in the mathematical classification: a connected chain
 graph, or a complete blow-up of the five-cycle. -/
def HasWOWII314StructuralClassification (G : SimpleGraph α) : Prop :=
  (∃ side : α → Bool,
      (∀ x y : α, G.Adj x y → side x ≠ side y) ∧
      (∀ a b : α, side a = side b →
        (∀ x : α, G.Adj a x → G.Adj b x) ∨
        (∀ x : α, G.Adj b x → G.Adj a x))) ∨
  (∃ bag : α → Fin 5, Function.Surjective bag ∧
      ∀ x y : α, G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y))

/-- Once the older dominating-edge classification is supplied, well-total-domination
 follows from the two independently formalized family theorems. -/
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

/-- The family theorem in the exact form needed by the ordinary classification. -/
theorem isWellTotallyDominated_of_WOWII314StructuralClassification
    [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hclass : HasWOWII314StructuralClassification G) :
    IsWellTotallyDominated G := by
  rcases hclass with hchain | hcycle
  · obtain ⟨side, hpart, hNested⟩ := hchain
    exact isWellTotallyDominated_of_connected_chain_graph G hG side hpart hNested
  · obtain ⟨bag, hsurj, hAdj⟩ := hcycle
    exact isWellTotallyDominated_of_cycle5_blowup G bag hsurj hAdj

/-- The exact repository theorem follows from the one remaining classification lemma. -/
theorem conjecture314_of_structural_classification
    [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (_hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (_hPath : largestInducedPathSize G ≤ 4)
    (hclass : HasWOWII314StructuralClassification G) :
    IsWellTotallyDominated G :=
  isWellTotallyDominated_of_WOWII314StructuralClassification G hG hclass

end WrittenOnTheWallII.GraphConjecture314
