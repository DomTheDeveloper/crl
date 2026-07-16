import APNOutputs.ErdosProblems.erdos_846
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

open Finset Fintype
open scoped EuclideanGeometry

namespace Erdos846Sharp

open SimpleGraph

/--
For an AlphaProof good map, a finite image is non-trilinear exactly when its
underlying valid edge set contains no `FormsTriangle` triple.
-/
theorem image_nonTrilinear_iff_no_formsTriangle
    (q : ℕ × ℕ → ℝ²) (hq : Erdos846.IsGoodMap q)
    (E : Finset (ℕ × ℕ))
    (hvalid : ∀ e ∈ E, e.1 < e.2) :
    EuclideanGeometry.NonTrilinear (↑(E.image q) : Set ℝ²) ↔
      ∀ e₁ ∈ E, ∀ e₂ ∈ E, ∀ e₃ ∈ E,
        e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
          ¬ Erdos846.FormsTriangle e₁ e₂ e₃ := by
  classical
  constructor
  · intro hnon e₁ he₁ e₂ he₂ e₃ he₃ h12 h13 h23 htri
    have hp₁ : q e₁ ∈ E.image q := Finset.mem_image.mpr ⟨e₁, he₁, rfl⟩
    have hp₂ : q e₂ ∈ E.image q := Finset.mem_image.mpr ⟨e₂, he₂, rfl⟩
    have hp₃ : q e₃ ∈ E.image q := Finset.mem_image.mpr ⟨e₃, he₃, rfl⟩
    have hq12 : q e₁ ≠ q e₂ := hq.1 e₁ e₂ (hvalid e₁ he₁) (hvalid e₂ he₂) h12
    have hq13 : q e₁ ≠ q e₃ := hq.1 e₁ e₃ (hvalid e₁ he₁) (hvalid e₃ he₃) h13
    have hq23 : q e₂ ≠ q e₃ := hq.1 e₂ e₃ (hvalid e₂ he₂) (hvalid e₃ he₃) h23
    have hcol : Collinear ℝ ({q e₁, q e₂, q e₃} : Set ℝ²) :=
      (hq.2 e₁ e₂ e₃
        (hvalid e₁ he₁) (hvalid e₂ he₂) (hvalid e₃ he₃)
        h12 h13 h23).mpr htri
    exact (hnon hp₁ hp₂ hp₃ hq12 hq23 hq13) hcol
  · intro hno
    apply Erdos846.nontrilinear_of_no_collinear_triples
    intro p₁ p₂ p₃ hp₁ hp₂ hp₃ hp12 hp13 hp23 hcol
    rcases Finset.mem_image.mp hp₁ with ⟨e₁, he₁, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨e₂, he₂, rfl⟩
    rcases Finset.mem_image.mp hp₃ with ⟨e₃, he₃, rfl⟩
    have h12 : e₁ ≠ e₂ := fun h => hp12 (congrArg q h)
    have h13 : e₁ ≠ e₃ := fun h => hp13 (congrArg q h)
    have h23 : e₂ ≠ e₃ := fun h => hp23 (congrArg q h)
    have htri : Erdos846.FormsTriangle e₁ e₂ e₃ :=
      (hq.2 e₁ e₂ e₃
        (hvalid e₁ he₁) (hvalid e₂ he₂) (hvalid e₃ he₃)
        h12 h13 h23).mp hcol
    exact hno e₁ he₁ e₂ he₂ e₃ he₃ h12 h13 h23 htri

/-- Mantel's extremal comparison in the exact form needed by the Erdős 846 construction. -/
theorem triangleFree_card_edges_le_turan
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    #G.edgeFinset ≤ #(turanGraph n 2).edgeFinset := by
  have hT := isTuranMaximal_turanGraph (n := n) (r := 2) (by omega)
  exact hT.2 (by simpa using hG)

/-- The familiar numerical Mantel bound: a triangle-free graph has at most `n²/4` edges. -/
theorem four_mul_triangleFree_card_edges_le_sq
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    4 * #G.edgeFinset ≤ n ^ 2 := by
  have hle := triangleFree_card_edges_le_turan G hG
  have hT : 4 * #(turanGraph n 2).edgeFinset ≤ n ^ 2 := by
    rw [card_edgeFinset_turanGraph]
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases hm with hm | hm <;> simp [hm] <;> omega
  exact (Nat.mul_le_mul_left 4 hle).trans hT

/-- The bound is attained by the complete bipartite Turán graph. -/
theorem exists_triangleFree_extremizer (n : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧
      #G.edgeFinset = #(turanGraph n 2).edgeFinset := by
  refine ⟨turanGraph n 2, ?_, rfl⟩
  simpa using turanGraph_cliqueFree (n := n) (r := 2) (by omega)

#print axioms Erdos846Sharp.image_nonTrilinear_iff_no_formsTriangle
#print axioms Erdos846Sharp.four_mul_triangleFree_card_edges_le_sq
#print axioms Erdos846Sharp.exists_triangleFree_extremizer

end Erdos846Sharp
