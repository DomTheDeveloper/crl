import C217.EndpointSurgery

namespace C217

open SimpleGraph

universe u

namespace SimpleGraph.Walk

variable {V : Type u} {H K : SimpleGraph V} {a b : V}

@[simp]
theorem getVert_castGraph (h : H = K) (p : H.Walk a b) (n : ℕ) :
    (castGraph h p).getVert n = p.getVert n := by
  subst K
  rfl

@[simp]
theorem edges_castGraph (h : H = K) (p : H.Walk a b) :
    (castGraph h p).edges = p.edges := by
  subst K
  rfl

end SimpleGraph.Walk

end C217
