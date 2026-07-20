import BernsteinObstacle.DiagonalRecovery
import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

/-!
# Translation stability of sequential Mosco convergence

If discrete zero-obstacle cones Mosco-converge and discrete obstacles converge
strongly, the translated obstacle cones Mosco-converge as well.
-/

section TranslatedMosco

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def translatedSet (a : E) (K : Set E) : Set E :=
  {x | x - a ∈ K}

@[simp]
theorem mem_translatedSet {a x : E} {K : Set E} :
    x ∈ translatedSet a K ↔ x - a ∈ K :=
  Iff.rfl

theorem stronglyConverges_add
    (u v : ℕ → E) (x y : E)
    (hu : StronglyConverges u x)
    (hv : StronglyConverges v y) :
    StronglyConverges (fun n => u n + v n) (x + y) := by
  unfold StronglyConverges at hu hv ⊢
  exact hu.add hv

theorem weaklyConverges_sub_stronglyConverges
    (u v : ℕ → E) (x y : E)
    (hu : WeaklyConverges u x)
    (hv : StronglyConverges v y) :
    WeaklyConverges (fun n => u n - v n) (x - y) := by
  unfold WeaklyConverges at hu ⊢
  unfold StronglyConverges at hv
  intro phi
  have hvphi :
      Tendsto (fun n => phi (v n)) atTop (nhds (phi y)) := by
    exact (phi.continuous.tendsto y).comp hv
  simpa using (hu phi).sub hvphi

theorem moscoConverges_translated
    (K : ℕ → Set E) (Klim : Set E)
    (a : ℕ → E) (alim : E)
    (hM : MoscoConverges K Klim)
    (ha : StronglyConverges a alim) :
    MoscoConverges
      (fun n => translatedSet (a n) (K n))
      (translatedSet alim Klim) := by
  constructor
  · intro x hx
    have hx0 : x - alim ∈ Klim := hx
    obtain ⟨u, huK, hu⟩ := hM.recovery (x - alim) hx0
    refine ⟨fun n => a n + u n, ?_, ?_⟩
    · intro n
      change a n + u n - a n ∈ K n
      simpa using huK n
    · have hsum :
          StronglyConverges (fun n => a n + u n) (alim + (x - alim)) :=
        stronglyConverges_add a u alim (x - alim) ha hu
      convert hsum using 1 <;> abel
  · intro index hindex u x hu hweak
    have haSubsequence :
        StronglyConverges (fun n => a (index n)) alim :=
      stronglyConverges_comp_tendsto_atTop
        a alim index ha hindex.tendsto_atTop
    have hweakShifted :
        WeaklyConverges
          (fun n => u n - a (index n))
          (x - alim) :=
      weaklyConverges_sub_stronglyConverges
        u (fun n => a (index n)) x alim hweak haSubsequence
    have hmemShifted :
        ∀ n, u n - a (index n) ∈ K (index n) := by
      intro n
      exact hu n
    exact hM.weak_limit index hindex
      (fun n => u n - a (index n)) (x - alim)
      hmemShifted hweakShifted

end TranslatedMosco

end BernsteinObstacle
