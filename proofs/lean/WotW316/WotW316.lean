import FormalConjectures.WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The non-pendant vertices. -/
def coreVertices : Finset α :=
  Finset.univ \ pendantVertices G

/-- Core vertices that support at least one pendant vertex. -/
def forcedVertices : Finset α :=
  (coreVertices G).filter fun c => ∃ l ∈ pendantVertices G, G.Adj l c

lemma mem_coreVertices_iff {v : α} :
    v ∈ coreVertices G ↔ G.degree v ≠ 1 := by
  classical
  simp [coreVertices, pendantVertices]

lemma mem_forcedVertices_iff {c : α} :
    c ∈ forcedVertices G ↔
      c ∈ coreVertices G ∧ ∃ l ∈ pendantVertices G, G.Adj l c := by
  classical
  simp [forcedVertices]

lemma forcedVertices_subset_of_totalDominating
    {S : Finset α} (hS : G.IsTotalDominatingSet S) :
    forcedVertices G ⊆ S := by
  classical
  intro c hc
  rw [mem_forcedVertices_iff] at hc
  rcases hc.2 with ⟨l, hl, hlc⟩
  have hdeg : G.degree l = 1 := by
    simpa [pendantVertices] using hl
  rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdeg with ⟨u, hlu, hu⟩
  rcases hS l with ⟨w, hwS, hlw⟩
  have hw : w = u := hu w hlw
  have hc' : c = u := hu c hlc
  simpa [hw, hc'] using hwS

lemma forcedVertices_nonempty
    (hP : (pendantVertices G).Nonempty)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G) :
    (forcedVertices G).Nonempty := by
  classical
  rcases hP with ⟨l, hl⟩
  have hdeg : G.degree l = 1 := by
    simpa [pendantVertices] using hl
  rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdeg with ⟨c, hlc, _⟩
  refine ⟨c, (mem_forcedVertices_iff G).2 ⟨hleaf_core l hl c hlc, ?_⟩⟩
  exact ⟨l, hl, hlc⟩

lemma forcedVertices_totalDominating_of_two_le
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcore_clique : ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v)
    (hcard : 2 ≤ (forcedVertices G).card) :
    G.IsTotalDominatingSet (forcedVertices G) := by
  classical
  intro v
  by_cases hv : v ∈ pendantVertices G
  · have hdeg : G.degree v = 1 := by
      simpa [pendantVertices] using hv
    rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdeg with ⟨c, hvc, _⟩
    have hcCore := hleaf_core v hv c hvc
    have hcF : c ∈ forcedVertices G :=
      (mem_forcedVertices_iff G).2 ⟨hcCore, ⟨v, hv, hvc⟩⟩
    exact ⟨c, hcF, hvc⟩
  · have hvCore : v ∈ coreVertices G := by
      simp [coreVertices, hv]
    have hex : ∃ c ∈ forcedVertices G, c ≠ v := by
      by_contra h
      push_neg at h
      have hsub : forcedVertices G ⊆ {v} := by
        intro c hc
        simpa using h c hc
      have hle := Finset.card_le_card hsub
      have hone : ({v} : Finset α).card = 1 := by simp
      rw [hone] at hle
      omega
    rcases hex with ⟨c, hcF, hcv⟩
    have hcCore := ((mem_forcedVertices_iff G).1 hcF).1
    exact ⟨c, hcF, hcore_clique v hvCore c hcCore hcv.symm⟩

lemma minimalTotalDominating_eq_forced_of_two_le
    {S : Finset α}
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcore_clique : ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v)
    (hcard : 2 ≤ (forcedVertices G).card)
    (hS : G.IsMinimalTotalDominatingSet S) :
    S = forcedVertices G := by
  classical
  have hsub : forcedVertices G ⊆ S :=
    forcedVertices_subset_of_totalDominating G hS.1
  have htds := forcedVertices_totalDominating_of_two_le G hleaf_core hcore_clique hcard
  by_contra hne
  have hss : forcedVertices G ⊂ S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne.symm⟩
  exact (hS.2 (forcedVertices G) hss) htds

lemma pair_totalDominating_of_forced_singleton
    {a x : α}
    (hF : forcedVertices G = {a})
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcore_clique : ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v)
    (hax : G.Adj a x) :
    G.IsTotalDominatingSet {a, x} := by
  classical
  intro v
  by_cases hv : v ∈ pendantVertices G
  · have hdeg : G.degree v = 1 := by
      simpa [pendantVertices] using hv
    rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdeg with ⟨c, hvc, _⟩
    have hcCore := hleaf_core v hv c hvc
    have hcF : c ∈ forcedVertices G :=
      (mem_forcedVertices_iff G).2 ⟨hcCore, ⟨v, hv, hvc⟩⟩
    have hca : c = a := by simpa [hF] using hcF
    subst c
    exact ⟨a, by simp, hvc⟩
  · have hvCore : v ∈ coreVertices G := by
      simp [coreVertices, hv]
    by_cases hva : v = a
    · subst v
      exact ⟨x, by simp, hax⟩
    · have haF : a ∈ forcedVertices G := by simp [hF]
      have haCore := ((mem_forcedVertices_iff G).1 haF).1
      exact ⟨a, by simp, hcore_clique v hvCore a haCore hva⟩

lemma minimalTotalDominating_card_eq_two_of_forced_singleton
    {S : Finset α} {a : α}
    (hF : forcedVertices G = {a})
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcore_clique : ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v)
    (hS : G.IsMinimalTotalDominatingSet S) :
    S.card = 2 := by
  classical
  have haF : a ∈ forcedVertices G := by simp [hF]
  have haS : a ∈ S :=
    forcedVertices_subset_of_totalDominating G hS.1 haF
  rcases hS.1 a with ⟨x, hxS, hax⟩
  have hpairTDS := pair_totalDominating_of_forced_singleton G hF hleaf_core hcore_clique hax
  have hpairSub : ({a, x} : Finset α) ⊆ S := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact haS
    · exact hxS
  have hpairEq : S = {a, x} := by
    by_contra hne
    have hss : ({a, x} : Finset α) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hpairSub, hne.symm⟩
    exact (hS.2 {a, x} hss) hpairTDS
  rw [hpairEq]
  have hne : a ≠ x := fun h => by subst x; exact G.loopless a hax
  simp [hne]

/-- If every pendant vertex is attached to the non-pendant clique, then the graph is well totally
 dominated. -/
theorem wellTotallyDominated_of_clique_core
    (hP : (pendantVertices G).Nonempty)
    (hleaf_core : ∀ l ∈ pendantVertices G, ∀ c, G.Adj l c → c ∈ coreVertices G)
    (hcore_clique : ∀ u ∈ coreVertices G, ∀ v ∈ coreVertices G, u ≠ v → G.Adj u v) :
    G.IsWellTotallyDominated := by
  classical
  intro S T hS hT
  have hFne := forcedVertices_nonempty G hP hleaf_core
  by_cases htwo : 2 ≤ (forcedVertices G).card
  · rw [minimalTotalDominating_eq_forced_of_two_le G hleaf_core hcore_clique htwo hS,
        minimalTotalDominating_eq_forced_of_two_le G hleaf_core hcore_clique htwo hT]
  · have hcard : (forcedVertices G).card = 1 := by
      have hpos := Finset.card_pos.mpr hFne
      omega
    rcases Finset.card_eq_one.mp hcard with ⟨a, hFa⟩
    rw [minimalTotalDominating_card_eq_two_of_forced_singleton G hFa hleaf_core hcore_clique hS,
        minimalTotalDominating_card_eq_two_of_forced_singleton G hFa hleaf_core hcore_clique hT]

/-- If every vertex is pendant, every total dominating set is the whole vertex set. -/
theorem wellTotallyDominated_of_all_pendant
    (hall : ∀ v : α, G.degree v = 1) :
    G.IsWellTotallyDominated := by
  classical
  intro S T hS hT
  have hall_mem (U : Finset α) (hU : G.IsTotalDominatingSet U) : U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rcases (G.degree_eq_one_iff_existsUnique_adj).mp (hall x) with ⟨y, hxy, hyuniq⟩
    rcases hU y with ⟨z, hzU, hyz⟩
    have hz : z = x := by
      have hyx : G.Adj y x := hxy.symm
      exact (hyuniq z hyz).trans (hyuniq x hyx).symm
    simpa [hz] using hzU
  rw [hall_mem S hS.1, hall_mem T hT.1]

#print axioms wellTotallyDominated_of_clique_core
#print axioms wellTotallyDominated_of_all_pendant

end

end WrittenOnTheWallII.GraphConjecture316
