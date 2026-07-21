import BernsteinObstacle.GenericShiftAveraging
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

/-!
# Fixed translations good at infinitely many mesh levels

A per-level positive-measure estimate is stronger than mere existence at each
level.  If every measurable good set has measure at least `q`, then the limsup
set of translations that are good at infinitely many levels also has measure at
least `q`.  No independence assumption is used.
-/

/-- The union of all good sets from level `N` onward. -/
def goodTail {Ω : Type*} (G : ℕ → Set Ω) (N : ℕ) : Set Ω :=
  ⋃ n, ⋃ (_h : N ≤ n), G n

/-- Translations that belong to good sets at arbitrarily large levels. -/
def infinitelyOftenGood {Ω : Type*} (G : ℕ → Set Ω) : Set Ω :=
  ⋂ N, goodTail G N

/-- Every level set is contained in its corresponding tail union. -/
theorem goodSet_subset_goodTail
    {Ω : Type*} (G : ℕ → Set Ω) (N : ℕ) :
    G N ⊆ goodTail G N := by
  intro ω hω
  apply Set.mem_iUnion.mpr
  refine ⟨N, ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨le_rfl, hω⟩

/-- Tail unions decrease as the starting level increases. -/
theorem goodTail_antitone
    {Ω : Type*} (G : ℕ → Set Ω) :
    Antitone (goodTail G) := by
  intro N M hNM ω hω
  rcases Set.mem_iUnion.mp hω with ⟨n, hω⟩
  rcases Set.mem_iUnion.mp hω with ⟨hMn, hGn⟩
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨hNM.trans hMn, hGn⟩

/-- Measurability of a tail union. -/
theorem measurableSet_goodTail
    {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet (G n)) (N : ℕ) :
    MeasurableSet (goodTail G N) := by
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _h => hG n

/-- Pointwise characterization of membership in the limsup good set. -/
theorem mem_infinitelyOftenGood_iff
    {Ω : Type*} (G : ℕ → Set Ω) (ω : Ω) :
    ω ∈ infinitelyOftenGood G ↔
      ∀ N, ∃ n, N ≤ n ∧ ω ∈ G n := by
  constructor
  · intro hω N
    have htail : ω ∈ goodTail G N := Set.mem_iInter.mp hω N
    rcases Set.mem_iUnion.mp htail with ⟨n, htail⟩
    rcases Set.mem_iUnion.mp htail with ⟨hNn, hGn⟩
    exact ⟨n, hNn, hGn⟩
  · intro hω
    apply Set.mem_iInter.mpr
    intro N
    rcases hω N with ⟨n, hNn, hGn⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨hNn, hGn⟩

/-- Uniform lower measure at every level passes to the limsup set. -/
theorem measure_infinitelyOftenGood_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : ℕ → Set Ω) (q : ENNReal)
    (hG : ∀ n, MeasurableSet (G n))
    (hlower : ∀ n, q ≤ μ (G n)) :
    q ≤ μ (infinitelyOftenGood G) := by
  have hmeas : ∀ N, NullMeasurableSet (goodTail G N) μ :=
    fun N => (measurableSet_goodTail G hG N).nullMeasurableSet
  have hfin : ∃ N, μ (goodTail G N) ≠ ⊤ := by
    exact ⟨0, by finiteness⟩
  change q ≤ μ (⋂ N, goodTail G N)
  rw [(goodTail_antitone G).measure_iInter hmeas hfin]
  exact le_iInf fun N =>
    (hlower N).trans (measure_mono (goodSet_subset_goodTail G N))

/-- Real-valued finite-measure version of the limsup lower bound. -/
theorem measureReal_infinitelyOftenGood_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : ℕ → Set Ω) (q : ℝ)
    (hG : ∀ n, MeasurableSet (G n))
    (hlower : ∀ n, q ≤ μ.real (G n)) :
    q ≤ μ.real (infinitelyOftenGood G) := by
  have hlevel : ∀ n, ENNReal.ofReal q ≤ μ (G n) := by
    intro n
    exact ENNReal.ofReal_le_of_le_toReal (by
      simpa [measureReal_def] using hlower n)
  have hmain := measure_infinitelyOftenGood_ge μ G (ENNReal.ofReal q) hG hlevel
  have htop : μ (infinitelyOftenGood G) ≠ ⊤ := by finiteness
  rw [ENNReal.ofReal_le_iff_le_toReal htop] at hmain
  simpa [measureReal_def] using hmain

/-- Applying the reverse averaging theorem level by level yields one fixed
positive-measure set of translations that is good at infinitely many levels. -/
theorem genericShift_infinitelyOften_measure_lowerBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p L : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (hXmeas : ∀ n, Measurable (X n))
    (hXint : ∀ n, Integrable (X n) μ)
    (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hXL : ∀ n ω, X n ω ≤ L)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = p * L) :
    p / (2 - p) ≤ μ.real
      (infinitelyOftenGood fun n => goodTranslationSet (X n) p L) := by
  apply measureReal_infinitelyOftenGood_ge μ
    (fun n => goodTranslationSet (X n) p L) (p / (2 - p))
  · intro n
    exact measurableSet_le measurable_const (hXmeas n)
  · intro n
    exact goodTranslationSet_measure_lowerBound
      μ (X n) p L hp0 hp1 hL
      (hXmeas n) (hXint n) (hX0 n) (hXL n) (hmean n)

/-- If the core fraction is strictly positive, there exists one translation
that is good along arbitrarily fine levels. -/
theorem exists_translation_good_infinitelyOften
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p L : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (hXmeas : ∀ n, Measurable (X n))
    (hXint : ∀ n, Integrable (X n) μ)
    (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hXL : ∀ n ω, X n ω ≤ L)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = p * L) :
    ∃ ω, ∀ N, ∃ n, N ≤ n ∧ ω ∈ goodTranslationSet (X n) p L := by
  let G : ℕ → Set Ω := fun n => goodTranslationSet (X n) p L
  have hmeasure : p / (2 - p) ≤ μ.real (infinitelyOftenGood G) := by
    exact genericShift_infinitelyOften_measure_lowerBound
      μ X p L hp0.le hp1 hL hXmeas hXint hX0 hXL hmean
  have hqpos : 0 < p / (2 - p) :=
    goodTranslationFraction_pos p hp0 hp1
  have hpos : 0 < μ.real (infinitelyOftenGood G) := hqpos.trans_le hmeasure
  have hnonempty : (infinitelyOftenGood G).Nonempty :=
    nonempty_of_measureReal_ne_zero (ne_of_gt hpos)
  rcases hnonempty with ⟨ω, hω⟩
  exact ⟨ω, (mem_infinitelyOftenGood_iff G ω).mp hω⟩

end

end BernsteinObstacle
