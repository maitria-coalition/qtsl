import SuFunctor.Universe.RecordLens
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening

/-! # The record lens, continuum stratum

`SuFunctor.Universe.RecordLens` carries the record lens at a finite
discrete stage space; this module carries the continuum stratum the
memos adopt: stages drawn from a **compact metric space**, graphs as
points of the hyperspace (on a compact ambient, Fell agrees with
Vietoris and with the Hausdorff metric — the adopted graph-face
topology, with no extra machinery), occupation measures as **Borel
probability measures under the narrow topology** of convergence in
distribution.

* **The measure face's lower half**
  (`lowerSemicontinuous_probabilityMeasure_apply`): the mass of an
  open set is narrow-lsc — the portmanteau liminf-on-opens inequality,
  read at the neighborhood filter.
* **The con condition is closed** (`isClosed_narrowCon`): a lens pair
  fails con exactly when mass escapes the graph; inner regularity
  pins the escape on a closed set, a compact-to-open thickening
  separates it from the graph, and the failure is then witnessed by
  one upper-face demand on the graph (miss the cthickening) and one
  lower-face demand on the measure (positive mass on the open
  thickening) — the memo's "one face of each half", exactly.
* **The lens space is compact** (`isCompact_narrowCon`): closed in
  (compact hyperspace) × (compact measure space); the measure side is
  Prokhorov's theorem on a compact base, from the library.
* **Two wall species, two faces** (`touchWallNarrow`,
  `dwellWallNarrow`): for an *open* bad region — the continuum
  polarity condition, no longer free as in the discrete stratum — the
  touch-wall is a graph-face citizen and the dwell-wall a measure-face
  citizen, and they separate on zero-dwell visits
  (`touch_dwell_separation_narrow`): the graph touches, the point
  mass elsewhere never dwells.  The universe still makes no
  measure-zero ruling; the species do, per clause.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace MeasureTheory

/-! ## The measure face's lower half -/

/-- The mass of an open set is lower semicontinuous in the narrow
topology: the portmanteau liminf-on-opens inequality at the
neighborhood filter. -/
theorem lowerSemicontinuous_probabilityMeasure_apply {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {U : Set X} (hU : IsOpen U) :
    LowerSemicontinuous fun μ : ProbabilityMeasure X => (μ : Measure X) U := by
  intro μ₀ y hy
  have h : (μ₀ : Measure X) U
      ≤ (nhds μ₀).liminf fun μ : ProbabilityMeasure X => (μ : Measure X) U :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto Filter.tendsto_id hU
  exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hy h)

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X]
  [BorelSpace X]

/-! ## The lens, and the con condition -/

variable (X) in
/-- The continuum record lens: graphs con-coupled with occupation
measures — the measure gives the graph full mass.  On a compact
metric stage space this is exactly "the support lies inside the
graph". -/
def narrowCon : Set (NonemptyCompacts X × ProbabilityMeasure X) :=
  {p | (p.2 : Measure X) (p.1 : Set X) = 1}

theorem mem_narrowCon_iff {p : NonemptyCompacts X × ProbabilityMeasure X} :
    p ∈ narrowCon X ↔ (p.2 : Measure X) (p.1 : Set X) = 1 :=
  Iff.rfl

/-- The carried-by reading of con: full mass on the graph is exactly
vanishing on every open set disjoint from it. -/
theorem mem_narrowCon_iff_forall_isOpen
    {p : NonemptyCompacts X × ProbabilityMeasure X} :
    p ∈ narrowCon X
      ↔ ∀ U : Set X, IsOpen U → Disjoint U (p.1 : Set X)
          → (p.2 : Measure X) U = 0 := by
  have hG : MeasurableSet (p.1 : Set X) :=
    p.1.isCompact.isClosed.measurableSet
  constructor
  · intro hcon U hU hdisj
    have hsub : U ⊆ ((p.1 : Set X))ᶜ := hdisj.subset_compl_right
    have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 := by
      rw [measure_compl hG (measure_ne_top _ _), measure_univ, hcon, tsub_self]
    exact le_antisymm (le_of_le_of_eq (measure_mono hsub) hcompl) zero_le
  · intro h
    have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 :=
      h _ p.1.isCompact.isClosed.isOpen_compl disjoint_compl_left
    have := measure_compl hG (measure_ne_top (p.2 : Measure X) _)
    rw [measure_univ, hcompl] at this
    have hle : (p.2 : Measure X) (p.1 : Set X) ≤ 1 := prob_le_one
    have : (1 : ℝ≥0∞) - (p.2 : Measure X) (p.1 : Set X) = 0 := this.symm
    rw [tsub_eq_zero_iff_le] at this
    exact le_antisymm hle this

/-- **The con condition is closed** in (Vietoris) × (narrow).  A
failing pair leaks mass off the graph; regularity concentrates the
leak on a closed set, a thickening separates it from the graph, and
the leak persists on one upper-face graph demand paired with one
lower-face measure demand. -/
theorem isClosed_narrowCon : IsClosed (narrowCon X) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨G₀, μ₀⟩ hp
  have hne : (μ₀ : Measure X) (G₀ : Set X) ≠ 1 := hp
  have hG₀meas : MeasurableSet (G₀ : Set X) :=
    G₀.isCompact.isClosed.measurableSet
  have hlt : (μ₀ : Measure X) (G₀ : Set X) < 1 :=
    lt_of_le_of_ne prob_le_one hne
  -- the leak: positive mass on the open complement of the graph
  have hcpos : 0 < (μ₀ : Measure X) ((G₀ : Set X))ᶜ := by
    rw [measure_compl hG₀meas (measure_ne_top _ _), measure_univ]
    exact tsub_pos_iff_lt.mpr hlt
  -- inner regularity: a closed (hence compact) set carries the leak
  have hreg := IsOpen.measure_eq_iSup_isClosed
    G₀.isCompact.isClosed.isOpen_compl (μ₀ : Measure X)
  rw [hreg] at hcpos
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp hcpos
  obtain ⟨hFsub, hF2⟩ := lt_iSup_iff.mp hF
  obtain ⟨hFclosed, hFpos⟩ := lt_iSup_iff.mp hF2
  -- a thickening of the leak's carrier misses the graph
  obtain ⟨δ, hδ0, hδsub⟩ := (hFclosed.isCompact).exists_cthickening_subset_open
    G₀.isCompact.isClosed.isOpen_compl hFsub
  -- the product neighborhood: miss the cthickening; keep mass on the
  -- open thickening
  refine ⟨{G : NonemptyCompacts X |
        (G : Set X) ⊆ (Metric.cthickening δ F)ᶜ}
      ×ˢ {μ : ProbabilityMeasure X |
        0 < (μ : Measure X) (Metric.thickening δ F)},
    ?_, ?_, ?_⟩
  · -- every pair in the neighborhood leaks: mass off the graph
    rintro ⟨G, μ⟩ ⟨hG, hμ⟩
    simp only [Set.mem_compl_iff, narrowCon, Set.mem_setOf_eq]
    intro hcon
    have hGsub : (G : Set X) ⊆ (Metric.thickening δ F)ᶜ :=
      hG.trans (Set.compl_subset_compl.mpr (Metric.thickening_subset_cthickening δ F))
    have hle : (μ : Measure X) (G : Set X)
        ≤ (μ : Measure X) (Metric.thickening δ F)ᶜ := measure_mono hGsub
    rw [measure_compl Metric.isOpen_thickening.measurableSet
      (measure_ne_top _ _), measure_univ] at hle
    have hlt1 : (1 : ℝ≥0∞) - (μ : Measure X) (Metric.thickening δ F) < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hμ.ne'
    exact absurd hcon (hle.trans_lt hlt1).ne
  · exact IsOpen.prod
      (NonemptyCompacts.isOpen_subsets_of_isOpen
        Metric.isClosed_cthickening.isOpen_compl)
      (lowerSemicontinuous_iff_isOpen_preimage.mp
        (lowerSemicontinuous_probabilityMeasure_apply
          Metric.isOpen_thickening) 0)
  · constructor
    · -- the graph misses the cthickening
      intro x hxG hxth
      exact hδsub hxth hxG
    · -- the leak's carrier keeps its mass inside its own thickening
      exact lt_of_lt_of_le hFpos
        (measure_mono (Metric.self_subset_thickening hδ0 F))

/-- **The lens space is compact**: closed in the product of the
compact hyperspace and the compact (Prokhorov) measure space. -/
theorem isCompact_narrowCon : IsCompact (narrowCon X) :=
  isClosed_narrowCon.isCompact

/-! ## The two wall species, continuum stratum -/

open Classical in
/-- The touch-wall: hard violation when the graph meets the bad
region.  A graph-face penalty; zero-duration contact violates. -/
noncomputable def touchWallNarrow (Bad : Set X) :
    NonemptyCompacts X × ProbabilityMeasure X → ℝ≥0∞ :=
  fun p => if (((p.1 : Set X)) ∩ Bad).Nonempty then ⊤ else 0

open Classical in
/-- The dwell-wall: hard violation when the occupation measure gives
the bad region positive mass.  A measure-face penalty;
supported-but-null visits are forgiven. -/
noncomputable def dwellWallNarrow (Bad : Set X) :
    NonemptyCompacts X × ProbabilityMeasure X → ℝ≥0∞ :=
  fun p => if 0 < (p.2 : Measure X) Bad then ⊤ else 0

/-- **The touch-wall is a lens citizen for open bad regions** — the
continuum polarity condition (forbidden regions open), no longer free
as at the discrete stratum. -/
theorem lowerSemicontinuous_touchWallNarrow {Bad : Set X}
    (hBad : IsOpen Bad) :
    LowerSemicontinuous (touchWallNarrow (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : NonemptyCompacts X × ProbabilityMeasure X |
      ((p.1 : Set X) ∩ Bad).Nonempty}) ?_ ?_ ?_
  · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hBad).preimage
      continuous_fst
  · intro p hp
    have hp' : ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWallNarrow]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWallNarrow]
    rw [if_neg hp']

/-- **The dwell-wall is a lens citizen for open bad regions**: its
trigger is narrow-open by the measure face's lower half. -/
theorem lowerSemicontinuous_dwellWallNarrow {Bad : Set X}
    (hBad : IsOpen Bad) :
    LowerSemicontinuous (dwellWallNarrow (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : NonemptyCompacts X × ProbabilityMeasure X |
      0 < (p.2 : Measure X) Bad}) ?_ ?_ ?_
  · exact (lowerSemicontinuous_iff_isOpen_preimage.mp
      (lowerSemicontinuous_probabilityMeasure_apply hBad) 0).preimage
      continuous_snd
  · intro p hp
    have hp' : 0 < (p.2 : Measure X) Bad := hp
    simp only [dwellWallNarrow]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ 0 < (p.2 : Measure X) Bad := hp
    simp only [dwellWallNarrow]
    rw [if_neg hp']

/-- **The species separate on zero-dwell visits**: a graph touching
the bad region, carrying a point mass elsewhere, violates the
touch-wall and satisfies the dwell-wall.  The measure-zero ruling
stays per clause at the continuum stratum. -/
theorem touch_dwell_separation_narrow {x₀ x₁ : X} {Bad : Set X}
    (hBad : MeasurableSet Bad) (hx₀ : x₀ ∈ Bad) (hx₁ : x₁ ∉ Bad) :
    ∃ p ∈ narrowCon X,
      touchWallNarrow Bad p = ⊤ ∧ dwellWallNarrow Bad p = 0 := by
  classical
  refine ⟨(⟨⟨{x₀, x₁}, ((Set.finite_singleton x₁).insert x₀).isCompact⟩,
      ⟨x₀, Set.mem_insert _ _⟩⟩,
    ⟨Measure.dirac x₁, inferInstance⟩), ?_, ?_, ?_⟩
  · -- con: the point mass sits inside the graph
    show Measure.dirac x₁ ({x₀, x₁} : Set X) = 1
    exact Measure.dirac_apply_of_mem (Set.mem_insert_of_mem _ rfl)
  · -- the graph touches the bad region
    simp only [touchWallNarrow]
    rw [if_pos ⟨x₀, Set.mem_insert _ _, hx₀⟩]
  · -- the point mass never dwells there
    simp only [dwellWallNarrow]
    rw [if_neg]
    show ¬ 0 < Measure.dirac x₁ Bad
    rw [Measure.dirac_apply' _ hBad, Set.indicator_of_notMem hx₁]
    exact lt_irrefl 0

end SuFunctor.Universe
