import SuFunctor.Universe.FellTopology
import SuFunctor.Universe.RecordLensContinuum
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # The record lens off the compact pin

`SuFunctor.Universe.RecordLensContinuum` carries the record lens on a
compact metric stage space, where the graph face is the (Vietoris =
Hausdorff-metric) hyperspace of nonempty compacts and compactness of
the lens comes free by Prokhorov.  This module transposes the lens's
closedness legs to the stratum that compactness never reaches:
noncompact stage spaces — unbounded horizons, noncompact state — with
graphs as **closed** sets under the **Fell** topology
(`SuFunctor.Universe.FellTopology`), and occupation laws as
probability measures under the narrow topology.

* **The con condition is closed off the pin** (`isClosed_fellCon`):
  on a locally compact, second-countable, completely-pseudo-metrizable
  ambient, `{(G, μ) | μ G = 1}` is closed in Fell × narrow.  The proof
  is the compact-stratum proof with its two pin-dependencies repaired:
  inner regularity by *closed* sets (enough on a compact ambient,
  where closed = compact) becomes inner regularity by *compact* sets —
  tightness, which complete pseudo-metrizability supplies — and the
  metric thickening that separated the leak from the graph becomes a
  compact interpolant (`exists_compact_between`), whose interior feeds
  the measure face's lower half and whose body feeds the graph face's
  miss demand.  One upper-face demand, one lower-face demand, exactly
  as at the compact stratum.
* **Compactness holds over every tight family**
  (`isCompact_fellCon_inter`): the graph face is compact outright
  (`FellCloseds.compactSpace`), so the lens is compact over any
  compact set of laws.  The lens's *full* compactification at this
  stratum — mass escaping to infinity paired with graphs escaping
  every compact — needs the vague topology on locally finite measures
  for its measure face and is deliberately out of scope here; with a
  probability-measure face the empty graph is con-excluded outright
  (`bot_notMem_fellCon`), which is that boundary's shadow.
* **The wall species transpose with their polarity law intact**
  (`lowerSemicontinuous_touchWallFell`,
  `lowerSemicontinuous_dwellWallFell`,
  `touch_dwell_separation_fell`): for an open bad region the
  touch-wall is a graph-face citizen — the hit face needs no
  compactness anywhere — and the dwell-wall a measure-face citizen,
  and they separate on zero-dwell visits.  The universe still makes no
  measure-zero ruling; the species do, per clause.

Every statement is stratum-general; the hypotheses name exactly what
each theorem consumes, and none of them is compactness of the
ambient.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace MeasureTheory Set

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

variable (X) in
/-- The record lens at the noncompact stratum: closed graphs (Fell
topology) con-coupled with occupation laws — the law gives the graph
full mass. -/
def fellCon : Set (FellCloseds X × ProbabilityMeasure X) :=
  {p | (p.2 : Measure X) (p.1 : Set X) = 1}

theorem mem_fellCon_iff {p : FellCloseds X × ProbabilityMeasure X} :
    p ∈ fellCon X ↔ (p.2 : Measure X) (p.1 : Set X) = 1 :=
  Iff.rfl

/-- The carried-by reading of con: full mass on the graph is exactly
vanishing on every open set disjoint from it. -/
theorem mem_fellCon_iff_forall_isOpen [OpensMeasurableSpace X]
    {p : FellCloseds X × ProbabilityMeasure X} :
    p ∈ fellCon X
      ↔ ∀ U : Set X, IsOpen U → Disjoint U (p.1 : Set X)
          → (p.2 : Measure X) U = 0 := by
  have hG : MeasurableSet (p.1 : Set X) := p.1.isClosed.measurableSet
  constructor
  · intro hcon U _ hdisj
    have hsub : U ⊆ ((p.1 : Set X))ᶜ := hdisj.subset_compl_right
    have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 := by
      rw [measure_compl hG (measure_ne_top _ _), measure_univ, hcon, tsub_self]
    exact le_antisymm (le_of_le_of_eq (measure_mono hsub) hcompl) zero_le
  · intro h
    have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 :=
      h _ p.1.isClosed.isOpen_compl disjoint_compl_left
    have hsplit := measure_compl hG (measure_ne_top (p.2 : Measure X) _)
    rw [measure_univ, hcompl] at hsplit
    have hle : (p.2 : Measure X) (p.1 : Set X) ≤ 1 := prob_le_one
    have hzero : (1 : ℝ≥0∞) - (p.2 : Measure X) (p.1 : Set X) = 0 := hsplit.symm
    rw [tsub_eq_zero_iff_le] at hzero
    exact le_antisymm hle hzero

/-- The empty graph is con-incompatible with every probability
measure: with a probability-measure face, the Fell hyperspace's escape
point never enters the lens.  (Pairing the escaped graph with escaped
mass is the vague stratum's job, out of scope here.) -/
@[simp]
theorem bot_notMem_fellCon (μ : ProbabilityMeasure X) :
    ((⊥ : FellCloseds X), μ) ∉ fellCon X := by
  intro hcon
  have h0 : (μ : Measure X) ((⊥ : FellCloseds X) : Set X) = 1 := hcon
  rw [FellCloseds.coe_bot, measure_empty] at h0
  exact zero_ne_one h0

/-- **The con condition is closed off the compact pin**: in
(Fell) × (narrow) over a locally compact, second-countable,
completely-pseudo-metrizable ambient, the lens is closed.  A failing
pair leaks mass off the graph; tightness concentrates part of the leak
on a *compact* carrier, a compact interpolant separates that carrier
from the graph, and the leak persists on one miss demand on the graph
face (Fell-open because the interpolant is compact — the repair the
Fell subbasis exists to make) paired with one mass demand on the
measure face's lower half (through the interpolant's interior). -/
theorem isClosed_fellCon
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [IsCompletelyPseudoMetrizableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X] :
    IsClosed (fellCon X) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨G₀, μ₀⟩ hp
  have hne : (μ₀ : Measure X) (G₀ : Set X) ≠ 1 := hp
  have hG₀meas : MeasurableSet (G₀ : Set X) := G₀.isClosed.measurableSet
  have hlt : (μ₀ : Measure X) (G₀ : Set X) < 1 :=
    lt_of_le_of_ne prob_le_one hne
  -- the leak: positive mass on the open complement of the graph
  have hcpos : 0 < (μ₀ : Measure X) ((G₀ : Set X))ᶜ := by
    rw [measure_compl hG₀meas (measure_ne_top _ _), measure_univ]
    exact tsub_pos_iff_lt.mpr hlt
  -- tightness: a compact set carries part of the leak
  obtain ⟨C, hCsub, hCcomp, hCpos⟩ :=
    MeasureTheory.innerRegularWRT_isCompact_isOpen (μ₀ : Measure X)
      G₀.isClosed.isOpen_compl 0 hcpos
  -- a compact interpolant separates the leak's carrier from the graph
  obtain ⟨L, hLcomp, hCint, hLsub⟩ :=
    exists_compact_between hCcomp G₀.isClosed.isOpen_compl hCsub
  -- the product neighborhood: miss the interpolant; keep mass in its
  -- interior
  refine ⟨{G : FellCloseds X | Disjoint (G : Set X) L}
      ×ˢ {μ : ProbabilityMeasure X | 0 < (μ : Measure X) (interior L)},
    ?_, ?_, ?_⟩
  · -- every pair in the neighborhood leaks: mass off the graph
    rintro ⟨G, μ⟩ ⟨hG, hμ⟩
    simp only [Set.mem_compl_iff, fellCon, Set.mem_setOf_eq]
    intro hcon
    have hGsub : (G : Set X) ⊆ (interior L)ᶜ :=
      (hG.mono_right interior_subset).subset_compl_right
    have hle : (μ : Measure X) (G : Set X)
        ≤ (μ : Measure X) (interior L)ᶜ := measure_mono hGsub
    rw [measure_compl isOpen_interior.measurableSet (measure_ne_top _ _),
      measure_univ] at hle
    have hlt1 : (1 : ℝ≥0∞) - (μ : Measure X) (interior L) < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hμ.ne'
    exact absurd hcon (hle.trans_lt hlt1).ne
  · exact IsOpen.prod
      (FellCloseds.isOpen_disjoint_of_isCompact hLcomp)
      (lowerSemicontinuous_iff_isOpen_preimage.mp
        (lowerSemicontinuous_probabilityMeasure_apply isOpen_interior) 0)
  · constructor
    · -- the graph misses the interpolant
      exact Set.disjoint_left.mpr fun a haG haL => hLsub haL haG
    · -- the leak's carrier keeps its mass inside the interior
      exact lt_of_lt_of_le hCpos (measure_mono hCint)

/-- Over any compact family of laws the lens is compact: the graph
face contributes `FellCloseds.compactSpace`, the measure face the
family's own compactness, and con-closedness cuts a closed subset.
This is the compactness available without the vague stratum. -/
theorem isCompact_fellCon_inter
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [IsCompletelyPseudoMetrizableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {M : Set (ProbabilityMeasure X)} (hM : IsCompact M) :
    IsCompact (fellCon X ∩ (univ ×ˢ M)) :=
  (isCompact_univ.prod hM).inter_left isClosed_fellCon

/-! ## The two wall species, noncompact stratum -/

open Classical in
/-- The touch-wall: hard violation when the graph meets the bad
region.  A graph-face penalty; zero-duration contact violates. -/
noncomputable def touchWallFell (Bad : Set X) :
    FellCloseds X × ProbabilityMeasure X → ℝ≥0∞ :=
  fun p => if (((p.1 : Set X)) ∩ Bad).Nonempty then ⊤ else 0

open Classical in
/-- The dwell-wall: hard violation when the occupation law gives the
bad region positive mass.  A measure-face penalty;
supported-but-null visits are forgiven. -/
noncomputable def dwellWallFell (Bad : Set X) :
    FellCloseds X × ProbabilityMeasure X → ℝ≥0∞ :=
  fun p => if 0 < (p.2 : Measure X) Bad then ⊤ else 0

/-- **The touch-wall is a lens citizen for open bad regions at every
stratum**: the hit face of the Fell topology is the Vietoris lower
face, and it never needed compactness — neither of the ambient nor of
the bad region.  (`OpensMeasurableSpace` enters only to topologize the
measure factor of the lens; the proof is graph-face throughout.) -/
theorem lowerSemicontinuous_touchWallFell [OpensMeasurableSpace X]
    {Bad : Set X} (hBad : IsOpen Bad) :
    LowerSemicontinuous (touchWallFell (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : FellCloseds X × ProbabilityMeasure X |
      ((p.1 : Set X) ∩ Bad).Nonempty}) ?_ ?_ ?_
  · exact (FellCloseds.isOpen_inter_nonempty_of_isOpen hBad).preimage
      continuous_fst
  · intro p hp
    have hp' : ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWallFell]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWallFell]
    rw [if_neg hp']

/-- **The dwell-wall is a lens citizen for open bad regions**: its
trigger is narrow-open by the measure face's lower half, which was
ambient-general from the start. -/
theorem lowerSemicontinuous_dwellWallFell [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {Bad : Set X} (hBad : IsOpen Bad) :
    LowerSemicontinuous (dwellWallFell (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : FellCloseds X × ProbabilityMeasure X |
      0 < (p.2 : Measure X) Bad}) ?_ ?_ ?_
  · exact (lowerSemicontinuous_iff_isOpen_preimage.mp
      (lowerSemicontinuous_probabilityMeasure_apply hBad) 0).preimage
      continuous_snd
  · intro p hp
    have hp' : 0 < (p.2 : Measure X) Bad := hp
    simp only [dwellWallFell]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ 0 < (p.2 : Measure X) Bad := hp
    simp only [dwellWallFell]
    rw [if_neg hp']

/-- **The species separate on zero-dwell visits**, off the pin exactly
as on it: a graph touching the bad region, carrying a point mass
elsewhere, violates the touch-wall and satisfies the dwell-wall.  The
measure-zero ruling stays per clause at every stratum. -/
theorem touch_dwell_separation_fell [T1Space X] {x₀ x₁ : X} {Bad : Set X}
    (hBad : MeasurableSet Bad) (hx₀ : x₀ ∈ Bad) (hx₁ : x₁ ∉ Bad) :
    ∃ p ∈ fellCon X,
      touchWallFell Bad p = ⊤ ∧ dwellWallFell Bad p = 0 := by
  classical
  refine ⟨(⟨{x₀, x₁}, ((Set.finite_singleton x₁).insert x₀).isClosed⟩,
    ⟨Measure.dirac x₁, inferInstance⟩), ?_, ?_, ?_⟩
  · -- con: the point mass sits inside the graph
    show Measure.dirac x₁ ({x₀, x₁} : Set X) = 1
    exact Measure.dirac_apply_of_mem (Set.mem_insert_of_mem _ rfl)
  · -- the graph touches the bad region
    simp only [touchWallFell]
    rw [if_pos ⟨x₀, Set.mem_insert _ _, hx₀⟩]
  · -- the point mass never dwells there
    simp only [dwellWallFell]
    rw [if_neg]
    show ¬ 0 < Measure.dirac x₁ Bad
    rw [Measure.dirac_apply' _ hBad, Set.indicator_of_notMem hx₁]
    exact lt_irrefl 0

end SuFunctor.Universe
