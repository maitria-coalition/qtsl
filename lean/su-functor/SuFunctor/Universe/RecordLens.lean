import SuFunctor.Universe.VietorisStratum

/-! # The record lens, finitary stratum

The record layer denotes a behavior by a **lens**: the pair of its
graph (a closed set of stages) and its occupation measure (how much
time it spends where), coupled by the **con condition** — the measure
lives inside the graph.  This module carries the finitary stratum:
stages drawn from a finite discrete type `X` (a finite time grid times
a finite observation alphabet), graphs as points of the hyperspace
`NonemptyCompacts X`, occupation measures as probability states
`ProbState X`.

* **The con condition is closed** (`isClosed_recordCon`), hence the
  lens space is compact (`isCompact_recordCon`): a closed subspace of
  (hyperspace) × (simplex).  At this stratum the proof is a finite
  intersection of (coordinate-vanishing) ∪ (membership) demands — the
  finitary shadow of the general pairing of the graph face's upper
  (miss) half with the measure face's lower (mass-lower-bound) half.
* **The canonical lift has full support**
  (`support_uniformLift_iff`): the uniform occupation measure of a
  nonempty graph is supported on exactly the graph.  In discrete time
  every stage has positive duration, so support equals graph with no
  strictness — the zero-duration strictness locus is a continuum
  phenomenon, and the lens keeps the slot for it: `recordCon` admits
  pairs whose support is strictly inside the graph, and the wall
  separation below lives on exactly those.
* **Two wall species, two faces** (`touchWall`, `dwellWall`): the
  touch-wall penalizes a graph that meets the bad region — a
  graph-face citizen (`lowerSemicontinuous_touchWall`; at the discrete
  stratum every region is open, so the open-bad-region polarity
  condition of the continuum stratum is met for free) — while the
  dwell-wall penalizes positive occupation of the bad region — a
  measure-face citizen (`lowerSemicontinuous_dwellWall`, genuinely
  topological: positive mass on a region is an open demand on the
  simplex).
* **The species separate on zero-dwell visits**
  (`touch_dwell_separation`): a lens point whose graph touches the bad
  region while its measure gives it no mass violates the touch-wall
  and satisfies the dwell-wall.  The semantic universe makes no
  measure-zero ruling; the two wall species make it per clause, and
  both are citizens of the lens.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-- Walls on open trigger classes are citizens: the shared lsc pattern
of both record-wall species. -/
theorem lowerSemicontinuous_wall_on_open {α : Type*} [TopologicalSpace α]
    {W : α → ℝ≥0∞} {S : Set α} (hS : IsOpen S)
    (hin : ∀ p ∈ S, W p = ⊤) (hout : ∀ p ∉ S, W p = 0) :
    LowerSemicontinuous W := by
  intro p y hy
  by_cases hp : p ∈ S
  · rw [hin p hp] at hy
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [hin q hq]
    exact hy
  · rw [hout p hp] at hy
    exact absurd hy (not_lt.mpr zero_le)

variable {X : Type*} [Fintype X] [TopologicalSpace X] [DiscreteTopology X]

/-- The record-lens con condition: the occupation measure is carried by
the graph. -/
def recordCon : Set (NonemptyCompacts X × ProbState X) :=
  {p | ∀ x, (p.2 : X → ℝ) x ≠ 0 → x ∈ p.1}

theorem mem_recordCon_iff {p : NonemptyCompacts X × ProbState X} :
    p ∈ recordCon ↔ ∀ x, (p.2 : X → ℝ) x ≠ 0 → x ∈ p.1 :=
  Iff.rfl

/-- Point membership is a closed demand on the graph face (the upper
face's contribution to con-closedness). -/
theorem isClosed_setOf_mem_graph (x : X) :
    IsClosed {K : NonemptyCompacts X | x ∈ K} := by
  rw [← isOpen_compl_iff]
  have heq : {K : NonemptyCompacts X | x ∈ K}ᶜ
      = {K : NonemptyCompacts X | (K : Set X) ⊆ {x}ᶜ} := by
    ext K
    simp [Set.subset_compl_singleton_iff]
  rw [heq]
  exact NonemptyCompacts.isOpen_subsets_of_isOpen isOpen_compl_singleton

/-- **The con condition is closed** in (graph face) × (measure face). -/
theorem isClosed_recordCon : IsClosed (recordCon (X := X)) := by
  have heq : recordCon (X := X)
      = ⋂ x : X, ({p : NonemptyCompacts X × ProbState X | (p.2 : X → ℝ) x = 0}
          ∪ {p | x ∈ p.1}) := by
    ext p
    simp only [recordCon, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    refine forall_congr' fun x => ?_
    by_cases h : (p.2 : X → ℝ) x = 0 <;> simp [h]
  rw [heq]
  refine isClosed_iInter fun x => IsClosed.union ?_ ?_
  · exact isClosed_eq
      (((continuous_apply x).comp continuous_subtype_val).comp continuous_snd)
      continuous_const
  · exact (isClosed_setOf_mem_graph x).preimage continuous_fst

/-- **The lens space is compact**: closed in (compact hyperspace) ×
(compact simplex). -/
theorem isCompact_recordCon : IsCompact (recordCon (X := X)) :=
  isClosed_recordCon.isCompact

/-! ## The canonical lift: uniform occupation of a graph -/

open Classical in
/-- The uniform occupation measure of a nonempty graph: every stage
carries duration `1 / |G|`. -/
noncomputable def uniformLift (G : NonemptyCompacts X) : ProbState X :=
  ⟨fun x => if x ∈ (G : Set X).toFinset
      then ((G : Set X).toFinset.card : ℝ)⁻¹ else 0, by
    have hcard : (0 : ℝ) < (G : Set X).toFinset.card := by
      have hne : (G : Set X).toFinset.Nonempty :=
        Set.toFinset_nonempty.mpr G.nonempty
      exact_mod_cast Finset.card_pos.mpr hne
    constructor
    · intro x
      by_cases h : x ∈ (G : Set X).toFinset <;>
        simp [h, inv_nonneg.mpr hcard.le]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']⟩

open Classical in
theorem uniformLift_coe (G : NonemptyCompacts X) :
    ((uniformLift G : ProbState X) : X → ℝ)
      = fun x => if x ∈ (G : Set X).toFinset
          then ((G : Set X).toFinset.card : ℝ)⁻¹ else 0 :=
  rfl

open Classical in
theorem uniformLift_apply_of_mem {G : NonemptyCompacts X} {x : X}
    (h : x ∈ G) :
    (uniformLift G : X → ℝ) x = ((G : Set X).toFinset.card : ℝ)⁻¹ := by
  have hx : x ∈ (G : Set X).toFinset := Set.mem_toFinset.mpr h
  simp only [uniformLift_coe]
  rw [if_pos hx]

open Classical in
theorem uniformLift_apply_of_not_mem {G : NonemptyCompacts X} {x : X}
    (h : x ∉ G) : (uniformLift G : X → ℝ) x = 0 := by
  have hx : x ∉ (G : Set X).toFinset := fun hc => h (Set.mem_toFinset.mp hc)
  simp only [uniformLift_coe]
  rw [if_neg hx]

open Classical in
/-- **Support equals graph** for the canonical lift: in discrete time
every stage has positive duration, so the lift loses nothing — the
finitary face of "support is the graph minus its zero-duration
stages". -/
theorem support_uniformLift_iff (G : NonemptyCompacts X) (x : X) :
    (uniformLift G : X → ℝ) x ≠ 0 ↔ x ∈ G := by
  by_cases h : x ∈ G
  · rw [uniformLift_apply_of_mem h]
    have hcard : (0 : ℝ) < (G : Set X).toFinset.card := by
      have hne : (G : Set X).toFinset.Nonempty :=
        Set.toFinset_nonempty.mpr G.nonempty
      exact_mod_cast Finset.card_pos.mpr hne
    simp only [h, iff_true]
    exact (inv_pos.mpr hcard).ne'
  · rw [uniformLift_apply_of_not_mem h]
    simp [h]

/-- Every graph, canonically lifted, is a lens point. -/
theorem uniformLift_mem_recordCon (G : NonemptyCompacts X) :
    (G, uniformLift G) ∈ recordCon :=
  fun x hx => (support_uniformLift_iff G x).mp hx

/-! ## The two wall species -/

open Classical in
/-- The touch-wall: hard violation when the graph meets the bad
region.  A graph-face penalty — zero-duration contact already
violates. -/
noncomputable def touchWall (Bad : Set X) :
    NonemptyCompacts X × ProbState X → ℝ≥0∞ :=
  fun p => if ((p.1 : Set X) ∩ Bad).Nonempty then ⊤ else 0

open Classical in
/-- The dwell-wall: hard violation when the occupation measure gives
the bad region positive mass.  A measure-face penalty —
supported-but-null visits are forgiven. -/
noncomputable def dwellWall (Bad : Set X) :
    NonemptyCompacts X × ProbState X → ℝ≥0∞ :=
  fun p => if ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0 then ⊤ else 0

/-- The dwell-wall's trigger is positive occupation mass: the support
form and the measure form agree, coordinates being nonnegative. -/
theorem dwellWall_trigger_iff (Bad : Set X) [DecidablePred (· ∈ Bad)]
    (p : NonemptyCompacts X × ProbState X) :
    (∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0)
      ↔ 0 < ∑ x ∈ Finset.univ.filter (· ∈ Bad), (p.2 : X → ℝ) x := by
  constructor
  · rintro ⟨x, hxB, hx0⟩
    refine Finset.sum_pos' (fun y _ => p.2.nonneg y) ⟨x, ?_, ?_⟩
    · simp [hxB]
    · exact (p.2.nonneg x).lt_of_ne (Ne.symm hx0)
  · intro hpos
    by_contra hno
    push Not at hno
    have hzero : ∑ x ∈ Finset.univ.filter (· ∈ Bad), (p.2 : X → ℝ) x = 0 :=
      Finset.sum_eq_zero fun x hx => hno x (Finset.mem_filter.mp hx).2
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos

/-- **The touch-wall is a lens citizen.**  Its trigger — the graph hits
the bad region — is open on the graph face; at the discrete stratum
every bad region is open, so the continuum polarity condition (bad
regions open, allowed regions closed) holds for free. -/
theorem lowerSemicontinuous_touchWall (Bad : Set X) :
    LowerSemicontinuous (touchWall (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : NonemptyCompacts X × ProbState X |
      ((p.1 : Set X) ∩ Bad).Nonempty}) ?_ ?_ ?_
  · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_discrete Bad)).preimage continuous_fst
  · intro p hp
    have hp' : ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWall]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ ((p.1 : Set X) ∩ Bad).Nonempty := hp
    simp only [touchWall]
    rw [if_neg hp']

/-- **The dwell-wall is a lens citizen.**  Its trigger — positive mass
on the bad region — is open on the measure face: a union of
coordinate-nonvanishing demands. -/
theorem lowerSemicontinuous_dwellWall (Bad : Set X) :
    LowerSemicontinuous (dwellWall (X := X) Bad) := by
  classical
  refine lowerSemicontinuous_wall_on_open
    (S := {p : NonemptyCompacts X × ProbState X |
      ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0}) ?_ ?_ ?_
  · have heq : {p : NonemptyCompacts X × ProbState X |
        ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0}
        = ⋃ x ∈ Bad, {p : NonemptyCompacts X × ProbState X |
            (p.2 : X → ℝ) x ≠ 0} := by
      ext p
      simp
    rw [heq]
    refine isOpen_biUnion fun x _ => ?_
    exact isOpen_ne.preimage
      (((continuous_apply x).comp continuous_subtype_val).comp continuous_snd)
  · intro p hp
    have hp' : ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0 := hp
    simp only [dwellWall]
    rw [if_pos hp']
  · intro p hp
    have hp' : ¬ ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0 := hp
    simp only [dwellWall]
    rw [if_neg hp']

/-- **The species separate on zero-dwell visits**: a lens point whose
graph touches the bad region with no occupation mass there violates
the touch-wall and satisfies the dwell-wall.  The universe carries
both species; the measure-zero ruling is made per clause. -/
theorem touch_dwell_separation [DecidableEq X] {x₀ x₁ : X} (h : x₀ ≠ x₁) :
    ∃ p ∈ recordCon (X := X),
      touchWall {x₀} p = ⊤ ∧ dwellWall {x₀} p = 0 := by
  classical
  refine ⟨(⟨⟨{x₀, x₁}, ((Set.finite_singleton x₁).insert x₀).isCompact⟩,
    ⟨x₀, Set.mem_insert _ _⟩⟩, ProbState.dirac x₁), ?_, ?_, ?_⟩
  · -- con: the point mass at `x₁` is carried by the graph
    intro x hx
    have hxx : x = x₁ := by
      by_contra hne
      exact hx (ProbState.dirac_apply_of_ne hne)
    subst hxx
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · -- the graph touches the bad region
    simp only [touchWall]
    rw [if_pos ⟨x₀, Set.mem_insert _ _, Set.mem_singleton _⟩]
  · -- the measure gives it no mass
    simp only [dwellWall]
    rw [if_neg]
    rintro ⟨x, hxB, hx0⟩
    rw [Set.mem_singleton_iff] at hxB
    subst hxB
    exact hx0 (ProbState.dirac_apply_of_ne h)

end SuFunctor.Universe
