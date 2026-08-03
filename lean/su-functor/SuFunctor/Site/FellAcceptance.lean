import SuFunctor.Site.FellWindow

/-! # Acceptance events on the record carrier: measurability by topology

A leg of the general battery program for the semantic universe: every
battery's undisplayed regularity pack — the `hmR`/`hmG` measurability
hypotheses that the discrete proofs *assume* of their region events —
restates over the Fell carrier as a theorem of the site's topology.
Region atoms are certified cells (closed box-unions, compact in the
state space); hit-events of compacts are Fell-closed, miss-events of
compacts Fell-open, hit-events of opens Fell-open, and confinement
events of closed walls Fell-closed — so under the Effros Borel
structure (`SuFunctor.Universe.FellMeasurable`) the acceptance events
are **measurable by the topology of the site rather than by
assumption**.

Three strata of content:

* **events and their algebra** — `hitEvent`, `missEvent`,
  `confinedEvent` on `FellCloseds α`, with the complementation and
  union laws.  The load-bearing algebraic fact is `hitEvent_iUnion`:
  hitting commutes with arbitrary unions in the set argument, which is
  the engine that turns countable set decompositions into countable
  event decompositions.
* **citizenship and measurability** — the four subbasic faces (open
  hit of an open, open miss of a compact, closed hit of a compact,
  closed miss of an open), the closed confinement face, their Borel
  corollaries, and the σ-compact extension: over a σ-compact ambient,
  hit-events of arbitrary *closed* sets are countable unions of closed
  hit-events, hence Borel.  Nothing here assumes Hausdorffness.
* **acceptance atoms as countable Boolean combinations** — the
  occupation-form Streett event (`streettEvent`: every requested pair
  answered), its infinitely-often-metered sibling (`streettIOEvent`,
  over a countable family of stage tails — the record-tier
  "arbitrarily late touch"), and the deadline-grid until event
  (`untilEvent`: some grid index at which the reach leg is hit and the
  avoid leg is missed).  Each is a countable Boolean combination of
  hit-events, and each measurability lemma consumes exactly the
  per-component tickets the citizenship layer issues.  The clocked
  instantiation shape is recorded at the corollaries: reach legs are
  closed (a `≤`-cut of stages times a closed target), avoid legs open
  (a `<`-cut times an open unsafe region) — and miss-events of opens
  are measurable with *no* compactness anywhere.

The FTraj corollaries at the bottom are the headline, cashed:
for a compact certified cell `R`, the visit event over a σ-compact
stage window is Borel (`measurableSet_hitEvent_univ_prod_of_isCompact`),
and for a closed safe region `D`, the confinement event — the safety
battery's acceptance event — is Borel over *every* window, with no
compactness and no σ-compactness (`measurableSet_confinedEvent_cylinder`).

Deliberately not claimed: the touch/dwell species fork and the metering
of "infinitely often" against occupation measure are the
adjustment legs' content (planned successors), not this module's — the
`streettIOEvent` here is the *touch*-species shadow at a declared
countable tail family, offered as measurability infrastructure for
whatever former the adjustment legs state.  Horizon typing (ticks
versus durations at clocked strata) likewise stays with the formers;
grid indices here are bare naturals.

Axiom probes at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx. -/

namespace SuFunctor

namespace Site

open SuFunctor.Universe

universe u

variable {α : Type*} [TopologicalSpace α]

/-! ## Events on the record carrier -/

/-- The hit event of a set: records meeting `A`. -/
def hitEvent (A : Set α) : Set (FellCloseds α) :=
  {F | ((F : Set α) ∩ A).Nonempty}

/-- The miss event of a set: records disjoint from `A`. -/
def missEvent (A : Set α) : Set (FellCloseds α) :=
  {F | Disjoint (F : Set α) A}

/-- The confinement event of a set: records contained in `A` — the
safety battery's acceptance event when `A` is the (cylinder over the)
safe region. -/
def confinedEvent (A : Set α) : Set (FellCloseds α) :=
  {F | (F : Set α) ⊆ A}

@[simp] theorem mem_hitEvent_iff {A : Set α} {F : FellCloseds α} :
    F ∈ hitEvent A ↔ ((F : Set α) ∩ A).Nonempty := Iff.rfl

@[simp] theorem mem_missEvent_iff {A : Set α} {F : FellCloseds α} :
    F ∈ missEvent A ↔ Disjoint (F : Set α) A := Iff.rfl

@[simp] theorem mem_confinedEvent_iff {A : Set α} {F : FellCloseds α} :
    F ∈ confinedEvent A ↔ (F : Set α) ⊆ A := Iff.rfl

/-! ## Event algebra -/

/-- Missing is not hitting. -/
theorem missEvent_eq_compl_hitEvent (A : Set α) :
    missEvent A = (hitEvent A)ᶜ := by
  ext F
  simp only [missEvent, hitEvent, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.disjoint_iff_inter_eq_empty, Set.not_nonempty_iff_eq_empty]

/-- Confinement is missing the complement. -/
theorem confinedEvent_eq_missEvent_compl (A : Set α) :
    confinedEvent A = missEvent Aᶜ := by
  ext F
  simp only [confinedEvent, missEvent, Set.mem_setOf_eq,
    Set.disjoint_left, Set.mem_compl_iff, not_not]
  exact Iff.rfl

theorem hitEvent_mono {A B : Set α} (h : A ⊆ B) :
    hitEvent A ⊆ hitEvent B :=
  fun _ ⟨x, hxF, hxA⟩ => ⟨x, hxF, h hxA⟩

/-- **Hitting commutes with unions in the set argument** — the engine
that turns countable set decompositions into countable event
decompositions.  Arbitrary index, pure set algebra. -/
theorem hitEvent_iUnion {ι : Sort*} (A : ι → Set α) :
    hitEvent (⋃ i, A i) = ⋃ i, hitEvent (A i) := by
  ext F
  simp only [hitEvent, Set.mem_setOf_eq, Set.mem_iUnion,
    Set.inter_iUnion, Set.nonempty_iUnion]

/-! ## Citizenship: the subbasic faces and the confinement face -/

/-- Hit events of open sets are Fell-open (the hit subbasis). -/
theorem isOpen_hitEvent {U : Set α} (hU : IsOpen U) :
    IsOpen (hitEvent U) :=
  FellCloseds.isOpen_inter_nonempty_of_isOpen hU

/-- Miss events of compact sets are Fell-open (the miss subbasis). -/
theorem isOpen_missEvent {K : Set α} (hK : IsCompact K) :
    IsOpen (missEvent K) :=
  FellCloseds.isOpen_disjoint_of_isCompact hK

/-- Hit events of compact sets are Fell-closed. -/
theorem isClosed_hitEvent {K : Set α} (hK : IsCompact K) :
    IsClosed (hitEvent K) :=
  FellCloseds.isClosed_inter_nonempty_of_isCompact hK

/-- Miss events of open sets are Fell-closed. -/
theorem isClosed_missEvent {U : Set α} (hU : IsOpen U) :
    IsClosed (missEvent U) := by
  rw [missEvent_eq_compl_hitEvent]
  exact (isOpen_hitEvent hU).isClosed_compl

/-- Confinement events of closed sets are Fell-closed — the safety
wall's citizenship, at every stratum, with no compactness anywhere. -/
theorem isClosed_confinedEvent {A : Set α} (hA : IsClosed A) :
    IsClosed (confinedEvent A) :=
  FellCloseds.isClosed_subsets_of_isClosed hA

/-! ## Effros measurability -/

theorem measurableSet_hitEvent_of_isOpen {U : Set α} (hU : IsOpen U) :
    MeasurableSet (hitEvent U) :=
  (isOpen_hitEvent hU).measurableSet

theorem measurableSet_hitEvent_of_isCompact {K : Set α}
    (hK : IsCompact K) : MeasurableSet (hitEvent K) :=
  (isClosed_hitEvent hK).measurableSet

theorem measurableSet_missEvent_of_isCompact {K : Set α}
    (hK : IsCompact K) : MeasurableSet (missEvent K) :=
  (isOpen_missEvent hK).measurableSet

theorem measurableSet_missEvent_of_isOpen {U : Set α} (hU : IsOpen U) :
    MeasurableSet (missEvent U) :=
  (isClosed_missEvent hU).measurableSet

/-- The safety acceptance event of a closed wall is Borel — no
compactness, no σ-compactness, no Hausdorffness. -/
theorem measurableSet_confinedEvent {A : Set α} (hA : IsClosed A) :
    MeasurableSet (confinedEvent A) :=
  (isClosed_confinedEvent hA).measurableSet

/-- Hit events pass countable unions of measurable pieces. -/
theorem measurableSet_hitEvent_iUnion {ι : Sort*} [Countable ι]
    {A : ι → Set α} (h : ∀ i, MeasurableSet (hitEvent (A i))) :
    MeasurableSet (hitEvent (⋃ i, A i)) := by
  rw [hitEvent_iUnion]
  exact MeasurableSet.iUnion h

/-- **The σ-compact extension**: over a σ-compact ambient, the hit
event of an arbitrary set decomposes as the countable union of its hit
events within the compact covering.  Pure covering algebra. -/
theorem hitEvent_eq_iUnion_inter_compactCovering [SigmaCompactSpace α]
    (A : Set α) :
    hitEvent A = ⋃ n, hitEvent (A ∩ compactCovering α n) := by
  calc hitEvent A
      = hitEvent (⋃ n, A ∩ compactCovering α n) := by
        rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    _ = ⋃ n, hitEvent (A ∩ compactCovering α n) := hitEvent_iUnion _

/-- Hit events of **closed** sets are Borel over a σ-compact ambient:
each covering piece is compact (closed ∩ compact), so the event is a
countable union of Fell-closed hit events. -/
theorem measurableSet_hitEvent_of_isClosed [SigmaCompactSpace α]
    {C : Set α} (hC : IsClosed C) : MeasurableSet (hitEvent C) := by
  rw [hitEvent_eq_iUnion_inter_compactCovering C]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_hitEvent_of_isCompact
      ((isCompact_compactCovering α n).inter_left hC)

/-- Miss events of closed sets are Borel over a σ-compact ambient. -/
theorem measurableSet_missEvent_of_isClosed [SigmaCompactSpace α]
    {C : Set α} (hC : IsClosed C) : MeasurableSet (missEvent C) := by
  rw [missEvent_eq_compl_hitEvent]
  exact (measurableSet_hitEvent_of_isClosed hC).compl

/-! ## Acceptance atoms as countable Boolean combinations -/

/-- The generic answered-pair event: for every listed pair, membership
of the first component's event forces membership of the second's.
`streettEvent` and `streettIOEvent` are its two instantiations. -/
def pairImpEvent (E : Set α → Set (FellCloseds α))
    (prs : List (Set α × Set α)) : Set (FellCloseds α) :=
  {F | ∀ pr ∈ prs, F ∈ E pr.1 → F ∈ E pr.2}

@[simp] theorem pairImpEvent_nil {E : Set α → Set (FellCloseds α)} :
    pairImpEvent E [] = Set.univ := by
  ext F
  simp [pairImpEvent]

theorem pairImpEvent_cons {E : Set α → Set (FellCloseds α)}
    {pr : Set α × Set α} {prs : List (Set α × Set α)} :
    pairImpEvent E (pr :: prs) =
      ((E pr.1)ᶜ ∪ E pr.2) ∩ pairImpEvent E prs := by
  ext F
  simp only [pairImpEvent, Set.mem_setOf_eq, List.mem_cons,
    Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  constructor
  · intro h
    exact ⟨imp_iff_not_or.mp (h pr (Or.inl rfl)),
      fun pr' hpr' => h pr' (Or.inr hpr')⟩
  · rintro ⟨hhd, htl⟩ pr' (rfl | hpr')
    · exact imp_iff_not_or.mpr hhd
    · exact htl pr' hpr'

/-- The answered-pair event is a finite Boolean combination of the
component events: measurable as soon as each listed component is. -/
theorem measurableSet_pairImpEvent {E : Set α → Set (FellCloseds α)}
    {prs : List (Set α × Set α)}
    (h : ∀ pr ∈ prs, MeasurableSet (E pr.1) ∧ MeasurableSet (E pr.2)) :
    MeasurableSet (pairImpEvent E prs) := by
  induction prs with
  | nil => rw [pairImpEvent_nil]; exact MeasurableSet.univ
  | cons pr tl ih =>
      rw [pairImpEvent_cons]
      have hpr := h pr (List.mem_cons.mpr (Or.inl rfl))
      exact (hpr.1.compl.union hpr.2).inter
        (ih fun pr' hpr' => h pr' (List.mem_cons_of_mem _ hpr'))

/-- **The occupation-form Streett event**: every requested pair is
answered — touching the request region forces touching the response
region.  The record-tier shadow of Streett acceptance, in the touch
species (the touch/dwell species fork is the
adjustment legs' content, not this module's). -/
def streettEvent (prs : List (Set α × Set α)) : Set (FellCloseds α) :=
  pairImpEvent hitEvent prs

theorem mem_streettEvent_iff {prs : List (Set α × Set α)}
    {F : FellCloseds α} :
    F ∈ streettEvent prs ↔ ∀ pr ∈ prs,
      ((F : Set α) ∩ pr.1).Nonempty → ((F : Set α) ∩ pr.2).Nonempty :=
  Iff.rfl

theorem measurableSet_streettEvent {prs : List (Set α × Set α)}
    (h : ∀ pr ∈ prs, MeasurableSet (hitEvent pr.1) ∧
      MeasurableSet (hitEvent pr.2)) :
    MeasurableSet (streettEvent prs) :=
  measurableSet_pairImpEvent h

/-- The Streett acceptance event over closed request/response regions
is Borel over a σ-compact ambient — the A8 discharge of the discrete
proofs' `hmR`/`hmG` pack at the record tier. -/
theorem measurableSet_streettEvent_of_isClosed [SigmaCompactSpace α]
    {prs : List (Set α × Set α)}
    (h : ∀ pr ∈ prs, IsClosed pr.1 ∧ IsClosed pr.2) :
    MeasurableSet (streettEvent prs) :=
  measurableSet_streettEvent fun pr hpr =>
    ⟨measurableSet_hitEvent_of_isClosed (h pr hpr).1,
      measurableSet_hitEvent_of_isClosed (h pr hpr).2⟩

/-- The infinitely-often shadow at a declared countable tail family:
the record touches `R` within **every** tail — "arbitrarily late
touches", read against whatever cofinal stage family the clocked
stratum declares.  A countable intersection of hit events. -/
def infOftenEvent (tail : ℕ → Set α) (R : Set α) :
    Set (FellCloseds α) :=
  ⋂ n, hitEvent (tail n ∩ R)

theorem mem_infOftenEvent_iff {tail : ℕ → Set α} {R : Set α}
    {F : FellCloseds α} :
    F ∈ infOftenEvent tail R ↔
      ∀ n, ((F : Set α) ∩ (tail n ∩ R)).Nonempty := by
  simp [infOftenEvent]

theorem measurableSet_infOftenEvent {tail : ℕ → Set α} {R : Set α}
    (h : ∀ n, MeasurableSet (hitEvent (tail n ∩ R))) :
    MeasurableSet (infOftenEvent tail R) :=
  MeasurableSet.iInter h

theorem measurableSet_infOftenEvent_of_isClosed [SigmaCompactSpace α]
    {tail : ℕ → Set α} {R : Set α} (htail : ∀ n, IsClosed (tail n))
    (hR : IsClosed R) : MeasurableSet (infOftenEvent tail R) :=
  measurableSet_infOftenEvent fun n =>
    measurableSet_hitEvent_of_isClosed ((htail n).inter hR)

/-- The infinitely-often-metered Streett event: every pair whose
request region is touched within every tail has its response region
touched within every tail. -/
def streettIOEvent (tail : ℕ → Set α) (prs : List (Set α × Set α)) :
    Set (FellCloseds α) :=
  pairImpEvent (infOftenEvent tail) prs

theorem measurableSet_streettIOEvent {tail : ℕ → Set α}
    {prs : List (Set α × Set α)}
    (h : ∀ pr ∈ prs, MeasurableSet (infOftenEvent tail pr.1) ∧
      MeasurableSet (infOftenEvent tail pr.2)) :
    MeasurableSet (streettIOEvent tail prs) :=
  measurableSet_pairImpEvent h

theorem measurableSet_streettIOEvent_of_isClosed [SigmaCompactSpace α]
    {tail : ℕ → Set α} {prs : List (Set α × Set α)}
    (htail : ∀ n, IsClosed (tail n))
    (h : ∀ pr ∈ prs, IsClosed pr.1 ∧ IsClosed pr.2) :
    MeasurableSet (streettIOEvent tail prs) :=
  measurableSet_streettIOEvent fun pr hpr =>
    ⟨measurableSet_infOftenEvent_of_isClosed htail (h pr hpr).1,
      measurableSet_infOftenEvent_of_isClosed htail (h pr hpr).2⟩

/-- **The deadline-grid until event**: at some grid index, the reach
leg is hit and the avoid leg is missed.  The countable-combination
skeleton of safety-until-a-deadline at the record tier: the clocked
instantiation takes `Reach n` = (stages ≤ nth cut) × target and
`Avoid n` = (stages < nth cut) × unsafe. -/
def untilEvent (Reach Avoid : ℕ → Set α) : Set (FellCloseds α) :=
  ⋃ n, hitEvent (Reach n) ∩ missEvent (Avoid n)

theorem mem_untilEvent_iff {Reach Avoid : ℕ → Set α}
    {F : FellCloseds α} :
    F ∈ untilEvent Reach Avoid ↔
      ∃ n, ((F : Set α) ∩ Reach n).Nonempty ∧
        Disjoint (F : Set α) (Avoid n) := by
  simp [untilEvent, hitEvent, missEvent]

theorem measurableSet_untilEvent {Reach Avoid : ℕ → Set α}
    (h₁ : ∀ n, MeasurableSet (hitEvent (Reach n)))
    (h₂ : ∀ n, MeasurableSet (missEvent (Avoid n))) :
    MeasurableSet (untilEvent Reach Avoid) :=
  MeasurableSet.iUnion fun n => (h₁ n).inter (h₂ n)

/-- The clocked until shape: closed reach legs (a `≤`-cut of stages
times a closed target), open avoid legs (a `<`-cut times an open
unsafe region).  The avoid legs' measurability costs nothing at all —
miss events of opens are Fell-closed at every stratum. -/
theorem measurableSet_untilEvent_of_isClosed_isOpen [SigmaCompactSpace α]
    {Reach Avoid : ℕ → Set α} (h₁ : ∀ n, IsClosed (Reach n))
    (h₂ : ∀ n, IsOpen (Avoid n)) :
    MeasurableSet (untilEvent Reach Avoid) :=
  measurableSet_untilEvent
    (fun n => measurableSet_hitEvent_of_isClosed (h₁ n))
    (fun n => measurableSet_missEvent_of_isOpen (h₂ n))

/-! ## The certified-cell face: cylinders over trajectory windows -/

section FTraj

variable {T : Type u} [TopologicalSpace T] {W : Set T}
  {X : Type u} [TopologicalSpace X]

/-- Visits to a compact cell within a compact stage set: a Fell-closed
event, no σ-compactness needed. -/
theorem measurableSet_visitEvent_of_isCompact {S : Set ↥W} {R : Set X}
    (hS : IsCompact S) (hR : IsCompact R) :
    MeasurableSet (hitEvent (S ×ˢ R) : Set (FTraj W X)) :=
  measurableSet_hitEvent_of_isCompact (hS.prod hR)

/-- Visits to a closed region within a closed stage set, over a
σ-compact window-state product. -/
theorem measurableSet_visitEvent_of_isClosed
    [SigmaCompactSpace (↥W × X)] {S : Set ↥W} {R : Set X}
    (hS : IsClosed S) (hR : IsClosed R) :
    MeasurableSet (hitEvent (S ×ˢ R) : Set (FTraj W X)) :=
  measurableSet_hitEvent_of_isClosed (hS.prod hR)

/-- **Hit-events of certified cells are Effros-measurable for free**
(the memo's headline, cashed): a compact cell's visit event over a
σ-compact stage window is a countable union of Fell-closed hit
events. -/
theorem measurableSet_hitEvent_univ_prod_of_isCompact
    [SigmaCompactSpace ↥W] {R : Set X} (hR : IsCompact R) :
    MeasurableSet
      (hitEvent ((Set.univ : Set ↥W) ×ˢ R) : Set (FTraj W X)) := by
  have h : (Set.univ : Set ↥W) ×ˢ R
      = ⋃ n, compactCovering ↥W n ×ˢ R := by
    rw [← Set.iUnion_prod_const, iUnion_compactCovering]
  rw [h, hitEvent_iUnion]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_hitEvent_of_isCompact
      ((isCompact_compactCovering ↥W n).prod hR)

/-- **The safety acceptance event is Borel over every window**: the
confinement event of a closed safe region's cylinder, with no
compactness and no σ-compactness — the A8 discharge of the safety
battery's measurability pack. -/
theorem measurableSet_confinedEvent_cylinder {D : Set X}
    (hD : IsClosed D) :
    MeasurableSet
      (confinedEvent ((Set.univ : Set ↥W) ×ˢ D) : Set (FTraj W X)) :=
  measurableSet_confinedEvent (isClosed_univ.prod hD)

end FTraj

end Site

end SuFunctor

#print axioms SuFunctor.Site.hitEvent_iUnion
#print axioms SuFunctor.Site.measurableSet_confinedEvent
#print axioms SuFunctor.Site.measurableSet_hitEvent_of_isClosed
#print axioms SuFunctor.Site.measurableSet_streettEvent_of_isClosed
#print axioms SuFunctor.Site.measurableSet_streettIOEvent_of_isClosed
#print axioms SuFunctor.Site.measurableSet_untilEvent_of_isClosed_isOpen
#print axioms SuFunctor.Site.measurableSet_hitEvent_univ_prod_of_isCompact
#print axioms SuFunctor.Site.measurableSet_confinedEvent_cylinder
