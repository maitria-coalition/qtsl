import SuFunctor.Spacetime.Walls

/-! # The hybrid-time pattern: the assumption slot is the realization class

The composition pattern that discharges multi-clock composition in
practice — put the discrete component's tick on a timer mechanism,
prove the component's rows schedule-generically, and carry the
schedule class (period bounds, jitter bracket) in the *assumption
slot* of the composition square.

This module states what that prose slot **is**, semantically, and it is
not a new construction: it is the clock's own admissible-realization
class.  A `SpacetimeClock` is a site (windows and their observation
points) *plus* a realization class per window, and the pinned and
jittered tick clocks of the base module are **one site with two
realization classes** (`tickSite_pinned_eq_jittered`, a `rfl`).  So
declaring a schedule assumption does not change what the component
observes; it changes only which realizations are admissible.  Three
consequences, proved below:

* **Schedule-genericity transports** (`scheduleGeneric_transport`): a
  component whose spec does not read the realization component of its
  records satisfies the coarse spec across any clock morphism whose
  window map is the identity — the semantic face of "prove the rows
  per-tick, in the component's own counter".
* **Jitter is a relaxation, priced at the wall**
  (`pinnedWall_le_jitteredWall`): relaxing the assumption slot from the
  pinned realization class to the jittered one weakens the seam's wall
  monotonically.  The certified tick premium measured at the valuation
  layer is therefore the price of *this* relaxation, not of a different
  pattern.
* **The refusal has semantic bite**
  (`exists_double_schedule_strictly_stronger`): the pattern admits at
  most one schedule assumption per component, and silently conjoining
  two would change the composite's meaning — the refusal is content,
  not bookkeeping.
* **The composition square itself** (`hybridTime_square_subset`,
  `hybridTime_square_eq_of_graph`, `tickSeam_hybridTime_square_eq`,
  `exists_hybridTime_square_strict`): the component's rows enter the
  composite either *compiled* — read at the carried coarse-port
  record of the seam-walled presentation — or *per-tick* — the usual
  component semantics read back through the declared clock morphism.
  The per-tick reading always entails the compiled one; when the
  transport relation is a function graph the two walled model classes
  coincide (the tick seam's pinned slot is such a graph, so the
  chapter's square closes as an equality, for every rows predicate);
  and a seam whose *coarse* realization class is jittered and read by
  the sample-point inclusion separates them strictly, with
  schedule-generic rows — the demonic choice of *which restriction
  the counter saw* is priced by the assumption slot and closed by
  nothing else: genericity is blind to the realization tag, while the
  gap lives in the realization-dependent reading.  Without the seam's
  wall row the two readings are incomparable outright
  (`exists_unwalled_square_fails`).

Both assumption slots are proper (`exists_pinnedSeam_wall_eq_zero`
beside the landed jittered witness): neither silently yields the
vacuous composite.

Everything here is order-theoretic instantiation over the landed site
storey.  In particular the pattern stays **spatial**: the clock is
object data on wires (records carry their own window and realization),
so the seam is one more wall conjunct on the joint carrier rather than
a reparametrization of time.  That is why this square exists while the
mode-switching pattern's temporal square is a priced obstruction.
-/

namespace SuFunctor

open scoped ENNReal

open Plain Universe

universe u

/-! ## Indicator-wall bridge lemmas (exact stratum) -/

namespace Plain

variable {X : Type u}

/-- Credal sets of intersections are intersections of credal sets. -/
theorem suppIn_inter {B C : Set X} :
    suppIn (B ∩ C) = suppIn B ∩ suppIn C := by
  ext μ
  simp only [mem_suppIn, Set.mem_inter_iff]
  exact Set.subset_inter_iff

/-- Conjoining two indicator walls is the indicator wall of the meet:
two more conjuncts are one wall on the intersected region. -/
theorem possWall_sup {B C : Set X} :
    possWall B ⊔ possWall C = possWall (B ∩ C) := by
  funext μ
  by_cases hB : μ ∈ suppIn B
  · by_cases hC : μ ∈ suppIn C
    · have hBC : μ ∈ suppIn (B ∩ C) := by
        rw [suppIn_inter]
        exact ⟨hB, hC⟩
      rw [Pi.sup_apply, possWall_apply_of_mem hB, possWall_apply_of_mem hC,
        possWall_apply_of_mem hBC, sup_idem]
    · have hBC : μ ∉ suppIn (B ∩ C) := by
        rw [suppIn_inter]
        exact fun h => hC h.2
      rw [Pi.sup_apply, possWall_apply_of_mem hB, possWall_apply_of_notMem hC,
        possWall_apply_of_notMem hBC, sup_top_eq]
  · have hBC : μ ∉ suppIn (B ∩ C) := by
      rw [suppIn_inter]
      exact fun h => hB h.1
    rw [Pi.sup_apply, possWall_apply_of_notMem hB,
      possWall_apply_of_notMem hBC, top_sup_eq]

end Plain

namespace Spacetime

/-! ## The assumption slot, exhibited -/

/-- The pinned and jittered tick clocks share their site on the nose:
a schedule assumption changes the admissible realizations, never the
observation structure.  The `rfl` is the content — this is what makes
"one value function, one cover, both time semantics" available at all.
-/
theorem tickSite_pinned_eq_jittered :
    (pinnedTickClock.{u}).site = (jitteredTickClock.{u}).site := rfl

/-- The pinned realization class is a point: the zero-jitter grid
admits exactly one realization per window. -/
theorem pinnedTickClock_real (w : (pinnedTickClock.{u}).site.Window) :
    (pinnedTickClock.{u}).Real w = PUnit := rfl

/-- The two clocks are nonetheless distinct objects: the jittered
realization class is not a point.  (Witness: two jitter choices over a
one-point window that differ at the sole sample point.) -/
theorem jitteredTickClock_real_nontrivial :
    ∃ (w : (jitteredTickClock.{u}).site.Window)
      (θ θ' : (jitteredTickClock.{u}).Real w), θ ≠ θ' := by
  refine ⟨⟨(0, 0)⟩, fun _ => ⟨0⟩, fun _ => ⟨1⟩, ?_⟩
  intro h
  exact absurd (congrArg ULift.down (congrFun h ⟨0⟩)) (by decide)

/-! ## Schedule-genericity

A spec over realized records is *schedule-generic* when it does not
read the realization component: it constrains the window and the
observation history only.  This is the semantic form of "prove the
component's rows per-tick, in its own counter". -/

section Generic

variable {c : SpacetimeClock.{u}} {X : Type u}

/-- A predicate on realized records is **schedule-generic** when it is
blind to the realization component. -/
def ScheduleGeneric (P : SpacetimeRec c X → Prop) : Prop :=
  ∀ (w : c.site.Window) (θ θ' : c.Real w) (x : c.site.pts w → X),
    P ⟨w, θ, x⟩ → P ⟨w, θ', x⟩

/-- Schedule-generic predicates are exactly those factoring through the
realization-forgetting data.  (Left-to-right is the definition read at
a chosen realization; right-to-left is immediate.) -/
theorem scheduleGeneric_iff {P : SpacetimeRec c X → Prop} :
    ScheduleGeneric P ↔
      ∀ (r r' : SpacetimeRec c X), r.w = r'.w →
        (∀ h : r.w = r'.w, h ▸ r.x = r'.x) → (P r ↔ P r') := by
  constructor
  · intro hP r r' hw hx
    obtain ⟨w, θ, x⟩ := r
    obtain ⟨w', θ', x'⟩ := r'
    cases hw
    have : x = x' := hx rfl
    cases this
    exact ⟨fun h => hP _ _ _ _ h, fun h => hP _ _ _ _ h⟩
  · intro h w θ θ' x hP
    exact (h ⟨w, θ, x⟩ ⟨w, θ', x⟩ rfl (fun _ => rfl)).mp hP

/-- **Schedule-genericity transports across an identity-window clock
morphism.**  If the coarse spec is blind to realizations and the
morphism keeps the window fixed, then every fine record transport-
related to a coarse record satisfying the spec has its own coarse
reading satisfy it — the observation history is the one the morphism
carries, and the realization it rode is exactly what the spec ignores.

This is the pattern's core move: the component's rows, proved once
per-tick, hold under every admissible realization the assumption slot
permits. -/
theorem scheduleGeneric_transport {S : SpacetimeSite.{u}}
    {R R' : S.Window → Type u}
    (φ : SpacetimeClockHom (⟨S, R⟩ : SpacetimeClock.{u}) ⟨S, R'⟩)
    (hw : ∀ w, φ.wmap w = w)
    {P : SpacetimeRec (⟨S, R⟩ : SpacetimeClock.{u}) X → Prop}
    (hP : ScheduleGeneric P)
    {rf : SpacetimeRec (⟨S, R'⟩ : SpacetimeClock.{u}) X}
    {rc : SpacetimeRec (⟨S, R⟩ : SpacetimeClock.{u}) X}
    (hrel : φ.transportRel X rf rc) (hc : P rc) :
    rf.w = rc.w ∧ ∀ θ : R rc.w, P ⟨rc.w, θ, rc.x⟩ := by
  obtain ⟨θ', x', -, -, hrf⟩ := hrel
  refine ⟨by rw [hrf]; exact hw rc.w, ?_⟩
  obtain ⟨w, θ, x⟩ := rc
  intro θ''
  exact hP w θ θ'' x hc

end Generic

/-! ## Jitter as a relaxation of the assumption slot

The tick seam's morphism (`tickSeamHom`) goes pinned into jittered over
the shared site with every co-realization admissible.  Two readings of
the seam differ only in the *coarse* clock's realization class, and the
wall is antitone in its support set — so relaxing the slot weakens the
wall. -/

section Relaxation

variable {W P : Type u}

/-- **Wall relaxation, generically**: if one declared seam's admissible
set is contained in another's, the tighter seam's wall dominates.  The
assumption slot enters the composite's presentation only through this
inclusion. -/
theorem sampleWireWall_antitone {κ : ULift.{u} Bool → SpacetimeClock.{u}}
    {X : Type u} {ports : P → W × W} {i i' : ULift.{u} Bool}
    {φ ψ : SpacetimeClockHom (κ i) (κ i')}
    (h : sampleWireSet κ X ports i i' φ ⊆ sampleWireSet κ X ports i i' ψ) :
    sampleWireWall κ X ports i i' ψ ≤ sampleWireWall κ X ports i i' φ :=
  possWall_antitone h

/-- A tick-seam morphism with the jitter class restricted to the
pinned co-realizations only: the *tight* assumption slot.  (Same window
map and inclusion as `tickSeamHom`; only the admissible co-realization
class shrinks — to the constant-zero jitter.) -/
def tickSeamHomPinned :
    SpacetimeClockHom (tickClkOf.{u} ⟨false⟩) (tickClkOf.{u} ⟨true⟩) where
  wmap := id
  jitter w := {p | p.2 = fun _ => ⟨0⟩}
  emb _ _ _ := id

/-- The tight slot's admissible set sits inside the relaxed slot's:
declaring zero jitter permits strictly fewer co-realizations. -/
theorem pinnedSeamSet_subset_tickSeamSet :
    sampleWireSet tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned ⊆
      sampleWireSet tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom := by
  rintro x ⟨w, θ, θ', -, hport⟩
  exact ⟨w, θ, θ', Set.mem_univ _, hport⟩

/-- **Jitter is a relaxation, priced at the wall.**  Relaxing the
assumption slot from the pinned realization class to the jittered one
weakens the seam's wall: the pinned wall dominates.  The certified tick
premium is the valuation-layer price of exactly this order relation —
the same pattern, a weaker assumption, a weaker wall. -/
theorem pinnedWall_le_jitteredWall :
    sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom ≤
      sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned :=
  possWall_antitone pinnedSeamSet_subset_tickSeamSet

/-- **Relaxation weakens the composite, at the presentation tier**:
every model of the tightly-walled presentation models the relaxed one.
Wall weakening along the assumption slot. -/
theorem pinnedWalled_modelClass_subset
    (D : SpecDnf (Joint (ULift.{u} Bool →
      ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1})))) :
    (D.withWall (sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts
        ⟨false⟩ ⟨true⟩ tickSeamHomPinned)).modelClass ⊆
      (D.withWall (sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts
        ⟨false⟩ ⟨true⟩ tickSeamHom)).modelClass :=
  SpecDnf.withWall_modelClass_antitone pinnedWall_le_jitteredWall D

end Relaxation

/-! ## Properness under either assumption slot -/

/-- The pinned seam admits the zero-jitter state: the tight slot is
satisfiable. -/
theorem tickSeamState_mem_pinned :
    tickSeamState.{u} ∈
      sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned :=
  ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => ⟨0⟩, rfl,
    fun _ => ⟨fun _ => PUnit.unit, rfl, rfl⟩⟩

/-- **Properness of the tight assumption slot**: the pinned seam's wall
admits a supported joint, so declaring zero jitter does not silently
yield the vacuous composite.  (Its relaxed sibling is the landed
`exists_tickSeam_wall_eq_zero`; both slots are proper.) -/
theorem exists_pinnedSeam_wall_eq_zero :
    ∃ μ, sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned μ = 0 :=
  ⟨Joint.dirac tickSeamState,
    possWall_apply_of_mem (Joint.dirac_mem_suppIn tickSeamState_mem_pinned)⟩

/-! ## At most one assumption per component

The pattern refuses a duplicate schedule declaration on one component.
That refusal is semantic content: two distinct slots' walls have a
strictly stronger meet, so silently conjoining them would change the
composite's meaning rather than merely duplicating a row. -/

/-- A jittered state the *tight* slot refuses: the fine port rides a
nonzero jitter realization.  (Admissible under the relaxed slot, by
`tickSeamState_mem`'s sibling construction.) -/
def tickJitteredState :
    ULift.{u} Bool → ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1}) :=
  fun v => cond v.down
    ⟨⟨true⟩, ⟨⟨(0, 0)⟩, fun _ => ⟨1⟩, fun _ => PUnit.unit⟩⟩
    ⟨⟨false⟩, ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => PUnit.unit⟩⟩

theorem tickJitteredState_mem_relaxed :
    tickJitteredState.{u} ∈
      sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom :=
  ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => ⟨1⟩, Set.mem_univ _,
    fun _ => ⟨fun _ => PUnit.unit, rfl, rfl⟩⟩

theorem tickJitteredState_notMem_pinned :
    tickJitteredState.{u} ∉
      sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned := by
  rintro ⟨w, θ, θ', hJ, hport⟩
  obtain ⟨x', -, hf⟩ := hport PUnit.unit
  -- `hJ` is the tight slot's demand: the fine realization is jitter-0.
  have hz : θ' = fun _ => ⟨0⟩ := hJ
  -- `hf` pins the fine port's record, whose realization is jitter-1.
  have hf' : (⟨⟨true⟩, ⟨⟨(0, 0)⟩, fun _ => ⟨1⟩, fun _ => PUnit.unit⟩⟩ :
      ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1})) =
      ⟨⟨true⟩, ⟨w, θ', x'⟩⟩ := hf
  injection hf' with _ h2
  have hrec : (⟨⟨(0, 0)⟩, fun _ => ⟨1⟩, fun _ => PUnit.unit⟩ :
      SpacetimeRec (tickClkOf.{u} ⟨true⟩) PUnit.{u + 1}) = ⟨w, θ', x'⟩ := h2
  injection hrec with hw hθ _
  subst hw
  have hone : θ' = fun _ => ⟨1⟩ := (eq_of_heq hθ).symm
  rw [hz] at hone
  exact absurd (congrArg (fun f => (f ⟨0⟩).down) hone) (by decide)

/-- **The refusal has semantic bite**: two distinct schedule
assumptions on the same component pair do not merely duplicate a row —
their walls differ, so conjoining them silently would strengthen the
composite.  Witness: the jittered state, permitted by the relaxed slot
and refused by the tight one, is exactly a model separated by the two
declarations.  This is why the pattern refuses a duplicate declaration
with both serialized rather than absorbing it. -/
theorem exists_double_schedule_strictly_stronger :
    ∃ x : ULift.{u} Bool →
        ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1}),
      x ∈ sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
          tickSeamHom ∧
      x ∉ sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
          tickSeamHomPinned :=
  ⟨tickJitteredState, tickJitteredState_mem_relaxed,
    tickJitteredState_notMem_pinned⟩

/-- The wall separation, read at the penalty tier: the tight slot's
wall is *strictly* above the relaxed one somewhere — the two
declarations present genuinely different composites. -/
theorem pinnedWall_strictly_above :
    ∃ μ, sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom μ <
      sampleWireWall tickClkOf.{u} PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHomPinned μ := by
  refine ⟨Joint.dirac tickJitteredState, ?_⟩
  unfold sampleWireWall
  rw [possWall_apply_of_mem
      (Joint.dirac_mem_suppIn tickJitteredState_mem_relaxed),
    possWall_apply_of_notMem
      (fun hmem => tickJitteredState_notMem_pinned
        (Joint.mem_of_dirac_mem_suppIn hmem))]
  exact ENNReal.zero_lt_top

/-! ## The hybrid-time square

The pattern's composition square, at the model-class tier.  The
component's rows — proved per-tick, in its own counter — enter the
composite in two ways: **compiled**, as the carried coarse-port
records of the seam-walled presentation (the timer declaration plus
the rows as one more pure-safety conjunct), or **per-tick**, as the
usual component semantics read back through the declared clock
morphism — every transported reading of the fine record satisfies
the rows, so the square's "include" is the transport relation
itself.

The per-tick reading always entails the compiled one
(`hybridTime_square_subset`: on the seam's support the carried coarse
record *is* a transported reading), and the two agree exactly when
the transport relation is the graph of a function
(`hybridTime_square_eq_of_graph`).  The tick seam is such a graph
(`tickSeam_transport_eq`) — its coarse clock is pinned — so the
square closes as an equality there
(`tickSeam_hybridTime_square_eq`), for *every* rows predicate.  The
demonic seam below (coarse realization class jittered, sample-point
inclusion reading it) separates the readings with schedule-generic
rows: strictly at the region tier (`exists_demonic_gap`), the wall
tier (`demonicWall_strictly_above`), and the model-class tier
(`exists_hybridTime_square_strict`).  One value function, one cover,
both time semantics — with the price of jitter carried by the
assumption slot, certified rather than assumed. -/

section HybridSquare

variable {Clk : Type u} (κ : Clk → SpacetimeClock.{u}) (X : Type u)
variable {W P : Type u} (ports : P → W × W) (i i' : Clk)
variable (φ : SpacetimeClockHom (κ i) (κ i'))
variable (Pc : SpacetimeRec (κ i) X → Prop)

/-- The **compiled reading** of the component's rows: the states whose
coarse-port records satisfy them — the rows read at the carried
record, as the composite presentation's row conjunct.  (Vacuous off
the coarse clock's tag: pinning the tag is the seam wall's content,
kept in its own conjunct.) -/
def coarseRowsSet : Set (W → ClockedEl Clk (SiteRec κ X)) :=
  {x | ∀ p : P, ∀ rc : SpacetimeRec (κ i) X, x (ports p).2 = ⟨i, rc⟩ → Pc rc}

/-- The **per-tick reading** of the component's rows: the states whose
fine-port records satisfy them at *every* transported coarse reading —
the component's usual semantics, read back through the declared clock
morphism.  Which restriction of the fine history the component's
counter saw is quantified demonically. -/
def perTickRowsSet : Set (W → ClockedEl Clk (SiteRec κ X)) :=
  {x | ∀ p : P, ∀ rf : SpacetimeRec (κ i') X, x (ports p).1 = ⟨i', rf⟩ →
    ∀ rc : SpacetimeRec (κ i) X, φ.transportRel X rf rc → Pc rc}

/-- On the seam's support the per-tick reading entails the compiled
one: the carried coarse record is itself a transported reading of the
fine record.  No genericity and no pinnedness is consumed — this
direction of the square is unconditional. -/
theorem seam_perTickRows_subset_coarseRows :
    sampleWireSet κ X ports i i' φ ∩ perTickRowsSet κ X ports i i' φ Pc ⊆
      coarseRowsSet κ X ports i Pc := by
  rintro x ⟨hsup, hrows⟩ p rc hrc
  obtain ⟨rf₀, rc₀, hf₀, hc₀, hrel₀⟩ :=
    sampleWireSet_ports_transport κ X hsup p
  have h := hc₀.symm.trans hrc
  injection h with _ h2
  exact h2 ▸ hrows p rf₀ hf₀ rc₀ hrel₀

/-- When the transport relation is the graph of a function, the
compiled reading conversely entails the per-tick one on the seam's
support: the carried coarse record is the *only* transported
reading. -/
theorem seam_coarseRows_subset_perTickRows_of_graph
    (hgraph : ∀ (rf : SpacetimeRec (κ i') X)
      (rc rc' : SpacetimeRec (κ i) X),
      φ.transportRel X rf rc → φ.transportRel X rf rc' → rc = rc') :
    sampleWireSet κ X ports i i' φ ∩ coarseRowsSet κ X ports i Pc ⊆
      perTickRowsSet κ X ports i i' φ Pc := by
  rintro x ⟨hsup, hrows⟩ p rf hrf rc hrel
  obtain ⟨rf₀, rc₀, hf₀, hc₀, hrel₀⟩ :=
    sampleWireSet_ports_transport κ X hsup p
  have h := hrf.symm.trans hf₀
  injection h with _ h2
  have hcc : rc = rc₀ := hgraph rf₀ rc rc₀ (h2 ▸ hrel) hrel₀
  exact hcc.symm ▸ hrows p rc₀ hc₀

/-- Wall-tier monotonicity of the seam-walled composite: if one row
region entails another on the seam's support, the walled model
classes compare.  The comparison consumes the seam's wall row — the
two readings are incomparable without it
(`exists_unwalled_square_fails`). -/
theorem seamWalled_modelClass_mono
    {B C : Set (W → ClockedEl Clk (SiteRec κ X))}
    (h : sampleWireSet κ X ports i i' φ ∩ B ⊆ C)
    (D : SpecDnf (Joint (W → ClockedEl Clk (SiteRec κ X)))) :
    ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall B)).modelClass ⊆
      ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall C)).modelClass := by
  intro σ hσ
  rw [SpecDnf.mem_modelClass_withWall] at hσ ⊢
  refine ⟨?_, hσ.2⟩
  have hseam : possWall (sampleWireSet κ X ports i i' φ) ≤ σ :=
    (SpecDnf.mem_modelClass_withWall.mp hσ.2).1
  have hB : possWall B ≤ σ := hσ.1
  rw [possWall_le_iff]
  intro μ hμ
  have hnot : μ ∉ suppIn (sampleWireSet κ X ports i i' φ ∩ B) :=
    fun hmem => hμ (suppIn_mono h hmem)
  rw [suppIn_inter, Set.mem_inter_iff] at hnot
  rcases not_and_or.mp hnot with hn | hn
  · exact possWall_le_iff.mp hseam μ hn
  · exact possWall_le_iff.mp hB μ hn

/-- **The hybrid-time square, lax face** (any declared clock
morphism): every model of the seam-walled presentation carrying the
per-tick conjunct models it carrying the compiled conjunct — the
walled composite is the weaker spec, so the demonic reading is
bounded by the assumption slot, never smuggled. -/
theorem hybridTime_square_subset
    (D : SpecDnf (Joint (W → ClockedEl Clk (SiteRec κ X)))) :
    ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall (perTickRowsSet κ X ports i i' φ Pc))).modelClass ⊆
      ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall (coarseRowsSet κ X ports i Pc))).modelClass :=
  seamWalled_modelClass_mono κ X ports i i' φ
    (seam_perTickRows_subset_coarseRows κ X ports i i' φ Pc) D

/-- **The hybrid-time square, equality face**: when the transport
relation is a function graph — one transported reading per fine
record — compile-then-denote and per-tick-then-include agree exactly,
for every residual component presentation. -/
theorem hybridTime_square_eq_of_graph
    (hgraph : ∀ (rf : SpacetimeRec (κ i') X)
      (rc rc' : SpacetimeRec (κ i) X),
      φ.transportRel X rf rc → φ.transportRel X rf rc' → rc = rc')
    (D : SpecDnf (Joint (W → ClockedEl Clk (SiteRec κ X)))) :
    ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall (perTickRowsSet κ X ports i i' φ Pc))).modelClass =
      ((D.withWall (sampleWireWall κ X ports i i' φ)).withWall
        (possWall (coarseRowsSet κ X ports i Pc))).modelClass :=
  Set.Subset.antisymm
    (hybridTime_square_subset κ X ports i i' φ Pc D)
    (seamWalled_modelClass_mono κ X ports i i' φ
      (seam_coarseRows_subset_perTickRows_of_graph κ X ports i i' φ Pc
        hgraph) D)

end HybridSquare

/-! ## The square at the tick seam: the pinned slot closes it -/

/-- The tick seam's transport relation is the graph of a function: the
coarse clock is pinned, so a fine record has exactly one transported
reading — its own history at the shared window.  This is what the
pinned assumption slot buys. -/
theorem tickSeam_transport_eq {X : Type u}
    {rf : SpacetimeRec (tickClkOf.{u} ⟨true⟩) X}
    {rc : SpacetimeRec (tickClkOf.{u} ⟨false⟩) X}
    (h : tickSeamHom.transportRel X rf rc) :
    rc = ⟨rf.w, PUnit.unit, rf.x⟩ := by
  obtain ⟨θ', x', -, hx, hrf⟩ := h
  subst hrf
  exact congrArg
    (fun t => (⟨rc.w, PUnit.unit, t⟩ :
      SpacetimeRec (tickClkOf.{u} ⟨false⟩) X))
    (show rc.x = x' from hx)

/-- The tick seam's transport is single-valued: the uniqueness the
equality face of the square consumes. -/
theorem tickSeam_transport_graph {X : Type u}
    (rf : SpacetimeRec (tickClkOf.{u} ⟨true⟩) X)
    (rc rc' : SpacetimeRec (tickClkOf.{u} ⟨false⟩) X)
    (h : tickSeamHom.transportRel X rf rc)
    (h' : tickSeamHom.transportRel X rf rc') : rc = rc' :=
  (tickSeam_transport_eq h).trans (tickSeam_transport_eq h').symm

/-- **The hybrid-time square closes as an equality at the tick seam**:
under the pinned assumption slot, compile-then-denote *is*
per-tick-then-include — one value function, one cover, both time
semantics.  For every rows predicate: the pinned slot needs no
genericity to close the square (genericity's job is transporting the
rows across the morphism, not comparing the two readings). -/
theorem tickSeam_hybridTime_square_eq {X : Type u}
    (Pc : SpacetimeRec (tickClkOf.{u} ⟨false⟩) X → Prop)
    (D : SpecDnf (Joint (ULift.{u} Bool →
      ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf X)))) :
    ((D.withWall (sampleWireWall tickClkOf X tickPorts ⟨false⟩ ⟨true⟩
          tickSeamHom)).withWall
        (possWall (perTickRowsSet tickClkOf X tickPorts ⟨false⟩ ⟨true⟩
          tickSeamHom Pc))).modelClass =
      ((D.withWall (sampleWireWall tickClkOf X tickPorts ⟨false⟩ ⟨true⟩
          tickSeamHom)).withWall
        (possWall (coarseRowsSet tickClkOf X tickPorts ⟨false⟩
          Pc))).modelClass :=
  hybridTime_square_eq_of_graph tickClkOf X tickPorts ⟨false⟩ ⟨true⟩
    tickSeamHom Pc tickSeam_transport_graph D

/-! ## The demonic instance: a jittered slot separates the readings

The gap the pinned slot closes, exhibited open: a seam whose *coarse*
realization class is jittered and whose sample-point inclusion reads
it.  A jitter draw of zero reads the true sample; any other draw
sticks the read at the window's first slot — so which restriction of
the fine history the component's counter saw is a live demonic
choice, and a schedule-generic rows predicate tells the readings
apart.  Genericity is blind to the realization *tag*; the gap lives
in the realization-dependent *reading* — which is exactly why the
assumption slot, and nothing else, carries the price of jitter. -/

/-- The swapped one-port seam interface: wire `false` fine (pinned),
wire `true` coarse (jittered). -/
def tickPortsSwap : PUnit.{u + 1} → ULift.{u} Bool × ULift.{u} Bool :=
  fun _ => (⟨false⟩, ⟨true⟩)

/-- The demonic tick seam: coarse clock jittered, fine clock pinned,
every co-realization admissible — and the sample-point inclusion
*reads the coarse realization*: a zero draw reads truly, any other
draw sticks at the window's first slot. -/
def demonicTickSeamHom :
    SpacetimeClockHom (tickClkOf.{u} ⟨true⟩) (tickClkOf.{u} ⟨false⟩) where
  wmap := id
  jitter _ := Set.univ
  emb _ θ _ p := if (θ p).down = 0 then p else ⟨0⟩

/-- The window of the demonic witness: one tick, two samples. -/
def demonicWindow : ULift.{u} (ℕ × ℕ) := ⟨(0, 1)⟩

/-- The fine history of the demonic witness: `false` at the first
sample, `true` at the second. -/
def demonicHistory : tickSite.{u}.pts demonicWindow → ULift.{u} Bool :=
  fun p => ⟨decide (p.down = 1)⟩

/-- The rows of the demonic witness: some sample reads `true`.
Schedule-generic — the predicate never reads the realization. -/
def demonicRows :
    SpacetimeRec (tickClkOf.{u} ⟨true⟩) (ULift.{u} Bool) → Prop :=
  fun r => ∃ q, r.x q = ⟨true⟩

/-- The demonic witness rows are schedule-generic: the separation
below is not an artifact of realization-reading rows. -/
theorem demonicRows_scheduleGeneric : ScheduleGeneric demonicRows :=
  fun _ _ _ _ h => h

/-- The demonic witness state: the fine record carries the two-sample
history; the coarse record rode the all-zero draw, so its carried
reading is the true history. -/
def demonicState :
    ULift.{u} Bool →
      ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf (ULift.{u} Bool)) :=
  fun v => cond v.down
    ⟨⟨true⟩, ⟨demonicWindow, fun _ => ⟨0⟩, demonicHistory⟩⟩
    ⟨⟨false⟩, ⟨demonicWindow, PUnit.unit, demonicHistory⟩⟩

theorem demonicState_mem :
    demonicState.{u} ∈
      sampleWireSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩ ⟨false⟩
        demonicTickSeamHom :=
  ⟨demonicWindow, fun _ => ⟨0⟩, PUnit.unit, Set.mem_univ _,
    fun _ => ⟨demonicHistory, rfl, rfl⟩⟩

theorem demonicState_mem_coarseRows :
    demonicState.{u} ∈
      coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
        demonicRows := by
  intro p rc hrc
  injection hrc with _ h2
  subst h2
  exact ⟨⟨1⟩, rfl⟩

theorem demonicState_notMem_perTickRows :
    demonicState.{u} ∉
      perTickRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩ ⟨false⟩
        demonicTickSeamHom demonicRows := by
  intro h
  have hPc := h PUnit.unit ⟨demonicWindow, PUnit.unit, demonicHistory⟩ rfl
    ⟨demonicWindow, fun _ => ⟨1⟩,
      fun q => demonicHistory (demonicTickSeamHom.emb demonicWindow
        (fun _ => ⟨1⟩) PUnit.unit q)⟩
    ⟨PUnit.unit, demonicHistory, Set.mem_univ _, rfl, rfl⟩
  obtain ⟨q, hq⟩ := hPc
  simp [demonicTickSeamHom, demonicHistory] at hq

/-- **The demonic gap**: under the jittered slot, the compiled
reading and the per-tick reading genuinely differ — a supported state
whose carried reading satisfies the rows while another admissible
reading violates them.  The rows are schedule-generic
(`demonicRows_scheduleGeneric`): genericity does not close the
gap. -/
theorem exists_demonic_gap :
    ∃ x : ULift.{u} Bool →
        ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf (ULift.{u} Bool)),
      x ∈ sampleWireSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          ⟨false⟩ demonicTickSeamHom ∧
      x ∈ coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          demonicRows ∧
      x ∉ perTickRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          ⟨false⟩ demonicTickSeamHom demonicRows :=
  ⟨demonicState, demonicState_mem, demonicState_mem_coarseRows,
    demonicState_notMem_perTickRows⟩

/-- The separation at the wall tier: the composite's joined wall under
the per-tick conjunct sits strictly above its compiled sibling
somewhere — the two readings present genuinely different
composites. -/
theorem demonicWall_strictly_above :
    ∃ μ, (sampleWireWall tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          ⟨false⟩ demonicTickSeamHom
        ⊔ possWall (coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap
          ⟨true⟩ demonicRows)) μ
      < (sampleWireWall tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          ⟨false⟩ demonicTickSeamHom
        ⊔ possWall (perTickRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap
          ⟨true⟩ ⟨false⟩ demonicTickSeamHom demonicRows)) μ := by
  refine ⟨Joint.dirac demonicState, ?_⟩
  unfold sampleWireWall
  rw [Pi.sup_apply, Pi.sup_apply,
    possWall_apply_of_mem (Joint.dirac_mem_suppIn demonicState_mem),
    possWall_apply_of_mem
      (Joint.dirac_mem_suppIn demonicState_mem_coarseRows),
    possWall_apply_of_notMem
      (fun hmem => demonicState_notMem_perTickRows
        (Joint.mem_of_dirac_mem_suppIn hmem)),
    sup_idem, sup_top_eq]
  exact ENNReal.zero_lt_top

/-- **The square's inclusion is strict**: under the jittered slot,
compile-then-denote admits a model the per-tick reading refuses — the
model-class face of the demonic gap, over the vacuous residual
presentation. -/
theorem exists_hybridTime_square_strict :
    ∃ σ : Pen (ULift.{u} Bool →
        ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf (ULift.{u} Bool))),
      σ ∈ (((SpecDnf.vacuous _).withWall
            (sampleWireWall tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
              ⟨false⟩ demonicTickSeamHom)).withWall
          (possWall (coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap
            ⟨true⟩ demonicRows))).modelClass ∧
      σ ∉ (((SpecDnf.vacuous _).withWall
            (sampleWireWall tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
              ⟨false⟩ demonicTickSeamHom)).withWall
          (possWall (perTickRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap
            ⟨true⟩ ⟨false⟩ demonicTickSeamHom demonicRows))).modelClass := by
  have hinter : demonicState.{u} ∈
      sampleWireSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩ ⟨false⟩
          demonicTickSeamHom ∩
        coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          demonicRows :=
    ⟨demonicState_mem, demonicState_mem_coarseRows⟩
  refine ⟨possWall (sampleWireSet tickClkOf (ULift.{u} Bool) tickPortsSwap
    ⟨true⟩ ⟨false⟩ demonicTickSeamHom ∩
    coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
      demonicRows), ?_, ?_⟩
  · rw [SpecDnf.mem_modelClass_withWall]
    refine ⟨possWall_antitone Set.inter_subset_right, ?_⟩
    rw [SpecDnf.mem_modelClass_withWall]
    refine ⟨possWall_antitone Set.inter_subset_left, ?_⟩
    rw [SpecDnf.mem_modelClass_iff]
    refine ⟨SpecAtom.vacuous _, rfl, pi_zero_le _, fun v hv => ?_⟩
    rw [SpecAtom.vacuous_marks, Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨Joint.dirac demonicState, by
      rw [possWall_apply_of_mem (Joint.dirac_mem_suppIn hinter),
        Pi.top_apply]
      exact ENNReal.zero_lt_top⟩
  · rw [SpecDnf.mem_modelClass_withWall]
    rintro ⟨hpt, -⟩
    have h := hpt (Joint.dirac demonicState)
    rw [possWall_apply_of_notMem
        (fun hmem => demonicState_notMem_perTickRows
          (Joint.mem_of_dirac_mem_suppIn hmem)),
      possWall_apply_of_mem (Joint.dirac_mem_suppIn hinter)] at h
    simp at h

/-- **The wall row is load-bearing for the square itself**: without
the seam's conjunct the two readings are incomparable — a state off
the seam satisfies the per-tick reading vacuously while its coarse
port violates the rows.  The square's very comparability rides the
timer declaration. -/
theorem exists_unwalled_square_fails :
    ∃ x : ULift.{u} Bool →
        ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf (ULift.{u} Bool)),
      x ∈ perTickRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          ⟨false⟩ demonicTickSeamHom demonicRows ∧
      x ∉ coarseRowsSet tickClkOf (ULift.{u} Bool) tickPortsSwap ⟨true⟩
          demonicRows := by
  refine ⟨fun _ => ⟨⟨true⟩, ⟨demonicWindow, fun _ => ⟨0⟩, fun _ => ⟨false⟩⟩⟩,
    ?_, ?_⟩
  · intro p rf hrf
    have h1 : (true : Bool) = false := congrArg (fun t => t.1.down) hrf
    exact Bool.noConfusion h1
  · intro h
    obtain ⟨q, hq⟩ :=
      h PUnit.unit ⟨demonicWindow, fun _ => ⟨0⟩, fun _ => ⟨false⟩⟩ rfl
    have h1 : (false : Bool) = true := congrArg ULift.down hq
    exact Bool.noConfusion h1

end Spacetime

end SuFunctor
