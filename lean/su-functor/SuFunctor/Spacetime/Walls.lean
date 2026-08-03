import SuFunctor.Spacetime.Universe
import SuFunctor.Plain.CheckerFace

/-! # Walls in the iterated fibres: profile pins and SampleWire seams

The instance vocabulary of the site dimension's fibre side (successor S1
of the site-dimension leg): the generic wall-conjunct machinery of
`SuFunctor.Spacetime.Universe` (`SpecAtom.withWall`,
`SpecDnf.mem_modelClass_withWall`), instantiated with the two walls the
staged cross-site design actually names —

* **the profile-pin wall** (`profilePinWall`): the indicator penalty of
  the profiled states inside the fused carrier.  Its region is exactly
  the constrained state space (`profilePinSet_eq_range`) — the
  profile-pinning content of `profiledEmbed`'s (non-invertible) unit
  comparison, as a wall in the iterated total's own fibres; and
* **the bundled SampleWire wall** (`sampleWireWall`): Definition 3 of
  the cross-site construction at the finite/possibilistic stratum —
  a declared clock morphism enters a composite's presentation as the
  indicator of its bundled admissible set (`sampleWireSet`): **one**
  demonic co-realization per clock-morphism instance, shared across all
  its ports.  The wall consumes the morphism only through its transport
  relation (`sampleWireSet_ports_transport`), and the bundling is
  load-bearing, not pedantry: a two-port state drawing distinct jitter
  realizations per port is admitted by the per-port variant and refused
  by the bundle (`tickTwoPortState_mem_perPort` /
  `tickTwoPortState_notMem_bundled` — the M8 separation, machine-checked
  at this stratum).

The concrete instances ride the tick clocks of the base module — the
pinned and jittered clocks whose realization-class relaxation priced the
2.66× certified-tick premium at the valuation layer — so the seam
vocabulary of that measurement now names objects inside the iterated
fibres.  The seam-crossing consumption is worked twice: entailment at
the wall tier (`sampleWire_entails_coarseClockPin`, with the load of the
wall witnessed by `exists_unwalled_leak`: dropping the wall row from the
premise makes the entailment false), and the landed blocking criterion
instantiated verbatim on the `Joint` fibre carrier with the SampleWire
wall joined into the premise floor (`sampleWire_union_refinement_iff`).

Everything here is order-theoretic instantiation: no topology, no new
adversary species, no new criterion lemma — per the staged design, the
demonic content of the seam lives entirely in the wall's *shape*, and
the criterion never opens the wall.
-/

namespace SuFunctor

open scoped ENNReal

universe u

/-! ## The indicator wall's order lemmas (generic, exact stratum) -/

namespace Plain

variable {X : Type u}

/-- Credal sets of regions are monotone in the region. -/
theorem suppIn_mono {B B' : Set X} (h : B ⊆ B') : suppIn B ⊆ suppIn B' :=
  fun _ hμ => Set.Subset.trans hμ h

/-- Domination of an indicator wall, read pointwise: a system dominates
`possWall B` iff it forbids outright every joint that leaks mass off
`B`. -/
theorem possWall_le_iff {B : Set X} {σ : Pen X} :
    possWall B ≤ σ ↔ ∀ μ, μ ∉ suppIn B → σ μ = ⊤ := by
  constructor
  · intro h μ hμ
    have h1 := h μ
    rw [possWall_apply_of_notMem hμ] at h1
    exact top_le_iff.mp h1
  · intro h μ
    by_cases hμ : μ ∈ suppIn B
    · rw [possWall_apply_of_mem hμ]
      exact bot_le
    · rw [possWall_apply_of_notMem hμ, h μ hμ]

/-- The indicator wall is antitone in its region: shrinking the
admissible set strengthens the wall. -/
theorem possWall_antitone {B B' : Set X} (h : B ⊆ B') :
    possWall B' ≤ possWall B := by
  intro μ
  by_cases hμ : μ ∈ suppIn B
  · rw [possWall_apply_of_mem (suppIn_mono h hμ)]
    exact bot_le
  · rw [possWall_apply_of_notMem hμ]
    exact le_top

/-- A region contains any point whose Dirac joint its credal set
contains — the converse of `Joint.dirac_mem_suppIn`. -/
theorem Joint.mem_of_dirac_mem_suppIn {B : Set X} {x : X}
    (h : Joint.dirac x ∈ suppIn B) : x ∈ B := by
  have h1 := mem_suppIn.mp h
  rw [Joint.dirac_support] at h1
  exact h1 (by simp)

end Plain

/-! ## Wall weakening, and the carrier-generic vacuous presentation -/

namespace Universe

variable {K : Type u}

/-- Weakening the wall weakens the walled presentation: the
one-more-conjunct reading's monotone face. -/
theorem SpecDnf.withWall_modelClass_antitone {w w' : K → ℝ≥0∞}
    (h : w' ≤ w) (D : SpecDnf K) :
    (D.withWall w).modelClass ⊆ (D.withWall w').modelClass := by
  intro σ hσ
  rw [SpecDnf.mem_modelClass_withWall] at hσ ⊢
  exact ⟨h.trans hσ.1, hσ.2⟩

/-- The vacuous atom over an arbitrary carrier: austere floor with the
properness demand only — the unit shape `(0, {⊤})`, carrier-generic
(the wiring layer's `unitAtom` is its instance at identity-pattern
apexes). -/
def SpecAtom.vacuous (K : Type u) : SpecAtom K :=
  ⟨0, {⊤}, Set.finite_singleton _, rfl⟩

@[simp] theorem SpecAtom.vacuous_floor (K : Type u) :
    (SpecAtom.vacuous K).floor = 0 := rfl

@[simp] theorem SpecAtom.vacuous_marks (K : Type u) :
    (SpecAtom.vacuous K).marks = {⊤} := rfl

/-- The vacuous DNF: the single vacuous atom. -/
def SpecDnf.vacuous (K : Type u) : SpecDnf K :=
  ⟨{SpecAtom.vacuous K}, Set.finite_singleton _⟩

@[simp] theorem SpecDnf.vacuous_atoms (K : Type u) :
    (SpecDnf.vacuous K).atoms = {SpecAtom.vacuous K} := rfl

end Universe

namespace Spacetime

open Plain Universe

variable {Clk : Type u} {Rec : Clk → Type u}

/-! ## The profile-pin wall

Pinning is the unit of the profiled world and a constraint in the fused
world (the lax-not-pseudo semantics of `profiledEmbed`).  At the spec
tier the constraint is a wall: the indicator of the profiled states
inside the fused carrier. -/

/-- The profile-pin region: the fused states obeying the profile. -/
def profilePinSet (A : SpacetimeBase Clk Rec) :
    Set (A.wires → ClockedEl Clk Rec) :=
  {x | IsProfiled A x}

/-- The pin region **is** the profiled state space: the constrained
states of the profiled base, as a region of the fused carrier (the
image of the states subtype — what `profiledEmbed`'s unit comparison
pins to). -/
theorem profilePinSet_eq_range (A : SpacetimeBase Clk Rec) :
    profilePinSet A
      = Set.range (Subtype.val : states A → A.wires → ClockedEl Clk Rec) := by
  ext x
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-- The profile-pin wall: the indicator penalty of the profiled
states. -/
noncomputable def profilePinWall (A : SpacetimeBase Clk Rec) :
    Pen (A.wires → ClockedEl Clk Rec) :=
  possWall (profilePinSet A)

/-- Pinning a presentation to the profile is exactly one more conjunct:
satisfaction of the pinned presentation is satisfaction of the original
plus outright forbidding of every joint that leaks mass off the
profiled states. -/
theorem mem_modelClass_withWall_profilePin {A : SpacetimeBase Clk Rec}
    {D : SpecDnf (Joint (A.wires → ClockedEl Clk Rec))}
    {σ : Joint (A.wires → ClockedEl Clk Rec) → ℝ≥0∞} :
    σ ∈ (D.withWall (profilePinWall A)).modelClass ↔
      (∀ μ, μ ∉ suppIn (profilePinSet A) → σ μ = ⊤) ∧ σ ∈ D.modelClass :=
  SpecDnf.mem_modelClass_withWall.trans (and_congr_left' possWall_le_iff)

/-! ## The clocked vocabulary, concretely

The parent memo's clause 1, cashed at record level: a small index of
clocks interpreted into `SpacetimeClock`, with realized records carrying
their clock — `ClockedEl Clk (SiteRec κ X) = Σ i, SpacetimeRec (κ i) X`
literally. -/

/-- Realized records over an indexed family of spacetime clocks. -/
abbrev SiteRec (κ : Clk → SpacetimeClock.{u}) (X : Type u) : Clk → Type u :=
  fun i => SpacetimeRec (κ i) X

/-- A spacetime clock morphism, at the finite/possibilistic stratum: a
window map, an admissible co-realization class per window (the jitter
class `J_φ`), and the realized sample-point inclusion.  The analytic
clauses (rate/jitter constants, closedness, nonemptiness-from-
regularity) are the ambient semantics' regularity content — the staged
design's named debt, out of scope here exactly as for
`SpacetimeClock`. -/
structure SpacetimeClockHom (c c' : SpacetimeClock.{u}) : Type u where
  /-- The window map. -/
  wmap : c.site.Window → c'.site.Window
  /-- The admissible co-realizations of each window: the jitter class
  `J_φ`. -/
  jitter : ∀ w : c.site.Window, Set (c.Real w × c'.Real (wmap w))
  /-- The realized sample-point inclusion: under a co-realization, each
  coarse observation slot lands on a fine one. -/
  emb : ∀ (w : c.site.Window), c.Real w → ∀ (_ : c'.Real (wmap w)),
    c.site.pts w → c'.site.pts (wmap w)

namespace SpacetimeClockHom

variable {c c' : SpacetimeClock.{u}}

/-- The transport relation `R_φ` of a clock morphism: a fine record
relates to a coarse record when some admissible co-realization carries
it there — the coarse history is the fine history read along the
realized inclusion.  The graph of a restriction function precisely when
the realization class is pinned; a genuine relation under jitter —
*which* restriction applies is the demonic choice of realization.  The
wall below consumes `φ` only through this relation. -/
def transportRel (φ : SpacetimeClockHom c c') (X : Type u) :
    SpacetimeRec c' X → SpacetimeRec c X → Prop :=
  fun r' r => ∃ (θ' : c'.Real (φ.wmap r.w))
    (x' : c'.site.pts (φ.wmap r.w) → X),
    (r.θ, θ') ∈ φ.jitter r.w ∧
    r.x = (fun p => x' (φ.emb r.w r.θ θ' p)) ∧
    r' = ⟨φ.wmap r.w, θ', x'⟩

end SpacetimeClockHom

/-! ## The bundled SampleWire wall (Definition 3, possibilistic stratum)

Generic over the wire type, so it instantiates at `A.wires` for any
profiled interface — which is where the iterated total's fibres
(`SpecDnf (Joint (A.wires → ClockedEl …))`, by
`spacetimeSpecFunctor_fibre_eq`) consume it. -/

section SampleWire

variable (κ : Clk → SpacetimeClock.{u}) (X : Type u)

/-- **The bundled SampleWire support set** `B_φ`: the fused states
admitting **one** demonic co-realization triple (window, coarse
realization, fine realization) per clock-morphism instance, shared
across all its ports — each port's coarse record is pinned to that
triple and reads its fine record along the realized inclusion.  Since
realized records carry their realizations, the sharing clause is an
ordinary support condition: equality of the realization components
across the family.  Port convention: `(ports p).1` the fine wire
(clock `i'`), `(ports p).2` the coarse wire (clock `i`). -/
def sampleWireSet {W P : Type u} (ports : P → W × W) (i i' : Clk)
    (φ : SpacetimeClockHom (κ i) (κ i')) :
    Set (W → ClockedEl Clk (SiteRec κ X)) :=
  {x | ∃ (w : (κ i).site.Window) (θ : (κ i).Real w)
      (θ' : (κ i').Real (φ.wmap w)), (θ, θ') ∈ φ.jitter w ∧
      ∀ p : P, ∃ x' : (κ i').site.pts (φ.wmap w) → X,
        x (ports p).2 = ⟨i, ⟨w, θ, fun q => x' (φ.emb w θ θ' q)⟩⟩ ∧
        x (ports p).1 = ⟨i', ⟨φ.wmap w, θ', x'⟩⟩}

/-- **The SampleWire wall** `D_φ`: the indicator penalty of the bundled
admissible set — the sampler seam as one more conjunct on the joint
carrier. -/
noncomputable def sampleWireWall {W P : Type u} (ports : P → W × W)
    (i i' : Clk) (φ : SpacetimeClockHom (κ i) (κ i')) :
    Pen (W → ClockedEl Clk (SiteRec κ X)) :=
  possWall (sampleWireSet κ X ports i i' φ)

/-- The wall consumes the morphism only through `R_φ`: every port pair
of a supported state is transport-related (with the shared realization
components — the bundle refines the per-port conjunction). -/
theorem sampleWireSet_ports_transport {W P : Type u} {ports : P → W × W}
    {i i' : Clk} {φ : SpacetimeClockHom (κ i) (κ i')}
    {x : W → ClockedEl Clk (SiteRec κ X)}
    (hx : x ∈ sampleWireSet κ X ports i i' φ) (p : P) :
    ∃ (rf : SpacetimeRec (κ i') X) (rc : SpacetimeRec (κ i) X),
      x (ports p).1 = ⟨i', rf⟩ ∧ x (ports p).2 = ⟨i, rc⟩ ∧
      φ.transportRel X rf rc := by
  obtain ⟨w, θ, θ', hJ, hport⟩ := hx
  obtain ⟨x', hc, hf⟩ := hport p
  exact ⟨⟨φ.wmap w, θ', x'⟩, ⟨w, θ, fun q => x' (φ.emb w θ θ' q)⟩, hf, hc,
    θ', x', hJ, rfl, rfl⟩

/-- The per-port variant: each port draws its **own** co-realization —
`|P|` independent clock instances, a different (and weaker) spec.
Grammatical, and deliberately distinct from Definition 3's bundle
(M8): independence is declared by splitting clock instances, never
silently. -/
def perPortSampleSet {W P : Type u} (ports : P → W × W) (i i' : Clk)
    (φ : SpacetimeClockHom (κ i) (κ i')) :
    Set (W → ClockedEl Clk (SiteRec κ X)) :=
  {x | ∀ p : P, ∃ (w : (κ i).site.Window) (θ : (κ i).Real w)
      (θ' : (κ i').Real (φ.wmap w)), (θ, θ') ∈ φ.jitter w ∧
      ∃ x' : (κ i').site.pts (φ.wmap w) → X,
        x (ports p).2 = ⟨i, ⟨w, θ, fun q => x' (φ.emb w θ θ' q)⟩⟩ ∧
        x (ports p).1 = ⟨i', ⟨φ.wmap w, θ', x'⟩⟩}

/-- The bundle refines the per-port reading: sharing a co-realization
only constrains more. -/
theorem sampleWireSet_subset_perPortSampleSet {W P : Type u}
    {ports : P → W × W} {i i' : Clk} {φ : SpacetimeClockHom (κ i) (κ i')} :
    sampleWireSet κ X ports i i' φ ⊆ perPortSampleSet κ X ports i i' φ := by
  rintro x ⟨w, θ, θ', hJ, hport⟩ p
  obtain ⟨x', hc, hf⟩ := hport p
  exact ⟨w, θ, θ', hJ, x', hc, hf⟩

/-- Declaring the seam pins the coarse ports to the sample clock: the
first-component reading of the bundled support condition. -/
def coarseClockPinSet {W P : Type u} (ports : P → W × W) (i : Clk) :
    Set (W → ClockedEl Clk (SiteRec κ X)) :=
  {x | ∀ p : P, (x (ports p).2).1 = i}

theorem sampleWireSet_subset_coarseClockPin {W P : Type u}
    (ports : P → W × W) (i i' : Clk) (φ : SpacetimeClockHom (κ i) (κ i')) :
    sampleWireSet κ X ports i i' φ ⊆ coarseClockPinSet κ X ports i := by
  rintro x ⟨w, θ, θ', -, hport⟩ p
  obtain ⟨x', hc, -⟩ := hport p
  rw [hc]

/-- **Entailment across the seam, at the wall tier**: every model of a
presentation walled by the SampleWire seam is a model of the same
presentation walled by the coarse-clock pin — wall weakening along the
support-set inclusion.  (The wall is load-bearing:
`exists_unwalled_leak` below exhibits a model of the *unwalled*
presentation refusing the conclusion, so deleting the seam's wall row
from the premise makes this entailment false.) -/
theorem sampleWire_entails_coarseClockPin {W P : Type u}
    (ports : P → W × W) (i i' : Clk) (φ : SpacetimeClockHom (κ i) (κ i'))
    (D : SpecDnf (Joint (W → ClockedEl Clk (SiteRec κ X)))) :
    (D.withWall (sampleWireWall κ X ports i i' φ)).modelClass ⊆
      (D.withWall (possWall (coarseClockPinSet κ X ports i))).modelClass :=
  SpecDnf.withWall_modelClass_antitone
    (possWall_antitone (sampleWireSet_subset_coarseClockPin κ X ports i i' φ))
    D

/-- **The seam-crossing criterion, in the iterated fibres**: the landed
blocking criterion with the SampleWire wall joined into the premise
floor, instantiated verbatim on the `Joint` fibre carrier at the
order-theoretic stratum (adversary class discharged at `⊤`): entailment
from the seam-walled premise is decided by the same finite blocking
table. -/
theorem sampleWire_union_refinement_iff {W P : Type u} {ports : P → W × W}
    {i i' : Clk} {φ : SpacetimeClockHom (κ i) (κ i')} {m : ℕ}
    {u : Pen (W → ClockedEl Clk (SiteRec κ X))}
    {𝒱 : Set (Pen (W → ClockedEl Clk (SiteRec κ X)))}
    {u' : Fin m → Pen (W → ClockedEl Clk (SiteRec κ X))}
    {𝒱' : Fin m → Set (Pen (W → ClockedEl Clk (SiteRec κ X)))} :
    (∀ σ, CoupledSat σ (u ⊔ sampleWireWall κ X ports i i' φ) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ sel, SelValid 𝒱' sel →
          Blocked (u ⊔ sampleWireWall κ X ports i i' φ) 𝒱 u' sel := by
  refine Iff.trans ?_
    (cross_site_union_refinement_iff (P := fun _ => True) fun _ _ => trivial)
  exact ⟨fun h σ _ => h σ, fun h σ => h σ trivial⟩

end SampleWire

/-! ## The tick seam: the premium's clocks, inside the fibres

The pinned and jittered tick clocks are the vocabulary in which the
2.66× certified-tick premium was measured (the wall's relaxation from
pinned to jittered realization classes, at the valuation layer).  The
instances below put that seam inside the iterated total's fibres:
a properness witness (Prop 3.1's nonemptiness clause at this stratum),
the M8 bundling separation, and the load-bearing-wall pin. -/

/-- The two-clock index of the tick seam: `false` ↦ pinned (coarse),
`true` ↦ jittered (fine). -/
def tickClkOf : ULift.{u} Bool → SpacetimeClock.{u} :=
  fun b => cond b.down jitteredTickClock pinnedTickClock

/-- The tick-seam clock morphism, pinned into jittered over the same
site: same windows, same sample points, every jitter co-realization
admissible. -/
def tickSeamHom :
    SpacetimeClockHom (tickClkOf.{u} ⟨false⟩) (tickClkOf.{u} ⟨true⟩) where
  wmap := id
  jitter _ := Set.univ
  emb _ _ _ := id

/-- The one-port seam interface: wire `true` fine, wire `false`
coarse. -/
def tickPorts : PUnit.{u + 1} → ULift.{u} Bool × ULift.{u} Bool :=
  fun _ => (⟨true⟩, ⟨false⟩)

/-- A supported state of the one-port tick seam: the zero-jitter
co-realization, trivial histories. -/
def tickSeamState :
    ULift.{u} Bool → ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1}) :=
  fun v => cond v.down
    ⟨⟨true⟩, ⟨⟨(0, 0)⟩, fun _ => ⟨0⟩, fun _ => PUnit.unit⟩⟩
    ⟨⟨false⟩, ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => PUnit.unit⟩⟩

theorem tickSeamState_mem :
    tickSeamState ∈
      sampleWireSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom :=
  ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => ⟨0⟩, Set.mem_univ _,
    fun _ => ⟨fun _ => PUnit.unit, rfl, rfl⟩⟩

/-- **Properness of the tick-seam wall** (Prop 3.1's nonemptiness
clause, possibilistic stratum): the wall admits a supported joint — the
Dirac joint at a supported state kills it. -/
theorem exists_tickSeam_wall_eq_zero :
    ∃ μ, sampleWireWall tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ ⟨true⟩
        tickSeamHom μ = 0 :=
  ⟨Joint.dirac tickSeamState,
    possWall_apply_of_mem (Joint.dirac_mem_suppIn tickSeamState_mem)⟩

/-- The two-port seam interface: wires `(port, fine?)`. -/
def tickTwoPorts :
    ULift.{u} Bool → ULift.{u} (Bool × Bool) × ULift.{u} (Bool × Bool) :=
  fun p => (⟨(p.down, true)⟩, ⟨(p.down, false)⟩)

/-- The M8 witness state: each port's fine record draws a **different**
jitter realization (port `false` draws jitter `0`, port `true` draws
jitter `1`); the coarse records agree. -/
def tickTwoPortState :
    ULift.{u} (Bool × Bool) →
      ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1}) :=
  fun v => cond v.down.2
    ⟨⟨true⟩, ⟨⟨(0, 0)⟩, fun _ => ⟨cond v.down.1 1 0⟩, fun _ => PUnit.unit⟩⟩
    ⟨⟨false⟩, ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => PUnit.unit⟩⟩

/-- Per-port, the witness is admissible: each port's own
co-realization works. -/
theorem tickTwoPortState_mem_perPort :
    tickTwoPortState ∈
      perPortSampleSet tickClkOf PUnit.{u + 1} tickTwoPorts ⟨false⟩ ⟨true⟩
        tickSeamHom :=
  fun ⟨p⟩ => ⟨⟨(0, 0)⟩, PUnit.unit, fun _ => ⟨cond p 1 0⟩, Set.mem_univ _,
    fun _ => PUnit.unit, rfl, rfl⟩

/-- **Bundled ≠ per-port** (the M8 separation, machine-checked at this
stratum): the bundle refuses the witness — a shared co-realization
would have to equal both ports' distinct jitter draws, and realized
records carry their realizations, so the support condition reads the
disagreement off the records themselves. -/
theorem tickTwoPortState_notMem_bundled :
    tickTwoPortState ∉
      sampleWireSet tickClkOf PUnit.{u + 1} tickTwoPorts ⟨false⟩ ⟨true⟩
        tickSeamHom := by
  rintro ⟨w, θ, θ', -, hport⟩
  obtain ⟨x0, -, hf0⟩ := hport ⟨false⟩
  obtain ⟨x1, -, hf1⟩ := hport ⟨true⟩
  injection hf0 with hfst0 hsnd0
  injection hf1 with hfst1 hsnd1
  injection hsnd0 with hw0 hθ0 hx0
  injection hsnd1 with hw1 hθ1 hx1
  have hw0' : (⟨(0, 0)⟩ : ULift.{u} (ℕ × ℕ)) = w := hw0
  subst hw0'
  have hθ : (fun _ => ⟨0⟩ : ULift.{u} (Fin (0 + 1)) → ULift.{u} (Fin 3))
      = fun _ => ⟨1⟩ :=
    (eq_of_heq hθ0).trans (eq_of_heq hθ1).symm
  exact absurd (congrArg ULift.down (congrFun hθ ⟨0⟩)) (by decide)

/-- A leaking state: everything on the jittered clock — the coarse
port is off the sample clock. -/
def tickLeakState :
    ULift.{u} Bool → ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1}) :=
  fun _ => ⟨⟨true⟩, ⟨⟨(0, 0)⟩, fun _ => ⟨0⟩, fun _ => PUnit.unit⟩⟩

theorem tickLeakState_notMem_pin :
    tickLeakState ∉
      coarseClockPinSet tickClkOf PUnit.{u + 1} tickPorts ⟨false⟩ := by
  intro h
  exact Bool.noConfusion (congrArg ULift.down (h PUnit.unit))

/-- **The wall row is load-bearing**: without the seam's wall, the
coarse-clock-pin entailment fails — the zero system models the unwalled
vacuous presentation while leaking mass off the sample clock.  (With
the wall, `sampleWire_entails_coarseClockPin` decides the entailment;
this witness is why no repair could survive deleting the wall row from
the premise.) -/
theorem exists_unwalled_leak :
    ∃ σ : Pen (ULift.{u} Bool →
        ClockedEl (ULift.{u} Bool) (SiteRec tickClkOf PUnit.{u + 1})),
      σ ∈ (SpecDnf.vacuous _).modelClass ∧
      σ ∉ ((SpecDnf.vacuous _).withWall
          (possWall (coarseClockPinSet tickClkOf PUnit.{u + 1} tickPorts
            ⟨false⟩))).modelClass := by
  refine ⟨0, ?_, ?_⟩
  · rw [SpecDnf.mem_modelClass_iff]
    refine ⟨SpecAtom.vacuous _, rfl, le_refl _, fun v hv => ?_⟩
    rw [SpecAtom.vacuous_marks, Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨Joint.zero _, lt_top_iff_ne_top.mpr ENNReal.zero_ne_top⟩
  · rw [SpecDnf.mem_modelClass_withWall]
    rintro ⟨hwall, -⟩
    have h := hwall (Joint.dirac tickLeakState)
    rw [possWall_apply_of_notMem
      (fun hmem => tickLeakState_notMem_pin
        (Joint.mem_of_dirac_mem_suppIn hmem))] at h
    simp at h

end Spacetime

end SuFunctor
