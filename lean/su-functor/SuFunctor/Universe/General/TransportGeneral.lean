import SuFunctor.Universe.General.CrescentStratum
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Transport citizenship at the general carrier

The decoration tier's fibre operations — tight/cell transport (penalty
pullback along a carrier map) and the compositor (pushforward-then-add)
— upgraded from the finite stratum
(`SuFunctor.Universe.TransportCitizenship`, `[Fintype V]`) to the
general subprobability carrier: `X`, `Y` arbitrary topological
measurable spaces, transport maps the **continuous** ones (with a Borel
codomain, so measurability is derived rather than assumed — at the
finite stratum every map was both, silently).

* **Pushforward** (`push`, `probPush`): mathlib's `FiniteMeasure.map` /
  `ProbabilityMeasure.map`, packaged on the carrier.  The two facts the
  dictionary rides are exactly the brief's pair: **mass exactness**
  (`mass_push` — pushforward of a measurable map preserves total mass)
  and **scaling linearity** (`push_scalePoint`, from the unconditional
  `FiniteMeasure.map_smul`).
* **The transport dictionary** (`compile_pullPen`): the body of a
  transported penalty is the *preimage* of its body — verbatim the
  finite-stratum statement, with the polar decomposition of the general
  carrier supplying what fibrewise sums supplied there.
* **Judgment invariance** (`coupledSat_pullPen_iff`): along transports
  whose pushforward is surjective on probability directions.  Honest
  general-stratum residue, stated not smoothed: bare surjectivity of
  `θ` does NOT produce surjectivity of the pushforward here — that is
  the measurable-selection frontier — so the hypothesis lives at the
  pushforward, with the measurable-section sufficient condition proven
  (`probPush_surjective_of_section`); the finite stratum recovered it
  from bare surjectivity because every section of a finite discrete
  carrier is measurable.  Off the surjective stratum the invariance
  fails in BOTH directions, kernel-checked
  (`exists_coupledSat_not_pullPen`, `exists_coupledSat_pullPen_not`).
* **The structure theorem**, split at its honest joints: the forward
  inclusion (`transportClass_crescentClass_subset`) consumes
  surjectivity of the pushforward exactly as at the finite stratum; the
  reverse inclusion (`mem_transportClass_of_closed_image`) consumes
  closedness of the image body — the supply that COMPACTNESS paid
  silently at the finite stratum and is a named hypothesis here; the
  equality (`transportClass_crescentClass`) packages both under
  `IsClosedMap`.
* **The off-surjective counterexample**
  (`exists_transport_not_subset_pulled_crescent`): the finite
  `Unit → Bool` witness, ported to the general machinery — the liveness
  mark is the mass-on-`true` observation through the narrow topology's
  own test pairing (continuous, hence a citizen), its escape region
  sits off the range of the pushforward, and its pullback is the zero
  penalty, against which nothing escapes.
* **The compositor dictionary** (`compile_add_radProd`): the body of a
  sum is the fibrewise radial grade product, over the general carrier;
  citizenship is preserved at the penalty level
  (`lowerSemicontinuous_add_penalty`, `lowerSemicontinuous_boxplus`).
  The class-level union-distribution receipts
  (`transportClass_union`, `transportClass_iUnion`) are here; the
  compositor-side receipts (`compositorClass_union_left/right`,
  `compositor_singleton`) are already carrier-general in
  `TransportCitizenship` and are consumed, not re-minted.  Ideal-point
  constructibility (`isConstructibleUnion_singleton`) needs a T1
  hyperspace; the general Fell hyperspace is T2 only over locally
  compact ambients (`FellCloseds.t2Space`) — a named residue, not a
  claim.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X Y : Type*}
  [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
  {θ : X → Y}

/-! ## Pushforward on the carriers -/

/-- Pushforward of a subprobability state along an outcome map:
mathlib's `FiniteMeasure.map` on the underlying finite measure.  Total
(the map is junk-valued off the measurable stratum; every lemma below
carries the continuity that rules the junk out), and mass-nonincreasing
unconditionally, so it stays on the carrier. -/
noncomputable def push (θ : X → Y) (ν : SubProbabilityMeasure X) :
    SubProbabilityMeasure Y :=
  ⟨(ν : FiniteMeasure X).map θ,
    le_trans (FiniteMeasure.mass_map_le θ _) ν.mass_le_one⟩

omit [TopologicalSpace Y] [BorelSpace Y] in
@[simp] theorem coe_push (θ : X → Y) (ν : SubProbabilityMeasure X) :
    ((push θ ν : SubProbabilityMeasure Y) : FiniteMeasure Y)
      = (ν : FiniteMeasure X).map θ := rfl

/-- Pushforward of a probability direction along a continuous outcome
map (Borel codomain: measurability is derived). -/
noncomputable def probPush (hθ : Continuous θ)
    (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  μ.map hθ.measurable.aemeasurable

theorem probPush_toFiniteMeasure (hθ : Continuous θ)
    (μ : ProbabilityMeasure X) :
    (probPush hθ μ).toFiniteMeasure = μ.toFiniteMeasure.map θ := rfl

/-- **Mass exactness**: the pushforward of a measurable map preserves
total mass on the nose — the first of the two facts the transport
dictionary rides. -/
theorem mass_push (hθ : Continuous θ) (ν : SubProbabilityMeasure X) :
    ((push θ ν : SubProbabilityMeasure Y) : FiniteMeasure Y).mass
      = (ν : FiniteMeasure X).mass := by
  have h : ((((push θ ν : SubProbabilityMeasure Y) : FiniteMeasure Y)).mass : ℝ≥0∞)
      = (((ν : FiniteMeasure X)).mass : ℝ≥0∞) := by
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass, coe_push,
      FiniteMeasure.toMeasure_map,
      Measure.map_apply hθ.measurable MeasurableSet.univ, Set.preimage_univ]
  exact_mod_cast h

/-- **Scaling linearity**: pushforward commutes with the radial action
— the second fact the dictionary rides (`FiniteMeasure.map_smul` is
unconditional). -/
theorem push_scalePoint (hθ : Continuous θ) {γ : ℝ≥0} (hγ : γ ≤ 1)
    (μ : ProbabilityMeasure X) :
    push θ (SubProbabilityMeasure.scalePoint γ hγ μ)
      = SubProbabilityMeasure.scalePoint γ hγ (probPush hθ μ) := by
  refine SubProbabilityMeasure.ext ?_
  rw [coe_push, SubProbabilityMeasure.coe_scalePoint,
    SubProbabilityMeasure.coe_scalePoint, FiniteMeasure.map_smul,
    probPush_toFiniteMeasure]

theorem continuous_push (hθ : Continuous θ) :
    Continuous (push θ : SubProbabilityMeasure X → SubProbabilityMeasure Y) :=
  Continuous.subtype_mk
    ((FiniteMeasure.continuous_map hθ).comp
      SubProbabilityMeasure.continuous_toFiniteMeasure) _

theorem continuous_probPush (hθ : Continuous θ) :
    Continuous (probPush hθ : ProbabilityMeasure X → ProbabilityMeasure Y) :=
  ProbabilityMeasure.continuous_map hθ

@[simp] theorem push_zero :
    push θ (0 : SubProbabilityMeasure X) = 0 := by
  refine SubProbabilityMeasure.ext ?_
  rw [coe_push, SubProbabilityMeasure.coe_zero, SubProbabilityMeasure.coe_zero]
  exact Subtype.ext (Measure.map_zero θ)

/-! ## Penalty transport, and the dictionary -/

/-- Penalty transport along a continuous outcome map: evaluate on the
pushforward.  The general face of the decoration tier's contravariant
penalty transport. -/
noncomputable def pullPen (hθ : Continuous θ) (f : Penalty Y) :
    Penalty X :=
  fun μ => f (probPush hθ μ)

@[simp] theorem pullPen_apply (hθ : Continuous θ) (f : Penalty Y)
    (μ : ProbabilityMeasure X) :
    pullPen hθ f μ = f (probPush hθ μ) := rfl

@[simp] theorem pullPen_zero (hθ : Continuous θ) :
    pullPen hθ (0 : Penalty Y) = 0 := rfl

/-- Citizens transport to citizens: the pullback of a lower
semicontinuous penalty along the (continuous) pushforward is lower
semicontinuous. -/
theorem lowerSemicontinuous_pullPen (hθ : Continuous θ) {f : Penalty Y}
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (pullPen hθ f) := fun μ c hc =>
  ((continuous_probPush hθ).tendsto μ).eventually (hf (probPush hθ μ) c hc)

/-- **The transport dictionary at the general carrier**: the pullback
of a penalty compiles to the *preimage* of its body under the
pushforward of subprobability states.  Penalty transport is body
preimage — preimages preserve containment unconditionally and produce
escape witnesses only inside the range, which decides everything
downstream.  `[Nonempty X]` pays for the bottom state's membership in
the backward direction. -/
theorem compile_pullPen [Nonempty X] (hθ : Continuous θ) (f : Penalty Y) :
    compile (pullPen hθ f) = push θ ⁻¹' compile f := by
  ext ν
  constructor
  · rintro ⟨μ, γ, hle, he⟩
    refine ⟨probPush hθ μ, γ, hle, ?_⟩
    rw [coe_push, he, FiniteMeasure.map_smul, probPush_toFiniteMeasure]
  · intro hν
    rcases SubProbabilityMeasure.exists_polar ν with h0 | ⟨μ, m, hm0, _, he⟩
    · rw [h0]
      exact zero_mem_compile _
    · have hpe : ((push θ ν : SubProbabilityMeasure Y) : FiniteMeasure Y)
          = m • (probPush hθ μ).toFiniteMeasure := by
        rw [coe_push, he, FiniteMeasure.map_smul, probPush_toFiniteMeasure]
      have hb : m ≤ gradeN (f (probPush hθ μ)) :=
        compile_scale_le hν hm0.ne' hpe
      exact ⟨μ, m, hb, he⟩

/-! ## Surjectivity at the general stratum

Bare surjectivity of `θ` does not hand the general stratum a
surjective pushforward: producing a preimage measure for an arbitrary
probability measure on `Y` needs a *measurable* section, and surjective
measurable maps admit none in general (the measurable-selection
frontier; on a finite discrete carrier every section is measurable,
which is why the finite stratum could consume bare surjectivity).  The
invariance and structure theorems therefore hypothesize surjectivity of
the pushforward itself; the measurable-section case discharges it. -/

/-- A measurable section of the outcome map induces a section of the
pushforward: the pushforward is surjective on probability
directions. -/
theorem probPush_surjective_of_section (hθ : Continuous θ) {s : Y → X}
    (hs_mble : Measurable s) (hs : Function.RightInverse s θ) :
    Function.Surjective (probPush hθ) := by
  intro ρ
  refine ⟨ρ.map hs_mble.aemeasurable, Subtype.ext ?_⟩
  show ((ρ.map hs_mble.aemeasurable).map hθ.measurable.aemeasurable
      : Measure Y) = (ρ : Measure Y)
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_map hθ.measurable hs_mble, hs.comp_eq_id, Measure.map_id]

/-- Pushforward surjectivity ascends from probability directions to the
whole carrier, along the polar decomposition.  `[Nonempty Y]` pays for
the polar decomposition on the target. -/
theorem push_surjective_of_probPush_surjective [Nonempty Y]
    (hθ : Continuous θ) (h : Function.Surjective (probPush hθ)) :
    Function.Surjective
      (push θ : SubProbabilityMeasure X → SubProbabilityMeasure Y) := by
  intro ρ
  rcases SubProbabilityMeasure.exists_polar ρ with h0 | ⟨μ', m, _, hm1, he⟩
  · exact ⟨0, by rw [push_zero, h0]⟩
  · obtain ⟨μ, hμ⟩ := h μ'
    refine ⟨SubProbabilityMeasure.scalePoint m hm1 μ, ?_⟩
    rw [push_scalePoint hθ, hμ]
    exact SubProbabilityMeasure.ext (by
      rw [SubProbabilityMeasure.coe_scalePoint, ← he])

/-- **Judgment invariance of atom transport** along transports with
surjective pushforward: pulling every constituent of a coupled atom
back along the pushforward changes no verdict.  (Mutant m2 drops
`hsurj`; the proof must go red at both `obtain ⟨μ, rfl⟩ := hsurj μ'`
sites — the off-range points.) -/
theorem coupledSat_pullPen_iff (hθ : Continuous θ)
    (hsurj : Function.Surjective (probPush hθ))
    {σ u : Penalty Y} {𝒱 : Set (Penalty Y)} :
    CoupledSat (pullPen hθ σ) (pullPen hθ u) (pullPen hθ '' 𝒱)
      ↔ CoupledSat σ u 𝒱 := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun μ' => ?_, fun v hv => ?_⟩
    · obtain ⟨μ, rfl⟩ := hsurj μ'
      exact hsafe μ
    · obtain ⟨μ, hμ⟩ := hlive (pullPen hθ v) ⟨v, hv, rfl⟩
      exact ⟨probPush hθ μ, hμ⟩
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun μ => hsafe _, ?_⟩
    rintro v' ⟨v, hv, rfl⟩
    obtain ⟨μ', hμ'⟩ := hlive v hv
    obtain ⟨μ, rfl⟩ := hsurj μ'
    exact ⟨μ, hμ'⟩

/-! ## The induced transport of hyperspace classes -/

/-- The transport of a general hyperspace class along an outcome map:
classes whose bodies arise as body preimages of members. -/
def transportClass (θ : X → Y)
    (C : Set (FellCloseds (SubProbabilityMeasure Y))) :
    Set (FellCloseds (SubProbabilityMeasure X)) :=
  {L | ∃ K ∈ C,
    (L : Set (SubProbabilityMeasure X))
      = push θ ⁻¹' (K : Set (SubProbabilityMeasure Y))}

theorem mem_transportClass_iff {C : Set (FellCloseds (SubProbabilityMeasure Y))}
    {L : FellCloseds (SubProbabilityMeasure X)} :
    L ∈ transportClass θ C ↔ ∃ K ∈ C,
      (L : Set (SubProbabilityMeasure X))
        = push θ ⁻¹' (K : Set (SubProbabilityMeasure Y)) :=
  Iff.rfl

/-- Class transport distributes over binary unions: the ∨-compatibility
receipt, transport half, at the general carrier. -/
theorem transportClass_union (θ : X → Y)
    (C₁ C₂ : Set (FellCloseds (SubProbabilityMeasure Y))) :
    transportClass θ (C₁ ∪ C₂)
      = transportClass θ C₁ ∪ transportClass θ C₂ := by
  ext L
  simp only [transportClass, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, hK | hK, hL⟩
    · exact Or.inl ⟨K, hK, hL⟩
    · exact Or.inr ⟨K, hK, hL⟩
  · rintro (⟨K, hK, hL⟩ | ⟨K, hK, hL⟩)
    · exact ⟨K, Or.inl hK, hL⟩
    · exact ⟨K, Or.inr hK, hL⟩

/-- ... and over arbitrary indexed unions — the DNF form of the
receipt. -/
theorem transportClass_iUnion {ι : Sort*} (θ : X → Y)
    (C : ι → Set (FellCloseds (SubProbabilityMeasure Y))) :
    transportClass θ (⋃ i, C i) = ⋃ i, transportClass θ (C i) := by
  ext L
  simp only [transportClass, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, ⟨i, hKi⟩, hL⟩
    exact ⟨i, K, hKi, hL⟩
  · rintro ⟨i, K, hKi, hL⟩
    exact ⟨K, ⟨i, hKi⟩, hL⟩

/-- The dictionary at hyperspace-point level: the transport of an ideal
point is the ideal point of the transported system. -/
theorem transportClass_singleton_compileF [Nonempty X] [Nonempty Y]
    (hθ : Continuous θ) {f : Penalty Y} (hf : LowerSemicontinuous f) :
    transportClass θ {compileF f hf}
      = {compileF (pullPen hθ f) (lowerSemicontinuous_pullPen hθ hf)} := by
  ext L
  simp only [transportClass, Set.mem_setOf_eq, Set.mem_singleton_iff,
    exists_eq_left, coe_compileF]
  constructor
  · intro hL
    exact FellCloseds.ext (hL.trans (compile_pullPen hθ f).symm)
  · rintro rfl
    rw [coe_compileF]
    exact compile_pullPen hθ f

/-- The safety face transports unconditionally: body preimages preserve
containment. -/
theorem transport_safety_face [Nonempty X] (hθ : Continuous θ)
    {u : Penalty Y} {K : Set (SubProbabilityMeasure Y)}
    (hK : K ⊆ compile u) :
    push θ ⁻¹' K ⊆ compile (pullPen hθ u) := by
  rw [compile_pullPen]
  exact Set.preimage_mono hK

/-- The escape face transports exactly onto the range: non-surjective
pushforwards lose escape witnesses — the seam the structure theorem's
surjectivity hypothesis guards. -/
theorem transport_escape_iff [Nonempty X] (hθ : Continuous θ)
    {v : Penalty Y} {K : Set (SubProbabilityMeasure Y)} :
    ((push θ ⁻¹' K) ∩ (compile (pullPen hθ v))ᶜ).Nonempty
      ↔ (K ∩ Set.range (push θ) ∩ (compile v)ᶜ).Nonempty := by
  rw [compile_pullPen]
  constructor
  · rintro ⟨y, hyK, hyv⟩
    exact ⟨push θ y, ⟨hyK, ⟨y, rfl⟩⟩, hyv⟩
  · rintro ⟨x, ⟨hxK, ⟨y, rfl⟩⟩, hxv⟩
    exact ⟨y, hxK, hxv⟩

/-- A class is saturated for an outcome map when it is a union of
fibres of the pushforward: the fingerprint of having arisen as a body
preimage. -/
def Saturated (θ : X → Y) (L : Set (SubProbabilityMeasure X)) : Prop :=
  L = push θ ⁻¹' (push θ '' L)

omit [TopologicalSpace Y] [BorelSpace Y] in
/-- Preimages are saturated — nothing consumed. -/
theorem saturated_preimage (θ : X → Y) (S : Set (SubProbabilityMeasure Y)) :
    Saturated θ (push θ ⁻¹' S) :=
  (Set.preimage_image_preimage).symm

/-- **Structure theorem, forward inclusion**: along a transport with
surjective pushforward, the transported class of a crescent sits inside
the crescent of the transported atom intersected with the saturated
classes.  Surjectivity is consumed only in the escape leg — exactly as
at the finite stratum. -/
theorem transportClass_crescentClass_subset [Nonempty X]
    (hθ : Continuous θ)
    (hsurj : Function.Surjective
      (push θ : SubProbabilityMeasure X → SubProbabilityMeasure Y))
    (u : Penalty Y) (𝒱 : Set (Penalty Y)) :
    transportClass θ (crescentClass u 𝒱)
      ⊆ crescentClass (pullPen hθ u) (pullPen hθ '' 𝒱)
        ∩ {L | Saturated θ (L : Set (SubProbabilityMeasure X))} := by
  rintro L ⟨K, hK, hL⟩
  obtain ⟨hsub, hesc⟩ := mem_crescentClass_iff.mp hK
  refine ⟨mem_crescentClass_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [hL]
    exact transport_safety_face hθ hsub
  · rintro v' ⟨v, hv, rfl⟩
    rw [hL, transport_escape_iff hθ]
    obtain ⟨x, hxK, hxv⟩ := hesc v hv
    have hrange : x ∈ Set.range (push θ) :=
      hsurj.range_eq ▸ Set.mem_univ x
    exact ⟨x, ⟨hxK, hrange⟩, hxv⟩
  · rw [Set.mem_setOf_eq, hL]
    exact saturated_preimage θ _

/-- **Structure theorem, reverse membership**: a saturated member of
the pulled atom's crescent whose image body is CLOSED arises as a
transport.  The image-closedness supply is the honest general-stratum
residue: at the finite stratum compactness paid it silently (images of
compacts are compact, hence hyperspace citizens); here it is a named
hypothesis — no surjectivity consumed. -/
theorem mem_transportClass_of_closed_image [Nonempty X]
    (hθ : Continuous θ) {u : Penalty Y} {𝒱 : Set (Penalty Y)}
    {L : FellCloseds (SubProbabilityMeasure X)}
    (hcres : L ∈ crescentClass (pullPen hθ u) (pullPen hθ '' 𝒱))
    (hsat : Saturated θ (L : Set (SubProbabilityMeasure X)))
    (himg : IsClosed (push θ '' (L : Set (SubProbabilityMeasure X)))) :
    L ∈ transportClass θ (crescentClass u 𝒱) := by
  obtain ⟨hsubL, hescL⟩ := mem_crescentClass_iff.mp hcres
  refine ⟨⟨push θ '' (L : Set (SubProbabilityMeasure X)), himg⟩,
    mem_crescentClass_iff.mpr ⟨?_, ?_⟩, hsat⟩
  · show push θ '' (L : Set (SubProbabilityMeasure X)) ⊆ compile u
    rw [Set.image_subset_iff, ← compile_pullPen hθ]
    exact hsubL
  · intro v hv
    show ((push θ '' (L : Set (SubProbabilityMeasure X)))
      ∩ (compile v)ᶜ).Nonempty
    obtain ⟨y, hyL, hyv⟩ := hescL (pullPen hθ v) ⟨v, hv, rfl⟩
    refine ⟨push θ y, ⟨y, hyL, rfl⟩, ?_⟩
    intro hmem
    exact hyv (by
      rw [compile_pullPen hθ]
      exact hmem)

/-- **The structure theorem of the surjective stratum, general
carrier**: along a transport whose pushforward is surjective AND a
closed map, the transported class of a crescent is exactly the crescent
of the transported atom intersected with the saturated classes.  The
closed-map hypothesis is what compactness bought at the finite stratum,
now priced explicitly. -/
theorem transportClass_crescentClass [Nonempty X] (hθ : Continuous θ)
    (hsurj : Function.Surjective
      (push θ : SubProbabilityMeasure X → SubProbabilityMeasure Y))
    (hmap : IsClosedMap
      (push θ : SubProbabilityMeasure X → SubProbabilityMeasure Y))
    (u : Penalty Y) (𝒱 : Set (Penalty Y)) :
    transportClass θ (crescentClass u 𝒱)
      = crescentClass (pullPen hθ u) (pullPen hθ '' 𝒱)
        ∩ {L | Saturated θ (L : Set (SubProbabilityMeasure X))} := by
  refine subset_antisymm
    (transportClass_crescentClass_subset hθ hsurj u 𝒱) ?_
  rintro L ⟨hcres, hsat⟩
  exact mem_transportClass_of_closed_image hθ hcres hsat
    (hmap _ L.isClosed)

/-! ## The compositor stratum -/

/-- The radial (grade-product) composite of two bodies at the general
carrier: on each ray, the composite admits exactly the products of the
component ray lengths. -/
def radProd (A B : Set (SubProbabilityMeasure X)) :
    Set (SubProbabilityMeasure X) :=
  {ν | ∃ (μ : ProbabilityMeasure X) (γ₁ γ₂ : ℝ≥0),
    (∃ a ∈ A, (a : FiniteMeasure X) = γ₁ • μ.toFiniteMeasure)
    ∧ (∃ b ∈ B, (b : FiniteMeasure X) = γ₂ • μ.toFiniteMeasure)
    ∧ (ν : FiniteMeasure X) = (γ₁ * γ₂) • μ.toFiniteMeasure}

/-- Mechanism composition is the grade product, membership form: the
body of `f + g` consists of the fibrewise products of ray lengths. -/
theorem mem_compile_add_iff {f g : Penalty X} {ν : SubProbabilityMeasure X} :
    ν ∈ compile (f + g)
      ↔ ∃ (μ : ProbabilityMeasure X) (γ₁ γ₂ : ℝ≥0),
          γ₁ ≤ gradeN (f μ) ∧ γ₂ ≤ gradeN (g μ)
          ∧ (ν : FiniteMeasure X) = (γ₁ * γ₂) • μ.toFiniteMeasure := by
  constructor
  · rintro ⟨μ, γ, hle, he⟩
    rw [Pi.add_apply, gradeN_add] at hle
    rcases eq_or_ne (gradeN (f μ)) 0 with hf0 | hf0
    · have hγ0 : γ = 0 := le_antisymm
        (by rw [hf0, zero_mul] at hle; exact hle) zero_le
      exact ⟨μ, 0, 0, zero_le, zero_le, by
        rw [mul_zero, ← hγ0]
        exact he⟩
    · have hfpos : 0 < gradeN (f μ) := pos_iff_ne_zero.mpr hf0
      refine ⟨μ, gradeN (f μ), γ / gradeN (f μ), le_rfl, ?_, ?_⟩
      · rw [div_le_iff₀ hfpos]
        rw [mul_comm (gradeN (f μ)) (gradeN (g μ))] at hle
        exact hle
      · rw [he]
        congr 1
        rw [mul_comm, div_mul_cancel₀ _ hfpos.ne']
  · rintro ⟨μ, γ₁, γ₂, hle1, hle2, he⟩
    refine ⟨μ, γ₁ * γ₂, ?_, he⟩
    rw [Pi.add_apply, gradeN_add]
    exact mul_le_mul' hle1 hle2

/-- **The compositor dictionary at the general carrier**: the body of a
sum of penalties is the radial product of the bodies.  (Mutant m3 drops
the grade product from `radProd`'s scaling; both inclusions here must
go red.) -/
theorem compile_add_radProd [Nonempty X] (f g : Penalty X) :
    compile (f + g) = radProd (compile f) (compile g) := by
  ext ν
  constructor
  · intro hν
    obtain ⟨μ, γ₁, γ₂, hle1, hle2, he⟩ := mem_compile_add_iff.mp hν
    exact ⟨μ, γ₁, γ₂,
      ⟨SubProbabilityMeasure.scalePoint γ₁ (hle1.trans (gradeN_le_one _)) μ,
        scalePoint_mem_compile hle1,
        SubProbabilityMeasure.coe_scalePoint _ _ _⟩,
      ⟨SubProbabilityMeasure.scalePoint γ₂ (hle2.trans (gradeN_le_one _)) μ,
        scalePoint_mem_compile hle2,
        SubProbabilityMeasure.coe_scalePoint _ _ _⟩, he⟩
  · rintro ⟨μ, γ₁, γ₂, ⟨a, haA, hae⟩, ⟨b, hbB, hbe⟩, he⟩
    rcases eq_or_ne γ₁ 0 with rfl | h1
    · have hν0 : ν = 0 := SubProbabilityMeasure.ext (by
        rw [he, zero_mul, zero_smul, SubProbabilityMeasure.coe_zero])
      rw [hν0]
      exact zero_mem_compile _
    · rcases eq_or_ne γ₂ 0 with rfl | h2
      · have hν0 : ν = 0 := SubProbabilityMeasure.ext (by
          rw [he, mul_zero, zero_smul, SubProbabilityMeasure.coe_zero])
        rw [hν0]
        exact zero_mem_compile _
      · exact mem_compile_add_iff.mpr ⟨μ, γ₁, γ₂,
          compile_scale_le haA h1 hae, compile_scale_le hbB h2 hbe, he⟩

/-- Penalty-level composition preserves citizenship at the general
carrier. -/
theorem lowerSemicontinuous_add_penalty {f g : Penalty X}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (f + g) :=
  hf.add hg

/-- The compositor's Universe face — pull each component to the glued
apex, add — preserves citizenship for *any* continuous outcome maps
(no surjectivity: composition rides pullback continuity and sum
semicontinuity only). -/
theorem lowerSemicontinuous_boxplus {Y₁ Y₂ : Type*}
    [MeasurableSpace Y₁] [TopologicalSpace Y₁] [BorelSpace Y₁]
    [MeasurableSpace Y₂] [TopologicalSpace Y₂] [BorelSpace Y₂]
    {j₁ : X → Y₁} {j₂ : X → Y₂} (hj₁ : Continuous j₁) (hj₂ : Continuous j₂)
    {f : Penalty Y₁} {g : Penalty Y₂}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (pullPen hj₁ f + pullPen hj₂ g) :=
  (lowerSemicontinuous_pullPen hj₁ hf).add
    (lowerSemicontinuous_pullPen hj₂ hg)

/-! ## The off-surjective seam, at the general carrier

The witness pair lives over `X := Unit`, `Y := Bool` (discrete Borel
spaces), `θ := const false`.  The liveness mark is the mass-on-`true`
observation, expressed through the narrow topology's own test pairing —
continuous, hence a citizen — whose escape region `{trueMass > 0}` sits
entirely off the range of the pushforward. -/

section OffSurjective

/-- The indicator of `{true}` as a bounded continuous test
observation. -/
noncomputable def trueIndicator : Bool →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

@[simp] theorem trueIndicator_apply (b : Bool) :
    trueIndicator b = if b then 1 else 0 := rfl

/-- The mass-on-`true` penalty: the narrow topology's own pairing
against the `trueIndicator` observation. -/
noncomputable def trueMass : Penalty Bool :=
  fun μ => ((μ.toFiniteMeasure.testAgainstNN trueIndicator : ℝ≥0) : ℝ≥0∞)

theorem continuous_trueMass : Continuous trueMass :=
  ENNReal.continuous_coe.comp
    (ProbabilityMeasure.continuous_testAgainstNN_eval trueIndicator)

/-- The point mass at an outcome, as a probability direction. -/
noncomputable def diracProb {Z : Type*} [MeasurableSpace Z] (z : Z) :
    ProbabilityMeasure Z :=
  ⟨Measure.dirac z, Measure.dirac.isProbabilityMeasure⟩

theorem trueMass_diracProb (b : Bool) :
    trueMass (diracProb b) = ((trueIndicator b : ℝ≥0) : ℝ≥0∞) := by
  show ((((diracProb b).toFiniteMeasure).testAgainstNN trueIndicator : ℝ≥0)
      : ℝ≥0∞) = _
  rw [FiniteMeasure.testAgainstNN_coe_eq]
  exact lintegral_dirac b fun x => ((trueIndicator x : ℝ≥0) : ℝ≥0∞)

@[simp] theorem trueMass_diracProb_false :
    trueMass (diracProb false) = 0 := by
  rw [trueMass_diracProb]
  simp

@[simp] theorem trueMass_diracProb_true :
    trueMass (diracProb true) = 1 := by
  rw [trueMass_diracProb]
  simp

/-- Every probability direction on `Unit` pushes to the point mass at
`false` along the constant map. -/
theorem probPush_const_false (μ : ProbabilityMeasure Unit) :
    probPush (continuous_const : Continuous fun _ : Unit => false) μ
      = diracProb false := by
  apply Subtype.ext
  show ((μ : Measure Unit)).map (fun _ : Unit => false) = Measure.dirac false
  rw [Measure.map_const, measure_univ, one_smul]

/-- The pulled liveness mark is the zero penalty: the mark's whole
escape region sits off the range. -/
theorem pullPen_trueMass_eq_zero :
    pullPen (continuous_const : Continuous fun _ : Unit => false) trueMass
      = 0 := by
  funext μ
  rw [pullPen_apply, probPush_const_false, trueMass_diracProb_false,
    Pi.zero_apply]

/-- The full-mass point at `true`: the state the liveness mark's escape
region contains. -/
noncomputable def diracTrueState : SubProbabilityMeasure Bool :=
  ⟨(diracProb true).toFiniteMeasure,
    (ProbabilityMeasure.mass_toFiniteMeasure _).le⟩

theorem diracTrueState_notMem_compile_trueMass :
    diracTrueState ∉ compile trueMass := by
  intro hmem
  have hd : ((diracTrueState : SubProbabilityMeasure Bool) : FiniteMeasure Bool)
      = (1 : ℝ≥0) • (diracProb true).toFiniteMeasure := by
    rw [one_smul]
    rfl
  have hb := compile_scale_le hmem one_ne_zero hd
  have hlt : gradeN (trueMass (diracProb true)) < 1 := by
    have h := gradeN_lt_gradeN_iff.mpr
      (by rw [trueMass_diracProb_true]; exact zero_lt_one
        : (0 : ℝ≥0∞) < trueMass (diracProb true))
    rwa [gradeN_zero] at h
  exact absurd hb (not_le.mpr hlt)

/-- **Judgment invariance fails downward off the surjective stratum**:
a coupled judgment holding upstairs whose pullback fails — the liveness
dip sits outside the range of the pushforward and dies under
transport. -/
theorem exists_coupledSat_not_pullPen :
    ∃ (θ : Unit → Bool) (hθ : Continuous θ) (σ u : Penalty Bool)
      (𝒱 : Set (Penalty Bool)),
      CoupledSat σ u 𝒱
        ∧ ¬ CoupledSat (pullPen hθ σ) (pullPen hθ u) (pullPen hθ '' 𝒱) := by
  refine ⟨fun _ => false, continuous_const, 0, 0, {trueMass},
    ⟨le_rfl, ?_⟩, ?_⟩
  · rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨diracProb true, by
      rw [Pi.zero_apply, trueMass_diracProb_true]
      exact zero_lt_one⟩
  · rintro ⟨-, hlive⟩
    obtain ⟨μ, hμ⟩ := hlive
      (pullPen (continuous_const : Continuous fun _ : Unit => false) trueMass)
      ⟨trueMass, Set.mem_singleton _, rfl⟩
    rw [pullPen_zero, Pi.zero_apply, pullPen_apply, probPush_const_false,
      trueMass_diracProb_false] at hμ
    exact absurd hμ (lt_irrefl 0)

/-- **...and upward**: a pulled judgment holding downstairs whose
original fails — safety is violated outside the range, where the
pullback cannot see. -/
theorem exists_coupledSat_pullPen_not :
    ∃ (θ : Unit → Bool) (hθ : Continuous θ) (σ u : Penalty Bool)
      (𝒱 : Set (Penalty Bool)),
      CoupledSat (pullPen hθ σ) (pullPen hθ u) (pullPen hθ '' 𝒱)
        ∧ ¬ CoupledSat σ u 𝒱 := by
  refine ⟨fun _ => false, continuous_const, 0, trueMass, ∅,
    ⟨fun μ => ?_, ?_⟩, ?_⟩
  · rw [pullPen_apply, probPush_const_false, trueMass_diracProb_false]
    exact zero_le
  · rintro v ⟨w, hw, rfl⟩
    exact absurd hw (Set.notMem_empty w)
  · rintro ⟨hsafe, -⟩
    have h := hsafe (diracProb true)
    rw [trueMass_diracProb_true, Pi.zero_apply] at h
    exact absurd (le_antisymm h zero_le) one_ne_zero

/-- **Raw image transport escapes the pulled atom's crescent** off the
surjective stratum, at the general carrier: the full-carrier body
transports (as a preimage) from the full-carrier body upstairs, but the
transported class member fails the pulled atom's escape demand — the
pulled liveness mark is the zero penalty, against which nothing
escapes. -/
theorem exists_transport_not_subset_pulled_crescent :
    ∃ (θ : Unit → Bool) (hθ : Continuous θ) (u : Penalty Bool)
      (𝒱 : Set (Penalty Bool)),
      LowerSemicontinuous u ∧ (∀ v ∈ 𝒱, LowerSemicontinuous v) ∧ 𝒱.Finite ∧
      ¬ (transportClass θ (crescentClass u 𝒱)
          ⊆ crescentClass (pullPen hθ u) (pullPen hθ '' 𝒱)) := by
  refine ⟨fun _ => false, continuous_const, 0, {trueMass},
    lowerSemicontinuous_const, ?_, Set.finite_singleton _, ?_⟩
  · rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact continuous_trueMass.lowerSemicontinuous
  · intro hsub
    have hKmem : (⟨Set.univ, isClosed_univ⟩ :
        FellCloseds (SubProbabilityMeasure Bool))
          ∈ crescentClass 0 {trueMass} := by
      rw [mem_crescentClass_iff]
      constructor
      · rw [compile_zero]
        exact fun x _ => Set.mem_univ x
      · intro v hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact ⟨diracTrueState, Set.mem_univ _,
          diracTrueState_notMem_compile_trueMass⟩
    have hLmem : (⟨Set.univ, isClosed_univ⟩ :
        FellCloseds (SubProbabilityMeasure Unit))
          ∈ transportClass (fun _ => false) (crescentClass 0 {trueMass}) :=
      ⟨_, hKmem, (Set.preimage_univ).symm⟩
    have hLcres := hsub hLmem
    obtain ⟨-, hesc⟩ := mem_crescentClass_iff.mp hLcres
    obtain ⟨y, -, hy⟩ := hesc
      (pullPen (continuous_const : Continuous fun _ : Unit => false) trueMass)
      ⟨trueMass, Set.mem_singleton _, rfl⟩
    apply hy
    rw [pullPen_trueMass_eq_zero, compile_zero]
    exact Set.mem_univ y

end OffSurjective

end SuFunctor.Universe.General
