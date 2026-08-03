import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.Semicontinuity.Basic
import SuFunctor.Plain.Penalty

/-! # Subprobability joints at the general stratum

The measure-theoretic stratum of the spec-class decoration tier's
scalar stock: subprobability Borel measures over an arbitrary
measurable carrier, their pushforward along carrier maps, penalty
functionals with contravariant transport, and the composite-penalty
calculus — the same theorem shapes as `SuFunctor.Plain.Penalty`, one
stratum up, with two deliberate differences that are constitutive of
the stratum rather than incidental:

* **Measurability is the morphism datum.**  The finite stratum's
  pushforward is functorial over *arbitrary* carrier maps (a finite
  sum reindexes unconditionally).  Here the operations are total in
  the carrier map (mathlib's junk-value convention for
  `MeasureTheory.Measure.map`, under which the subprobability carrier
  is still closed, by `FiniteMeasure.mass_map_le`), but the *laws*
  — functoriality (`push_push`) and exact mass transport
  (`mass_push`) — hold along measurable maps: the general stratum's
  tight maps are measurable maps, and the categorical packaging in
  `SuFunctor.Plain.GeneralFunctor` takes exactly that as its base.
* **Topology is content.**  The carrier inherits the subspace
  topology of the weak (narrow) topology on finite measures;
  pushforward along a continuous map is continuous
  (`continuous_push`, mathlib's `FiniteMeasure.continuous_map` —
  marginalization is the functor part of the Giry monad, and
  `push_toMeasure` exhibits the identification by `rfl`), and the
  standing membership hypothesis for penalty functionals is lower
  semicontinuity, with its closure calculus (`lsc` section) and the
  wall-grade consumer: attainment of the infimum on nonempty compact
  sets of joints.

The coherence cores of the composite-penalty calculus
(`pull_mboxplus_of_comm`, `pull_mboxplus_assoc`,
`pull_mboxplus_zero_left`/`_right`) are stated base-free, with the
comparison identities of a wiring base carried as commuting-square
*hypotheses*: the finite stratum's state-family presentation
discharges those squares definitionally (its comparison maps are
`Σ`-reshuffles), which is how `SuFunctor.Plain.SpecFunctor`'s cores
arise as the special case where every square is `rfl`.

Compact support is a *subclass*, not a restriction: the calculus above
needs no support hypothesis, and `IsCompactlySupported` — closed under
pushforward along continuous maps into Hausdorff carriers
(`IsCompactlySupported.push`) — is available where a downstream
tightness or liveness argument wants it.

## Preregistered mutant battery

Recorded before elaboration, run on side branches against the green
tip, never landed; each perturbs one load-bearing hypothesis and each
prediction names the exact locus expected to refuse:

* **m1 — drop measurability from functoriality**: delete the
  `Measurable` hypotheses of `MeasJoint.push_push`; predicted red at
  the `Measure.map_map` application inside it (functoriality is
  exactly where the general stratum's measurability binds; the finite
  stratum's `push_push` needed none).
* **m2 — weaken the membership hypothesis**: drop the
  `LowerSemicontinuous` hypothesis of
  `exists_isMinOn_of_lowerSemicontinuous`; predicted red at the
  `LowerSemicontinuousOn.exists_isMinOn` application (attainment is
  the wall-grade consumer that forces lower semicontinuity as the
  standing hypothesis, rather than any weaker regularity).
* **m3 — break the seam's mass bookkeeping**: in
  `SuFunctor.Plain.GeneralSeam`, replace the weighted point-mass sum
  `∑ᵢ μ.wt i • δᵢ` by the unweighted `∑ᵢ δᵢ`; predicted red at
  `Joint.toMeas`'s mass field (a support's worth of unit masses is
  not submass) and at `toMeas_mass`.

## Design notes, at the stratum boundary

Four decisions where the general stratum deliberately differs from a
verbatim transposition of the finite one, each argued in place in the
relevant docstring: operations total with laws hypothesized (this
header, above); the tight-tier base contravariant over measurable
carriers (`SuFunctor.Plain.GeneralFunctor`); coherence cores base-free
with the comparison squares as hypotheses rather than a
double-categorical total over a measurable wiring base (the `Cores`
section — the finite total's state-family presentation makes those
squares definitional, and a measurable base owes its own transport
data before a total can be assembled); the subprobability carrier
spelled as the mass-bounded subtype of `FiniteMeasure`, matching the
classical carrier of the point-free development so the two remain
definitionally reconcilable.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {X Y Z U V W : Type u}

/-- A subprobability joint over a measurable carrier: a finite Borel
measure of total mass at most one.  Mass strictly below one is
meaningful (a joint licensed to lose mass), matching the
partiality-native reading of the denotation tier — and matching the
finite stratum's `Joint`, of which this carrier is the general form
(`SuFunctor.Plain.GeneralSeam`). -/
def MeasJoint (X : Type u) [MeasurableSpace X] : Type u :=
  {μ : FiniteMeasure X // μ.mass ≤ 1}

namespace MeasJoint

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The underlying finite measure. -/
def toFiniteMeasure (μ : MeasJoint X) : FiniteMeasure X := μ.1

instance : Coe (MeasJoint X) (FiniteMeasure X) := ⟨toFiniteMeasure⟩

theorem mass_le_one (μ : MeasJoint X) : μ.1.mass ≤ 1 := μ.2

theorem ext {μ ν : MeasJoint X} (h : μ.1 = ν.1) : μ = ν := Subtype.ext h

/-- Equality of subprobability joints follows from equality of the
underlying measures. -/
theorem ext' {μ ν : MeasJoint X} (h : (μ.1 : Measure X) = (ν.1 : Measure X)) :
    μ = ν :=
  ext (FiniteMeasure.toMeasure_injective h)

/-- The zero joint: all mass lost.  It exists over every measurable
carrier, which keeps the refutation pins of the battery
carrier-uniform, exactly as at the finite stratum. -/
def zero (X : Type u) [MeasurableSpace X] : MeasJoint X :=
  ⟨0, by rw [FiniteMeasure.zero_mass]; exact zero_le_one⟩

@[simp] theorem zero_val (X : Type u) [MeasurableSpace X] :
    (zero X).1 = 0 := rfl

instance : Inhabited (MeasJoint X) := ⟨zero X⟩

/-- Pushforward of a subprobability joint along a carrier map.  The
operation is total (mathlib's junk-value convention for non-measurable
maps, under which mass can only shrink: `FiniteMeasure.mass_map_le`);
its laws below carry measurability hypotheses — at the general stratum,
functoriality is exactly where measurability binds. -/
def push (h : X → Y) (μ : MeasJoint X) : MeasJoint Y :=
  ⟨μ.1.map h, le_trans (FiniteMeasure.mass_map_le h μ.1) μ.2⟩

/-- The underlying measure of a pushforward is `Measure.map` — the
functor part of the Giry monad, definitionally. -/
@[simp] theorem push_toMeasure (h : X → Y) (μ : MeasJoint X) :
    ((μ.push h).1 : Measure Y) = (μ.1 : Measure X).map h := rfl

@[simp] theorem push_id (μ : MeasJoint X) : μ.push id = μ :=
  ext' (Measure.map_id)

/-- Pushforward is functorial along measurable maps: the two-step image
is the image along the composite.  (The finite stratum's `push_push`
needed no measurability; this hypothesis is constitutive of the general
stratum.) -/
theorem push_push (h₁ : X → Y) (h₂ : Y → Z) (hm₁ : Measurable h₁)
    (hm₂ : Measurable h₂) (μ : MeasJoint X) :
    (μ.push h₁).push h₂ = μ.push (h₂ ∘ h₁) :=
  ext' (Measure.map_map hm₂ hm₁)

/-- Mass is transported exactly along measurable maps (along arbitrary
maps it can only shrink, which is what keeps `push` total). -/
theorem mass_push (h : X → Y) (hm : Measurable h) (μ : MeasJoint X) :
    (μ.push h).1.mass = μ.1.mass := by
  show (μ.1.map h) Set.univ = μ.1 Set.univ
  rw [FiniteMeasure.map_apply μ.1 hm MeasurableSet.univ, Set.preimage_univ]

end MeasJoint

/-- A penalty functional on subprobability joints over a measurable
carrier: graded prohibition, valued in `ℝ≥0∞` — `0` permitted outright,
`⊤` forbidden outright, intermediate values pricing partial
incompatibility.  The general stratum of `SuFunctor.Plain.Pen`. -/
abbrev MeasPen (X : Type u) [MeasurableSpace X] : Type u :=
  MeasJoint X → ℝ≥0∞

namespace MeasPen

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Transport of a penalty along a carrier map, contravariantly:
evaluate on the pushforward of the joint. -/
def pull (h : X → Y) (F : MeasPen Y) : MeasPen X :=
  fun μ => F (μ.push h)

@[simp] theorem pull_apply (h : X → Y) (F : MeasPen Y) (μ : MeasJoint X) :
    pull h F μ = F (μ.push h) := rfl

@[simp] theorem pull_id (F : MeasPen X) : pull id F = F :=
  funext fun μ => congrArg F (MeasJoint.push_id μ)

/-- Contravariant functoriality of penalty transport, along measurable
maps. -/
theorem pull_pull (h₂ : Y → Z) (h₁ : X → Y) (hm₂ : Measurable h₂)
    (hm₁ : Measurable h₁) (F : MeasPen Z) :
    pull h₁ (pull h₂ F) = pull (h₂ ∘ h₁) F :=
  funext fun μ => congrArg F (MeasJoint.push_push h₁ h₂ hm₁ hm₂ μ)

@[simp] theorem pull_const (h : X → Y) (c : ℝ≥0∞) :
    pull h (fun _ => c) = fun _ => c := rfl

end MeasPen

/-! ## The composite-penalty calculus -/

section Mboxplus

variable [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]

/-- Pushforward-then-add over an arbitrary marginalization pair:
marginalize a joint over a common carrier to each component, evaluate,
add.  The composite penalty of the chapter (`f ⊞ g`), at the general
stratum, base-free: the two maps are *any* pair out of a common
carrier, of which a wiring base's glued-apex projections are the
motivating instance. -/
def mboxplus (π₁ : W → U) (π₂ : W → V) (F : MeasPen U) (G : MeasPen V) :
    MeasPen W :=
  fun ν => F (ν.push π₁) + G (ν.push π₂)

@[simp] theorem mboxplus_apply (π₁ : W → U) (π₂ : W → V) (F : MeasPen U)
    (G : MeasPen V) (ν : MeasJoint W) :
    mboxplus π₁ π₂ F G ν = F (ν.push π₁) + G (ν.push π₂) := rfl

end Mboxplus

/-! ## The coherence cores, base-free

Each law of a class-level compositor over a wiring base reduces to one
of the following shapes, in which the base's comparison identities
appear as commuting-square hypotheses.  At the finite stratum
(`SuFunctor.Plain.SpecFunctor`, the `Cores` section) the base is the
state-family presentation and every square is definitional; a
measurable wiring base discharges the same squares with its own
transport data. -/

section Cores

variable [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]

/-- Naturality core: transporting a composite along a map compatible
with both marginalization squares is the composite of the
transports. -/
theorem pull_mboxplus_of_comm {W' U' V' : Type u} [MeasurableSpace W']
    [MeasurableSpace U'] [MeasurableSpace V']
    (k : W → W') (π₁ : W' → U') (π₂ : W' → V') (π₁' : W → U) (π₂' : W → V)
    (k₁ : U → U') (k₂ : V → V')
    (hk : Measurable k) (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂)
    (hπ₁' : Measurable π₁') (hπ₂' : Measurable π₂')
    (hk₁ : Measurable k₁) (hk₂ : Measurable k₂)
    (sq₁ : π₁ ∘ k = k₁ ∘ π₁') (sq₂ : π₂ ∘ k = k₂ ∘ π₂')
    (F : MeasPen U') (G : MeasPen V') :
    MeasPen.pull k (mboxplus π₁ π₂ F G) =
      mboxplus π₁' π₂' (MeasPen.pull k₁ F) (MeasPen.pull k₂ G) := by
  funext ν
  simp only [MeasPen.pull_apply, mboxplus_apply]
  rw [MeasJoint.push_push k π₁ hk hπ₁, MeasJoint.push_push k π₂ hk hπ₂,
    sq₁, sq₂, ← MeasJoint.push_push π₁' k₁ hπ₁' hk₁,
    ← MeasJoint.push_push π₂' k₂ hπ₂' hk₂]

/-- Associativity core: reassociating a threefold composite along a
map compatible with the two association orders' marginalization data is
reassociation of the sum. -/
theorem pull_mboxplus_assoc {W' T S V₁ V₂ V₃ : Type u}
    [MeasurableSpace W'] [MeasurableSpace T] [MeasurableSpace S]
    [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace V₃]
    (a : W' → W) (π₁₂ : W → T) (π₃ : W → V₃) (q₁ : T → V₁) (q₂ : T → V₂)
    (r₁ : W' → V₁) (r₂₃ : W' → S) (s₂ : S → V₂) (s₃ : S → V₃)
    (ha : Measurable a) (hπ₁₂ : Measurable π₁₂) (hπ₃ : Measurable π₃)
    (hq₁ : Measurable q₁) (hq₂ : Measurable q₂)
    (hr₂₃ : Measurable r₂₃) (hs₂ : Measurable s₂) (hs₃ : Measurable s₃)
    (e₁ : q₁ ∘ π₁₂ ∘ a = r₁) (e₂ : q₂ ∘ π₁₂ ∘ a = s₂ ∘ r₂₃)
    (e₃ : π₃ ∘ a = s₃ ∘ r₂₃)
    (F : MeasPen V₁) (G : MeasPen V₂) (H : MeasPen V₃) :
    MeasPen.pull a (mboxplus π₁₂ π₃ (mboxplus q₁ q₂ F G) H) =
      mboxplus r₁ r₂₃ F (mboxplus s₂ s₃ G H) := by
  funext ν
  simp only [MeasPen.pull_apply, mboxplus_apply]
  rw [MeasJoint.push_push a π₁₂ ha hπ₁₂,
    MeasJoint.push_push (π₁₂ ∘ a) q₁ (hπ₁₂.comp ha) hq₁,
    MeasJoint.push_push (π₁₂ ∘ a) q₂ (hπ₁₂.comp ha) hq₂,
    MeasJoint.push_push a π₃ ha hπ₃, e₁, e₂, e₃,
    ← MeasJoint.push_push r₂₃ s₂ hr₂₃ hs₂,
    ← MeasJoint.push_push r₂₃ s₃ hr₂₃ hs₃, add_assoc]

/-- Left unit core: composing with the zero penalty and stripping the
unit along any section of the second marginalization returns the
penalty on the nose — unit transparency without tax, base-free. -/
theorem pull_mboxplus_zero_left (e : V → W) (π₁ : W → U) (π₂ : W → V)
    (he : Measurable e) (hπ₂ : Measurable π₂) (hsec : π₂ ∘ e = id)
    (F : MeasPen V) :
    MeasPen.pull e (mboxplus π₁ π₂ (fun _ => 0) F) = F := by
  funext ν
  simp only [MeasPen.pull_apply, mboxplus_apply, zero_add]
  rw [MeasJoint.push_push e π₂ he hπ₂, hsec, MeasJoint.push_id]

/-- Right unit core, dually. -/
theorem pull_mboxplus_zero_right (e : U → W) (π₁ : W → U) (π₂ : W → V)
    (he : Measurable e) (hπ₁ : Measurable π₁) (hsec : π₁ ∘ e = id)
    (F : MeasPen U) :
    MeasPen.pull e (mboxplus π₁ π₂ F (fun _ => 0)) = F := by
  funext ν
  simp only [MeasPen.pull_apply, mboxplus_apply, add_zero]
  rw [MeasJoint.push_push e π₁ he hπ₁, hsec, MeasJoint.push_id]

end Cores

/-! ## The weak topology, and lower semicontinuity as the standing
membership hypothesis -/

section WeakTopology

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The subspace topology of the weak (narrow) topology on finite
measures. -/
instance : TopologicalSpace (MeasJoint X) :=
  inferInstanceAs (TopologicalSpace {μ : FiniteMeasure X // μ.mass ≤ 1})

theorem continuous_toFiniteMeasure :
    Continuous (MeasJoint.toFiniteMeasure : MeasJoint X → FiniteMeasure X) :=
  continuous_subtype_val

variable [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]

/-- Pushforward of subprobability joints along a continuous map is
continuous in the weak topologies: marginalization is functorial
(`push_push`) *and* weakly continuous — the functor part of the Giry
monad, at the subprobability carrier. -/
theorem continuous_push {h : X → Y} (h_cont : Continuous h) :
    Continuous (fun μ : MeasJoint X => μ.push h) :=
  Continuous.subtype_mk
    ((FiniteMeasure.continuous_map h_cont).comp continuous_subtype_val) _

/-- Penalty transport preserves lower semicontinuity along continuous
maps: the standing membership hypothesis of the penalty universe is
closed under the tier's contravariant transport. -/
theorem lowerSemicontinuous_pull {h : X → Y} (h_cont : Continuous h)
    {F : MeasPen Y} (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (MeasPen.pull h F) :=
  hF.comp (continuous_push h_cont)

/-- The zero penalty is lower semicontinuous: the compositor's unit is
a citizen. -/
theorem lowerSemicontinuous_zeroPen :
    LowerSemicontinuous (fun _ : MeasJoint X => (0 : ℝ≥0∞)) :=
  lowerSemicontinuous_const

/-- **Attainment**: a lower semicontinuous penalty attains its infimum
on a nonempty compact set of joints — the wall-grade consumer of the
membership hypothesis, and the reason lower semicontinuity (rather
than any weaker regularity) is the standing hypothesis. -/
theorem exists_isMinOn_of_lowerSemicontinuous {F : MeasPen X}
    (hF : LowerSemicontinuous F) {K : Set (MeasJoint X)} (hne : K.Nonempty)
    (hK : IsCompact K) : ∃ μ ∈ K, IsMinOn F K μ :=
  LowerSemicontinuousOn.exists_isMinOn hne hK (hF.lowerSemicontinuousOn K)

end WeakTopology

section LscMboxplus

variable [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]
variable [TopologicalSpace U] [BorelSpace U] [TopologicalSpace V]
variable [BorelSpace V] [TopologicalSpace W] [OpensMeasurableSpace W]

/-- The composite penalty of lower semicontinuous penalties along
continuous marginalizations is lower semicontinuous: the compositor
preserves citizenship. -/
theorem lowerSemicontinuous_mboxplus {π₁ : W → U} {π₂ : W → V}
    (h₁ : Continuous π₁) (h₂ : Continuous π₂) {F : MeasPen U}
    {G : MeasPen V} (hF : LowerSemicontinuous F)
    (hG : LowerSemicontinuous G) :
    LowerSemicontinuous (mboxplus π₁ π₂ F G) :=
  LowerSemicontinuous.add (hF.comp (continuous_push h₁))
    (hG.comp (continuous_push h₂))

end LscMboxplus

/-! ## Compact support: a subclass, not a restriction

The calculus above holds on the full subprobability carrier; compact
support is the subclass a tightness or liveness argument restricts to,
and it is closed under the tier's transport. -/

section CompactSupport

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- A joint is compactly supported when some compact set carries all
of its mass. -/
def IsCompactlySupported (μ : MeasJoint X) : Prop :=
  ∃ K : Set X, IsCompact K ∧ (μ.1 : Measure X) Kᶜ = 0

omit [OpensMeasurableSpace X] in
/-- Every joint over a compact carrier is compactly supported. -/
theorem isCompactlySupported_of_compactSpace [CompactSpace X]
    (μ : MeasJoint X) : IsCompactlySupported μ :=
  ⟨Set.univ, isCompact_univ, by simp⟩

variable [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [T2Space Y]

/-- Compact support is closed under pushforward along continuous maps
into Hausdorff carriers: the image of a carrying compact carries the
image mass. -/
theorem IsCompactlySupported.push {h : X → Y} (h_cont : Continuous h)
    {μ : MeasJoint X} (hμ : IsCompactlySupported μ) :
    IsCompactlySupported (μ.push h) := by
  obtain ⟨K, hK, hK0⟩ := hμ
  refine ⟨h '' K, hK.image h_cont, ?_⟩
  rw [MeasJoint.push_toMeasure,
    Measure.map_apply h_cont.measurable
      (hK.image h_cont).isClosed.isOpen_compl.measurableSet]
  exact measure_mono_null
    (fun x hx hxK => hx (Set.mem_image_of_mem h hxK)) hK0

end CompactSupport

end

end Plain

end SuFunctor
