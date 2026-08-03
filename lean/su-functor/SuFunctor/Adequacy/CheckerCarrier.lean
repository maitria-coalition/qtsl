import SuFunctor.Plain.CheckerFace
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # The checker carrier: the sequent's valuation carrier as a wire object's record space

The checker face (`SuFunctor.Plain.CheckerFace`) identifies the
certificate calculus's verdict with a vanishing upper probability at
the sequent's own valuation carrier.  The wiring layer
(`SuFunctor.Adequacy.SemanticUniverseWiring`) states its judgments over
a record space supplied directly, naming the construction of the wire
object from the judged artifact as a separate stratum.  This module is
that stratum, at verdict altitude: it ties the face to the semantic
universe's fibres by exhibiting the wire object a sequent's verdict is
judged over, in three identifications.

* **The wall dialect** (`possWall_eq_wallPen`): the face module's
  possibilistic wall *is* the wiring layer's wall penalty of the credal
  compile — one definition met from two sides, recorded as an equation.
* **The judgment reading** (`semanticallyValid_iff_mem_modelClass`):
  the verdict is a coupled-judgment membership.  The conclusion's wall
  is the floor of a single-disjunct coupled DNF (liveness exactly the
  properness demand, which wall systems satisfy freely — the zero joint
  inhabits every credal compile), the premise-and-admissibility
  cylinder's wall is the system, and semantic validity is membership of
  that system in that presentation's model class
  (`coupledSat_wallPen_wallPen_iff`: between wall systems the coupled
  judgment is the behavioural superset test).
* **The record space** (`valWire`, `valState`, `range_valState`,
  `semanticallyValid_iff_fibre`): the wire object of a hypernet has the
  hypernet's typed wires as wires and the sigma of tensor values as its
  (hypernet-independent) state stock; valuations embed injectively into
  its state space, with image exactly the well-typed states — the
  dependent carrier read as an erased function type plus a wellformedness
  guard.  The face and the judgment transport along the embedding
  (`upperProb_image`: upper probability read at the record space equals
  the intrinsic one — at every level, not merely at zero), so the
  verdict is a judgment in the semantic universe's fibre over
  `valWire H`, on the nose (`sequentSpec`, a citizen of
  `DnfSpec (valWire H)` by type).

Design notes:

* The tie is deliberately *pointwise in the hypernet*: no functoriality
  in `H`, no naturality of `valState`, no sheaf-tier content — the
  record space of a bare sequent verdict is a single-observation
  carrier, and the compositional story lives with the wiring base, not
  here.
* Statements stay in the plain vocabulary (joints, penalties, walls,
  coupled satisfaction, wire-object state spaces).  The two
  deliberately universe-facing declarations (`sequentSpec`,
  `semanticallyValid_iff_fibre`) are type-level readings of theorems
  already stated one line above them.
* The transport lemmas (`massOn_push`, `suppIn_image`,
  `upperProb_image`) are carrier-general: any injection of carriers
  transports the face calculus, the sequent instantiation being the
  case this module exists for.
-/

namespace SuFunctor

namespace Adequacy

noncomputable section

open scoped NNReal ENNReal
open SuFunctor.Plain
open SuFunctor.Universe (Dip CoupledSat SpecAtom SpecDnf)
open CategoryTheory CategoryTheory.WireSpan

universe u

variable {X Y : Type u}

/-! ## The wall dialect: one wall, two modules -/

/-- The face module's possibilistic wall is the wiring layer's wall
penalty of the credal compile. -/
theorem possWall_eq_wallPen (B : Set X) :
    possWall B = wallPen (suppIn B) :=
  rfl

/-! ## The coupled judgment between wall systems -/

/-- Between wall penalties, pointwise domination is containment of the
permitted sets. -/
theorem wallPen_le_wallPen_iff {W W' : Set (Plain.Joint X)} :
    wallPen W' ≤ wallPen W ↔ W ⊆ W' := by
  constructor
  · intro h ν hν
    by_contra hν'
    have hle := h ν
    rw [wallPen_apply_of_mem hν, wallPen_apply_of_not_mem hν'] at hle
    exact ENNReal.top_ne_zero (le_zero_iff.mp hle)
  · intro hWW' ν
    by_cases hν : ν ∈ W
    · rw [wallPen_apply_of_mem hν, wallPen_apply_of_mem (hWW' hν)]
    · rw [wallPen_apply_of_not_mem hν]
      exact le_top

/-- The zero joint inhabits every credal compile: its support is
empty. -/
theorem zero_mem_suppIn (B : Set X) : Joint.zero X ∈ suppIn B := by
  rw [mem_suppIn, Joint.zero_wt]
  simp

/-- Containment of credal compiles is containment of regions: the
forward direction is witnessed by Dirac joints, the backward is
monotonicity of the compile. -/
theorem suppIn_subset_suppIn_iff {B E : Set X} :
    suppIn B ⊆ suppIn E ↔ B ⊆ E := by
  constructor
  · intro h x hx
    have hd := h (Joint.dirac_mem_suppIn hx)
    rw [mem_suppIn, Joint.dirac_support] at hd
    simpa using hd
  · intro h μ hμ
    rw [mem_suppIn] at hμ ⊢
    exact hμ.trans h

/-- **The coupled judgment between wall systems is the behavioural
superset test**: the wall of one credal compile satisfies the atom
whose floor is the wall of another exactly when the first region is
contained in the second.  Liveness is the properness demand, satisfied
freely — the zero joint is everywhere. -/
theorem coupledSat_wallPen_wallPen_iff {B E : Set X} :
    CoupledSat (wallPen (suppIn B)) (wallPen (suppIn E))
      {(⊤ : Plain.Pen X)} ↔ B ⊆ E := by
  rw [coupledSat_wallPen_iff]
  constructor
  · rintro ⟨hsafe, -⟩
    rw [← suppIn_subset_suppIn_iff (X := X)]
    intro ν hν
    have h0 := hsafe ν hν
    rwa [← possWall_eq_wallPen, possWall_eq_zero_iff] at h0
  · intro hBE
    refine ⟨fun ν hν => ?_, fun v hv => ?_⟩
    · exact wallPen_apply_of_mem (suppIn_subset_suppIn_iff.mpr hBE hν)
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨Joint.zero X, zero_mem_suppIn B, by simp⟩

/-! ## The verdict as a fibre citizen at its own carrier -/

section SequentJudgment

open PPLC

/-- The spec atom of a sequent: floor the conclusion's wall, liveness
the properness demand — the single-disjunct genre of the compiled
diagrams. -/
def sequentAtom (H : Hypernet) (seq : Sequent) :
    SpecAtom (Plain.Joint H.Valuation) where
  floor := wallPen (suppIn (postEvt H seq))
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

@[simp] theorem sequentAtom_floor (H : Hypernet) (seq : Sequent) :
    (sequentAtom H seq).floor = wallPen (suppIn (postEvt H seq)) := rfl

@[simp] theorem sequentAtom_marks (H : Hypernet) (seq : Sequent) :
    (sequentAtom H seq).marks = {(⊤ : Plain.Pen H.Valuation)} := rfl

/-- The sequent's coupled-DNF presentation: one disjunct. -/
def sequentDnf (H : Hypernet) (seq : Sequent) :
    SpecDnf (Plain.Joint H.Valuation) where
  atoms := {sequentAtom H seq}
  finite_atoms := Set.finite_singleton _

/-- The cylinder's wall: the credal compile of the premise-and-
admissibility cylinder, entering the judgment as a wall system. -/
def cylWall (H : Hypernet) (seq : Sequent) : Plain.Pen H.Valuation :=
  wallPen (suppIn (admCyl H seq))

/-- **The verdict is a coupled-judgment membership at the sequent's own
carrier**: semantic validity is membership of the cylinder's wall in
the model class of the sequent's presentation. -/
theorem semanticallyValid_iff_mem_modelClass (H : Hypernet)
    (seq : Sequent) :
    seq.semanticallyValid H ↔
      cylWall H seq ∈ (sequentDnf H seq).modelClass := by
  rw [SpecDnf.mem_modelClass_iff]
  constructor
  · intro h
    exact ⟨sequentAtom H seq, rfl,
      coupledSat_wallPen_wallPen_iff.mpr
        ((semanticallyValid_iff_subset H seq).mp h)⟩
  · rintro ⟨a, ha, hsat⟩
    rw [show (sequentDnf H seq).atoms = {sequentAtom H seq} from rfl,
      Set.mem_singleton_iff] at ha
    subst ha
    exact (semanticallyValid_iff_subset H seq).mpr
      (coupledSat_wallPen_wallPen_iff.mp hsat)

end SequentJudgment

/-! ## The wire object of a hypernet -/

section WireObject

open PPLC

/-- The state stock of certificate wire objects: a tensor type together
with a value of it.  Hypernet-independent, so a single `WireSpan`
instance hosts every certificate's wire object — the untyped stratum of
the wiring base, consumed as designed. -/
def ElVal : Type := Σ τ : TensorType, TensorValue τ

/-- The wire object of a hypernet: its typed wires, over the common
state stock. -/
def valWire (H : Hypernet) : WireSpan ElVal :=
  ⟨{w : Wire // (H.wireType w).isSome}⟩

/-- A valuation of the hypernet, read as a state of its wire object:
each typed wire is sent to its declared type together with the
valuation's value on it. -/
def valState {H : Hypernet} (σ : H.Valuation) : states (valWire H) :=
  fun w =>
    ⟨(H.wireType w.1).get w.2,
      σ w.1 ((H.wireType w.1).get w.2) (Option.some_get w.2).symm⟩

/-- Distinct valuations read as distinct states: the embedding loses
nothing. -/
theorem valState_injective (H : Hypernet) :
    Function.Injective (valState (H := H)) := by
  intro σ σ' h
  funext w τ hτ
  have hw : (H.wireType w).isSome := Option.isSome_iff_exists.mpr ⟨τ, hτ⟩
  have happ := congrFun h ⟨w, hw⟩
  have hget : (H.wireType w).get hw = τ :=
    Option.some.inj ((Option.some_get hw).trans hτ)
  subst hget
  injection happ

/-- Wellformedness of a state of the wire object: on each wire, the
state's type component is the wire's declared type. -/
def StateWf (H : Hypernet) (s : states (valWire H)) : Prop :=
  ∀ w : (valWire H).wires, (s w).1 = (H.wireType w.1).get w.2

/-- Reconstruct a valuation from a well-typed state. -/
def valOfState {H : Hypernet} (s : states (valWire H))
    (hs : StateWf H s) : H.Valuation := fun w τ h =>
  have hw : (H.wireType w).isSome := Option.isSome_iff_exists.mpr ⟨τ, h⟩
  cast (congrArg TensorValue
    ((hs ⟨w, hw⟩).trans
      (Option.some.inj ((Option.some_get hw).trans h))))
    (s ⟨w, hw⟩).2

theorem valState_valOfState {H : Hypernet} (s : states (valWire H))
    (hs : StateWf H s) : valState (valOfState s hs) = s := by
  funext w
  exact Sigma.ext ((hs w).symm) (cast_heq _ _)

/-- **The identification**: the valuations are exactly the well-typed
states of the wire object — the dependent carrier, read as an erased
function type guarded by wellformedness. -/
theorem range_valState (H : Hypernet) :
    Set.range (valState (H := H)) = {s | StateWf H s} := by
  ext s
  constructor
  · rintro ⟨σ, rfl⟩
    exact fun w => rfl
  · intro hs
    exact ⟨valOfState s hs, valState_valOfState s hs⟩

end WireObject

/-! ## Transport of the face calculus along an injection of carriers -/

section Transport

variable {f : X → Y}

/-- Event mass of a pushforward along an injection: the mass of the
preimage event. -/
theorem massOn_push (hf : Function.Injective f) (μ : Plain.Joint X)
    (E : Set Y) : (μ.push f).massOn E = μ.massOn (f ⁻¹' E) := by
  classical
  rw [Joint.massOn, Joint.massOn, Joint.push_wt]
  rw [Finset.sum_subset Finsupp.mapDomain_support (fun y _ hy => by
    rw [Set.indicator_apply]
    split
    · rw [Finsupp.notMem_support_iff.mp hy]
      simp
    · rfl)]
  rw [Finset.sum_image fun x _ y _ hxy => hf hxy]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hxE : f x ∈ E
  · rw [Set.indicator_of_mem hxE,
      Set.indicator_of_mem (show x ∈ f ⁻¹' E from hxE),
      Finsupp.mapDomain_apply hf]
  · rw [Set.indicator_of_notMem hxE,
      Set.indicator_of_notMem (show x ∉ f ⁻¹' E from hxE)]

/-- Pushforward joints of an image compile: membership descends along
an injection. -/
theorem push_mem_suppIn_iff (hf : Function.Injective f) {B : Set X}
    {μ : Plain.Joint X} :
    μ.push f ∈ suppIn (f '' B) ↔ μ ∈ suppIn B := by
  classical
  rw [mem_suppIn, mem_suppIn, Joint.push_wt]
  constructor
  · intro h x hx
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
    have hfx : f x ∈ (μ.wt.mapDomain f).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hf]
      exact hx
    obtain ⟨x', hx', he⟩ := h (Finset.mem_coe.mpr hfx)
    rwa [← hf he]
  · intro h y hy
    rw [Finset.mem_coe] at hy
    have him := Finsupp.mapDomain_support hy
    rw [Finset.mem_image] at him
    obtain ⟨x, hx, rfl⟩ := him
    exact ⟨x, h (Finset.mem_coe.mpr hx), rfl⟩

/-- **The compile of an image region is the image of the compile**: a
joint supported inside the image region lives in the range of the
pushforward (nothing outside the image carries its mass), and pulls
back to a joint supported inside the region. -/
theorem suppIn_image (hf : Function.Injective f) (B : Set X) :
    suppIn (f '' B) = Joint.push f '' suppIn B := by
  classical
  ext μ
  constructor
  · intro hμ
    have hsupp : (↑μ.wt.support : Set Y) ⊆ f '' B := mem_suppIn.mp hμ
    have hrange : (↑μ.wt.support : Set Y) ⊆ Set.range f :=
      hsupp.trans (Set.image_subset_range f B)
    have hbij : Set.BijOn f (f ⁻¹' ↑μ.wt.support) ↑μ.wt.support :=
      ⟨fun x hx => hx, hf.injOn, fun y hy => by
        obtain ⟨x, rfl⟩ := hrange hy
        exact ⟨x, hy, rfl⟩⟩
    refine ⟨⟨μ.wt.comapDomain f hf.injOn, ?_⟩, ?_, ?_⟩
    · calc ((μ.wt.comapDomain f hf.injOn).sum fun _ v => v)
          = (μ.wt.sum fun _ v => v) :=
            Finsupp.sum_comapDomain f μ.wt (fun _ v => v) hbij
        _ ≤ 1 := μ.mass_le_one
    · rw [mem_suppIn]
      intro x hx
      rw [Finset.mem_coe] at hx
      have hfx : f x ∈ μ.wt.support := by
        rw [Finsupp.mem_support_iff]
        rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at hx
        exact hx
      obtain ⟨x', hx', he⟩ := hsupp (Finset.mem_coe.mpr hfx)
      rwa [← hf he]
    · apply Joint.ext
      rw [Joint.push_wt]
      ext y
      by_cases hy : y ∈ Set.range f
      · obtain ⟨x, rfl⟩ := hy
        rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply]
      · have hy0 : μ.wt y = 0 := by
          by_contra hz
          exact hy (hrange (Finset.mem_coe.mpr
            (Finsupp.mem_support_iff.mpr hz)))
        rw [Finsupp.mapDomain_notin_range _ _ hy, hy0]
  · rintro ⟨ν, hν, rfl⟩
    exact (push_mem_suppIn_iff hf).mpr hν

/-- **Upper probability transports along an injection of carriers**:
read at the image compile, it is the intrinsic upper probability of
the preimage event — at every level, not merely at zero. -/
theorem upperProb_image (hf : Function.Injective f) (B : Set X)
    (E : Set Y) : upperProb (f '' B) E = upperProb B (f ⁻¹' E) := by
  rw [upperProb, upperProb, suppIn_image hf, iSup_image]
  exact iSup_congr fun ν => iSup_congr fun _ => massOn_push hf ν E

end Transport

/-! ## The verdict at the record space -/

section RecordSpace

open PPLC

/-- **The checker face at the record space**: semantic validity is the
vanishing upper probability of the conclusion's complement, read over
the wire object's state space along the valuation embedding. -/
theorem semanticallyValid_iff_face_valWire (H : Hypernet)
    (seq : Sequent) :
    seq.semanticallyValid H ↔
      upperProb (valState '' admCyl H seq)
        ((valState '' postEvt H seq))ᶜ = 0 := by
  rw [upperProb_image (valState_injective H), Set.preimage_compl,
    Set.preimage_image_eq _ (valState_injective H)]
  exact semanticallyValid_iff_face H seq

/-- The sequent's spec atom at the record space. -/
def sequentAtomW (H : Hypernet) (seq : Sequent) :
    SpecAtom (Plain.Joint (states (valWire H))) where
  floor := wallPen (suppIn (valState '' postEvt H seq))
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

/-- The sequent's coupled-DNF presentation at the record space. -/
def sequentDnfW (H : Hypernet) (seq : Sequent) :
    SpecDnf (Plain.Joint (states (valWire H))) where
  atoms := {sequentAtomW H seq}
  finite_atoms := Set.finite_singleton _

/-- The cylinder's wall at the record space. -/
def cylWallW (H : Hypernet) (seq : Sequent) :
    Plain.Pen (states (valWire H)) :=
  wallPen (suppIn (valState '' admCyl H seq))

/-- The verdict is a coupled-judgment membership at the record
space. -/
theorem semanticallyValid_iff_mem_modelClass_valWire (H : Hypernet)
    (seq : Sequent) :
    seq.semanticallyValid H ↔
      cylWallW H seq ∈ (sequentDnfW H seq).modelClass := by
  rw [SpecDnf.mem_modelClass_iff]
  constructor
  · intro h
    exact ⟨sequentAtomW H seq, rfl,
      coupledSat_wallPen_wallPen_iff.mpr
        (Set.image_mono ((semanticallyValid_iff_subset H seq).mp h))⟩
  · rintro ⟨a, ha, hsat⟩
    rw [show (sequentDnfW H seq).atoms = {sequentAtomW H seq} from rfl,
      Set.mem_singleton_iff] at ha
    subst ha
    have hsub := coupledSat_wallPen_wallPen_iff.mp hsat
    rw [Set.image_subset_image_iff (valState_injective H)] at hsub
    exact (semanticallyValid_iff_subset H seq).mpr hsub

/-- The sequent's presentation is a citizen of the semantic universe's
fibre over the hypernet's wire object — by type. -/
def sequentSpec (H : Hypernet) (seq : Sequent) : DnfSpec (valWire H) :=
  sequentDnfW H seq

/-- **The verdict in the fibre**: a sequent is semantically valid
exactly when the cylinder's wall system belongs to the model class of
its presentation, in the semantic universe's fibre over the hypernet's
wire object. -/
theorem semanticallyValid_iff_fibre (H : Hypernet) (seq : Sequent) :
    seq.semanticallyValid H ↔
      cylWallW H seq ∈ (sequentSpec H seq).modelClass :=
  semanticallyValid_iff_mem_modelClass_valWire H seq

end RecordSpace

end

end Adequacy

end SuFunctor
