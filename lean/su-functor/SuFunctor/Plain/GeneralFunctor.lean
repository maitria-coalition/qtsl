import Mathlib.MeasureTheory.Category.MeasCat
import SuFunctor.Plain.MeasJoint

/-! # The spec-class decoration functor at the general stratum

The tight tier of the decoration functor over measurable carriers:
to each measurable space the classes of penalty functionals on
subprobability joints over it, transported by the image of penalty
pullback along measurable maps.  The base is `MeasCatᵒᵖ`: the chapter's
wire maps act on state spaces contravariantly, so state-side the
functor is contravariant — at the finite stratum the wiring base is
wire-side, which is where the op hides.  Measurability being the
morphism datum of the base is constitutive of the stratum: the functor
laws consume exactly `MeasJoint.push_push`'s measurability hypotheses
(the finite stratum's base needed none).

The acceptance battery of `SuFunctor.Plain.Battery` transposes row by
row (the module records the general form of each row that generalizes;
the exact-rational rows of the certificate stratum are constitutive of
exactness and stay where they are), including the two refutation pins:
a taxed compositor breaks unit transparency and a funnel compositor
breaks the unit law against the empty class, both witnessed over every
measurable carrier by the zero joint.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal

universe u

/-- The spec-class fibre at a measurable carrier: classes of penalty
functionals on subprobability joints over it, ordered by inclusion. -/
abbrev MeasSpecClass (X : Type u) [MeasurableSpace X] : Type u :=
  Set (MeasPen X)

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- Tight transport of spec classes at the general stratum: the image
of penalty pullback (cylinder extension) along a carrier map. -/
def measSpecMap (h : X → Y) (𝒮 : MeasSpecClass Y) : MeasSpecClass X :=
  MeasPen.pull h '' 𝒮

/-- **The decoration functor's tight tier at the general stratum**:
spec classes over measurable carriers, transported by the image of
penalty pullback.  Functoriality is the Giry-functor part
(`Measure.map_id`, `Measure.map_map`) read through the penalty stock;
the base's measurability is what the composition law consumes.
(Morphisms of `Type u` at the house mathlib pin are wrapped functions —
`TypeCat.Hom` — so the transport is promoted with `TypeCat.ofHom`.) -/
def measSpecObj : MeasCat.{u}ᵒᵖ ⥤ Type u where
  obj X := MeasSpecClass ↥X.unop
  map f := TypeCat.ofHom (measSpecMap f.unop.1)
  map_id X :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => by
      show MeasPen.pull (𝟙 X.unop : X.unop ⟶ X.unop).1 '' 𝒮 = 𝒮
      have h : MeasPen.pull (X := ↥X.unop) (𝟙 X.unop : X.unop ⟶ X.unop).1 = id :=
        funext fun F => MeasPen.pull_id F
      rw [h, Set.image_id])
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => by
      show MeasPen.pull ((f ≫ g).unop).1 '' 𝒮 =
        MeasPen.pull g.unop.1 '' (MeasPen.pull f.unop.1 '' 𝒮)
      rw [← Set.image_comp]
      congr 1
      funext F
      exact (MeasPen.pull_pull f.unop.1 g.unop.1 f.unop.2 g.unop.2 F).symm)

/-! ## The battery, transposed to the general stratum

Row-by-row generals of `SuFunctor.Plain.Battery`; each proof is the
same set-algebra fact, now over measurable carriers with the
composite-penalty calculus of `SuFunctor.Plain.MeasJoint`. -/

section Battery

variable {U V W : Type u} [MeasurableSpace U] [MeasurableSpace V]
variable [MeasurableSpace W]

/-- **No funnel, membership form**: the composite class is exactly the
image of the pairs. -/
theorem mem_mboxplusClass_iff {π₁ : W → U} {π₂ : W → V}
    {𝒰₁ : Set (MeasPen U)} {𝒰₂ : Set (MeasPen V)} {H : MeasPen W} :
    H ∈ Set.image2 (mboxplus π₁ π₂) 𝒰₁ 𝒰₂ ↔
      ∃ F ∈ 𝒰₁, ∃ G ∈ 𝒰₂, mboxplus π₁ π₂ F G = H :=
  Set.mem_image2

/-- **No funnel, nonemptiness form**: nonempty inputs never collapse. -/
theorem mboxplusClass_nonempty {π₁ : W → U} {π₂ : W → V}
    {𝒰₁ : Set (MeasPen U)} {𝒰₂ : Set (MeasPen V)} (h₁ : 𝒰₁.Nonempty)
    (h₂ : 𝒰₂.Nonempty) :
    (Set.image2 (mboxplus π₁ π₂) 𝒰₁ 𝒰₂).Nonempty :=
  h₁.image2 h₂

/-- **No tax, class form**: the class of the zero penalty composes
transparently on the nose along any section of the second
marginalization — the general form of unit transparency, whose base
instance (the wiring base's unitor) discharges the section equation
definitionally. -/
theorem munitClass_transparent (e : V → W) (π₁ : W → U) (π₂ : W → V)
    (he : Measurable e) (hπ₂ : Measurable π₂) (hsec : π₂ ∘ e = id)
    (𝒰 : Set (MeasPen V)) :
    MeasPen.pull e ''
      Set.image2 (mboxplus π₁ π₂) ({fun _ => 0} : Set (MeasPen U)) 𝒰 = 𝒰 := by
  rw [Set.image2_singleton_left, ← Set.image_comp]
  have h : MeasPen.pull e ∘ mboxplus π₁ π₂ (fun _ => 0) = id :=
    funext fun F => pull_mboxplus_zero_left e π₁ π₂ he hπ₂ hsec F
  rw [h, Set.image_id]

/-- **Ideal points compose**: the composite of two singleton classes is
the singleton of the composite. -/
theorem msingleton_mboxplus {π₁ : W → U} {π₂ : W → V} (F : MeasPen U)
    (G : MeasPen V) :
    Set.image2 (mboxplus π₁ π₂) ({F} : Set (MeasPen U))
      ({G} : Set (MeasPen V)) = {mboxplus π₁ π₂ F G} :=
  Set.image2_singleton

/-- **Ideal points transport**: tight transport of a singleton class is
the singleton of the transported penalty. -/
theorem mtransport_singleton (h : X → Y) (F : MeasPen Y) :
    measSpecMap h {F} = {MeasPen.pull h F} :=
  Set.image_singleton

/-- **The judgment is the fibre order**: an ideal point satisfies a
spec class iff its singleton is included in it — carrier-free, exactly
as at the finite stratum. -/
theorem midealPoint_le_iff (F : MeasPen X) (𝒮 : MeasSpecClass X) :
    ({F} : MeasSpecClass X) ⊆ 𝒮 ↔ F ∈ 𝒮 :=
  Set.singleton_subset_iff

/-- **Compositor monotonicity** in the inclusion order. -/
theorem mboxplusClass_mono {π₁ : W → U} {π₂ : W → V}
    {𝒰₁ 𝒰₁' : Set (MeasPen U)} {𝒰₂ 𝒰₂' : Set (MeasPen V)}
    (h₁ : 𝒰₁ ⊆ 𝒰₁') (h₂ : 𝒰₂ ⊆ 𝒰₂') :
    Set.image2 (mboxplus π₁ π₂) 𝒰₁ 𝒰₂ ⊆
      Set.image2 (mboxplus π₁ π₂) 𝒰₁' 𝒰₂' :=
  Set.image2_subset h₁ h₂

/-- **Transport monotonicity**: the tight transport of every carrier
map is monotone. -/
theorem measSpecMap_mono (h : X → Y) {𝒮 𝒮' : MeasSpecClass Y}
    (hsub : 𝒮 ⊆ 𝒮') : measSpecMap h 𝒮 ⊆ measSpecMap h 𝒮' :=
  Set.image_mono hsub

end Battery

/-! ## Preregistered refutation pins, transposed -/

section Mutants

variable {U V W : Type u} [MeasurableSpace U] [MeasurableSpace V]
variable [MeasurableSpace W]

/-- Mutant, the tax: pushforward-then-add plus a constant charge on
every composite. -/
def taxedMboxplus (π₁ : W → U) (π₂ : W → V) (c : ℝ≥0∞) (F : MeasPen U)
    (G : MeasPen V) : MeasPen W :=
  fun ν => mboxplus π₁ π₂ F G ν + c

/-- **The tax fails**, at every marginalization configuration: any
nonzero surcharge breaks unit transparency, witnessed by the zero
penalty at the zero joint — which exists over every measurable
carrier.  (No section or measurability hypotheses: the taxed
compositor fails even in the configurations where the untaxed one is
transparent, which is the sharpest reading of "tax-free exactly
because it must be".) -/
theorem taxedMboxplus_breaks_unit_transparency (e : V → W) (π₁ : W → U)
    (π₂ : W → V) {c : ℝ≥0∞} (hc : c ≠ 0) :
    ¬ ∀ F : MeasPen V,
      MeasPen.pull e (taxedMboxplus π₁ π₂ c (fun _ => 0) F) = F := by
  intro hAll
  have h0 := congrFun (hAll fun _ => 0) (MeasJoint.zero V)
  simp only [MeasPen.pull_apply, taxedMboxplus, mboxplus_apply, zero_add] at h0
  exact hc h0

/-- Mutant, the funnel: a composite that ignores its inputs (the
marginalization pair enters only to fix the composite's carrier). -/
def funnelMComp (_π₁ : W → U) (_π₂ : W → V) (_ : Set (MeasPen U))
    (_ : Set (MeasPen V)) : Set (MeasPen W) :=
  Set.univ

/-- **The funnel fails**: against the empty class, stripping the unit
from the funnelled composite yields a nonempty class — content
retention is forced by the unit law at the general stratum exactly as
at the finite one. -/
theorem funnelMComp_breaks_unit_coherence (e : V → W) (π₁ : W → U)
    (π₂ : W → V) :
    ¬ ∀ 𝒰 : Set (MeasPen V),
      MeasPen.pull e '' funnelMComp π₁ π₂ ({fun _ => 0} : Set (MeasPen U)) 𝒰
        = 𝒰 := by
  intro hAll
  have h0 := hAll ∅
  simp only [funnelMComp] at h0
  have hne : (MeasPen.pull e '' (Set.univ : Set (MeasPen W))).Nonempty :=
    Set.univ_nonempty.image _
  rw [h0] at hne
  exact Set.not_nonempty_empty hne

end Mutants

end

end Plain

end SuFunctor
