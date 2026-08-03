import SuFunctor.Plain.Penalty
import DoubleCat.Grothendieck

/-! # The spec-class decoration functor, and its plain double Grothendieck total

The decoration functor of the spec tier: over the wiring base in
state-family presentation (`DoubleCat.WireSpan`), assign to each
interface the *classes of penalty functionals* on joints over its states,
ordered by inclusion; to each wiring pattern the *apex penalty classes*
(couplings with their content absorbed and their boundary classes
designated by the indexing); compose by the class-level
pushforward-then-add, and take the austere unit class.  This is a
span-valued **lax double functor** in the strict covariant form — every
obligation of `CategoryTheory.LaxDoubleFunctor` is proved below, none
assumed — so the plain (non-virtual) double Grothendieck construction
(`DoubleCat.Grothendieck`) applies as-is, and the total
`SpecTotal` is a pseudo double category with a strict projection to the
wiring base.

Two design points carry the result:

* **Fibres are inclusion-ordered classes, and decorations are classes.**
  The compositor combines two apex classes by the *image* of the
  element-level pushforward-then-add: no threshold arithmetic, no
  information loss a coherence law could detect.  Where a one-slot
  composite of single functionals provably cannot be sound, unital, and
  syntactic at once (the refutations kept in `SuFunctorLegacy.Refute`), the
  class-level composite satisfies associativity, both unit laws, and
  naturality *on the nose modulo the base transports* — proved below as
  the compositor coherence of the functor.
* **The base transports are definitional.**  In the state-family
  presentation the comparison maps between iterated glued apexes are
  `Σ`-reshuffles (`DoubleCat.WireSpan`, the `Tot`-calculus), so every
  coherence proof below reduces to: pushforward functoriality
  (`Finsupp.mapDomain`'s), the commutative-monoid laws of `ℝ≥0∞`, and
  image algebra.  This is the precise sense in which inclusion-ordered
  fibres flatten the cast calculus that priced the wiring-base assembly
  out of the earlier design round: the casts do not vanish, but nothing
  semantic rides them.

The laxators are deliberately *not* invertible — a class over a glued
apex need not be an image class — matching the chapter's reading that
laxity is content; the lax-functor interface never demands invertibility,
which is why plainness was never blocked by laxity itself.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open scoped NNReal ENNReal

universe u

variable {El : Type u}

/-- The spec-class fibre at an interface: classes of penalty functionals
on joints over its states, ordered by inclusion (the order is `⊆` on
`Set`; the judgment against a class is membership of an ideal point,
i.e. the fibre order on singletons). -/
abbrev SpecClass (A : WireSpan El) : Type u := Set (Pen (states A))

/-- The decorations over a wiring pattern: apex penalty classes.  The
boundary classes are pure designations (the indexing of the two-sided
family), exactly as the chapter's couplings carry their boundary parties
as designated references; the bulk-and-content of a coupling is absorbed
into the one apex class. -/
abbrev Cpl {A B : WireSpan El} (M : Pat A B) : Type u := Set (Pen (Pat.Tot M))

/-- Pushforward-then-add, element level: marginalize a joint over the
glued apex to each component, evaluate, add.  The composite penalty of
the chapter (`f ⊞ g = f ∘ (j_A)_♯ + g ∘ (j_B)_♯`), at the exact
stratum. -/
def boxplus {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N)) : Pen (Pat.Tot (Pat.comp M N)) :=
  fun ν => u₁ (ν.push (Pat.compFst M N)) + u₂ (ν.push (Pat.compSnd M N))

@[simp] theorem boxplus_apply {A B C : WireSpan El} {M : Pat A B}
    {N : Pat B C} (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N))
    (ν : Joint (Pat.Tot (Pat.comp M N))) :
    boxplus u₁ u₂ ν =
      u₁ (ν.push (Pat.compFst M N)) + u₂ (ν.push (Pat.compSnd M N)) := rfl

/-- The austere unit: the zero penalty on the identity pattern's apex —
everything permitted, no residue.  (Unit austerity is what the unit
coherence laws consume; a unit with content would tax them.) -/
def unitPen (A : WireSpan El) : Pen (Pat.Tot (Pat.id A)) := fun _ => 0

@[simp] theorem unitPen_apply (A : WireSpan El)
    (ν : Joint (Pat.Tot (Pat.id A))) : unitPen A ν = 0 := rfl

/-! ## The element-level coherence cores

Each law of the compositor, at a single pair of penalties.  The `Σ`-
reshuffle identities of the `Tot`-calculus are definitional, so each
proof is: collapse pushforward chains (`Joint.push_push`), then a monoid
law of `ℝ≥0∞`, then `rfl`. -/

section Cores

variable {A B C D A' B' C' : WireSpan El}

/-- Naturality core: transporting a composite along a loose-wise
composite cell is the composite of the transports. -/
theorem pull_tot_hComp_boxplus {M₁ : Pat A B} {M₂ : Pat B C}
    {N₁ : Pat A' B'} {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'}
    {ψ : C ⟶ C'} (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ)
    (u₁ : Pen (Pat.Tot M₁)) (u₂ : Pen (Pat.Tot M₂)) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β))
        (boxplus u₁ u₂) =
      boxplus (Pen.pull (PatCell.tot α) u₁)
        (Pen.pull (PatCell.tot β) u₂) := by
  funext ν
  simp only [Pen.pull_apply, boxplus_apply, Joint.push_push]
  rfl

/-- Associativity core: reassociating a threefold composite along the
base associator's apex transport is reassociation of the sum. -/
theorem pull_tot_lAssoc_boxplus (M : Pat A B) (N : Pat B C) (P : Pat C D)
    (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N)) (u₃ : Pen (Pat.Tot P)) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P))
        (boxplus (boxplus u₁ u₂) u₃) =
      boxplus u₁ (boxplus u₂ u₃) := by
  funext ν
  simp only [Pen.pull_apply, boxplus_apply, Joint.push_push]
  rw [add_assoc]
  rfl

/-- Left unit core: composing with the austere unit and stripping the
unit pattern returns the penalty on the nose — **unit transparency
without tax**.  (The retired one-slot composition provably taxed some
tautology whenever its graded rows were sound; at class-element level
the tax is gone because nothing forces content through a threshold
row.) -/
theorem pull_tot_lLeftUnitor_boxplus (M : Pat A B) (u : Pen (Pat.Tot M)) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
        (boxplus (unitPen A) u) = u := by
  funext ν
  simp only [Pen.pull_apply, boxplus_apply, Joint.push_push,
    unitPen_apply, zero_add]
  show u (ν.push id) = u ν
  rw [Joint.push_id]

/-- Right unit core, dually. -/
theorem pull_tot_lRightUnitor_boxplus (M : Pat A B) (u : Pen (Pat.Tot M)) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))
        (boxplus u (unitPen B)) = u := by
  funext ν
  simp only [Pen.pull_apply, boxplus_apply, Joint.push_push,
    unitPen_apply, add_zero]
  show u (ν.push id) = u ν
  rw [Joint.push_id]

end Cores

/-! ## The functor -/

/-- Tight transport of spec classes: the image of penalty pushforward
(cylinder extension) along the wire map. -/
def specMap {A B : WireSpan El} (φ : A ⟶ B) (𝒮 : SpecClass A) :
    SpecClass B :=
  Pen.pull (res φ) '' 𝒮

/-- The object-and-tight-arrow tier: spec classes, transported by the
image of penalty pushforward (cylinder extension) along the wire map.
(Morphisms of `Type u` at the house mathlib pin are wrapped functions —
`TypeCat.Hom` — so the transport is promoted with `TypeCat.ofHom`;
applications of promoted morphisms reduce definitionally, and the functor
laws are `congrArg` of the promotion at function-level identities.) -/
def specObj (El : Type u) : WireSpan El ⥤ Type u where
  obj A := Set (Pen (states A))
  map φ := TypeCat.ofHom (specMap φ)
  map_id A :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => by
      show Pen.pull (res (𝟙 A)) '' 𝒮 = 𝒮
      have h : Pen.pull (res (𝟙 A)) = id := funext fun f => Pen.pull_id f
      rw [h, Set.image_id])
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => by
      show Pen.pull (res (f ≫ g)) '' 𝒮 =
        Pen.pull (res g) '' (Pen.pull (res f) '' 𝒮)
      rw [← Set.image_comp]
      congr 1
      funext u
      exact (Pen.pull_pull (res f) (res g) u).symm)

/-- Applying a boundary-cast cell between constant families: the cast is
pointwise invisible, because constant families do not read the tight
boundaries.  (The general transport lemma specializes to an equality
here; this is the pointwise face of "inclusion-ordered class fibres
flatten the cast calculus".) -/
theorem cast_apply_const {A B A' B' P Q : Type u}
    {f f' : A ⟶ A'} {g g' : B ⟶ B'} (hf : f = f') (hg : g = g')
    (φ : DepSpan.FamCell (fun _ _ => P) (fun _ _ => Q) f g)
    (x : A) (y : B) (s : P) :
    PseudoDoubleCategoryStruct.Cell.cast (C := Type u) hf hg φ x y s =
      φ x y s := by
  subst hf; subst hg; rfl

/-- **The spec-class decoration functor**: a span-valued lax double
functor on the wiring base, with inclusion-ordered class fibres.  Every
comparison datum is constructed and every coherence law is proved — the
plain double Grothendieck construction consumes this instance as-is. -/
def specFunctor (El : Type u) :
    SpanValued.{u + 1, u, u, u + 1, u} (WireSpan El) where
  toFunctor := specObj El
  mapLoose M := fun _ _ => Cpl M
  mapCell γ := fun _ _ 𝒰 => Pen.pull (PatCell.tot γ) '' 𝒰
  mapCell_vId M := by
    have key : ∀ 𝒰 : Cpl M,
        Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M)) '' 𝒰 = 𝒰 := by
      intro 𝒰
      have h : Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M)) = id :=
        funext fun u => Pen.pull_id u
      rw [h, Set.image_id]
    funext 𝒮 𝒯 𝒰
    exact (key 𝒰).trans (eq_of_heq (DepSpan.FamCell.heq_apply
      ((specObj El).map_id _) ((specObj El).map_id _)
      (Cell.cast_heq ((specObj El).map_id _).symm ((specObj El).map_id _).symm
        (PseudoDoubleCategoryStruct.vId (C := Type u) (fun _ _ => Cpl M)))
      𝒮 𝒯 𝒰)).symm
  mapCell_vComp α β := by
    have key : ∀ 𝒰,
        Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.vComp (C := WireSpan El) α β)) '' 𝒰 =
          Pen.pull (PatCell.tot β) '' (Pen.pull (PatCell.tot α) '' 𝒰) := by
      intro 𝒰
      rw [← Set.image_comp]
      congr 1
      funext u
      exact (Pen.pull_pull (PatCell.tot α) (PatCell.tot β) u).symm
    funext 𝒮 𝒯 𝒰
    rw [cast_apply_const]
    exact key 𝒰
  laxComp M N := fun _ _ s => Set.image2 boxplus s.2.1 s.2.2
  laxId A := fun _ _ _ => {unitPen A}
  laxComp_natural α β := by
    have key : ∀ (𝒰₁ : Cpl _) (𝒰₂ : Cpl _),
        Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)) ''
            Set.image2 boxplus 𝒰₁ 𝒰₂ =
          Set.image2 boxplus (Pen.pull (PatCell.tot α) '' 𝒰₁)
            (Pen.pull (PatCell.tot β) '' 𝒰₂) := by
      intro 𝒰₁ 𝒰₂
      rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
      exact Set.image2_congr fun u₁ _ u₂ _ => pull_tot_hComp_boxplus α β u₁ u₂
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1 s.2.2))
  laxId_natural f := by
    have key : Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f)) ''
        {unitPen _} = {unitPen _} := by
      rw [Set.image_singleton]
      exact rfl
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒮' e => heq_of_eq key)
  laxComp_assoc M N P := by
    have key : ∀ (𝒰₁ : Cpl M) (𝒰₂ : Cpl N) (𝒰₃ : Cpl P),
        Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P)) ''
            Set.image2 boxplus (Set.image2 boxplus 𝒰₁ 𝒰₂) 𝒰₃ =
          Set.image2 boxplus 𝒰₁ (Set.image2 boxplus 𝒰₂ 𝒰₃) := by
      intro 𝒰₁ 𝒰₂ 𝒰₃
      rw [Set.image_image2]
      exact Set.image2_assoc fun u₁ u₂ u₃ =>
        pull_tot_lAssoc_boxplus M N P u₁ u₂ u₃
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1.2.1 s.2.1.2.2 s.2.2))
  laxComp_leftUnitor M := by
    have key : ∀ 𝒰 : Cpl M,
        Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
            Set.image2 boxplus ({unitPen _} : Cpl (Pat.id _)) 𝒰 = 𝒰 := by
      intro 𝒰
      rw [Set.image2_singleton_left, ← Set.image_comp]
      have h : Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ∘
            boxplus (unitPen _) = id :=
        funext fun u => pull_tot_lLeftUnitor_boxplus M u
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒮', e, 𝒰⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))
  laxComp_rightUnitor M := by
    have key : ∀ 𝒰 : Cpl M,
        Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)) ''
            Set.image2 boxplus 𝒰 ({unitPen _} : Cpl (Pat.id _)) = 𝒰 := by
      intro 𝒰
      rw [Set.image2_singleton_right, ← Set.image_comp]
      have h : Pen.pull (PatCell.tot
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)) ∘
            (fun u => boxplus u (unitPen _)) = id :=
        funext fun u => pull_tot_lRightUnitor_boxplus M u
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒯', 𝒰, e⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))

/-! ## The total: the plain construction goes through -/

/-- **The double category of open spec-classes**: the plain double
Grothendieck construction applied to the spec-class decoration functor.
Objects are interfaces with a designated spec class; loose arrows are
wiring patterns with an apex penalty class; the fibre order (`⊆`) is the
judgment layer, carried on top of this total rather than as a second
fibration. -/
abbrev SpecTotal (El : Type u) := SpanValued.Grothendieck (specFunctor El)

/-- The verdict, machine form: the total of the spec-class decoration
functor under the *plain* construction is a pseudo double category —
no virtual machinery consumed. -/
theorem specTotal_pseudoDoubleCategory (El : Type u) :
    ∃ _ : PseudoDoubleCategory (SpecTotal El), True :=
  ⟨inferInstance, trivial⟩

/-- The strict projection to the wiring base. -/
def specProj (El : Type u) :
    LaxDoubleFunctor (SpecTotal El) (WireSpan El) :=
  SpanValued.proj (specFunctor El)

/-- The projection is pseudo (its laxators are invertible): the total
sits over the wiring base strictly, with the canonical-lift opcartesian
data of the covariant construction. -/
theorem specProj_isPseudo (El : Type u) : (specProj El).IsPseudo :=
  SpanValued.proj_isPseudo (specFunctor El)

end

end Plain

end SuFunctor
