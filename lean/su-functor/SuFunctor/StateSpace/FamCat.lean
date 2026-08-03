import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Countable.Basic

/-! # The free countable coproduct completion: the category of countable families

`FamObj C` is the category of countable families of objects of `C`:

* an object is a countable index type `ι : Type` together with a family
  `X : ι → C`;
* a morphism `(ι, X) ⟶ (κ, Y)` is a reindexing function `r : ι → κ`
  together with componentwise morphisms `X i ⟶ Y (r i)`.

This is the classical `Fam` construction (the free coproduct completion,
here at the countable size), hand-rolled because mathlib does not carry
it.  Countable coproducts exist freely (`StateSpace/FamCoproducts.lean`),
finite limits exist whenever `C` has them (`StateSpace/FamLimits.lean`),
and the singleton embedding (`ySing` on objects, bundled as the functor
`yFam`) is fully faithful.  The intended instantiation is `C` = the
category of ω-semialgebraic spaces (`StateSpace/FamCompletion.lean`),
where the completion hosts the bag/marking spaces `∐ₙ Symⁿ(X)` whose
sector dimensions grow unboundedly — the objects the concrete
tagged-union coproducts of `StateSpace/CountableCoproducts.lean` cannot
reach.

Two structural facts proved here are used throughout:

* morphism equality decomposes as reindexing equality plus componentwise
  equality up to `eqToHom` transport (`FamObj.Hom.ext'`,
  `FamObj.Hom.congr_app`) — and `eqToHom` transports whose endpoints
  agree definitionally are identities on the nose (`eqToHom_self`, by
  proof irrelevance), which keeps the bookkeeping light;
* an isomorphism of families has a *bijective* reindexing
  (`famIsIso_reindex_bijective`) — pure index algebra.  Families
  remember their sector structure: this is what makes the completion's
  coproducts disjoint, and it is also why the embedding does not send
  the old in-ambient tagged unions to the new coproducts (the comparison
  morphism is never invertible; see `StateSpace/FamCompletion.lean`).

Mechanization note: `ySing` is `@[reducible]` deliberately — its index
type must be *reducibly* `PUnit` so that unit-structure eta closes the
index-equality goals and instance search sees through it. -/

namespace SuFunctor.StateSpace

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A transport along a self-equality is the identity: proofs are
irrelevant, so the proof is definitionally `rfl`. -/
@[simp]
theorem eqToHom_self {X : C} (h : X = X) : eqToHom h = 𝟙 X := rfl

/-- An object of the free countable coproduct completion: a countable
family of objects of `C`. -/
structure FamObj (C : Type u) [Category.{v} C] : Type (max u 1) where
  /-- The index type of the family. -/
  ι : Type
  /-- The index type is countable. -/
  [countableI : Countable ι]
  /-- The components. -/
  X : ι → C

attribute [instance] FamObj.countableI

namespace FamObj

/-- A morphism of families: a reindexing together with componentwise
morphisms into the reindexed components. -/
structure Hom (A B : FamObj C) : Type v where
  /-- The reindexing function. -/
  r : A.ι → B.ι
  /-- The componentwise morphisms. -/
  app : ∀ i : A.ι, A.X i ⟶ B.X (r i)

/-- Morphism equality from reindexing equality plus componentwise
equality up to the induced transport. -/
theorem Hom.ext' {A B : FamObj C} {f g : Hom A B} (hr : f.r = g.r)
    (happ : ∀ i : A.ι,
      f.app i ≫ eqToHom (congrArg B.X (congrFun hr i)) = g.app i) : f = g := by
  obtain ⟨fr, fapp⟩ := f
  obtain ⟨gr, gapp⟩ := g
  dsimp only at hr
  subst hr
  simp only [eqToHom_self, Category.comp_id] at happ
  exact congrArg (Hom.mk fr) (funext happ)

/-- Componentwise consequence of a morphism equality, with the transport
made explicit. -/
theorem Hom.congr_app {A B : FamObj C} {f g : Hom A B} (h : f = g) (i : A.ι) :
    f.app i = g.app i ≫
      eqToHom (congrArg B.X (congrFun (congrArg Hom.r h) i)).symm := by
  subst h; simp

instance : Category (FamObj C) where
  Hom A B := Hom A B
  id A := ⟨fun i => i, fun i => 𝟙 (A.X i)⟩
  comp f g := ⟨fun i => g.r (f.r i), fun i => f.app i ≫ g.app (f.r i)⟩
  id_comp f := Hom.ext' rfl (fun i => by simp)
  comp_id f := Hom.ext' rfl (fun i => by simp)
  assoc f g h := Hom.ext' rfl (fun i => by simp)

@[simp] lemma id_r (A : FamObj C) (i : A.ι) : Hom.r (𝟙 A) i = i := rfl

@[simp] lemma id_app (A : FamObj C) (i : A.ι) : Hom.app (𝟙 A) i = 𝟙 (A.X i) := rfl

@[simp] lemma comp_r {A B D : FamObj C} (f : A ⟶ B) (g : B ⟶ D) (i : A.ι) :
    Hom.r (f ≫ g) i = g.r (f.r i) := rfl

@[simp] lemma comp_app {A B D : FamObj C} (f : A ⟶ B) (g : B ⟶ D) (i : A.ι) :
    Hom.app (f ≫ g) i = f.app i ≫ g.app (f.r i) := rfl

/-! ## Isomorphisms have bijective reindexings -/

/-- The reindexing of an isomorphism of families is a bijection: from the
two composite identities the reindexings are mutually inverse — pure index
algebra, independent of the components.  Families remember their sector
structure (including empty sectors). -/
theorem famIsIso_reindex_bijective {A B : FamObj C} (f : A ⟶ B) [IsIso f] :
    Function.Bijective f.r := by
  have h₁ : ∀ i : A.ι, (inv f).r (f.r i) = i := fun i =>
    congrFun (congrArg Hom.r (IsIso.hom_inv_id f)) i
  have h₂ : ∀ j : B.ι, f.r ((inv f).r j) = j := fun j =>
    congrFun (congrArg Hom.r (IsIso.inv_hom_id f)) j
  exact Function.bijective_iff_has_inverse.mpr ⟨(inv f).r, h₁, h₂⟩

/-! ## The singleton embedding -/

/-- A singleton family.  Reducible so that the index type is *reducibly*
`PUnit` (unit eta then closes index-equality goals). -/
@[reducible]
def ySing (V : C) : FamObj C := ⟨PUnit, fun _ => V⟩

/-- The singleton image of a morphism. -/
@[reducible]
def ySingMap {V W : C} (f : V ⟶ W) : ySing V ⟶ ySing W :=
  ⟨fun i => i, fun _ => f⟩

/-- Morphisms between singleton families are single morphisms:
full faithfulness of the embedding, as an equivalence of hom types. -/
def ySingHomEquiv (V W : C) : (ySing V ⟶ ySing W) ≃ (V ⟶ W) where
  toFun f := f.app PUnit.unit
  invFun f := ySingMap f
  left_inv f := Hom.ext' (funext fun _ => rfl) (fun _ => by simp [ySingMap])
  right_inv f := rfl

@[simp] lemma ySingMap_comp {V W U : C} (f : V ⟶ W) (g : W ⟶ U) :
    ySingMap (f ≫ g) = ySingMap f ≫ ySingMap g := rfl

/-- The singleton embedding, as a functor. -/
def yFam : C ⥤ FamObj C where
  obj := ySing
  map := ySingMap
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma yFam_obj (V : C) : yFam.obj V = ySing V := rfl

@[simp] lemma yFam_map {V W : C} (f : V ⟶ W) : yFam.map f = ySingMap f := rfl

instance : yFam (C := C).Faithful where
  map_injective {V W f g} h := by
    have h' := Hom.congr_app h PUnit.unit
    simpa using h'

instance : yFam (C := C).Full where
  map_surjective f := ⟨f.app PUnit.unit, (ySingHomEquiv _ _).left_inv f⟩

/-- The singleton embedding preserves monomorphisms.  (Test morphisms
into a singleton family have trivial reindexing, so the mono test
reduces componentwise.) -/
theorem ySingMap_mono {V W : C} (f : V ⟶ W) [Mono f] :
    Mono (ySingMap f) := by
  constructor
  intro A u v huv
  refine Hom.ext' (funext fun i => rfl) (fun i => ?_)
  have h := Hom.congr_app huv i
  simp only [comp_app] at h
  simp only [ySingMap, eqToHom_self, Category.comp_id] at h ⊢
  exact (cancel_mono f).mp h

/-- The singleton embedding preserves epimorphisms. -/
theorem ySingMap_epi {V W : C} (f : V ⟶ W) [Epi f] :
    Epi (ySingMap f) := by
  constructor
  intro A u v huv
  refine Hom.ext' (funext fun i => ?_) (fun i => ?_)
  · exact congrFun (congrArg Hom.r huv) i
  · have h := Hom.congr_app huv i
    simp only [comp_app, ySingMap] at h
    rw [Category.assoc] at h
    replace h := (cancel_epi f).mp h
    rw [comp_eqToHom_iff]
    exact h

/-- The singleton embedding reflects isomorphisms: if the image of `f`
is invertible in the completion, `f` was invertible in `C`. -/
theorem ySingMap_isIso {V W : C} (f : V ⟶ W) [IsIso (ySingMap f)] :
    IsIso f := by
  refine ⟨(inv (ySingMap f)).app PUnit.unit, ?_, ?_⟩
  · have h := Hom.congr_app (IsIso.hom_inv_id (ySingMap f)) PUnit.unit
    simpa [ySingMap] using h
  · have h := Hom.congr_app (IsIso.inv_hom_id (ySingMap f)) PUnit.unit
    simp only [comp_app, id_app, eqToHom_self, Category.comp_id,
      Category.id_comp] at h
    exact h

end FamObj

end SuFunctor.StateSpace
