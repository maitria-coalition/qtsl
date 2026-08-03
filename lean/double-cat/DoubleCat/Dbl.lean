import DoubleCat.Functor.Whiskering
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The strict 2-category of pseudo double categories

`Dbl` bundles a category equipped with a pseudo double category structure.
Lax double functors and tight transformations make `Dbl` a bicategory
(Grandis–Paré, "Adjoint for double categories", 2004, §2.2;
Cruttwell–Lambert–Pronk–Szyld, "Double fibrations", 2022), and this
bicategory is strict: composition of lax double functors is associative and
unital on the nose (`LaxDoubleFunctor.comp_assoc` and friends, proved in
`DoubleCat.Functor.Whiskering` via the componentwise extensionality lemma),
and the structure isomorphisms below have identity components.

This bicategory is the codomain shape for the 2-functoriality of the double
Grothendieck construction: with the hom-categories of
`DoubleCat.Transformation` and the whiskerings of
`DoubleCat.Functor.Whiskering`, the statement "`∫` is a 2-functor into
`Dbl`" is expressible (see `DoubleCat.GrothendieckMap`).

## Implementation

The structure isomorphisms are *defined* with identity components (in the
style of `CategoryTheory.Cat`), rather than as `eqToIso` of the strict
composition laws: identity components keep every 2-cell computation in the
bicategory axioms syntactically transparent, with no stuck `Eq.rec` terms.
The components typecheck because the two sides of each composition law
agree definitionally on all underlying data (only the laxators differ,
propositionally); the heterogeneous equality of the laxators is extracted
from the composition law with `congr_arg_heq` (a `rw` inside the `HEq`
would need a motive abstracting a dependent field, and fails).  The
comparison with `eqToIso` is then proved (`Bicategory.Strict`), using the
component formulas for `eqToHom` 2-cells
(`TightTransformation.eqToHom_app`, `eqToHom_looseApp_heq`).
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w₀ t₀ v₀ u₀ w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂ w₃ t₃ v₃ u₃ w t v u

section EqToHom

variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]

/-- The tight component of an `eqToHom` transformation is an `eqToHom`. -/
theorem TightTransformation.eqToHom_app {F G : LaxDoubleFunctor C D}
    (h : F = G) (a : C) :
    (eqToHom h : TightTransformation F G).app a =
      eqToHom (congrArg (fun K : LaxDoubleFunctor C D => K.obj a) h) := by
  subst h; rfl

/-- The cell component of an `eqToHom` transformation is heterogeneously a
tight-wise identity cell. -/
theorem TightTransformation.eqToHom_looseApp_heq {F G : LaxDoubleFunctor C D}
    (h : F = G) {a b : C} (m : Loose a b) :
    (eqToHom h : TightTransformation F G).looseApp m ≍ vId (F.mapLoose m) := by
  subst h; rfl

end EqToHom

namespace LaxDoubleFunctor

variable {B : Type u₀} [Category.{v₀} B] [PseudoDoubleCategoryStruct B]
  [PseudoDoubleCategory B]
variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]
variable {E : Type u₃} [Category.{v₃} E] [PseudoDoubleCategoryStruct E]
  [PseudoDoubleCategory E]

/-- The associator for composition of lax double functors, with identity
components (composition is strictly associative). -/
def associator (F : LaxDoubleFunctor B C) (G : LaxDoubleFunctor C D)
    (H : LaxDoubleFunctor D E) : (F.comp G).comp H ≅ F.comp (G.comp H) where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor B E => K.laxComp m n)
            (comp_assoc F G H)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor B E => K.laxId a)
            (comp_assoc F G H)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor B E => K.laxComp m n)
            (comp_assoc F G H).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor B E => K.laxId a)
            (comp_assoc F G H).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  hom_inv_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)
  inv_hom_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)

/-- The left unitor, with identity components. -/
def leftUnitor (F : LaxDoubleFunctor C D) :
    (LaxDoubleFunctor.id).comp F ≅ F where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxComp m n)
            (id_comp F)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxId a)
            (id_comp F)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxComp m n)
            (id_comp F).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxId a)
            (id_comp F).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  hom_inv_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)
  inv_hom_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)

/-- The right unitor, with identity components. -/
def rightUnitor (F : LaxDoubleFunctor C D) :
    F.comp (LaxDoubleFunctor.id) ≅ F where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxComp m n)
            (comp_id F)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxId a)
            (comp_id F)).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
      looseApp := fun _ => vId _
      looseApp_natural := fun _ => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans
          (PseudoDoubleCategory.vId_vComp_heq _).symm
      looseApp_laxComp := fun m n => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxComp m n)
            (comp_id F).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)).symm HEq.rfl)
      looseApp_laxId := fun a => by
        rw [Cell.eq_cast_iff_heq]
        exact (PseudoDoubleCategory.vComp_vId_heq _).trans <|
          (congr_arg_heq (fun K : LaxDoubleFunctor C D => K.laxId a)
            (comp_id F).symm).trans <|
          (PseudoDoubleCategory.vId_vComp_heq _).symm.trans
          (vComp_congr_heq rfl rfl rfl rfl
            (heq_of_eq (PseudoDoubleCategory.hId_id _)).symm HEq.rfl) }
  hom_inv_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)
  inv_hom_id :=
    TightTransformation.ext (fun _ => (Category.id_comp _).trans rfl)
      (fun _ => PseudoDoubleCategory.vId_vComp_heq _)

@[simp]
theorem associator_hom_app (F : LaxDoubleFunctor B C)
    (G : LaxDoubleFunctor C D) (H : LaxDoubleFunctor D E) (a : B) :
    (associator F G H).hom.app a = 𝟙 _ := rfl

@[simp]
theorem associator_inv_app (F : LaxDoubleFunctor B C)
    (G : LaxDoubleFunctor C D) (H : LaxDoubleFunctor D E) (a : B) :
    (associator F G H).inv.app a = 𝟙 _ := rfl

@[simp]
theorem associator_hom_looseApp (F : LaxDoubleFunctor B C)
    (G : LaxDoubleFunctor C D) (H : LaxDoubleFunctor D E) {a b : B}
    (m : Loose a b) :
    (associator F G H).hom.looseApp m =
      vId ((F.comp (G.comp H)).mapLoose m) := rfl

@[simp]
theorem associator_inv_looseApp (F : LaxDoubleFunctor B C)
    (G : LaxDoubleFunctor C D) (H : LaxDoubleFunctor D E) {a b : B}
    (m : Loose a b) :
    (associator F G H).inv.looseApp m =
      vId ((F.comp (G.comp H)).mapLoose m) := rfl

@[simp]
theorem leftUnitor_hom_app (F : LaxDoubleFunctor C D) (a : C) :
    (leftUnitor F).hom.app a = 𝟙 _ := rfl

@[simp]
theorem leftUnitor_inv_app (F : LaxDoubleFunctor C D) (a : C) :
    (leftUnitor F).inv.app a = 𝟙 _ := rfl

@[simp]
theorem leftUnitor_hom_looseApp (F : LaxDoubleFunctor C D) {a b : C}
    (m : Loose a b) :
    (leftUnitor F).hom.looseApp m = vId (F.mapLoose m) := rfl

@[simp]
theorem leftUnitor_inv_looseApp (F : LaxDoubleFunctor C D) {a b : C}
    (m : Loose a b) :
    (leftUnitor F).inv.looseApp m = vId (F.mapLoose m) := rfl

@[simp]
theorem rightUnitor_hom_app (F : LaxDoubleFunctor C D) (a : C) :
    (rightUnitor F).hom.app a = 𝟙 _ := rfl

@[simp]
theorem rightUnitor_inv_app (F : LaxDoubleFunctor C D) (a : C) :
    (rightUnitor F).inv.app a = 𝟙 _ := rfl

@[simp]
theorem rightUnitor_hom_looseApp (F : LaxDoubleFunctor C D) {a b : C}
    (m : Loose a b) :
    (rightUnitor F).hom.looseApp m = vId (F.mapLoose m) := rfl

@[simp]
theorem rightUnitor_inv_looseApp (F : LaxDoubleFunctor C D) {a b : C}
    (m : Loose a b) :
    (rightUnitor F).inv.looseApp m = vId (F.mapLoose m) := rfl

end LaxDoubleFunctor

/-- A bundled pseudo double category: a category together with a lawful
pseudo double category structure on it. -/
structure Dbl : Type (max (u + 1) (v + 1) (w + 1) (t + 1)) where

  carrier : Type u
  [cat : Category.{v} carrier]
  [struct : PseudoDoubleCategoryStruct.{w, t} carrier]
  [law : PseudoDoubleCategory carrier]

namespace Dbl

attribute [instance] Dbl.cat Dbl.struct Dbl.law

instance : CoeSort Dbl.{w, t, v, u} (Type u) :=
  ⟨Dbl.carrier⟩

/-- Bundle a pseudo double category. -/
def of (C : Type u) [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
    [PseudoDoubleCategory C] : Dbl :=
  ⟨C⟩

/-- The bicategory of pseudo double categories, lax double functors, and
tight transformations. -/
instance bicategory : Bicategory Dbl.{w, t, v, u} where
  Hom C D := LaxDoubleFunctor C D
  id C := LaxDoubleFunctor.id
  comp F G := F.comp G
  homCategory _ _ := inferInstance
  whiskerLeft := @fun _ _ _ F _ _ σ => TightTransformation.whiskerLeft F σ
  whiskerRight := @fun _ _ _ _ _ σ H => σ.whiskerRight H
  associator F G H := LaxDoubleFunctor.associator F G H
  leftUnitor F := LaxDoubleFunctor.leftUnitor F
  rightUnitor F := LaxDoubleFunctor.rightUnitor F
  whiskerLeft_id := by
    intro a b c F G
    exact TightTransformation.whiskerLeft_id F G
  whiskerLeft_comp := by
    intro a b c F g h i σ τ
    exact TightTransformation.whiskerLeft_vcomp F σ τ
  id_whiskerLeft := by
    intro a b F G σ
    apply TightTransformation.ext
    · intro x
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
    · intro p q m
      exact
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm
  comp_whiskerLeft := by
    intro a b c d F G h h' σ
    apply TightTransformation.ext
    · intro x
      simp
    · intro p q m
      exact
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm
  id_whiskerRight := by
    intro a b c F G
    exact TightTransformation.id_whiskerRight F G
  comp_whiskerRight := by
    intro a b c f g h σ τ H
    exact TightTransformation.vcomp_whiskerRight σ τ H
  whiskerRight_id := by
    intro a b F G σ
    apply TightTransformation.ext
    · intro x
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
    · intro p q m
      exact
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm
  whiskerRight_comp := by
    intro a b c d f f' σ G H
    apply TightTransformation.ext
    · intro x
      simp
    · intro p q m
      exact
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm
  whisker_assoc := by
    intro a b c d F g g' σ H
    apply TightTransformation.ext
    · intro x
      simp
    · intro p q m
      exact
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm
  whisker_exchange := by
    intro a b c f g h i σ τ
    exact (TightTransformation.whisker_exchange σ τ).symm
  pentagon := by
    intro a b c d e f g h i
    apply TightTransformation.ext
    · intro x
      simp
    · intro p q m
      exact
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (i.mapCell_vId_heq _) HEq.rfl).trans
        (PseudoDoubleCategory.vId_vComp_heq _)
  triangle := by
    intro a b c f g
    apply TightTransformation.ext
    · intro x
      show 𝟙 _ ≫ 𝟙 _ = g.map (𝟙 _)
      simp
    · intro p q m
      exact (PseudoDoubleCategory.vId_vComp_heq _).trans
        (g.mapCell_vId_heq _).symm

/-- The bicategory of pseudo double categories is strict. -/
instance : Bicategory.Strict Dbl.{w, t, v, u} where
  id_comp := by
    intro a b F
    exact LaxDoubleFunctor.id_comp F
  comp_id := by
    intro a b F
    exact LaxDoubleFunctor.comp_id F
  assoc := by
    intro a b c d F G H
    exact LaxDoubleFunctor.comp_assoc F G H
  leftUnitor_eqToIso := by
    intro a b F
    apply Iso.ext
    apply TightTransformation.ext
    · intro x
      rw [eqToIso.hom, TightTransformation.eqToHom_app]
      exact rfl
    · intro p q m
      rw [eqToIso.hom]
      exact (TightTransformation.eqToHom_looseApp_heq _ m).symm
  rightUnitor_eqToIso := by
    intro a b F
    apply Iso.ext
    apply TightTransformation.ext
    · intro x
      rw [eqToIso.hom, TightTransformation.eqToHom_app]
      exact rfl
    · intro p q m
      rw [eqToIso.hom]
      exact (TightTransformation.eqToHom_looseApp_heq _ m).symm
  associator_eqToIso := by
    intro a b c d F G H
    apply Iso.ext
    apply TightTransformation.ext
    · intro x
      rw [eqToIso.hom, TightTransformation.eqToHom_app]
      exact rfl
    · intro p q m
      rw [eqToIso.hom]
      exact (TightTransformation.eqToHom_looseApp_heq _ m).symm

/-- The 1-truncation of `Dbl` as a category, defined directly (choice-free) —
mathlib's `StrictBicategory.category` would also apply but carries
`Classical.choice`. -/
instance : Category Dbl.{w, t, v, u} where
  Hom C D := LaxDoubleFunctor C D
  id C := LaxDoubleFunctor.id
  comp F G := F.comp G
  id_comp F := LaxDoubleFunctor.id_comp F
  comp_id F := LaxDoubleFunctor.comp_id F
  assoc F G H := LaxDoubleFunctor.comp_assoc F G H

end Dbl

end CategoryTheory
