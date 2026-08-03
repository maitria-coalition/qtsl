import DoubleCat.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The loose bicategory of a pseudo double category

The globular cells of a pseudo double category — those whose tight sides
are identities — form a category over each pair of objects
(`CategoryTheory.PseudoDoubleCategoryStruct.globularCategory`), and the
objects, loose arrows, and globular cells together form a bicategory
(`CategoryTheory.LooseBicat`): the underlying "horizontal bicategory" of
Grandis–Paré ("Adjoint for double categories", 2004) and Shulman ("Framed
bicategories and monoidal fibrations", 2008).

Besides packaging the globular fragment, the instance imports all of
mathlib's bicategory theory for globular reasoning in any pseudo double
category.  The first dividend is Kelly-style derived coherence: mathlib
proves `λ_ (𝟙 a) = ρ_ (𝟙 a)` in any bicategory from pentagon, triangle,
naturality, and invertibility, and transporting it along this instance
yields the corresponding fact for the loose unitors on a loose identity
(`CategoryTheory.PseudoDoubleCategoryStruct.lLeftUnitor_lId_eq_lRightUnitor_lId`)
— the coherence that makes the identity companion work
(`CategoryTheory.Companion.id`).

## Implementation

Composition in the globular category is tight-wise composition
transported along `𝟙 ≫ 𝟙 = 𝟙` (`Cell.cast`); the unfolding lemmas
`globularId_def`/`globularComp_def` convert between the categorical and
the double-categorical spellings.  The whiskerings need no transport at
all — `vId f ⊚ η` is globular on the nose — and the structure
isomorphisms are the structure cells of the double category.  Every
bicategory axiom is proved by converting to heterogeneous equality and
chasing with the congruence calculus of `DoubleCat.Basic`; the pentagon
and triangle are the base pentagon and triangle verbatim.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w t v u

namespace PseudoDoubleCategoryStruct

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]

/-- Globular cells between fixed endpoints, as a category structure: `m ⟶ n`
is a cell with identity tight sides, composing tight-wise (transported along
`𝟙 ≫ 𝟙 = 𝟙`). -/
instance globularCategoryStruct (a b : C) : CategoryStruct (Loose a b) where
  Hom m n := Cell m n (𝟙 a) (𝟙 b)
  id m := vId m
  comp α β := (α ≫ᵥ β).cast (Category.id_comp _) (Category.id_comp _)

/-- Unfolding: the globular identity is the tight-wise identity cell. -/
theorem globularId_def {a b : C} (m : Loose a b) : 𝟙 m = vId m := rfl

/-- Unfolding: globular composition is tight-wise composition transported
along `𝟙 ≫ 𝟙 = 𝟙`. -/
theorem globularComp_def {a b : C} {m n p : Loose a b} (α : m ⟶ n)
    (β : n ⟶ p) :
    α ≫ β = (α ≫ᵥ β).cast (Category.id_comp _) (Category.id_comp _) := rfl

variable [PseudoDoubleCategory C]

open PseudoDoubleCategory in

/-- Globular cells form a category. -/
instance globularCategory (a b : C) : Category (Loose a b) where
  id_comp α := by
    rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
    exact vId_vComp_heq α
  comp_id α := by
    rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
    exact vComp_vId_heq α
  assoc α β γ := by
    rw [globularComp_def, globularComp_def, globularComp_def,
      globularComp_def, Cell.cast_eq_iff_heq]
    exact (vComp_congr_heq (by simp) (by simp) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|
      (vComp_assoc_heq α β γ).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm

end PseudoDoubleCategoryStruct

/-- The loose bicategory of a pseudo double category: a type synonym for `C`
carrying the `Bicategory` instance whose 1-morphisms are loose arrows and
whose 2-morphisms are globular cells. -/
def LooseBicat (C : Type u) := C

namespace LooseBicat

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

/-- Interpret an object of `C` as an object of the loose bicategory. -/
def mk (a : C) : LooseBicat C := a

/-- Interpret an object of the loose bicategory as an object of `C`. -/
def unmk (a : LooseBicat C) : C := a

open PseudoDoubleCategory in

/-- The bicategory of objects, loose arrows, and globular cells.  Whiskerings
are loose-wise composition with tight-wise identity cells (no transport
needed); the structure isomorphisms are the structure cells. -/
instance bicategory : Bicategory (LooseBicat C) where
  Hom a b := Loose (unmk a) (unmk b)
  id a := lId (unmk a)
  comp m n := m ⊙ n
  homCategory a b := globularCategory (unmk a) (unmk b)
  whiskerLeft := @fun _ _ _ f _ _ η => vId f ⊚ η
  whiskerRight := @fun _ _ _ _ _ η p => η ⊚ vId p
  associator m n p :=
    { hom := lAssoc m n p
      inv := lAssocInv m n p
      hom_inv_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lAssoc_lAssocInv_heq m n p
      inv_hom_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lAssocInv_lAssoc_heq m n p }
  leftUnitor m :=
    { hom := lLeftUnitor m
      inv := lLeftUnitorInv m
      hom_inv_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lLeftUnitor_lLeftUnitorInv_heq m
      inv_hom_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lLeftUnitorInv_lLeftUnitor_heq m }
  rightUnitor m :=
    { hom := lRightUnitor m
      inv := lRightUnitorInv m
      hom_inv_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lRightUnitor_lRightUnitorInv_heq m
      inv_hom_id := by
        rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
        exact lRightUnitorInv_lRightUnitor_heq m }
  whiskerLeft_id := by
    intro a b c f g
    rw [globularId_def, globularId_def]
    exact hComp_vId f g
  whiskerLeft_comp := by
    intro a b c f g h i η θ
    rw [globularComp_def, globularComp_def, Cell.eq_cast_iff_heq]
    exact (hComp_congr_heq (by simp) (by simp) (by simp)
        (vComp_vId_heq (vId f)).symm (Cell.cast_heq _ _ _)).trans
      (heq_of_eq (interchange (vId f) η (vId f) θ))
  id_whiskerLeft := by
    intro a b f g η
    exact eq_of_heq <|
      (hComp_congr_heq rfl rfl rfl
        (heq_of_eq (hId_id (unmk a)).symm) HEq.rfl).trans <|
      (vComp_vId_heq _).symm.trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lLeftUnitor_lLeftUnitorInv_heq g).symm).trans <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lLeftUnitor_natural_heq η) HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm
  comp_whiskerLeft := by
    intro a b c d f g h h' η
    exact eq_of_heq <|
      (hComp_congr_heq rfl rfl rfl
        (heq_of_eq (hComp_vId f g).symm) HEq.rfl).trans <|
      (vComp_vId_heq _).symm.trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lAssoc_lAssocInv_heq f g h').symm).trans <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq (vId f) (vId g) η) HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm
  id_whiskerRight := by
    intro a b c f g
    rw [globularId_def, globularId_def]
    exact hComp_vId f g
  comp_whiskerRight := by
    intro a b c f g h η θ i
    rw [globularComp_def, globularComp_def, Cell.eq_cast_iff_heq]
    exact (hComp_congr_heq (by simp) (by simp) (by simp)
        (Cell.cast_heq _ _ _) (vComp_vId_heq (vId i)).symm).trans
      (heq_of_eq (interchange η (vId i) θ (vId i)))
  whiskerRight_id := by
    intro a b f g η
    exact eq_of_heq <|
      (hComp_congr_heq rfl rfl rfl HEq.rfl
        (heq_of_eq (hId_id (unmk b)).symm)).trans <|
      (vComp_vId_heq _).symm.trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lRightUnitor_lRightUnitorInv_heq g).symm).trans <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lRightUnitor_natural_heq η) HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm
  whiskerRight_comp := by
    intro a b c d f f' η g h
    exact eq_of_heq <|
      (hComp_congr_heq rfl rfl rfl HEq.rfl
        (heq_of_eq (hComp_vId g h).symm)).trans <|
      (vId_vComp_heq _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssocInv_lAssoc_heq f g h).symm HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lAssoc_natural_heq η (vId g) (vId h)).symm).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm
  whisker_assoc := by
    intro a b c d f g g' η h
    exact eq_of_heq <|
      (vComp_vId_heq _).symm.trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lAssoc_lAssocInv_heq f g' h).symm).trans <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq (vId f) η (vId h)) HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm
  whisker_exchange := by
    intro a b c f g h i η θ
    rw [globularComp_def, globularComp_def, Cell.cast_eq_iff_heq]
    exact (heq_of_eq (interchange (vId f) θ η (vId i)).symm).trans <|
      (hComp_congr_heq (by simp) (by simp) (by simp)
        (vId_vComp_heq η) (vComp_vId_heq θ)).trans <|
      (hComp_congr_heq (by simp) (by simp) (by simp)
        (vComp_vId_heq η).symm (vId_vComp_heq θ).symm).trans <|
      (heq_of_eq (interchange η (vId h) (vId g) θ)).trans
      (Cell.cast_heq _ _ _).symm
  pentagon := by
    intro a b c d e f g h i
    exact eq_of_heq <|
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|
      (pentagon_heq f g h i).trans
      (Cell.cast_heq _ _ _).symm
  triangle := by
    intro a b c f g
    rw [globularComp_def, Cell.cast_eq_iff_heq]
    exact triangle_heq f g

end LooseBicat

namespace PseudoDoubleCategoryStruct

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

/-- Derived coherence: on a loose identity, the left and right unitors agree —
mathlib's `λ_ (𝟙 a) = ρ_ (𝟙 a)`, transported from the loose bicategory. -/
theorem lLeftUnitor_lId_eq_lRightUnitor_lId (a : C) :
    lLeftUnitor (𝟙ˡ a) = lRightUnitor (𝟙ˡ a) :=
  Bicategory.unitors_equal (a := LooseBicat.mk a)

/-- Inverse form of `lLeftUnitor_lId_eq_lRightUnitor_lId`. -/
theorem lLeftUnitorInv_lId_eq_lRightUnitorInv_lId (a : C) :
    lLeftUnitorInv (𝟙ˡ a) = lRightUnitorInv (𝟙ˡ a) :=
  Bicategory.unitors_inv_equal (a := LooseBicat.mk a)

theorem vId_lId_hComp_lLeftUnitor {a b : C} (m : Loose a b) :
    vId (𝟙ˡ a) ⊚ lLeftUnitor m = lLeftUnitor ((𝟙ˡ a) ⊙ m) := by
  have h := Bicategory.id_whiskerLeft
    (η := (Bicategory.leftUnitor
      (show (LooseBicat.mk a : LooseBicat C) ⟶ LooseBicat.mk b from m)).hom)
  simp only [Iso.hom_inv_id, Category.comp_id] at h
  exact h

end PseudoDoubleCategoryStruct

end CategoryTheory
