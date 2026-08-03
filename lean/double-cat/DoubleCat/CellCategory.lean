import DoubleCat.Basic

/-!
# The category of loose arrows and cells

Given a pseudo double category on `C`, the loose arrows (with their
endpoints) and the cells between them form an ordinary category under
tight-wise composition, with strict source and target functors to `C`.
This recovers the classical presentation of a (pseudo) double category as a
pair of categories `𝔹₀`, `𝔹₁` with source/target functors (Grandis–Paré):
here `𝔹₀` is `C` itself and `𝔹₁` is `LoosePair C` as constructed below.

The construction is also the basic sanity check on the axioms of
`CategoryTheory.PseudoDoubleCategory`: the tight-wise category laws stated
there (up to `Cell.cast`) are exactly what is needed for `LoosePair C` to
be a category on the nose.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w t v u

variable (C : Type u) [Category.{v} C] [PseudoDoubleCategoryStruct C]

/-- The type of loose arrows of a pseudo double category, bundled with their
endpoints.  These are the objects of the category of loose arrows and
cells. -/
structure LoosePair where

  /-- The source object. -/
  src : C

  /-- The target object. -/
  tgt : C

  /-- The loose arrow. -/
  loose : Loose src tgt

namespace LoosePair

variable {C}

/-- A morphism of bundled loose arrows: a cell together with its tight
sides. -/
@[ext]
structure Hom (M N : LoosePair C) where

  srcHom : M.src ⟶ N.src

  tgtHom : M.tgt ⟶ N.tgt

  cell : Cell M.loose N.loose srcHom tgtHom

instance : CategoryStruct (LoosePair C) where
  Hom M N := Hom M N
  id M := ⟨𝟙 M.src, 𝟙 M.tgt, vId M.loose⟩
  comp α β := ⟨α.srcHom ≫ β.srcHom, α.tgtHom ≫ β.tgtHom, α.cell ≫ᵥ β.cell⟩

@[simp]
theorem id_srcHom (M : LoosePair C) : Hom.srcHom (𝟙 M) = 𝟙 M.src := rfl

@[simp]
theorem id_tgtHom (M : LoosePair C) : Hom.tgtHom (𝟙 M) = 𝟙 M.tgt := rfl

@[simp]
theorem id_cell (M : LoosePair C) : Hom.cell (𝟙 M) = vId M.loose := rfl

@[simp]
theorem comp_srcHom {M N P : LoosePair C} (α : M ⟶ N) (β : N ⟶ P) :
    (α ≫ β).srcHom = α.srcHom ≫ β.srcHom := rfl

@[simp]
theorem comp_tgtHom {M N P : LoosePair C} (α : M ⟶ N) (β : N ⟶ P) :
    (α ≫ β).tgtHom = α.tgtHom ≫ β.tgtHom := rfl

@[simp]
theorem comp_cell {M N P : LoosePair C} (α : M ⟶ N) (β : N ⟶ P) :
    (α ≫ β).cell = α.cell ≫ᵥ β.cell := rfl

/-- Morphisms of bundled loose arrows are determined by their three
components. -/
theorem hom_ext {M N : LoosePair C} {α β : M ⟶ N}
    (hsrc : α.srcHom = β.srcHom) (htgt : α.tgtHom = β.tgtHom)
    (hcell : α.cell.cast hsrc htgt = β.cell) : α = β := by
  obtain ⟨fs, ft, fc⟩ := α
  obtain ⟨gs, gt, gc⟩ := β
  dsimp at hsrc htgt
  subst hsrc; subst htgt
  cases hcell
  rfl

variable [PseudoDoubleCategory C]

/-- Loose arrows and cells form a category under tight-wise composition: the
category laws are the tight-wise category laws of the double category, with
the casts absorbed by the bundled tight sides. -/
instance : Category (LoosePair C) where
  id_comp α := by
    apply hom_ext (by simp) (by simp)
    simp [PseudoDoubleCategory.vId_vComp]
  comp_id α := by
    apply hom_ext (by simp) (by simp)
    simp [PseudoDoubleCategory.vComp_vId]
  assoc α β γ := by
    apply hom_ext (by simp) (by simp)
    simp [PseudoDoubleCategory.vComp_assoc]

variable (C)

/-- The strict source functor from loose arrows and cells to `C`. -/
@[simps]
def srcFunctor : LoosePair C ⥤ C where
  obj M := M.src
  map α := α.srcHom

/-- The strict target functor from loose arrows and cells to `C`. -/
@[simps]
def tgtFunctor : LoosePair C ⥤ C where
  obj M := M.tgt
  map α := α.tgtHom

/-- The loose-identity functor `C ⥤ LoosePair C`, a section of both the source
and the target functor. -/
@[simps]
def lIdFunctor : C ⥤ LoosePair C where
  obj a := ⟨a, a, lId a⟩
  map f := ⟨f, f, hId f⟩
  map_id a := by
    apply hom_ext (by simp) (by simp)
    simp [PseudoDoubleCategory.hId_id]
  map_comp f g := by
    apply hom_ext (by simp) (by simp)
    simp [PseudoDoubleCategory.hId_comp]

@[simp]
theorem lIdFunctor_srcFunctor : lIdFunctor C ⋙ srcFunctor C = 𝟭 C := rfl

@[simp]
theorem lIdFunctor_tgtFunctor : lIdFunctor C ⋙ tgtFunctor C = 𝟭 C := rfl

end LoosePair

end CategoryTheory
