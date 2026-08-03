import DoubleCat.Basic

/-!
# The vertically-trivial pseudo double category on a category

The tight-only double reading of a category: loose arrows and cells are
both `PUnit`, so the loose direction carries no information and every
coherence law holds by proof irrelevance.  This is the initial-flavored
way to regard a category as a pseudo double category; decoration layers
over it (`DoubleCat.JudgLayer`) recover proposition-valued loose
structure — the implication double category is the judgment layer over
this base at the propositional decoration datum.

Universes are pinned at the loose and cell slots (`PUnit.{1}`): an
unpinned `PUnit` would auto-generalize the instance's universes and
float metavariables through every downstream declaration (the
`Category.{0}` precedent of the claim-context instances).
-/

namespace CategoryTheory

universe v u

/-- The carrier of the vertically-trivial double category on `C`:
objects of `C`, wrapped so the instance collides with nothing `C`
itself carries. -/
structure Vert (C : Type u) : Type u where
  /-- Wrap an object. -/
  of ::
  /-- Unwrap an object. -/
  un : C

namespace Vert

variable {C : Type u} [Category.{v} C]

instance : Category.{v} (Vert C) where
  Hom a b := a.un ⟶ b.un
  id a := 𝟙 a.un
  comp f g := f ≫ g

/-- Loose arrows and cells are trivial: the tight-only double
category. -/
instance : PseudoDoubleCategoryStruct.{0, 0} (Vert C) where
  Loose _ _ := PUnit.{1}
  Cell _ _ _ _ := PUnit.{1}
  vId _ := ⟨⟩
  vComp _ _ := ⟨⟩
  lId _ := ⟨⟩
  lComp _ _ := ⟨⟩
  hId _ := ⟨⟩
  hComp _ _ := ⟨⟩
  lAssoc _ _ _ := ⟨⟩
  lAssocInv _ _ _ := ⟨⟩
  lLeftUnitor _ := ⟨⟩
  lLeftUnitorInv _ := ⟨⟩
  lRightUnitor _ := ⟨⟩
  lRightUnitorInv _ := ⟨⟩

open PseudoDoubleCategoryStruct

instance {a b c d : Vert C} (m : Loose a b) (n : Loose c d)
    (f : a ⟶ c) (g : b ⟶ d) : Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton PUnit.{1})

/-- The vertically-trivial double category is a pseudo double category:
its cells are proof-irrelevant. -/
instance : PseudoDoubleCategory (Vert C) where
  vId_vComp _ := Subsingleton.elim _ _
  vComp_vId _ := Subsingleton.elim _ _
  vComp_assoc _ _ _ := Subsingleton.elim _ _
  hId_id _ := Subsingleton.elim _ _
  hId_comp _ _ := Subsingleton.elim _ _
  hComp_vId _ _ := Subsingleton.elim _ _
  interchange _ _ _ _ := Subsingleton.elim _ _
  lAssoc_natural _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_natural _ := Subsingleton.elim _ _
  lRightUnitor_natural _ := Subsingleton.elim _ _
  lAssoc_lAssocInv _ _ _ := Subsingleton.elim _ _
  lAssocInv_lAssoc _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_lLeftUnitorInv _ := Subsingleton.elim _ _
  lLeftUnitorInv_lLeftUnitor _ := Subsingleton.elim _ _
  lRightUnitor_lRightUnitorInv _ := Subsingleton.elim _ _
  lRightUnitorInv_lRightUnitor _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

end Vert

end CategoryTheory
