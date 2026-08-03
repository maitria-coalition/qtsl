import DoubleCat.Basic

/-!
# The implication double category over a tight base

The thin pseudo double category of propositions over an arbitrary tight
category: loose arrows are propositions, loose composition is
conjunction with `True` as loose identity, and a cell is (the lift of)
an implication from its loose source to its loose target — tight
boundaries are carried but impose nothing.  Every cell type is a
subsingleton, so the pseudo double category axioms hold by proof
irrelevance, exactly as for the free promotion.

This is the universal thin receiver for statement-level semantics: an
interpretation valued in propositions (a judgment layer read as "the
statement holds") lands here, with entailments as cells.  The wrapper
carrier keeps the instance from colliding with any pseudo double
category structure the base itself may carry.
-/

namespace CategoryTheory

universe v u

/-- The carrier of the implication double category over `C`: objects of
`C`, wrapped. -/
structure ImplDouble (C : Type u) : Type u where
  /-- Wrap an object. -/
  of ::
  /-- Unwrap an object. -/
  un : C

namespace ImplDouble

variable {C : Type u} [Category.{v} C]

instance : Category.{v} (ImplDouble C) where
  Hom a b := a.un ⟶ b.un
  id a := 𝟙 a.un
  comp f g := f ≫ g

/-- Loose arrows are propositions; cells are implications (lifted);
loose composition is conjunction. -/
instance : PseudoDoubleCategoryStruct (ImplDouble C) where
  Loose _ _ := Prop
  Cell m n _ _ := PLift (m → n)
  vId _ := ⟨fun h => h⟩
  vComp α β := ⟨fun h => β.down (α.down h)⟩
  lId _ := True
  lComp m n := m ∧ n
  hId _ := ⟨fun h => h⟩
  hComp α β := ⟨fun h => ⟨α.down h.1, β.down h.2⟩⟩
  lAssoc _ _ _ := ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  lAssocInv _ _ _ := ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  lLeftUnitor _ := ⟨fun h => h.2⟩
  lLeftUnitorInv _ := ⟨fun h => ⟨trivial, h⟩⟩
  lRightUnitor _ := ⟨fun h => h.1⟩
  lRightUnitorInv _ := ⟨fun h => ⟨h, trivial⟩⟩

open PseudoDoubleCategoryStruct

instance {a b c d : ImplDouble C} (m : Loose a b) (n : Loose c d)
    (f : a ⟶ c) (g : b ⟶ d) : Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- Thinness, in the explicit form the free-promotion transpose
consumes. -/
theorem cell_subsingleton {a b c d : ImplDouble C} (m : Loose a b)
    (n : Loose c d) (f : a ⟶ c) (g : b ⟶ d) :
    Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- The implication double category is a pseudo double category: its
cells are proof-irrelevant. -/
instance : PseudoDoubleCategory (ImplDouble C) where
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

end ImplDouble

end CategoryTheory
