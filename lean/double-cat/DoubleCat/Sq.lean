import DoubleCat.Basic

/-!
# The double category of commutative squares

For any category `C`, the pseudo double category `Sq C` has the objects of
`C` as objects, the morphisms of `C` as both tight and loose arrows, and the
commutative squares of `C` as cells.  It is strict: loose composition is the
composition of `C`, and all structure cells are (casts of) identity cells.

This is the simplest nontrivial pseudo double category and serves as the
basic witness that the axioms of `CategoryTheory.PseudoDoubleCategory` are
satisfiable; since its cells are proof-irrelevant, all cell equations hold
by `Subsingleton.elim`.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe v u

variable (C : Type u) [Category.{v} C]

/-- The double category of commutative squares of `C`: a type synonym for `C`
carrying the `PseudoDoubleCategory` instance whose loose arrows are the
morphisms of `C` and whose cells are commutative squares. -/
def Sq (C : Type u) := C

namespace Sq

instance : Category.{v} (Sq C) := inferInstanceAs (Category C)

variable {C}

/-- Interpret an object of `C` as an object of `Sq C`. -/
def mk (a : C) : Sq C := a

/-- Interpret an object of `Sq C` as an object of `C`. -/
def unmk (a : Sq C) : C := a

variable (C)

/-- The double category structure on `Sq C`: loose arrows are morphisms of
`C`, and a cell is a proof that the square commutes. -/
instance : PseudoDoubleCategoryStruct (Sq C) where
  Loose a b := a ⟶ b
  Cell m n f g := PLift (m ≫ g = f ≫ n)
  vId m := ⟨by simp⟩
  vComp α β := ⟨by
    rw [← Category.assoc, α.down, Category.assoc, β.down, ← Category.assoc]⟩
  lId a := 𝟙 a
  lComp m n := m ≫ n
  hId f := ⟨by simp⟩
  hComp α β := ⟨by
    rw [Category.assoc, β.down, ← Category.assoc, α.down, Category.assoc]⟩
  lAssoc m n p := ⟨by simp⟩
  lAssocInv m n p := ⟨by simp⟩
  lLeftUnitor m := ⟨by simp⟩
  lLeftUnitorInv m := ⟨by simp⟩
  lRightUnitor m := ⟨by simp⟩
  lRightUnitorInv m := ⟨by simp⟩

instance {a b c d : Sq C} (m : Loose a b) (n : Loose c d) (f : a ⟶ c)
    (g : b ⟶ d) : Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

variable {C}

@[simp]
theorem lId_def (a : Sq C) : 𝟙ˡ a = 𝟙 a := rfl

@[simp]
theorem lComp_def {a b c : Sq C} (m : Loose a b) (n : Loose b c) :
    m ⊙ n = m ≫ n := rfl

variable (C)

/-- The axioms hold: cells are proof-irrelevant, so every cell equation is
`Subsingleton.elim`. -/
instance : PseudoDoubleCategory (Sq C) where
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

end Sq

end CategoryTheory
