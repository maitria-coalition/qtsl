import DoubleCat.Monoidal
import DoubleCat.Functor.Pseudo
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Ring

/-!
# Strong monoidal double categories, with a negative control

Following Shulman ("Framed bicategories and monoidal fibrations", 2008,
§5) and Hansen–Shulman ("Constructing symmetric monoidal bicategories
functorially", 2019), the tensor of a monoidal double category is a
*pseudo* double functor: its interchanger `chi` and unit interchanger `mu`
are invertible.  The data classes in `DoubleCat.Monoidal` do not impose
this (they describe the lax variant), so strength is its own mixin,
`StrongMonoidalDoubleCategory`, in terms of
`PseudoDoubleCategoryStruct.Cell.IsInvertible`.

Controls:

* positive — the integer-graded witness of
  `DoubleCat.Monoidal.GradedCounterexample` is strong (the instance is
  registered in that file), as is every graded model over group-valued
  weights (`DoubleCat.Monoidal.GradedModel.instStrong`);
* negative (this file) — on the one-object double category with natural
  number grades and weights (`NatGraded` of `DoubleCat.Functor.Pseudo`),
  the monoidal structure whose interchanger has constant weight `1`
  satisfies all the data-level laws but is not strong: a weight-`1` cell
  has no additive inverse in `ℕ` (`NatGraded.not_strong`).

A definition of strength that were accidentally vacuous would fail the
negative control; one that were accidentally too strong would fail the
positive ones.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct MonoidalDoubleCategoryStruct

universe w t v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  [PseudoDoubleCategoryStruct.{w, t} C] [PseudoDoubleCategory C]
  [MonoidalDoubleCategoryStruct C]

/-- A monoidal double category is *strong* when its interchanger `chi` and
unit interchanger `mu` are invertible globular cells, i.e. the tensor is a
pseudo (not merely lax) double functor. -/
class StrongMonoidalDoubleCategory : Prop where
  chi_isInvertible : ∀ {a b c a' b' c' : C} (m : Loose a b) (n : Loose b c)
    (m' : Loose a' b') (n' : Loose b' c'), (chi m n m' n').IsInvertible
  mu_isInvertible : ∀ a b : C, (mu a b).IsInvertible

namespace NatGraded

instance : MonoidalCategory Pt :=
  inferInstanceAs (MonoidalCategory (Discrete PUnit))

instance : Subsingleton Pt :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The monoidal data on the natural-number-graded one-object double category
whose interchanger has constant weight `1` and all other components weight
`0`. -/
instance monStructOne : MonoidalDoubleCategoryStruct Pt where
  tLoose m n := nadd m n
  tCell α β := ⟨by rw [α.eq, β.eq], α.wt + β.wt⟩
  chi m n m' n' := ⟨by simp only [lComp_eq, nadd_eq]; ring, 1⟩
  mu a b := ⟨by simp only [lId_eq, nadd_eq], 0⟩
  tAssoc m n p := ⟨by simp only [nadd_eq]; ring, 0⟩
  tAssocInv m n p := ⟨by simp only [nadd_eq]; ring, 0⟩
  tLeftUnitor m := ⟨by simp only [lId_eq, nadd_eq]; ring, 0⟩
  tLeftUnitorInv m := ⟨by simp only [lId_eq, nadd_eq]; ring, 0⟩
  tRightUnitor m := ⟨by simp only [lId_eq, nadd_eq]; ring, 0⟩
  tRightUnitorInv m := ⟨by simp only [lId_eq, nadd_eq]; ring, 0⟩

@[simp] theorem tLoose_eq {a b c d : Pt} (m : Loose a b) (n : Loose c d) :
    m ⊠ n = nadd m n := rfl

@[simp] theorem tCell_wt {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Pt}
    {m₁ : Loose a₁ b₁} {n₁ : Loose c₁ d₁} {m₂ : Loose a₂ b₂}
    {n₂ : Loose c₂ d₂} {f₁ : a₁ ⟶ c₁} {g₁ : b₁ ⟶ d₁} {f₂ : a₂ ⟶ c₂}
    {g₂ : b₂ ⟶ d₂} (α : Cell m₁ n₁ f₁ g₁) (β : Cell m₂ n₂ f₂ g₂) :
    (α ⊠ᶜ β).wt = α.wt + β.wt := rfl

@[simp] theorem chi_wt {a b c a' b' c' : Pt} (m : Loose a b) (n : Loose b c)
    (m' : Loose a' b') (n' : Loose b' c') : (chi m n m' n').wt = 1 := rfl

@[simp] theorem mu_wt (a b : Pt) : (mu a b).wt = 0 := rfl

@[simp] theorem tAssoc_wt {a b c d e f : Pt} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) : (tAssoc m n p).wt = 0 := rfl

@[simp] theorem tAssocInv_wt {a b c d e f : Pt} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) : (tAssocInv m n p).wt = 0 := rfl

@[simp] theorem tLeftUnitor_wt {a b : Pt} (m : Loose a b) :
    (tLeftUnitor m).wt = 0 := rfl

@[simp] theorem tLeftUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (tLeftUnitorInv m).wt = 0 := rfl

@[simp] theorem tRightUnitor_wt {a b : Pt} (m : Loose a b) :
    (tRightUnitor m).wt = 0 := rfl

@[simp] theorem tRightUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (tRightUnitorInv m).wt = 0 := rfl

instance : MonoidalDoubleCategory Pt where
  tCell_vId _ _ := NCell.ext (by simp)
  tCell_vComp _ _ _ _ := NCell.ext (by simp; ring)
  chi_natural _ _ _ _ := NCell.ext (by simp; ring)
  mu_natural _ _ := NCell.ext (by simp)
  tAssoc_natural _ _ _ := NCell.ext (by simp; ring)
  tLeftUnitor_natural _ := NCell.ext (by simp)
  tRightUnitor_natural _ := NCell.ext (by simp)
  tAssoc_tAssocInv _ _ _ := NCell.ext (by simp)
  tAssocInv_tAssoc _ _ _ := NCell.ext (by simp)
  tLeftUnitor_tLeftUnitorInv _ := NCell.ext (by simp)
  tLeftUnitorInv_tLeftUnitor _ := NCell.ext (by simp)
  tRightUnitor_tRightUnitorInv _ := NCell.ext (by simp)
  tRightUnitorInv_tRightUnitor _ := NCell.ext (by simp)

/-- Negative control: the weight-`1` interchanger satisfies all data-level
laws but is not invertible — a weight-`1` cell has no additive inverse in
`ℕ`. -/
theorem not_strong : ¬ StrongMonoidalDoubleCategory Pt := by
  intro h
  obtain ⟨β, h₁, -⟩ :=
    h.chi_isInvertible (a := pt) (b := pt) (c := pt) (a' := pt) (b' := pt)
      (c' := pt) (m := (1 : ℕ)) (n := (1 : ℕ)) (m' := (1 : ℕ)) (n' := (1 : ℕ))
  have hw := congrArg NCell.wt h₁
  simp at hw

end NatGraded

end CategoryTheory
