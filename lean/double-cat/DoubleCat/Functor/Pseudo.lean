import DoubleCat.Functor.Lax
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Ring

/-!
# Pseudo double functors, with positive and negative controls

A lax double functor is *pseudo* when its compositor and unit comparison
are invertible globular cells.  This file defines invertibility for
globular cells (`Cell.IsInvertible`) and pseudo-ness
(`LaxDoubleFunctor.IsPseudo`), and then calibrates the definitions against
known examples in both directions:

* **positive control**: the identity lax double functor is pseudo
  (`LaxDoubleFunctor.isPseudo_id`);
* **negative control**: on the one-object double category with natural
  number grades and natural number weights, the identity-on-objects
  endofunctor whose compositor at a pair of nonzero grades carries weight
  `1` is a perfectly good *lax* double functor (`NatGraded.laxWeight`)
  that is **not** pseudo (`NatGraded.not_isPseudo_laxWeight`): a
  weight-`1` cell has no additive inverse in `ℕ`.

A definition of pseudo-ness that were accidentally vacuous would fail the
negative control; one that were accidentally too strong would fail the
positive one.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w t v u w₂ t₂ v₂ u₂

section IsInvertible

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

/-- A globular cell is invertible when it has a two-sided inverse with respect
to tight-wise composition (up to the casts along `𝟙 ≫ 𝟙 = 𝟙`). -/
def PseudoDoubleCategoryStruct.Cell.IsInvertible {a b : C}
    {m n : Loose a b} (α : Cell m n (𝟙 a) (𝟙 b)) : Prop :=
  ∃ β : Cell n m (𝟙 a) (𝟙 b),
    α ≫ᵥ β = (vId m).cast (by simp) (by simp) ∧
    β ≫ᵥ α = (vId n).cast (by simp) (by simp)

/-- Tight-wise identity cells are invertible. -/
theorem PseudoDoubleCategoryStruct.Cell.isInvertible_vId {a b : C}
    (m : Loose a b) : (vId m).IsInvertible :=
  ⟨vId m, by simp, by simp⟩

variable {D : Type u₂} [Category.{v₂} D]
  [PseudoDoubleCategoryStruct.{w₂, t₂} D] [PseudoDoubleCategory D]

/-- A lax double functor is *pseudo* when its compositor and unit comparison
are invertible globular cells. -/
structure LaxDoubleFunctor.IsPseudo (F : LaxDoubleFunctor C D) : Prop where
  laxComp_isInvertible : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    (F.laxComp m n).IsInvertible
  laxId_isInvertible : ∀ a : C, (F.laxId a).IsInvertible

/-- Positive control: the identity lax double functor is pseudo. -/
theorem LaxDoubleFunctor.isPseudo_id :
    (LaxDoubleFunctor.id : LaxDoubleFunctor C C).IsPseudo where
  laxComp_isInvertible m n :=
    PseudoDoubleCategoryStruct.Cell.isInvertible_vId (m ⊙ n)
  laxId_isInvertible a :=
    PseudoDoubleCategoryStruct.Cell.isInvertible_vId (lId a)

end IsInvertible

namespace NatGraded

/-- The one-object base category for the graded counterexamples. -/
def Pt : Type := Discrete PUnit

/-- The point. -/
def pt : Pt := ⟨PUnit.unit⟩

instance : Category Pt := inferInstanceAs (Category (Discrete PUnit))

/-- A cell between natural-number grades: it exists only for equal grades and
carries a natural-number weight. -/
structure NCell (m n : ℕ) : Type where

  eq : m = n

  wt : ℕ

theorem NCell.ext {m n : ℕ} {α β : NCell m n} (h : α.wt = β.wt) : α = β := by
  obtain ⟨e₁, w₁⟩ := α
  obtain ⟨e₂, w₂⟩ := β
  cases h
  rfl

/-- The one-object double category with natural-number grades as loose arrows
(composing by addition) and weighted cells (weights adding in both
directions). -/
instance ptStruct : PseudoDoubleCategoryStruct Pt where
  Loose _ _ := ℕ
  Cell m n _ _ := NCell m n
  vId _ := ⟨rfl, 0⟩
  vComp α β := ⟨α.eq.trans β.eq, α.wt + β.wt⟩
  lId _ := 0
  lComp m n := m + n
  hId _ := ⟨rfl, 0⟩
  hComp α β := ⟨by rw [α.eq, β.eq], α.wt + β.wt⟩
  lAssoc m n p := ⟨add_assoc m n p, 0⟩
  lAssocInv m n p := ⟨(add_assoc m n p).symm, 0⟩
  lLeftUnitor m := ⟨zero_add m, 0⟩
  lLeftUnitorInv m := ⟨(zero_add m).symm, 0⟩
  lRightUnitor m := ⟨add_zero m, 0⟩
  lRightUnitorInv m := ⟨(add_zero m).symm, 0⟩

@[simp]
theorem ncast {a b c d : Pt} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hf : f = f') (hg : g = g')
    (α : Cell m n f g) : Cell.cast hf hg α = α := by
  subst hf; subst hg; rfl

@[reducible] def nadd (x y : ℕ) : ℕ := x + y

@[simp] theorem nadd_eq (x y : ℕ) : nadd x y = x + y := rfl

@[simp] theorem lComp_eq {a b c : Pt} (m : Loose a b) (n : Loose b c) :
    m ⊙ n = nadd m n := rfl

@[simp] theorem lId_eq (a : Pt) : (lId a : Loose a a) = (0 : ℕ) := rfl

@[simp] theorem vComp_wt {a b c d e f : Pt} {m : Loose a b} {n : Loose c d}
    {p : Loose e f} {f₁ : a ⟶ c} {g₁ : b ⟶ d} {f₂ : c ⟶ e} {g₂ : d ⟶ f}
    (α : Cell m n f₁ g₁) (β : Cell n p f₂ g₂) :
    (α ≫ᵥ β).wt = α.wt + β.wt := rfl

@[simp] theorem hComp_wt {a₁ a₂ a₃ b₁ b₂ b₃ : Pt}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂}
    {n₂ : Loose b₂ b₃} {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h) :
    (α ⊚ β).wt = α.wt + β.wt := rfl

@[simp] theorem vId_wt {a b : Pt} (m : Loose a b) : (vId m).wt = 0 := rfl

@[simp] theorem hId_wt {a b : Pt} (f : a ⟶ b) : (hId f).wt = 0 := rfl

@[simp] theorem lAssoc_wt {a b c d : Pt} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) : (lAssoc m n p).wt = 0 := rfl

@[simp] theorem lAssocInv_wt {a b c d : Pt} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) : (lAssocInv m n p).wt = 0 := rfl

@[simp] theorem lLeftUnitor_wt {a b : Pt} (m : Loose a b) :
    (lLeftUnitor m).wt = 0 := rfl

@[simp] theorem lLeftUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (lLeftUnitorInv m).wt = 0 := rfl

@[simp] theorem lRightUnitor_wt {a b : Pt} (m : Loose a b) :
    (lRightUnitor m).wt = 0 := rfl

@[simp] theorem lRightUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (lRightUnitorInv m).wt = 0 := rfl

instance : PseudoDoubleCategory Pt where
  vId_vComp _ := NCell.ext (by simp)
  vComp_vId _ := NCell.ext (by simp)
  vComp_assoc _ _ _ := NCell.ext (by simp <;> ring)
  hId_id _ := NCell.ext (by simp)
  hId_comp _ _ := NCell.ext (by simp)
  hComp_vId _ _ := NCell.ext (by simp)
  interchange _ _ _ _ := NCell.ext (by simp <;> ring)
  lAssoc_natural _ _ _ := NCell.ext (by simp <;> ring)
  lLeftUnitor_natural _ := NCell.ext (by simp <;> ring)
  lRightUnitor_natural _ := NCell.ext (by simp <;> ring)
  lAssoc_lAssocInv _ _ _ := NCell.ext (by simp)
  lAssocInv_lAssoc _ _ _ := NCell.ext (by simp)
  lLeftUnitor_lLeftUnitorInv _ := NCell.ext (by simp)
  lLeftUnitorInv_lLeftUnitor _ := NCell.ext (by simp)
  lRightUnitor_lRightUnitorInv _ := NCell.ext (by simp)
  lRightUnitorInv_lRightUnitor _ := NCell.ext (by simp)
  pentagon _ _ _ _ := NCell.ext (by simp)
  triangle _ _ := NCell.ext (by simp)

/-- The compositor weight: `1` at a pair of nonzero grades, `0` otherwise. -/
def lw (m n : ℕ) : ℕ := if m = 0 ∨ n = 0 then 0 else 1

/-- The identity-on-objects endofunctor whose compositor at a pair of nonzero
grades carries weight `1`.  The unit-triangle coherences hold precisely
because `lw` vanishes when either grade is zero. -/
def laxWeight : LaxDoubleFunctor Pt Pt where
  toFunctor := Functor.id Pt
  mapLoose m := m
  mapCell α := α
  mapCell_vId m := NCell.ext (by simp)
  mapCell_vComp α β := NCell.ext (by simp)
  laxComp m n := ⟨rfl, lw m n⟩
  laxId a := ⟨rfl, 0⟩
  laxComp_natural {a₁ a₂ a₃ b₁ b₂ b₃} {m₁ m₂ n₁ n₂} {f g h} α β := by
    obtain ⟨hae, aw⟩ := α
    obtain ⟨hbe, bw⟩ := β
    subst hae
    subst hbe
    exact NCell.ext (by simp <;> ring)
  laxId_natural f := NCell.ext (by simp)
  laxComp_assoc m n p :=
    NCell.ext (by
      simp only [vComp_wt, hComp_wt, vId_wt, lAssoc_wt, ncast, lComp_eq,
        nadd_eq, lw]
      split_ifs <;> omega)
  laxComp_leftUnitor m :=
    NCell.ext (by
      simp only [vComp_wt, hComp_wt, vId_wt, hId_wt, lLeftUnitor_wt, ncast]
      show 0 + 0 + (lw 0 m + 0) = 0
      simp [lw])
  laxComp_rightUnitor m :=
    NCell.ext (by
      simp only [vComp_wt, hComp_wt, vId_wt, hId_wt, lRightUnitor_wt, ncast]
      show 0 + 0 + (lw m 0 + 0) = 0
      simp [lw])

/-- Negative control: `laxWeight` is lax but not pseudo — a weight-`1` cell
has no additive inverse in `ℕ`. -/
theorem not_isPseudo_laxWeight : ¬ laxWeight.IsPseudo := by
  intro h
  obtain ⟨β, h₁, -⟩ :=
    h.laxComp_isInvertible (a := pt) (b := pt) (c := pt)
      (m := (1 : ℕ)) (n := (1 : ℕ))
  have hw := congrArg NCell.wt h₁
  simp [laxWeight, lw] at hw

end NatGraded

end CategoryTheory
