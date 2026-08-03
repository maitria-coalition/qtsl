import DoubleCat.Monoidal
import DoubleCat.Monoidal.Strong
import DoubleCat.Functor.Pseudo
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-!
# The associator–interchanger axiom is independent of the others

This file constructs a symmetric monoidal double category structure on the
one-object pseudo double category whose loose arrows are the integers
(grades, composing by addition) and whose cells `m ⟶ n` exist only for
`m = n` and are integers (weights, composing by addition in both
directions).  All monoidal data is taken to be zero-weight except the
interchanger, whose component at composable pairs of grades
`(s, t), (s', t')` is
`g(s, t; s', t') = c(s, s') + c(t, t') - c(s + t, s' + t')` with
`c(x, y) = x² y²` — a coboundary in the composition pairing.

Every pasting equation in this model linearizes: the weight of a composite
is the sum of the weights of its parts, transports contribute nothing, and
the structure is otherwise strict.  The data-level laws
(`MonoidalDoubleCategory`, `BraidedDoubleCategory`) therefore hold, and the
coboundary shape of `g` makes the interchanger associative (`M4`) and
compatible with everything except the associator–interchanger square:

* instances are provided for `M1`, `M2`, `M3`, `M4`, `M5`, `M6`, `M7`,
  `M10`, `M11a`, `M11b`;
* `M9` **fails**, witnessed at grades `(1, 1, 2)` in all six slots
  (`not_m9AssociatorInterchanger`).

Hence the associator–interchanger square is not derivable from the
remaining axioms of the package: a hypothesis list for a monoidal double
category (or for the monoidal structure of a double Grothendieck
construction) that omits it is incomplete.  The failure is exactly the
non-vanishing of the coboundary of `g` in the tensor direction: writing
`D := δc` for the coboundary of `c` in one variable pair, the square at
grades `(s₁,s₂,s₃),(t₁,t₂,t₃)` demands
`D s₁ s₂ s₃ + D t₁ t₂ t₃ = D (s₁+t₁) (s₂+t₂) (s₃+t₃)`, and
`D a b c = 2·a·b·c·(c - a)` is not additive:
`D 1 1 2 + D 1 1 2 = 8 ≠ 64 = D 2 2 4`.
-/

namespace CategoryTheory

namespace MonoidalDoubleCategory

namespace GradedCounterexample

open PseudoDoubleCategoryStruct MonoidalDoubleCategoryStruct MonoidalCategory

/-- The one-object base category of the integer-graded model. -/
def Pt : Type := Discrete PUnit

/-- The point. -/
def pt : Pt := ⟨PUnit.unit⟩

instance : Category Pt := inferInstanceAs (Category (Discrete PUnit))

instance : MonoidalCategory Pt :=
  inferInstanceAs (MonoidalCategory (Discrete PUnit))

instance : Subsingleton Pt :=
  ⟨fun a b => by cases a; cases b; rfl⟩

instance (X Y : Pt) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ULift (PLift _)))

instance : BraidedCategory Pt where
  braiding _ _ := eqToIso (Subsingleton.elim _ _)
  braiding_naturality_right := by intros; exact Subsingleton.elim _ _
  braiding_naturality_left := by intros; exact Subsingleton.elim _ _
  hexagon_forward := by intros; exact Subsingleton.elim _ _
  hexagon_reverse := by intros; exact Subsingleton.elim _ _

instance : SymmetricCategory Pt where
  symmetry := by intros; exact Subsingleton.elim _ _

/-- A cell between integer grades: it exists only for equal grades and
carries an integer weight. -/
structure GCell (m n : ℤ) : Type where

  eq : m = n

  wt : ℤ

theorem GCell.ext {m n : ℤ} {α β : GCell m n} (h : α.wt = β.wt) : α = β := by
  obtain ⟨e₁, w₁⟩ := α
  obtain ⟨e₂, w₂⟩ := β
  cases h
  rfl

/-- The one-object double category with integer grades as loose arrows
(composing by addition) and integer-weighted cells (weights adding in both
directions). -/
instance ptStruct : PseudoDoubleCategoryStruct Pt where
  Loose _ _ := ℤ
  Cell m n _ _ := GCell m n
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
theorem gcast {a b c d : Pt} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hf : f = f') (hg : g = g')
    (α : Cell m n f g) : Cell.cast hf hg α = α := by
  subst hf; subst hg; rfl

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

@[simp] theorem lRightUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (lRightUnitorInv m).wt = 0 := rfl

@[simp] theorem lRightUnitor_wt {a b : Pt} (m : Loose a b) :
    (lRightUnitor m).wt = 0 := rfl

@[reducible] def zadd (x y : ℤ) : ℤ := x + y

@[simp] theorem zadd_eq (x y : ℤ) : zadd x y = x + y := rfl

@[simp] theorem lComp_eq {a b c : Pt} (m : Loose a b) (n : Loose b c) :
    m ⊙ n = zadd m n := rfl

@[simp] theorem lId_eq (a : Pt) : (lId a : Loose a a) = (0 : ℤ) := rfl

instance : PseudoDoubleCategory Pt where
  vId_vComp _ := GCell.ext (by simp)
  vComp_vId _ := GCell.ext (by simp)
  vComp_assoc _ _ _ := GCell.ext (by simp <;> ring)
  hId_id _ := GCell.ext (by simp)
  hId_comp _ _ := GCell.ext (by simp)
  hComp_vId _ _ := GCell.ext (by simp)
  interchange _ _ _ _ := GCell.ext (by simp <;> ring)
  lAssoc_natural _ _ _ := GCell.ext (by simp <;> ring)
  lLeftUnitor_natural _ := GCell.ext (by simp <;> ring)
  lRightUnitor_natural _ := GCell.ext (by simp <;> ring)
  lAssoc_lAssocInv _ _ _ := GCell.ext (by simp)
  lAssocInv_lAssoc _ _ _ := GCell.ext (by simp)
  lLeftUnitor_lLeftUnitorInv _ := GCell.ext (by simp)
  lLeftUnitorInv_lLeftUnitor _ := GCell.ext (by simp)
  lRightUnitor_lRightUnitorInv _ := GCell.ext (by simp)
  lRightUnitorInv_lRightUnitor _ := GCell.ext (by simp)
  pentagon _ _ _ _ := GCell.ext (by simp)
  triangle _ _ := GCell.ext (by simp)

/-- The interchanger weight: the coboundary
`c(s, s') + c(t, t') - c(s + t, s' + t')` of `c(x, y) = x²y²` in the
composition pairing. -/
def gW (s t s' t' : ℤ) : ℤ :=
  s ^ 2 * s' ^ 2 + t ^ 2 * t' ^ 2 - (s + t) ^ 2 * (s' + t') ^ 2

/-- The monoidal data: all components zero-weight except the interchanger,
which carries `gW`. -/
instance monStruct : MonoidalDoubleCategoryStruct Pt where
  tLoose m n := zadd m n
  tCell α β := ⟨by rw [α.eq, β.eq], α.wt + β.wt⟩
  chi m n m' n' :=
    ⟨by simp only [lComp_eq, zadd_eq]; ring, gW m n m' n'⟩
  mu a b := ⟨by simp only [lId_eq, zadd_eq]; ring, 0⟩
  tAssoc m n p := ⟨by simp only [zadd_eq]; ring, 0⟩
  tAssocInv m n p := ⟨by simp only [zadd_eq]; ring, 0⟩
  tLeftUnitor m := ⟨by simp only [lId_eq, zadd_eq]; ring, 0⟩
  tLeftUnitorInv m := ⟨by simp only [lId_eq, zadd_eq]; ring, 0⟩
  tRightUnitor m := ⟨by simp only [lId_eq, zadd_eq]; ring, 0⟩
  tRightUnitorInv m := ⟨by simp only [lId_eq, zadd_eq]; ring, 0⟩

@[simp] theorem tLoose_eq {a b c d : Pt} (m : Loose a b) (n : Loose c d) :
    m ⊠ n = zadd m n := rfl

/-- The braided data: zero-weight braiding cells. -/
instance braidedStruct : BraidedDoubleCategoryStruct Pt where
  toMonoidalDoubleCategoryStruct := monStruct
  tBraiding m n := ⟨by simp only [tLoose_eq, zadd_eq]; ring, 0⟩
  tBraidingInv m n := ⟨by simp only [tLoose_eq, zadd_eq]; ring, 0⟩

@[simp] theorem tCell_wt {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Pt}
    {m₁ : Loose a₁ b₁} {n₁ : Loose c₁ d₁} {m₂ : Loose a₂ b₂}
    {n₂ : Loose c₂ d₂} {f₁ : a₁ ⟶ c₁} {g₁ : b₁ ⟶ d₁} {f₂ : a₂ ⟶ c₂}
    {g₂ : b₂ ⟶ d₂} (α : Cell m₁ n₁ f₁ g₁) (β : Cell m₂ n₂ f₂ g₂) :
    (α ⊠ᶜ β).wt = α.wt + β.wt := rfl

@[simp] theorem chi_wt {a b c a' b' c' : Pt} (m : Loose a b) (n : Loose b c)
    (m' : Loose a' b') (n' : Loose b' c') :
    (chi m n m' n').wt = gW (m : ℤ) n m' n' := rfl

@[simp] theorem mu_wt (a b : Pt) : (mu a b).wt = 0 := rfl

@[simp] theorem tAssoc_wt {a b c d e f : Pt} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) : (tAssoc m n p).wt = 0 := rfl

@[simp] theorem tAssocInv_wt {a b c d e f : Pt} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) : (tAssocInv m n p).wt = 0 := rfl

@[simp] theorem tLeftUnitor_wt {a b : Pt} (m : Loose a b) :
    (tLeftUnitor m).wt = 0 := rfl

@[simp] theorem tLeftUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (tLeftUnitorInv m).wt = 0 := rfl

@[simp] theorem tRightUnitorInv_wt {a b : Pt} (m : Loose a b) :
    (tRightUnitorInv m).wt = 0 := rfl

@[simp] theorem tRightUnitor_wt {a b : Pt} (m : Loose a b) :
    (tRightUnitor m).wt = 0 := rfl

@[simp] theorem tBraiding_wt {a b c d : Pt} (m : Loose a b)
    (n : Loose c d) : (tBraiding m n).wt = 0 := rfl

@[simp] theorem tBraidingInv_wt {a b c d : Pt} (m : Loose a b)
    (n : Loose c d) : (tBraidingInv m n).wt = 0 := rfl

instance : MonoidalDoubleCategory Pt where
  tCell_vId _ _ := GCell.ext (by simp)
  tCell_vComp _ _ _ _ := GCell.ext (by simp <;> ring)
  chi_natural α β α' β' :=
    GCell.ext (by simp [α.eq, β.eq, α'.eq, β'.eq] <;> ring)
  mu_natural _ _ := GCell.ext (by simp)
  tAssoc_natural _ _ _ := GCell.ext (by simp <;> ring)
  tLeftUnitor_natural _ := GCell.ext (by simp <;> ring)
  tRightUnitor_natural _ := GCell.ext (by simp <;> ring)
  tAssoc_tAssocInv _ _ _ := GCell.ext (by simp)
  tAssocInv_tAssoc _ _ _ := GCell.ext (by simp)
  tLeftUnitor_tLeftUnitorInv _ := GCell.ext (by simp)
  tLeftUnitorInv_tLeftUnitor _ := GCell.ext (by simp)
  tRightUnitor_tRightUnitorInv _ := GCell.ext (by simp)
  tRightUnitorInv_tRightUnitor _ := GCell.ext (by simp)

instance : BraidedDoubleCategory Pt where
  tBraiding_natural _ _ := GCell.ext (by simp <;> ring)
  tBraiding_tBraidingInv _ _ := GCell.ext (by simp)
  tBraidingInv_tBraiding _ _ := GCell.ext (by simp)

instance : M1Pentagon Pt where
  pentagon _ _ _ _ := GCell.ext (by simp)

instance : M2Triangle Pt where
  triangle _ _ := GCell.ext (by simp)

instance : M3Hexagons Pt where
  hexagon_forward _ _ _ := GCell.ext (by simp)
  hexagon_reverse _ _ _ := GCell.ext (by simp)
  involutive _ _ := GCell.ext (by simp)

instance : M4InterchangerAssoc Pt where
  assoc m n p m' n' p' := GCell.ext (by simp [gW] <;> ring)

instance : M5InterchangerUnit Pt where
  left m m' := GCell.ext (by simp [gW] <;> ring)
  right m m' := GCell.ext (by simp [gW] <;> ring)

instance : M6BraidingInterchanger Pt where
  braiding_chi m n m' n' := GCell.ext (by simp [gW] <;> ring)

instance : M7UnitorUnit Pt where
  left _ := GCell.ext (by simp)
  right _ := GCell.ext (by simp)

instance : M10UnitorInterchanger Pt where
  left m n := GCell.ext (by simp [gW] <;> ring)
  right m n := GCell.ext (by simp [gW])

instance : M11aAssociatorUnit Pt where
  assoc_mu _ _ _ := GCell.ext (by simp)

instance : M11bBraidingUnit Pt where
  braiding_mu _ _ := GCell.ext (by simp)

theorem chi_isInvertible {a b c a' b' c' : Pt} (m : Loose a b)
    (n : Loose b c) (m' : Loose a' b') (n' : Loose b' c') :
    (chi m n m' n').IsInvertible :=
  ⟨⟨by simp only [lComp_eq, tLoose_eq, zadd_eq]; ring, -gW m n m' n'⟩,
    GCell.ext (by simp), GCell.ext (by simp)⟩

theorem mu_isInvertible (a b : Pt) : (mu a b).IsInvertible :=
  ⟨⟨by simp only [lId_eq, tLoose_eq, zadd_eq]; ring, 0⟩,
    GCell.ext (by simp), GCell.ext (by simp)⟩

instance : StrongMonoidalDoubleCategory Pt where
  chi_isInvertible := chi_isInvertible
  mu_isInvertible := mu_isInvertible

theorem not_m9AssociatorInterchanger : ¬ M9AssociatorInterchanger Pt := by
  intro h
  have e := h.assoc_chi (a₁ := pt) (b₁ := pt) (c₁ := pt) (a₂ := pt)
    (b₂ := pt) (c₂ := pt) (a₃ := pt) (b₃ := pt) (c₃ := pt)
    (m₁ := (1 : ℤ)) (n₁ := (1 : ℤ)) (m₂ := (1 : ℤ)) (n₂ := (1 : ℤ))
    (m₃ := (2 : ℤ)) (n₃ := (2 : ℤ))
  have ew := congrArg GCell.wt e
  simp [gW] at ew

end GradedCounterexample

end MonoidalDoubleCategory

end CategoryTheory
