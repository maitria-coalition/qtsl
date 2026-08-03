import DoubleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidal double categories: data and the coherence-axiom mixins

A monoidal double category (Shulman, "Framed bicategories and monoidal
fibrations", 2008, §5; Hansen–Shulman, "Constructing symmetric monoidal
bicategories functorially", 2019) is a pseudo double category `C` whose
tight category is monoidal, together with a tensor product of loose arrows
and of cells over the tight tensor, comparison cells `chi` and `mu` making
the tensor a lax double functor (the interchangers), loose-level
associator, unitor, and (in the braided/symmetric case) braiding cells over
the corresponding tight structure isomorphisms, and coherence axioms.

## Design

* `MonoidalDoubleCategoryStruct` / `BraidedDoubleCategoryStruct` carry the
  *data*; `MonoidalDoubleCategory` / `BraidedDoubleCategory` carry the
  data-level *laws* (functoriality of the tensor on cells, naturality of
  every structure cell, invertibility of the loose structure isomorphisms).
  These laws hold for arbitrary component values in the linearized
  (one-object, group-weighted) models of `DoubleCat.Monoidal.GradedModel`,
  so they are kept separate from the coherence axioms below, which do not.

* The coherence axioms are stated as **named `Prop`-mixins `M1`–`M11`**,
  one class each, so that "which axioms does a construction satisfy" is an
  instance query, and independence results are stated as non-instances.
  The numbering (and the composite forms) follows a hypothesis package for
  the monoidal double Grothendieck construction: M1 pentagon, M2 triangle,
  M3 hexagons + involutivity, M4 interchanger associativity, M5
  interchanger unit squares, M6 braiding–interchanger, M7 unitor–unit,
  M9 associator–interchanger, M10 unitor–interchanger, M11 associator- and
  braiding–unit squares.  **M9, M10, M11 are not consequences of the
  others**: the associator–interchanger square in particular is
  independent of all the rest (see
  `DoubleCat.Monoidal.GradedCounterexample` for the formal non-instance
  witnessing this, and `DoubleCat.Monoidal.Falsifiability` for the full
  refutation table).

* **M8 (endpoint discipline) has no `Prop` content in this encoding**: the
  globularity of `chi` and `mu` and the source/target lifting of the loose
  structure cells are carried by the *types* of the fields (their tight
  sides are identities), so there is no separate axiom to state.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct MonoidalCategory

universe w t v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  [PseudoDoubleCategoryStruct.{w, t} C]

/-- The data of a monoidal double category on a monoidal category `C`: a
tensor of loose arrows over the tight tensor, a tensor of cells, a loose
unit, interchanger cells `chi` and `mu` making the tensor lax functorial,
and loose associator and unitor cells over the tight structure
isomorphisms, with their inverses. -/
class MonoidalDoubleCategoryStruct where

  tLoose : ∀ {a b c d : C}, Loose a b → Loose c d → Loose (a ⊗ c) (b ⊗ d)

  tCell : ∀ {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : C}
    {m₁ : Loose a₁ b₁} {n₁ : Loose c₁ d₁} {m₂ : Loose a₂ b₂}
    {n₂ : Loose c₂ d₂} {f₁ : a₁ ⟶ c₁} {g₁ : b₁ ⟶ d₁} {f₂ : a₂ ⟶ c₂}
    {g₂ : b₂ ⟶ d₂},
    Cell m₁ n₁ f₁ g₁ → Cell m₂ n₂ f₂ g₂ →
      Cell (tLoose m₁ m₂) (tLoose n₁ n₂) (f₁ ⊗ₘ f₂) (g₁ ⊗ₘ g₂)

  chi : ∀ {a b c a' b' c' : C} (m : Loose a b) (n : Loose b c)
    (m' : Loose a' b') (n' : Loose b' c'),
    Cell (lComp (tLoose m m') (tLoose n n')) (tLoose (lComp m n) (lComp m' n'))
      (𝟙 (a ⊗ a')) (𝟙 (c ⊗ c'))

  mu : ∀ (a b : C),
    Cell (lId (a ⊗ b)) (tLoose (lId a) (lId b)) (𝟙 (a ⊗ b)) (𝟙 (a ⊗ b))

  tAssoc : ∀ {a b c d e f : C} (m : Loose a b) (n : Loose c d)
    (p : Loose e f),
    Cell (tLoose (tLoose m n) p) (tLoose m (tLoose n p))
      (α_ a c e).hom (α_ b d f).hom

  tAssocInv : ∀ {a b c d e f : C} (m : Loose a b) (n : Loose c d)
    (p : Loose e f),
    Cell (tLoose m (tLoose n p)) (tLoose (tLoose m n) p)
      (α_ a c e).inv (α_ b d f).inv

  tLeftUnitor : ∀ {a b : C} (m : Loose a b),
    Cell (tLoose (lId (𝟙_ C)) m) m (λ_ a).hom (λ_ b).hom

  tLeftUnitorInv : ∀ {a b : C} (m : Loose a b),
    Cell m (tLoose (lId (𝟙_ C)) m) (λ_ a).inv (λ_ b).inv

  tRightUnitor : ∀ {a b : C} (m : Loose a b),
    Cell (tLoose m (lId (𝟙_ C))) m (ρ_ a).hom (ρ_ b).hom

  tRightUnitorInv : ∀ {a b : C} (m : Loose a b),
    Cell m (tLoose m (lId (𝟙_ C))) (ρ_ a).inv (ρ_ b).inv

namespace MonoidalDoubleCategoryStruct

scoped infixr:70 " ⊠ " => MonoidalDoubleCategoryStruct.tLoose

scoped infixr:70 " ⊠ᶜ " => MonoidalDoubleCategoryStruct.tCell

end MonoidalDoubleCategoryStruct

open MonoidalDoubleCategoryStruct

/-- The braided data: a loose braiding cell over the tight braiding, with its
inverse. -/
class BraidedDoubleCategoryStruct [BraidedCategory C]
    extends MonoidalDoubleCategoryStruct C where

  tBraiding : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    Cell (tLoose m n) (tLoose n m) (β_ a c).hom (β_ b d).hom

  tBraidingInv : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    Cell (tLoose n m) (tLoose m n) (β_ a c).inv (β_ b d).inv

export BraidedDoubleCategoryStruct (tBraiding tBraidingInv)

section Laws

variable [PseudoDoubleCategory C]

/-- The data-level laws of a monoidal double category: functoriality of the
tensor on cells, naturality of every structure cell, and invertibility of
the loose structure isomorphisms.  These hold in every graded model
regardless of component weights (`DoubleCat.Monoidal.GradedModel`), which is
why they are kept separate from the coherence mixins `M1`–`M11`. -/
class MonoidalDoubleCategory [MonoidalDoubleCategoryStruct C] : Prop where
  tCell_vId : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    vId m ⊠ᶜ vId n = (vId (m ⊠ n)).cast (by simp) (by simp)
  tCell_vComp : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {m₁' : Loose a₁' b₁'} {m₂' : Loose a₂' b₂'} {m₃' : Loose a₃' b₃'}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    {f₁' : a₁' ⟶ a₂'} {g₁' : b₁' ⟶ b₂'} {f₂' : a₂' ⟶ a₃'} {g₂' : b₂' ⟶ b₃'}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂)
    (α' : Cell m₁' m₂' f₁' g₁') (β' : Cell m₂' m₃' f₂' g₂'),
    (α ≫ᵥ β) ⊠ᶜ (α' ≫ᵥ β') =
      ((α ⊠ᶜ α') ≫ᵥ (β ⊠ᶜ β')).cast (by simp) (by simp)
  chi_natural : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ a₁' a₂' a₃' b₁' b₂' b₃' : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂}
    {n₂ : Loose b₂ b₃} {m₁' : Loose a₁' a₂'} {m₂' : Loose a₂' a₃'}
    {n₁' : Loose b₁' b₂'} {n₂' : Loose b₂' b₃'}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    {f' : a₁' ⟶ b₁'} {g' : a₂' ⟶ b₂'} {h' : a₃' ⟶ b₃'}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h)
    (α' : Cell m₁' n₁' f' g') (β' : Cell m₂' n₂' g' h'),
    chi m₁ m₂ m₁' m₂' ≫ᵥ ((α ⊚ β) ⊠ᶜ (α' ⊚ β')) =
      (((α ⊠ᶜ α') ⊚ (β ⊠ᶜ β')) ≫ᵥ chi n₁ n₂ n₁' n₂').cast
        (by simp) (by simp)
  mu_natural : ∀ {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b'),
    mu a a' ≫ᵥ (hId f ⊠ᶜ hId f') =
      (hId (f ⊗ₘ f') ≫ᵥ mu b b').cast (by simp) (by simp)
  tAssoc_natural : ∀ {a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : C}
    {m : Loose a₁ b₁} {n : Loose c₁ d₁} {p : Loose e₁ f₁}
    {m' : Loose a₂ b₂} {n' : Loose c₂ d₂} {p' : Loose e₂ f₂}
    {fm : a₁ ⟶ a₂} {gm : b₁ ⟶ b₂} {fn : c₁ ⟶ c₂} {gn : d₁ ⟶ d₂}
    {fp : e₁ ⟶ e₂} {gp : f₁ ⟶ f₂}
    (α : Cell m m' fm gm) (β : Cell n n' fn gn) (γ : Cell p p' fp gp),
    ((α ⊠ᶜ β) ⊠ᶜ γ) ≫ᵥ tAssoc m' n' p' =
      (tAssoc m n p ≫ᵥ (α ⊠ᶜ (β ⊠ᶜ γ))).cast
        (by simp) (by simp)
  tLeftUnitor_natural : ∀ {a b a' b' : C} {m : Loose a b} {m' : Loose a' b'}
    {f : a ⟶ a'} {g : b ⟶ b'} (α : Cell m m' f g),
    (vId (lId (𝟙_ C)) ⊠ᶜ α) ≫ᵥ tLeftUnitor m' =
      (tLeftUnitor m ≫ᵥ α).cast (by simp) (by simp)
  tRightUnitor_natural : ∀ {a b a' b' : C} {m : Loose a b} {m' : Loose a' b'}
    {f : a ⟶ a'} {g : b ⟶ b'} (α : Cell m m' f g),
    (α ⊠ᶜ vId (lId (𝟙_ C))) ≫ᵥ tRightUnitor m' =
      (tRightUnitor m ≫ᵥ α).cast (by simp) (by simp)
  tAssoc_tAssocInv : ∀ {a b c d e f : C} (m : Loose a b) (n : Loose c d)
    (p : Loose e f),
    tAssoc m n p ≫ᵥ tAssocInv m n p =
      (vId (tLoose (tLoose m n) p)).cast (by simp) (by simp)
  tAssocInv_tAssoc : ∀ {a b c d e f : C} (m : Loose a b) (n : Loose c d)
    (p : Loose e f),
    tAssocInv m n p ≫ᵥ tAssoc m n p =
      (vId (tLoose m (tLoose n p))).cast (by simp) (by simp)
  tLeftUnitor_tLeftUnitorInv : ∀ {a b : C} (m : Loose a b),
    tLeftUnitor m ≫ᵥ tLeftUnitorInv m =
      (vId (tLoose (lId (𝟙_ C)) m)).cast (by simp) (by simp)
  tLeftUnitorInv_tLeftUnitor : ∀ {a b : C} (m : Loose a b),
    tLeftUnitorInv m ≫ᵥ tLeftUnitor m = (vId m).cast (by simp) (by simp)
  tRightUnitor_tRightUnitorInv : ∀ {a b : C} (m : Loose a b),
    tRightUnitor m ≫ᵥ tRightUnitorInv m =
      (vId (tLoose m (lId (𝟙_ C)))).cast (by simp) (by simp)
  tRightUnitorInv_tRightUnitor : ∀ {a b : C} (m : Loose a b),
    tRightUnitorInv m ≫ᵥ tRightUnitor m = (vId m).cast (by simp) (by simp)

/-- The data-level laws of the braiding: naturality and invertibility of the
loose braiding cells. -/
class BraidedDoubleCategory [BraidedCategory C]
    [BraidedDoubleCategoryStruct C] : Prop
    extends MonoidalDoubleCategory C where
  tBraiding_natural : ∀ {a b c d a' b' c' d' : C}
    {m : Loose a b} {n : Loose c d} {m' : Loose a' b'} {n' : Loose c' d'}
    {f : a ⟶ a'} {g : b ⟶ b'} {f' : c ⟶ c'} {g' : d ⟶ d'}
    (α : Cell m m' f g) (β : Cell n n' f' g'),
    (α ⊠ᶜ β) ≫ᵥ tBraiding m' n' =
      (tBraiding m n ≫ᵥ (β ⊠ᶜ α)).cast (by simp) (by simp)
  tBraiding_tBraidingInv : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    tBraiding m n ≫ᵥ tBraidingInv m n =
      (vId (tLoose m n)).cast (by simp) (by simp)
  tBraidingInv_tBraiding : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    tBraidingInv m n ≫ᵥ tBraiding m n =
      (vId (tLoose n m)).cast (by simp) (by simp)

end Laws

namespace MonoidalDoubleCategory

section Mixins

variable {C}
variable [MonoidalDoubleCategoryStruct C]

variable (C) in

/-- Coherence mixin M1: the pentagon for the loose associator. -/
class M1Pentagon [PseudoDoubleCategory C] : Prop where
  pentagon : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C} (m : Loose a₁ b₁)
    (n : Loose a₂ b₂) (p : Loose a₃ b₃) (q : Loose a₄ b₄),
    (tAssoc m n p ⊠ᶜ vId q) ≫ᵥ tAssoc m (n ⊠ p) q ≫ᵥ
        (vId m ⊠ᶜ tAssoc n p q) =
      (tAssoc (m ⊠ n) p q ≫ᵥ tAssoc m n (p ⊠ q)).cast
        (by simp [← MonoidalCategory.pentagon])
        (by simp [← MonoidalCategory.pentagon])

variable (C) in

/-- Coherence mixin M2: the triangle for the loose associator and unitors. -/
class M2Triangle [PseudoDoubleCategory C] : Prop where
  triangle : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    tAssoc m (lId (𝟙_ C)) n ≫ᵥ (vId m ⊠ᶜ tLeftUnitor n) =
      (tRightUnitor m ⊠ᶜ vId n).cast
        (by simp [← MonoidalCategory.triangle])
        (by simp [← MonoidalCategory.triangle])

variable (C) in

/-- Coherence mixin M4: associativity of the interchanger `chi`. -/
class M4InterchangerAssoc [PseudoDoubleCategory C] : Prop where
  assoc : ∀ {a b c d a' b' c' d' : C}
    (m : Loose a b) (n : Loose b c) (p : Loose c d)
    (m' : Loose a' b') (n' : Loose b' c') (p' : Loose c' d'),
    (chi m n m' n' ⊚ vId (p ⊠ p')) ≫ᵥ chi (m ⊙ n) p (m' ⊙ n') p' ≫ᵥ
        (lAssoc m n p ⊠ᶜ lAssoc m' n' p') =
      (lAssoc (m ⊠ m') (n ⊠ n') (p ⊠ p') ≫ᵥ
          (vId (m ⊠ m') ⊚ chi n p n' p') ≫ᵥ chi m (n ⊙ p) m' (n' ⊙ p')).cast
        (by simp) (by simp)

variable (C) in

/-- Coherence mixin M5: the unit squares for the interchangers. -/
class M5InterchangerUnit [PseudoDoubleCategory C] : Prop where
  left : ∀ {a b a' b' : C} (m : Loose a b) (m' : Loose a' b'),
    (mu a a' ⊚ vId (m ⊠ m')) ≫ᵥ chi (lId a) m (lId a') m' ≫ᵥ
        (lLeftUnitor m ⊠ᶜ lLeftUnitor m') =
      (lLeftUnitor (m ⊠ m')).cast (by simp) (by simp)
  right : ∀ {a b a' b' : C} (m : Loose a b) (m' : Loose a' b'),
    (vId (m ⊠ m') ⊚ mu b b') ≫ᵥ chi m (lId b) m' (lId b') ≫ᵥ
        (lRightUnitor m ⊠ᶜ lRightUnitor m') =
      (lRightUnitor (m ⊠ m')).cast (by simp) (by simp)

variable (C) in

/-- Coherence mixin M7: compatibility of the loose unitors with `mu`. -/
class M7UnitorUnit [PseudoDoubleCategory C] : Prop where
  left : ∀ a : C,
    mu (𝟙_ C) a ≫ᵥ tLeftUnitor (lId a) =
      (hId (λ_ a).hom).cast (by simp) (by simp)
  right : ∀ a : C,
    mu a (𝟙_ C) ≫ᵥ tRightUnitor (lId a) =
      (hId (ρ_ a).hom).cast (by simp) (by simp)

variable (C) in

/-- Coherence mixin M9: the associator–interchanger square.  Independent of
all the other mixins (`DoubleCat.Monoidal.GradedCounterexample`). -/
class M9AssociatorInterchanger [PseudoDoubleCategory C] : Prop where
  assoc_chi : ∀ {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : C}
    (m₁ : Loose a₁ b₁) (n₁ : Loose b₁ c₁)
    (m₂ : Loose a₂ b₂) (n₂ : Loose b₂ c₂)
    (m₃ : Loose a₃ b₃) (n₃ : Loose b₃ c₃),
    (chi (m₁ ⊠ m₂) (n₁ ⊠ n₂) m₃ n₃ ≫ᵥ
        (chi m₁ n₁ m₂ n₂ ⊠ᶜ vId (m₃ ⊙ n₃))) ≫ᵥ
        tAssoc (m₁ ⊙ n₁) (m₂ ⊙ n₂) (m₃ ⊙ n₃) =
      ((tAssoc m₁ m₂ m₃ ⊚ tAssoc n₁ n₂ n₃) ≫ᵥ
          chi m₁ n₁ (m₂ ⊠ m₃) (n₂ ⊠ n₃) ≫ᵥ
          (vId (m₁ ⊙ n₁) ⊠ᶜ chi m₂ n₂ m₃ n₃)).cast
        (by simp) (by simp)

variable (C) in

/-- Coherence mixin M10: the unitor–interchanger squares. -/
class M10UnitorInterchanger [PseudoDoubleCategory C] : Prop where
  left : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    (chi (lId (𝟙_ C)) (lId (𝟙_ C)) m n ≫ᵥ
        (lLeftUnitor (lId (𝟙_ C)) ⊠ᶜ vId (m ⊙ n))) ≫ᵥ
        tLeftUnitor (m ⊙ n) =
      (tLeftUnitor m ⊚ tLeftUnitor n).cast (by simp) (by simp)
  right : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    (chi m n (lId (𝟙_ C)) (lId (𝟙_ C)) ≫ᵥ
        (vId (m ⊙ n) ⊠ᶜ lLeftUnitor (lId (𝟙_ C)))) ≫ᵥ
        tRightUnitor (m ⊙ n) =
      (tRightUnitor m ⊚ tRightUnitor n).cast (by simp) (by simp)

variable (C) in

/-- Coherence mixin M11a: the associator–unit square. -/
class M11aAssociatorUnit [PseudoDoubleCategory C] : Prop where
  assoc_mu : ∀ a b c : C,
    (mu (a ⊗ b) c ≫ᵥ (mu a b ⊠ᶜ vId (lId c))) ≫ᵥ
        tAssoc (lId a) (lId b) (lId c) =
      (hId (α_ a b c).hom ≫ᵥ mu a (b ⊗ c) ≫ᵥ
          (vId (lId a) ⊠ᶜ mu b c)).cast (by simp) (by simp)

end Mixins

section BraidedMixins

variable {C}
variable [BraidedCategory C] [BraidedDoubleCategoryStruct C]
  [PseudoDoubleCategory C]

variable (C) in

/-- Coherence mixin M6: compatibility of the braiding with the interchanger. -/
class M6BraidingInterchanger : Prop where
  braiding_chi : ∀ {a b c a' b' c' : C} (m : Loose a b) (n : Loose b c)
    (m' : Loose a' b') (n' : Loose b' c'),
    chi m n m' n' ≫ᵥ tBraiding (m ⊙ n) (m' ⊙ n') =
      ((tBraiding m m' ⊚ tBraiding n n') ≫ᵥ chi m' n' m n).cast
        (by simp) (by simp)

variable (C) in

/-- Coherence mixin M11b: the braiding–unit square. -/
class M11bBraidingUnit : Prop where
  braiding_mu : ∀ a b : C,
    mu a b ≫ᵥ tBraiding (lId a) (lId b) =
      (hId (β_ a b).hom ≫ᵥ mu b a).cast (by simp) (by simp)

end BraidedMixins

section SymmetricMixins

variable {C}
variable [SymmetricCategory C] [BraidedDoubleCategoryStruct C]
  [PseudoDoubleCategory C]

variable (C) in

/-- Coherence mixin M3: the two hexagons for the loose braiding, and
involutivity over a symmetric base. -/
class M3Hexagons : Prop where
  hexagon_forward : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : C} (m : Loose a₁ b₁)
    (n : Loose a₂ b₂) (p : Loose a₃ b₃),
    tAssoc m n p ≫ᵥ tBraiding m (n ⊠ p) ≫ᵥ tAssoc n p m =
      ((tBraiding m n ⊠ᶜ vId p) ≫ᵥ tAssoc n m p ≫ᵥ
          (vId n ⊠ᶜ tBraiding m p)).cast
        (by
          simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
          exact (BraidedCategory.hexagon_forward _ _ _).symm)
        (by
          simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
          exact (BraidedCategory.hexagon_forward _ _ _).symm)
  hexagon_reverse : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : C} (m : Loose a₁ b₁)
    (n : Loose a₂ b₂) (p : Loose a₃ b₃),
    tAssocInv m n p ≫ᵥ tBraiding (m ⊠ n) p ≫ᵥ tAssocInv p m n =
      ((vId m ⊠ᶜ tBraiding n p) ≫ᵥ tAssocInv m p n ≫ᵥ
          (tBraiding m p ⊠ᶜ vId n)).cast
        (by
          simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
          exact (BraidedCategory.hexagon_reverse _ _ _).symm)
        (by
          simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
          exact (BraidedCategory.hexagon_reverse _ _ _).symm)
  involutive : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d),
    tBraiding m n ≫ᵥ tBraiding n m = (vId (m ⊠ n)).cast (by simp) (by simp)

end SymmetricMixins

end MonoidalDoubleCategory

end CategoryTheory
