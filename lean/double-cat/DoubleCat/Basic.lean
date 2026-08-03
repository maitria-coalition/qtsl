import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom

/-!
# Pseudo double categories

This file defines pseudo double categories (also called weak double
categories), following Grandis–Paré ("Limits in double categories", 1999;
"Adjoint for double categories", 2004), Shulman ("Framed bicategories and
monoidal fibrations", 2008), and the presentation used in
Cruttwell–Lambert–Pronk–Szyld ("Double fibrations", 2022) and Patterson
("Structured and decorated cospans from the viewpoint of double category
theory", 2023).

## Main definitions

* `CategoryTheory.PseudoDoubleCategoryStruct`: the data of a pseudo double
  category on a category `C`: loose arrows `Loose a b` (composing weakly,
  written `m ⊙ n`), cells (squares) `Cell m n f g` with loose source `m`,
  loose target `n`, and tight sides `f`, `g` (composing strictly in the
  tight direction, written `α ≫ᵥ β`, and along the loose direction, written
  `α ⊚ β`), together with loose identities, loose composition, and the
  structure cells (associator and unitors).
* `CategoryTheory.PseudoDoubleCategoryStruct.Cell.cast`: transport of a cell
  along equalities of its tight boundaries.  Tight arrows compose strictly
  but only propositionally so (`Category.assoc` is a proposition, not a
  definitional equality), so iterated tight-wise composites of cells inhabit
  types that agree only up to propositional equality of the tight
  boundaries; `Cell.cast` is the canonical transport, and the axioms of a
  pseudo double category are stated with it.
* `CategoryTheory.PseudoDoubleCategory`: the axioms: the tight-wise category
  laws for cells, functoriality of the loose identity and of loose
  composition (interchange), naturality of the structure cells,
  invertibility of the structure cells, and the pentagon and triangle
  coherence laws.

## Conventions

We use the tight/loose terminology (Shulman).  The tight arrows of the
double category are the morphisms of the underlying category `C` and compose
strictly; the loose arrows are the extra directed structure and compose up
to coherent isomorphism.  A cell

```
        m
    a ----↛ b
    |       |
  f |   α   | g
    v       v
    c ----↛ d
        n
```

is written `α : Cell m n f g`; `f` is its tight source side and `g` its
tight target side.  In the classical examples the loose arrows are spans,
cospans, profunctors, or bimodules, none of which compose strictly — which
is why the loose direction is weak and the theory is not a special case of a
strict 2-dimensional structure.

Cells compose tight-wise (`≫ᵥ`, "vertically" if one draws loose arrows
horizontally as above) and loose-wise (`⊚`, "horizontally").  Both
directions of identity exist: `vId m` is the tight-wise identity cell on a
loose arrow `m`, and `hId f` is the loose-identity cell on a tight arrow
`f`.  The globular cells (those with identity tight sides) between fixed
endpoints form a category; the associator and unitors are invertible
globular cells.

## Design notes

The definition keeps the strict (tight) direction dependent and the weak
(loose) direction total: cells are indexed by their tight sides, so
tight-wise composition accumulates propositional equalities of tight
boundaries (handled by `Cell.cast`), while loose-wise composition needs no
transport at all — the associator is a cell, not an equality.  In particular
the interchange law and the functoriality of loose identities are stated
without any transport.

An alternative encoding of double categories as internal categories in `Cat`
makes the loose direction a category object; it captures only strict double
categories and is not adequate for span-like examples.
-/

namespace CategoryTheory

universe w t v u

set_option linter.checkUnivs false in

/-- The data of a pseudo double category on a category `C`.

The morphisms of `C` are the *tight* arrows.  `Loose a b` is the type of loose
arrows from `a` to `b`, and `Cell m n f g` is the type of cells with loose
source `m`, loose target `n`, tight source side `f` and tight target side `g`.

This structure carries all data (including the associator and unitor cells and
their inverses) but no axioms; the axioms are in
`CategoryTheory.PseudoDoubleCategory`.

The universes `w` (loose arrows) and `t` (cells) are genuinely independent:
e.g. the double category of commutative squares has `w := v` and `t := 0`. -/
class PseudoDoubleCategoryStruct (C : Type u) [Category.{v} C] where

  /-- Loose arrows from `a` to `b`. -/
  Loose : C → C → Type w

  /-- Cells (squares): `Cell m n f g` has loose source `m : Loose a b`, loose
  target `n : Loose c d`, tight source side `f : a ⟶ c` and tight target side
  `g : b ⟶ d`. -/
  Cell : ∀ {a b c d : C}, Loose a b → Loose c d → (a ⟶ c) → (b ⟶ d) → Type t

  /-- The tight-wise identity cell on a loose arrow. -/
  vId : ∀ {a b : C} (m : Loose a b), Cell m m (𝟙 a) (𝟙 b)

  /-- Tight-wise composition of cells. -/
  vComp : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃},
    Cell m₁ m₂ f₁ g₁ → Cell m₂ m₃ f₂ g₂ → Cell m₁ m₃ (f₁ ≫ f₂) (g₁ ≫ g₂)

  /-- The loose identity arrow on an object. -/
  lId : ∀ (a : C), Loose a a

  /-- Loose composition of loose arrows, in diagrammatic order. -/
  lComp : ∀ {a b c : C}, Loose a b → Loose b c → Loose a c

  /-- The loose-identity cell on a tight arrow. -/
  hId : ∀ {a b : C} (f : a ⟶ b), Cell (lId a) (lId b) f f

  /-- Loose-wise composition of cells, in diagrammatic order. -/
  hComp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃},
    Cell m₁ n₁ f g → Cell m₂ n₂ g h → Cell (lComp m₁ m₂) (lComp n₁ n₂) f h

  /-- The associator cell for loose composition. -/
  lAssoc : ∀ {a b c d : C} (m : Loose a b) (n : Loose b c) (p : Loose c d),
    Cell (lComp (lComp m n) p) (lComp m (lComp n p)) (𝟙 a) (𝟙 d)

  /-- The inverse associator cell. -/
  lAssocInv : ∀ {a b c d : C} (m : Loose a b) (n : Loose b c) (p : Loose c d),
    Cell (lComp m (lComp n p)) (lComp (lComp m n) p) (𝟙 a) (𝟙 d)

  /-- The left unitor cell for loose composition. -/
  lLeftUnitor : ∀ {a b : C} (m : Loose a b), Cell (lComp (lId a) m) m (𝟙 a) (𝟙 b)

  /-- The inverse left unitor cell. -/
  lLeftUnitorInv : ∀ {a b : C} (m : Loose a b), Cell m (lComp (lId a) m) (𝟙 a) (𝟙 b)

  /-- The right unitor cell for loose composition. -/
  lRightUnitor : ∀ {a b : C} (m : Loose a b), Cell (lComp m (lId b)) m (𝟙 a) (𝟙 b)

  /-- The inverse right unitor cell. -/
  lRightUnitorInv : ∀ {a b : C} (m : Loose a b), Cell m (lComp m (lId b)) (𝟙 a) (𝟙 b)

namespace PseudoDoubleCategoryStruct

/-- Loose composition, in diagrammatic order. -/
scoped infixr:80 " ⊙ " => PseudoDoubleCategoryStruct.lComp

/-- Tight-wise composition of cells, in diagrammatic order. -/
scoped infixr:80 " ≫ᵥ " => PseudoDoubleCategoryStruct.vComp

/-- Loose-wise composition of cells, in diagrammatic order. -/
scoped infixr:80 " ⊚ " => PseudoDoubleCategoryStruct.hComp

/-- The loose identity arrow on an object. -/
scoped prefix:max "𝟙ˡ " => PseudoDoubleCategoryStruct.lId

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct C]

/-- Transport a cell along equalities of its tight boundaries.

Tight arrows compose strictly but only propositionally so; `Cell.cast` is the
canonical transport of a cell along equalities of its two tight sides.  All
axioms of `CategoryTheory.PseudoDoubleCategory` whose two sides have
propositionally-but-not-syntactically equal tight boundaries are stated up to
this transport. -/
def Cell.cast {a b c d : C} {m : Loose a b} {n : Loose c d} {f f' : a ⟶ c}
    {g g' : b ⟶ d} (hf : f = f') (hg : g = g') (α : Cell m n f g) :
    Cell m n f' g' :=
  hf ▸ hg ▸ α

@[simp]
theorem Cell.cast_rfl {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) :
    α.cast rfl rfl = α :=
  rfl

/-- Casting along self-equalities is the identity (the equality proofs are
irrelevant, so this is definitional). -/
@[simp]
theorem Cell.cast_id {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (hf : f = f) (hg : g = g) (α : Cell m n f g) :
    α.cast hf hg = α :=
  rfl

theorem Cell.cast_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hf : f = f') (hg : g = g')
    (α : Cell m n f g) : (α.cast hf hg) ≍ α := by
  subst hf; subst hg; rfl

@[simp]
theorem Cell.cast_cast {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' f'' : a ⟶ c} {g g' g'' : b ⟶ d}
    (hf : f = f') (hg : g = g') (hf' : f' = f'') (hg' : g' = g'')
    (α : Cell m n f g) :
    (α.cast hf hg).cast hf' hg' = α.cast (hf.trans hf') (hg.trans hg') := by
  subst hf; subst hg; subst hf'; subst hg'; rfl

/-- Two casts of the same cell agree as soon as their target boundaries agree;
the particular equality proofs are irrelevant. -/
theorem Cell.cast_irrel {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hf hf' : f = f') (hg hg' : g = g')
    (α : Cell m n f g) : α.cast hf hg = α.cast hf' hg' :=
  rfl

theorem Cell.cast_eq_iff_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} {hf : f = f'} {hg : g = g'}
    {α : Cell m n f g} {β : Cell m n f' g'} :
    α.cast hf hg = β ↔ α ≍ β := by
  subst hf; subst hg
  exact ⟨fun h => h ▸ HEq.rfl, fun h => eq_of_heq h⟩

theorem Cell.eq_cast_iff_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} {hf : f = f'} {hg : g = g'}
    {α : Cell m n f' g'} {β : Cell m n f g} :
    α = β.cast hf hg ↔ α ≍ β := by
  subst hf; subst hg
  exact ⟨fun h => h ▸ HEq.rfl, fun h => eq_of_heq h⟩

/-!
### The heterogeneous-equality calculus for cells

Equations between iterated composites of cells hold only up to `Cell.cast`
along equalities of tight boundaries.  Chasing such equations directly
requires threading the casts through every congruence step.  It is often
lighter to work with heterogeneous equality: `Cell.cast_heq` strips a cast,
the congruence lemmas below rebuild composites, and
`Cell.cast_eq_iff_heq`/`Cell.eq_cast_iff_heq` convert back to the cast-level
statement at the end.  Since the equality proofs in `Cell.cast` are
irrelevant, an `HEq` between cells with the same loose boundaries carries
exactly the same information as a cast equation, with none of the plumbing.
-/

/-- Congruence of tight-wise composition along heterogeneous equality of the
factors (with equal loose boundaries and propositionally equal tight
boundaries). -/
theorem vComp_congr_heq {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ f₁' : a₁ ⟶ a₂} {g₁ g₁' : b₁ ⟶ b₂} {f₂ f₂' : a₂ ⟶ a₃} {g₂ g₂' : b₂ ⟶ b₃}
    {α : Cell m₁ m₂ f₁ g₁} {α' : Cell m₁ m₂ f₁' g₁'}
    {β : Cell m₂ m₃ f₂ g₂} {β' : Cell m₂ m₃ f₂' g₂'}
    (hf₁ : f₁ = f₁') (hg₁ : g₁ = g₁') (hf₂ : f₂ = f₂') (hg₂ : g₂ = g₂')
    (hα : α ≍ α') (hβ : β ≍ β') : α ≫ᵥ β ≍ α' ≫ᵥ β' := by
  subst hf₁; subst hg₁; subst hf₂; subst hg₂
  rw [eq_of_heq hα, eq_of_heq hβ]

/-- Congruence of loose-wise composition along heterogeneous equality of the
factors (with equal loose boundaries and propositionally equal tight
boundaries). -/
theorem hComp_congr_heq {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f f' : a₁ ⟶ b₁} {g g' : a₂ ⟶ b₂} {h h' : a₃ ⟶ b₃}
    {α : Cell m₁ n₁ f g} {α' : Cell m₁ n₁ f' g'}
    {β : Cell m₂ n₂ g h} {β' : Cell m₂ n₂ g' h'}
    (hf : f = f') (hg : g = g') (hh : h = h')
    (hα : α ≍ α') (hβ : β ≍ β') : α ⊚ β ≍ α' ⊚ β' := by
  subst hf; subst hg; subst hh
  rw [eq_of_heq hα, eq_of_heq hβ]

/-- Congruence of the loose-identity cell along equality of tight arrows. -/
theorem hId_congr_heq {a b : C} {f f' : a ⟶ b} (h : f = f') :
    hId f ≍ hId f' := by
  subst h; rfl

/-- Push a cast out of the left factor of a tight-wise composite. -/
@[simp]
theorem cast_vComp {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ f₁' : a₁ ⟶ a₂} {g₁ g₁' : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (hf : f₁ = f₁') (hg : g₁ = g₁')
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) :
    (α.cast hf hg) ≫ᵥ β = (α ≫ᵥ β).cast (by rw [hf]) (by rw [hg]) := by
  subst hf; subst hg; rfl

/-- Push a cast out of the right factor of a tight-wise composite. -/
@[simp]
theorem vComp_cast {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ f₂' : a₂ ⟶ a₃} {g₂ g₂' : b₂ ⟶ b₃}
    (hf : f₂ = f₂') (hg : g₂ = g₂')
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) :
    α ≫ᵥ (β.cast hf hg) = (α ≫ᵥ β).cast (by rw [hf]) (by rw [hg]) := by
  subst hf; subst hg; rfl

/-- Push casts out of both factors of a loose-wise composite.  The middle tight
boundary must be recast coherently on both sides. -/
theorem cast_hComp_cast {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f f' : a₁ ⟶ b₁} {g g' : a₂ ⟶ b₂} {h h' : a₃ ⟶ b₃}
    (hf : f = f') (hg : g = g') (hh : h = h')
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h) :
    (α.cast hf hg) ⊚ (β.cast hg hh) = (α ⊚ β).cast hf hh := by
  subst hf; subst hg; subst hh; rfl

end PseudoDoubleCategoryStruct

open PseudoDoubleCategoryStruct

/-- A pseudo double category: a category of objects and tight arrows, loose
arrows composing up to coherent isomorphism, and cells.

The axioms are: cells form a category under tight-wise composition (up to
`Cell.cast` along the category laws of the tight boundaries); the loose
identity is functorial in tight arrows; loose-wise composition is functorial
with respect to tight-wise composition (the interchange law); the associator
and unitors are tight-wise natural, invertible, and satisfy the pentagon and
triangle laws.

Statements involving no `Cell.cast` (the interchange law, functoriality of
`hId`) hold on the nose. -/
class PseudoDoubleCategory (C : Type u) [Category.{v} C]
    [PseudoDoubleCategoryStruct C] : Prop where

  /-- Tight-wise composition of cells is unital on the left. -/
  vId_vComp : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d} {f : a ⟶ c}
    {g : b ⟶ d} (α : Cell m n f g),
    vId m ≫ᵥ α = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp f).symm (Category.id_comp g).symm α

  /-- Tight-wise composition of cells is unital on the right. -/
  vComp_vId : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d} {f : a ⟶ c}
    {g : b ⟶ d} (α : Cell m n f g),
    α ≫ᵥ vId n = PseudoDoubleCategoryStruct.Cell.cast (Category.comp_id f).symm (Category.comp_id g).symm α

  /-- Tight-wise composition of cells is associative. -/
  vComp_assoc : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃} {m₄ : Loose a₄ b₄}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    {f₃ : a₃ ⟶ a₄} {g₃ : b₃ ⟶ b₄}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) (γ : Cell m₃ m₄ f₃ g₃),
    (α ≫ᵥ β) ≫ᵥ γ =
      PseudoDoubleCategoryStruct.Cell.cast (Category.assoc f₁ f₂ f₃).symm (Category.assoc g₁ g₂ g₃).symm
        (α ≫ᵥ (β ≫ᵥ γ))

  /-- The loose-identity cell on a tight identity is a tight-wise identity. -/
  hId_id : ∀ (a : C), hId (𝟙 a) = vId (lId a)

  /-- Loose-identity cells compose tight-wise. -/
  hId_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c),
    hId (f ≫ g) = hId f ≫ᵥ hId g

  /-- Loose-wise composition preserves tight-wise identities. -/
  hComp_vId : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    vId m ⊚ vId n = vId (m ⊙ n)

  /-- The interchange law: loose-wise composition preserves tight-wise
  composition. -/
  interchange : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃}
    {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {p₁ : Loose c₁ c₂} {p₂ : Loose c₂ c₃}
    {f₁ : a₁ ⟶ b₁} {g₁ : a₂ ⟶ b₂} {h₁ : a₃ ⟶ b₃}
    {f₂ : b₁ ⟶ c₁} {g₂ : b₂ ⟶ c₂} {h₂ : b₃ ⟶ c₃}
    (α₁ : Cell m₁ n₁ f₁ g₁) (α₂ : Cell m₂ n₂ g₁ h₁)
    (β₁ : Cell n₁ p₁ f₂ g₂) (β₂ : Cell n₂ p₂ g₂ h₂),
    (α₁ ≫ᵥ β₁) ⊚ (α₂ ≫ᵥ β₂) = (α₁ ⊚ α₂) ≫ᵥ (β₁ ⊚ β₂)

  /-- Tight-wise naturality of the associator. -/
  lAssoc_natural : ∀ {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : C}
    {m₁ : Loose a₁ b₁} {n₁ : Loose b₁ c₁} {p₁ : Loose c₁ d₁}
    {m₂ : Loose a₂ b₂} {n₂ : Loose b₂ c₂} {p₂ : Loose c₂ d₂}
    {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} {h : c₁ ⟶ c₂} {i : d₁ ⟶ d₂}
    (α : Cell m₁ m₂ f g) (β : Cell n₁ n₂ g h) (γ : Cell p₁ p₂ h i),
    ((α ⊚ β) ⊚ γ) ≫ᵥ lAssoc m₂ n₂ p₂ =
      PseudoDoubleCategoryStruct.Cell.cast (by simp) (by simp) (lAssoc m₁ n₁ p₁ ≫ᵥ (α ⊚ (β ⊚ γ)))

  /-- Tight-wise naturality of the left unitor. -/
  lLeftUnitor_natural : ∀ {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g),
    (hId f ⊚ α) ≫ᵥ lLeftUnitor m₂ =
      PseudoDoubleCategoryStruct.Cell.cast (by simp) (by simp) (lLeftUnitor m₁ ≫ᵥ α)

  /-- Tight-wise naturality of the right unitor. -/
  lRightUnitor_natural : ∀ {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g),
    (α ⊚ hId g) ≫ᵥ lRightUnitor m₂ =
      PseudoDoubleCategoryStruct.Cell.cast (by simp) (by simp) (lRightUnitor m₁ ≫ᵥ α)

  /-- The associator and its inverse compose to the identity. -/
  lAssoc_lAssocInv : ∀ {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d),
    lAssoc m n p ≫ᵥ lAssocInv m n p = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 d)).symm
      (vId (lComp (lComp m n) p))

  /-- The inverse associator and the associator compose to the identity. -/
  lAssocInv_lAssoc : ∀ {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d),
    lAssocInv m n p ≫ᵥ lAssoc m n p = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 d)).symm
      (vId (lComp m (lComp n p)))

  /-- The left unitor and its inverse compose to the identity. -/
  lLeftUnitor_lLeftUnitorInv : ∀ {a b : C} (m : Loose a b),
    lLeftUnitor m ≫ᵥ lLeftUnitorInv m = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 b)).symm
      (vId (lComp (lId a) m))

  /-- The inverse left unitor and the left unitor compose to the identity. -/
  lLeftUnitorInv_lLeftUnitor : ∀ {a b : C} (m : Loose a b),
    lLeftUnitorInv m ≫ᵥ lLeftUnitor m = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 b)).symm (vId m)

  /-- The right unitor and its inverse compose to the identity. -/
  lRightUnitor_lRightUnitorInv : ∀ {a b : C} (m : Loose a b),
    lRightUnitor m ≫ᵥ lRightUnitorInv m = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 b)).symm
      (vId (lComp m (lId b)))

  /-- The inverse right unitor and the right unitor compose to the identity. -/
  lRightUnitorInv_lRightUnitor : ∀ {a b : C} (m : Loose a b),
    lRightUnitorInv m ≫ᵥ lRightUnitor m = PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 b)).symm (vId m)

  /-- The pentagon law for the associator. -/
  pentagon : ∀ {a b c d e : C} (m : Loose a b) (n : Loose b c) (p : Loose c d)
    (q : Loose d e),
    (lAssoc m n p ⊚ vId q) ≫ᵥ lAssoc m (n ⊙ p) q ≫ᵥ (vId m ⊚ lAssoc n p q) =
      PseudoDoubleCategoryStruct.Cell.cast (by simp) (by simp) (lAssoc (m ⊙ n) p q ≫ᵥ lAssoc m n (p ⊙ q))

  /-- The triangle law for the associator and unitors. -/
  triangle : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    lAssoc m (lId b) n ≫ᵥ (vId m ⊚ lLeftUnitor n) =
      PseudoDoubleCategoryStruct.Cell.cast (Category.id_comp (𝟙 a)).symm (Category.id_comp (𝟙 c)).symm
        (lRightUnitor m ⊚ vId n)

namespace PseudoDoubleCategory

attribute [simp] vId_vComp vComp_vId hId_id hId_comp hComp_vId
  lAssoc_lAssocInv lAssocInv_lAssoc
  lLeftUnitor_lLeftUnitorInv lLeftUnitorInv_lLeftUnitor
  lRightUnitor_lRightUnitorInv lRightUnitorInv_lRightUnitor

section Heq

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]

/-!
### The tight-wise category laws, in heterogeneous form

The cast-free `HEq` versions of the tight-wise category laws, for use with
the congruence lemmas of the heterogeneous-equality calculus
(`PseudoDoubleCategoryStruct.vComp_congr_heq` and friends).
-/

theorem vId_vComp_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) : vId m ≫ᵥ α ≍ α := by
  rw [vId_vComp]; exact Cell.cast_heq _ _ _

theorem vComp_vId_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) : α ≫ᵥ vId n ≍ α := by
  rw [vComp_vId]; exact Cell.cast_heq _ _ _

theorem vComp_assoc_heq {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃} {m₄ : Loose a₄ b₄}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    {f₃ : a₃ ⟶ a₄} {g₃ : b₃ ⟶ b₄}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) (γ : Cell m₃ m₄ f₃ g₃) :
    (α ≫ᵥ β) ≫ᵥ γ ≍ α ≫ᵥ (β ≫ᵥ γ) := by
  rw [vComp_assoc]; exact Cell.cast_heq _ _ _

theorem lAssoc_natural_heq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : C}
    {m₁ : Loose a₁ b₁} {n₁ : Loose b₁ c₁} {p₁ : Loose c₁ d₁}
    {m₂ : Loose a₂ b₂} {n₂ : Loose b₂ c₂} {p₂ : Loose c₂ d₂}
    {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} {h : c₁ ⟶ c₂} {i : d₁ ⟶ d₂}
    (α : Cell m₁ m₂ f g) (β : Cell n₁ n₂ g h) (γ : Cell p₁ p₂ h i) :
    ((α ⊚ β) ⊚ γ) ≫ᵥ lAssoc m₂ n₂ p₂ ≍ lAssoc m₁ n₁ p₁ ≫ᵥ (α ⊚ (β ⊚ γ)) := by
  rw [lAssoc_natural]; exact Cell.cast_heq _ _ _

theorem lLeftUnitor_natural_heq {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g) :
    (hId f ⊚ α) ≫ᵥ lLeftUnitor m₂ ≍ lLeftUnitor m₁ ≫ᵥ α := by
  rw [lLeftUnitor_natural]; exact Cell.cast_heq _ _ _

theorem lRightUnitor_natural_heq {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g) :
    (α ⊚ hId g) ≫ᵥ lRightUnitor m₂ ≍ lRightUnitor m₁ ≫ᵥ α := by
  rw [lRightUnitor_natural]; exact Cell.cast_heq _ _ _

theorem lAssoc_lAssocInv_heq {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) :
    lAssoc m n p ≫ᵥ lAssocInv m n p ≍ vId (lComp (lComp m n) p) := by
  rw [lAssoc_lAssocInv]; exact Cell.cast_heq _ _ _

theorem lAssocInv_lAssoc_heq {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) :
    lAssocInv m n p ≫ᵥ lAssoc m n p ≍ vId (lComp m (lComp n p)) := by
  rw [lAssocInv_lAssoc]; exact Cell.cast_heq _ _ _

theorem lLeftUnitor_lLeftUnitorInv_heq {a b : C} (m : Loose a b) :
    lLeftUnitor m ≫ᵥ lLeftUnitorInv m ≍ vId (lComp (lId a) m) := by
  rw [lLeftUnitor_lLeftUnitorInv]; exact Cell.cast_heq _ _ _

theorem lLeftUnitorInv_lLeftUnitor_heq {a b : C} (m : Loose a b) :
    lLeftUnitorInv m ≫ᵥ lLeftUnitor m ≍ vId m := by
  rw [lLeftUnitorInv_lLeftUnitor]; exact Cell.cast_heq _ _ _

theorem lRightUnitor_lRightUnitorInv_heq {a b : C} (m : Loose a b) :
    lRightUnitor m ≫ᵥ lRightUnitorInv m ≍ vId (lComp m (lId b)) := by
  rw [lRightUnitor_lRightUnitorInv]; exact Cell.cast_heq _ _ _

theorem lRightUnitorInv_lRightUnitor_heq {a b : C} (m : Loose a b) :
    lRightUnitorInv m ≫ᵥ lRightUnitor m ≍ vId m := by
  rw [lRightUnitorInv_lRightUnitor]; exact Cell.cast_heq _ _ _

/-- Naturality of the inverse left unitor, in heterogeneous form
(derived from the forward naturality by conjugation). -/
theorem lLeftUnitorInv_natural_heq {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g) :
    α ≫ᵥ lLeftUnitorInv m₂ ≍ lLeftUnitorInv m₁ ≫ᵥ (hId f ⊚ α) := by
  exact (vId_vComp_heq _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (lLeftUnitorInv_lLeftUnitor_heq m₁).symm HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lLeftUnitor_natural_heq α).symm HEq.rfl)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lLeftUnitor_lLeftUnitorInv_heq m₂))).trans
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_vId_heq _))

/-- Naturality of the inverse associator, in heterogeneous form
(derived from the forward naturality by conjugation, exactly as
`lLeftUnitorInv_natural_heq`). -/
theorem lAssocInv_natural_heq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : C}
    {m₁ : Loose a₁ b₁} {n₁ : Loose b₁ c₁} {p₁ : Loose c₁ d₁}
    {m₂ : Loose a₂ b₂} {n₂ : Loose b₂ c₂} {p₂ : Loose c₂ d₂}
    {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} {h : c₁ ⟶ c₂} {i : d₁ ⟶ d₂}
    (α : Cell m₁ m₂ f g) (β : Cell n₁ n₂ g h) (γ : Cell p₁ p₂ h i) :
    (α ⊚ (β ⊚ γ)) ≫ᵥ lAssocInv m₂ n₂ p₂ ≍
      lAssocInv m₁ n₁ p₁ ≫ᵥ ((α ⊚ β) ⊚ γ) := by
  exact (vId_vComp_heq _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (lAssocInv_lAssoc_heq m₁ n₁ p₁).symm HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq α β γ).symm HEq.rfl)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lAssoc_lAssocInv_heq m₂ n₂ p₂))).trans
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_vId_heq _))

/-- Naturality of the inverse right unitor, in heterogeneous form
(derived from the forward naturality by conjugation; the mirror image of
`lLeftUnitorInv_natural_heq`). -/
theorem lRightUnitorInv_natural_heq {a₁ b₁ a₂ b₂ : C} {m₁ : Loose a₁ b₁}
    {m₂ : Loose a₂ b₂} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} (α : Cell m₁ m₂ f g) :
    α ≫ᵥ lRightUnitorInv m₂ ≍ lRightUnitorInv m₁ ≫ᵥ (α ⊚ hId g) := by
  exact (vId_vComp_heq _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (lRightUnitorInv_lRightUnitor_heq m₁).symm HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lRightUnitor_natural_heq α).symm HEq.rfl)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lRightUnitor_lRightUnitorInv_heq m₂))).trans
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_vId_heq _))

theorem pentagon_heq {a b c d e : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) (q : Loose d e) :
    (lAssoc m n p ⊚ vId q) ≫ᵥ lAssoc m (n ⊙ p) q ≫ᵥ (vId m ⊚ lAssoc n p q) ≍
      lAssoc (m ⊙ n) p q ≫ᵥ lAssoc m n (p ⊙ q) := by
  rw [pentagon]; exact Cell.cast_heq _ _ _

theorem triangle_heq {a b c : C} (m : Loose a b) (n : Loose b c) :
    lAssoc m (lId b) n ≫ᵥ (vId m ⊚ lLeftUnitor n) ≍
      lRightUnitor m ⊚ vId n := by
  rw [triangle]; exact Cell.cast_heq _ _ _

end Heq

end PseudoDoubleCategory

end CategoryTheory
