import DoubleCat.Basic
import DoubleCat.Virtual

/-!
# The underlying virtual double category of a pseudo double category

Every pseudo double category has an underlying virtual double category
(Cruttwell–Shulman, Example 2.7 / §3): the loose arrows are unchanged and
a multicell `ps ⇒ q` is a cell out of the loose composite of the string
`ps`.  Identity multicells are right unitors; substitution folds the
covering sequence loose-wise and re-associates with structure cells.

This file constructs the data (`VirtualDoubleCategoryStruct.ofPseudo`).
The axioms are supplied per instance: for thin pseudo double categories —
every instance in this development — they hold by proof irrelevance
(`VirtualDoubleCategory.of_subsingleton`); for the general case they are
the coherence theorem for the fold of structure cells, which nothing here
consumes and which is left to a dedicated development.

## Main definitions

* `CategoryTheory.LoosePath.fold`: the right-associated loose composite of
  a string of loose arrows, with the loose identity as the empty fold.
* `CategoryTheory.LoosePath.foldCompCell`: the globular structure cell
  re-associating the fold of a concatenation into the composite of the
  folds — the canonical comparison built from unitors and associators.
* `CategoryTheory.VirtualDoubleCategoryStruct.ofPseudo`: the underlying
  virtual double category structure.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w t v u

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct C]

namespace LoosePath

/-- The right-associated loose composite of a string of loose arrows; the
empty string folds to the loose identity. -/
def fold : ∀ {a b : C},
    LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a b → Loose a b
  | a, _, .nil => lId a
  | _, _, .cons q ps => q ⊙ ps.fold

@[simp] theorem fold_nil {a : C} :
    (LoosePath.nil :
      LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a a).fold = lId a :=
  rfl

@[simp] theorem fold_cons {a b c : C} (q : Loose a b)
    (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) b c) :
    (LoosePath.cons q ps).fold = q ⊙ ps.fold := rfl

/-- The canonical globular comparison from the fold of a concatenation to
the loose composite of the folds, built from inverse unitors and inverse
associators.  In a thin pseudo double category this is the only such
cell; in general it is the canonical one. -/
def foldCompCell : ∀ {a b c : C}
    (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a b)
    (rs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) b c),
    Cell (ps.comp rs).fold (ps.fold ⊙ rs.fold) (𝟙 a) (𝟙 c)
  | _, _, _, .nil, rs => lLeftUnitorInv rs.fold
  | _, _, _, .cons q ps, rs =>
      Cell.cast (Category.id_comp _) (Category.id_comp _)
        ((vId q ⊚ foldCompCell ps rs) ≫ᵥ lAssocInv q ps.fold rs.fold)

end LoosePath

/-- The loose arrows and multicells underlying a pseudo double category:
a multicell out of a string is a cell out of the string's fold.  A local
instance below (scoped to this file) lets the covering-sequence
machinery elaborate against it directly. -/
@[reducible] def VirtualDoubleCategoryData.ofPseudo :
    VirtualDoubleCategoryData.{w, t, v, u} C where
  Loose := PseudoDoubleCategoryStruct.Loose (C := C)
  Cell ps q f g := PseudoDoubleCategoryStruct.Cell ps.fold q f g

attribute [local instance] VirtualDoubleCategoryData.ofPseudo

/-- Fold a covering sequence of multicells (over the underlying data of a
pseudo double category) into a single cell between the folds, by loose
composition of its entries and the canonical re-association. -/
def VirtualDoubleCategoryData.seqFoldAux : ∀ {a b c d : C}
    {qs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) c d}
    {ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a b}
    {u : a ⟶ c} {v : b ⟶ d},
    VirtualDoubleCategoryData.CellSeq (C := C) qs ps u v →
    PseudoDoubleCategoryStruct.Cell ps.fold qs.fold u v
  | _, _, _, _, _, _, _, _, .nil f => hId f
  | _, _, _, _, _, _, _, _, .cons β V =>
      Cell.cast (Category.id_comp _) (Category.id_comp _)
        (LoosePath.foldCompCell _ _ ≫ᵥ
          (β ⊚ VirtualDoubleCategoryData.seqFoldAux V))

/-- The underlying virtual double category structure of a pseudo double
category: identity multicells are right unitors, and substitution folds
the covering sequence and composes tight-wise. -/
@[reducible] def VirtualDoubleCategoryStruct.ofPseudo :
    VirtualDoubleCategoryStruct.{w, t, v, u} C where
  toVirtualDoubleCategoryData := VirtualDoubleCategoryData.ofPseudo
  cid q := lRightUnitor q
  ccomp α V := VirtualDoubleCategoryData.seqFoldAux V ≫ᵥ α

/-- Multicells of the underlying virtual double category are
proof-irrelevant as soon as the pseudo double category's cells are (the
thin case), so the virtual axioms hold by
`VirtualDoubleCategory.of_subsingleton`. -/
theorem VirtualDoubleCategoryStruct.ofPseudo_lawful
    (h : ∀ {a b c d : C} (m : Loose a b) (n : Loose c d) (f : a ⟶ c)
      (g : b ⟶ d), Subsingleton (PseudoDoubleCategoryStruct.Cell m n f g)) :
    @VirtualDoubleCategory C _ (VirtualDoubleCategoryStruct.ofPseudo) :=
  @VirtualDoubleCategory.of_subsingleton C _
    (VirtualDoubleCategoryStruct.ofPseudo)
    (fun ps q f g => h ps.fold q f g)

end CategoryTheory
