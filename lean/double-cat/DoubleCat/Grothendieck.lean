import DoubleCat.DepSpan
import DoubleCat.Functor.Lax
import DoubleCat.Functor.Pseudo
import Mathlib.CategoryTheory.Elements

/-!
# The double category of elements of a span-valued lax double functor

A span-valued lax double functor on a pseudo double category `C` is a lax
double functor into the matrix double category on `Type u`
(`DoubleCat.DepSpan`): the value on a loose arrow `m : a ↛ b` is a
two-sided family `F₁ m : F₀ a → F₀ b → Type u`, i.e. a span presented
dependently, so a decoration over chosen endpoints is an element of an
*indexed* type and source/target-strictness is definitional.

This file introduces `SpanValued`, the double category of elements `∫ F`
(objects and tight arrows via mathlib's category of elements; loose arrows
and cells as decorated base data), the element-level constructions (loose
identity and composition, tight identity and composition of cells, the
loose-identity cell, loose-wise composition, and the structure cells), the
`PseudoDoubleCategoryStruct`/`PseudoDoubleCategory` instances on `∫ F`,
and the strict projection `∫ F → C`.  In every *data* field the decoration
is a direct application or a constructor; every equation between elements
lives in a `Prop` field, discharged through the transport lemmas of
`DoubleCat.DepSpan` (`FamCell.heq_apply`, `FamCell.apply_congr_heq`,
`comp_heq`).

Each structure cell's decoration condition is one coherence axiom of the
lax functor read at elements (`laxComp_assoc`/`laxComp_leftUnitor`/
`laxComp_rightUnitor`); the *inverse* structure cells need no further
functor axioms — their conditions transfer along tight-wise invertibility
of the base cell (`GCell.dec_inv`).  The axioms of
`PseudoDoubleCategory (∫ F)` reduce componentwise to the base's through
one heterogeneous extensionality lemma (`GCell.heq_ext`), since the
decoration condition is a proposition.

References: Patterson, "Structured and decorated cospans from the
viewpoint of double category theory" (2023), the double Grothendieck
construction; Grandis–Paré, "Limits in double categories" (1999), §3
(spans); Cruttwell–Lambert–Pronk–Szyld, "Double fibrations" (2022) for
the general fibrational picture.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w t v u₁ u

variable {C : Type u₁} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

/-- A span-valued lax double functor: a lax double functor from `C` to the
dependent-span double category on `Type u`.  Its value on a loose arrow is a
two-sided family, i.e. a span presented by its fibres. -/
abbrev SpanValued (C : Type u₁) [Category.{v} C]
    [PseudoDoubleCategoryStruct.{w, t} C] [PseudoDoubleCategory C] :=
  LaxDoubleFunctor C (Type u)

namespace SpanValued

variable (F : SpanValued.{w, t, v, u₁, u} C)

/-- The double category of elements of a span-valued lax double functor:
objects and tight arrows are mathlib's category of elements of the underlying
functor; loose arrows and cells are added below. -/
def Grothendieck := F.toFunctor.Elements

instance : Category (Grothendieck F) :=
  inferInstanceAs (Category F.toFunctor.Elements)

variable {F}

/-- A loose arrow of the double category of elements: a loose arrow of the
base together with a decoration — an element of the family `F` assigns to it,
indexed at the endpoints' points. -/
structure GLoose (p q : Grothendieck F) where

  base : Loose p.1 q.1

  dec : F.mapLoose base p.2 q.2

/-- A cell of the double category of elements: a cell of the base whose action
on decorations (via `F`'s cell action, read at elements) carries the source
decoration to the target decoration. -/
structure GCell {p q r s : Grothendieck F} (M : GLoose p q) (N : GLoose r s)
    (φ : p ⟶ r) (ψ : q ⟶ s) where

  base : Cell M.base N.base φ.1 ψ.1

  dec : F.mapCell base p.2 q.2 M.dec ≍ N.dec

namespace GLoose

@[reducible] def id (p : Grothendieck F) : GLoose p p :=
  ⟨𝟙ˡ p.1, F.laxId p.1 p.2 p.2 ⟨⟨rfl⟩⟩⟩

@[reducible] def comp {p q r : Grothendieck F} (M : GLoose p q) (N : GLoose q r) :
    GLoose p r :=
  ⟨M.base ⊙ N.base, F.laxComp M.base N.base p.2 r.2 ⟨q.2, M.dec, N.dec⟩⟩

end GLoose

namespace GCell

/-- Cells of `∫ F` are determined by their base cells. -/
theorem ext {p q r s : Grothendieck F} {M : GLoose p q} {N : GLoose r s}
    {φ : p ⟶ r} {ψ : q ⟶ s} {α β : GCell M N φ ψ}
    (h : α.base = β.base) : α = β := by
  cases α; cases β; cases h; rfl

@[reducible] def vId {p q : Grothendieck F} (M : GLoose p q) : GCell M M (𝟙 p) (𝟙 q) where
  base := PseudoDoubleCategoryStruct.vId M.base
  dec :=
    DepSpan.FamCell.heq_apply (F.map_id p.1) (F.map_id q.1)
      (F.mapCell_vId_heq M.base) p.2 q.2 M.dec

@[reducible] def vComp {p₁ q₁ p₂ q₂ p₃ q₃ : Grothendieck F}
    {M₁ : GLoose p₁ q₁} {M₂ : GLoose p₂ q₂} {M₃ : GLoose p₃ q₃}
    {φ₁ : p₁ ⟶ p₂} {ψ₁ : q₁ ⟶ q₂} {φ₂ : p₂ ⟶ p₃} {ψ₂ : q₂ ⟶ q₃}
    (α : GCell M₁ M₂ φ₁ ψ₁) (β : GCell M₂ M₃ φ₂ ψ₂) :
    GCell M₁ M₃ (φ₁ ≫ φ₂) (ψ₁ ≫ ψ₂) where
  base := α.base ≫ᵥ β.base
  dec :=
    (DepSpan.FamCell.heq_apply (F.map_comp φ₁.1 φ₂.1) (F.map_comp ψ₁.1 ψ₂.1)
        (F.mapCell_vComp_heq α.base β.base) p₁.2 q₁.2 M₁.dec).trans
      ((DepSpan.FamCell.apply_congr_heq (F.mapCell β.base) φ₁.2 ψ₁.2
          α.dec).trans
        β.dec)

@[reducible] def hId {p r : Grothendieck F} (φ : p ⟶ r) :
    GCell (GLoose.id p) (GLoose.id r) φ φ where
  base := PseudoDoubleCategoryStruct.hId φ.1
  dec :=
    (DepSpan.FamCell.heq_apply rfl rfl (F.laxId_natural_heq φ.1)
        p.2 p.2 ⟨⟨rfl⟩⟩).trans
      (DepSpan.FamCell.apply_congr_heq (F.laxId r.1) φ.2 φ.2
        (DepSpan.diag_heq φ.2))

@[reducible] def hComp {p q r p' q' r' : Grothendieck F}
    {M₁ : GLoose p q} {M₂ : GLoose q r} {N₁ : GLoose p' q'} {N₂ : GLoose q' r'}
    {φ : p ⟶ p'} {γ : q ⟶ q'} {ψ : r ⟶ r'}
    (α : GCell M₁ N₁ φ γ) (β : GCell M₂ N₂ γ ψ) :
    GCell (M₁.comp M₂) (N₁.comp N₂) φ ψ where
  base := α.base ⊚ β.base
  dec :=
    (DepSpan.FamCell.heq_apply (by simp) (by simp)
        (F.laxComp_natural_heq α.base β.base) p.2 r.2
        ⟨q.2, M₁.dec, M₂.dec⟩).trans
      (DepSpan.FamCell.apply_congr_heq (F.laxComp N₁.base N₂.base) φ.2 ψ.2
        (DepSpan.comp_heq φ.2 ψ.2 γ.2 α.dec β.dec))

/-- Decoration conditions transfer along tight-wise invertibility of the base
cell: the inverse structure cells of `∫ F` need no further functor axioms. -/
theorem dec_inv {p q : Grothendieck F} {M N : GLoose p q}
    {χ : Cell M.base N.base (𝟙 p.1) (𝟙 q.1)}
    {χ' : Cell N.base M.base (𝟙 p.1) (𝟙 q.1)}
    (hdec : F.mapCell χ p.2 q.2 M.dec ≍ N.dec)
    (hinv : χ ≫ᵥ χ' ≍ PseudoDoubleCategoryStruct.vId M.base) :
    F.mapCell χ' p.2 q.2 N.dec ≍ M.dec :=
  (DepSpan.FamCell.apply_congr_heq (F.mapCell χ')
      (by simp) (by simp) hdec.symm).trans
    (DepSpan.FamCell.heq_apply (by simp) (by simp)
      ((F.mapCell_vComp_heq χ χ').symm.trans
        ((F.mapCell_congr_heq (by simp) (by simp) hinv).trans
          (F.mapCell_vId_heq M.base)))
      p.2 q.2 M.dec)

@[reducible] def lAssoc {p q r s : Grothendieck F} (M : GLoose p q) (N : GLoose q r)
    (P : GLoose r s) :
    GCell ((M.comp N).comp P) (M.comp (N.comp P)) (𝟙 p) (𝟙 s) where
  base := PseudoDoubleCategoryStruct.lAssoc M.base N.base P.base
  dec :=
    DepSpan.FamCell.heq_apply (by simp) (by simp)
      (F.laxComp_assoc_heq M.base N.base P.base) p.2 s.2
      ⟨r.2, ⟨q.2, M.dec, N.dec⟩, P.dec⟩

@[reducible] def lAssocInv {p q r s : Grothendieck F} (M : GLoose p q) (N : GLoose q r)
    (P : GLoose r s) :
    GCell (M.comp (N.comp P)) ((M.comp N).comp P) (𝟙 p) (𝟙 s) where
  base := PseudoDoubleCategoryStruct.lAssocInv M.base N.base P.base
  dec :=
    dec_inv (lAssoc M N P).dec
      (PseudoDoubleCategory.lAssoc_lAssocInv_heq M.base N.base P.base)

@[reducible] def lLeftUnitor {p q : Grothendieck F} (M : GLoose p q) :
    GCell ((GLoose.id p).comp M) M (𝟙 p) (𝟙 q) where
  base := PseudoDoubleCategoryStruct.lLeftUnitor M.base
  dec :=
    DepSpan.FamCell.heq_apply (by simp) (by simp)
      (F.laxComp_leftUnitor_heq M.base) p.2 q.2 ⟨p.2, ⟨⟨rfl⟩⟩, M.dec⟩

@[reducible] def lLeftUnitorInv {p q : Grothendieck F} (M : GLoose p q) :
    GCell M ((GLoose.id p).comp M) (𝟙 p) (𝟙 q) where
  base := PseudoDoubleCategoryStruct.lLeftUnitorInv M.base
  dec :=
    dec_inv (lLeftUnitor M).dec
      (PseudoDoubleCategory.lLeftUnitor_lLeftUnitorInv_heq M.base)

@[reducible] def lRightUnitor {p q : Grothendieck F} (M : GLoose p q) :
    GCell (M.comp (GLoose.id q)) M (𝟙 p) (𝟙 q) where
  base := PseudoDoubleCategoryStruct.lRightUnitor M.base
  dec :=
    DepSpan.FamCell.heq_apply (by simp) (by simp)
      (F.laxComp_rightUnitor_heq M.base) p.2 q.2 ⟨q.2, M.dec, ⟨⟨rfl⟩⟩⟩

@[reducible] def lRightUnitorInv {p q : Grothendieck F} (M : GLoose p q) :
    GCell M (M.comp (GLoose.id q)) (𝟙 p) (𝟙 q) where
  base := PseudoDoubleCategoryStruct.lRightUnitorInv M.base
  dec :=
    dec_inv (lRightUnitor M).dec
      (PseudoDoubleCategory.lRightUnitor_lRightUnitorInv_heq M.base)

/-- Heterogeneous extensionality: cells of `∫ F` with heterogeneously equal
base cells (and equal boundaries) are heterogeneously equal — the decoration
condition is a proposition.  All axioms of `PseudoDoubleCategory (∫ F)`
reduce through this lemma to the base's. -/
theorem heq_ext {p q r s : Grothendieck F} {M : GLoose p q} {N : GLoose r s}
    {φ φ' : p ⟶ r} {ψ ψ' : q ⟶ s} {α : GCell M N φ ψ} {β : GCell M N φ' ψ'}
    (hφ : φ = φ') (hψ : ψ = ψ') (h : α.base ≍ β.base) : α ≍ β := by
  subst hφ; subst hψ
  exact heq_of_eq (ext (eq_of_heq h))

end GCell

/-- The double category structure on `∫ F`: every data field decorates the
corresponding base construction. -/
instance instPseudoDoubleCategoryStruct :
    PseudoDoubleCategoryStruct (Grothendieck F) where
  Loose p q := GLoose p q
  Cell M N φ ψ := GCell M N φ ψ
  vId M := GCell.vId M
  vComp α β := GCell.vComp α β
  lId p := GLoose.id p
  lComp M N := GLoose.comp M N
  hId φ := GCell.hId φ
  hComp α β := GCell.hComp α β
  lAssoc M N P := GCell.lAssoc M N P
  lAssocInv M N P := GCell.lAssocInv M N P
  lLeftUnitor M := GCell.lLeftUnitor M
  lLeftUnitorInv M := GCell.lLeftUnitorInv M
  lRightUnitor M := GCell.lRightUnitor M
  lRightUnitorInv M := GCell.lRightUnitorInv M

@[simp]
theorem lId_def (p : Grothendieck F) : 𝟙ˡ p = GLoose.id p := rfl

@[simp]
theorem lComp_def {p q r : Grothendieck F} (M : Loose p q) (N : Loose q r) :
    M ⊙ N = GLoose.comp M N := rfl

/-- The axioms of `∫ F`, componentwise from the base through `GCell.heq_ext`. -/
instance instPseudoDoubleCategory : PseudoDoubleCategory (Grothendieck F) where
  vId_vComp α := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.vId_vComp_heq α.base))
  vComp_vId α := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.vComp_vId_heq α.base))
  vComp_assoc α β γ := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.vComp_assoc_heq α.base β.base γ.base))
  hId_id p := GCell.ext (PseudoDoubleCategory.hId_id p.1)
  hId_comp φ ψ := GCell.ext (PseudoDoubleCategory.hId_comp φ.1 ψ.1)
  hComp_vId M N := GCell.ext (PseudoDoubleCategory.hComp_vId M.base N.base)
  interchange α₁ α₂ β₁ β₂ := GCell.ext
    (PseudoDoubleCategory.interchange α₁.base α₂.base β₁.base β₂.base)
  lAssoc_natural α β γ := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lAssoc_natural_heq α.base β.base γ.base))
  lLeftUnitor_natural α := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lLeftUnitor_natural_heq α.base))
  lRightUnitor_natural α := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lRightUnitor_natural_heq α.base))
  lAssoc_lAssocInv M N P := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lAssoc_lAssocInv_heq M.base N.base P.base))
  lAssocInv_lAssoc M N P := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lAssocInv_lAssoc_heq M.base N.base P.base))
  lLeftUnitor_lLeftUnitorInv M := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lLeftUnitor_lLeftUnitorInv_heq M.base))
  lLeftUnitorInv_lLeftUnitor M := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lLeftUnitorInv_lLeftUnitor_heq M.base))
  lRightUnitor_lRightUnitorInv M := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lRightUnitor_lRightUnitorInv_heq M.base))
  lRightUnitorInv_lRightUnitor M := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.lRightUnitorInv_lRightUnitor_heq M.base))
  pentagon M N P Q := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.pentagon_heq M.base N.base P.base Q.base))
  triangle M N := Cell.eq_cast_iff_heq.mpr
    (GCell.heq_ext (by simp) (by simp)
      (PseudoDoubleCategory.triangle_heq M.base N.base))

variable (F)

/-- The strict projection `∫ F → C`: forget decorations.  Its laxators are
(casts of) identity cells. -/
def proj : LaxDoubleFunctor (Grothendieck F) C where
  toFunctor := CategoryOfElements.π F.toFunctor
  mapLoose M := M.base
  mapCell α := α.base
  mapCell_vId M := rfl
  mapCell_vComp α β := rfl
  laxComp M N := PseudoDoubleCategoryStruct.vId (M.base ⊙ N.base)
  laxId p := PseudoDoubleCategoryStruct.vId (𝟙ˡ p.1)

  laxComp_natural α β :=
    Cell.eq_cast_iff_heq.mpr
      ((PseudoDoubleCategory.vId_vComp_heq _).trans
        (PseudoDoubleCategory.vComp_vId_heq _).symm)
  laxId_natural φ :=
    Cell.eq_cast_iff_heq.mpr
      ((PseudoDoubleCategory.vId_vComp_heq _).trans
        (PseudoDoubleCategory.vComp_vId_heq _).symm)
  laxComp_assoc M N P :=
    Cell.eq_cast_iff_heq.mpr
      (((vComp_congr_heq rfl rfl (by simp) (by simp)
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
            (PseudoDoubleCategory.vId_vComp_heq _)).trans
          (PseudoDoubleCategory.vId_vComp_heq _)).trans
        ((vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
            ((PseudoDoubleCategory.vComp_vId_heq _).trans
              (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)))).trans
          (PseudoDoubleCategory.vComp_vId_heq _)).symm)
  laxComp_leftUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      ((vComp_congr_heq rfl rfl (by simp) (by simp)
          (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
          (PseudoDoubleCategory.vId_vComp_heq _)).trans
        (PseudoDoubleCategory.vId_vComp_heq _))
  laxComp_rightUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      ((vComp_congr_heq rfl rfl (by simp) (by simp)
          (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
          (PseudoDoubleCategory.vId_vComp_heq _)).trans
        (PseudoDoubleCategory.vId_vComp_heq _))

/-- The strict projection is pseudo. -/
theorem proj_isPseudo : (proj F).IsPseudo where
  laxComp_isInvertible M N :=
    PseudoDoubleCategoryStruct.Cell.isInvertible_vId (M.base ⊙ N.base)
  laxId_isInvertible p :=
    PseudoDoubleCategoryStruct.Cell.isInvertible_vId (𝟙ˡ p.1)

end SpanValued

end CategoryTheory
