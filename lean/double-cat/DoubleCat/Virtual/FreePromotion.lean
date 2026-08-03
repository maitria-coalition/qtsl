import DoubleCat.Basic
import DoubleCat.Virtual

/-!
# The free promotion of a virtual double category

Freely adding loose composites to a virtual double category yields a
pseudo double category: loose arrows become composable strings, loose
composition becomes concatenation, and a cell from a string `ps` to a
string `qs` is a covering of `qs` by multicells whose domains concatenate
to `ps` (Cruttwell–Shulman, §7, where this is the unit-and-composite
cocompletion; the strings-and-coverings pseudo double category is the
image of the left adjoint to the underlying-virtual-double-category
functor of `DoubleCat.Virtual.OfPseudo`).

This file constructs the promotion in the thin case — cells are the
*existence* of a covering — which is the case every instance in this
development inhabits, and the case in which the promotion is the precise
comparison object between the two presentations of an entailment
structure: as a virtual double category of judgments and multi-premise
entailment cells, or as a pseudo double category of formal conjunctions
(lists) of judgments with pointwise-generated cells.  The two present the
same content exactly when the pseudo presentation's cells from `ps` to
`qs` are the coverings by multicells; that is this construction, so "the
list presentation is the free promotion of the virtual one" becomes a
concrete equivalence to check against `FreePromotion`.

Of the adjunction itself (functors of virtual double categories into an
underlying pseudo double category correspond to structure-preserving
functors out of the promotion), the existence direction — the transpose —
is mechanized for thin targets in `DoubleCat.Virtual.Promote`
(`VirtualDoubleFunctor.promoteThin`); the uniqueness direction and the
triangle identities are not, since nothing downstream consumes them.  The
promotion, the transpose, and both comparison directions at the instance
level are what the applications use.

## Main definitions

* `CategoryTheory.VirtualDoubleCategoryData.CellSeq.split`: a covering of
  a concatenation splits (propositionally) into coverings of the two
  parts.
* `CategoryTheory.VirtualDoubleCategoryData.CellSeq.nonempty_vcomp`:
  coverings compose tight-wise — substitution of a covering into a
  covering, blockwise via `split`.
* `CategoryTheory.FreePromotion`: the carrier, its
  `PseudoDoubleCategoryStruct` (strings, concatenation, coverings), and
  the `PseudoDoubleCategory` axioms (by proof irrelevance: cells are
  `PLift` of a proposition).
-/

namespace CategoryTheory

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

universe w t v u

namespace VirtualDoubleCategoryData

section Split

variable {C : Type u} [Category.{v} C] [VirtualDoubleCategoryData.{w, t, v, u} C]

/-- A covering of a concatenated string splits into coverings of the two
parts, with the split point and its boundary tight arrow exposed
existentially. -/
theorem CellSeq.split :
    ∀ {c m d : C} (qs₁ : LoosePath Loose c m) (qs₂ : LoosePath Loose m d)
      {a b : C} {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d},
      CellSeq (qs₁.comp qs₂) ps u v →
      ∃ (x : C) (ps₁ : LoosePath Loose a x) (ps₂ : LoosePath Loose x b)
        (w : x ⟶ m), ps = ps₁.comp ps₂ ∧
          Nonempty (CellSeq qs₁ ps₁ u w) ∧ Nonempty (CellSeq qs₂ ps₂ w v) := by
  intro c m d qs₁
  induction qs₁ with
  | nil =>
      intro qs₂ a b ps u v V
      exact ⟨a, .nil, ps, u, rfl, ⟨.nil u⟩, ⟨V⟩⟩
  | cons q qs₁' ih =>
      intro qs₂ a b ps u v V
      cases V with
      | cons β V' =>
          obtain ⟨x, rs₁, rs₂, w, hr, ⟨W₁⟩, ⟨W₂⟩⟩ := ih qs₂ V'
          subst hr
          exact ⟨x, _, rs₂, w, (LoosePath.comp_assoc _ _ _).symm,
            ⟨.cons β W₁⟩, ⟨W₂⟩⟩

/-- Coverings substitute into coverings: given a covering of `rs` by
multicells with domains concatenating to `qs`, and a covering of `qs`
with domains concatenating to `ps`, there is a covering of `rs` with
domains concatenating to `ps`.  This is the tight-wise composition of
the free promotion's cells. -/
theorem CellSeq.nonempty_vcomp {C : Type u} [Category.{v} C]
    [VirtualDoubleCategoryStruct.{w, t, v, u} C] :
    ∀ {c d e e' : C} {rs : LoosePath Loose e e'} {qs : LoosePath Loose c d}
      {f : c ⟶ e} {g : d ⟶ e'},
      CellSeq rs qs f g →
      ∀ {a b : C} {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d},
      Nonempty (CellSeq qs ps u v) →
      Nonempty (CellSeq rs ps (u ≫ f) (v ≫ g)) := by
  intro c d e e' rs qs f g B
  induction B with
  | nil f =>
      intro a b ps u v hW
      obtain ⟨W⟩ := hW
      cases W with
      | nil u => exact ⟨.nil (u ≫ f)⟩
  | cons γ B' ih =>
      intro a b ps u v hW
      obtain ⟨W⟩ := hW
      obtain ⟨x, ps₁, ps₂, w', hp, ⟨W₁⟩, hW₂⟩ := CellSeq.split _ _ W
      subst hp
      obtain ⟨T⟩ := ih hW₂
      exact ⟨.cons (ccomp γ W₁) T⟩

end Split

end VirtualDoubleCategoryData

/-- The carrier of the free promotion of a virtual double category
structure on `C`: the same objects, wrapped so that the promoted loose
structure does not collide with any pseudo double category structure `C`
itself may carry. -/
structure FreePromotion (C : Type u) : Type u where
  /-- Wrap an object. -/
  of ::
  /-- Unwrap an object. -/
  un : C

namespace FreePromotion

variable {C : Type u} [Category.{v} C]

instance : Category.{v} (FreePromotion C) where
  Hom a b := a.un ⟶ b.un
  id a := 𝟙 a.un
  comp f g := f ≫ g

section Struct

variable [VirtualDoubleCategoryStruct.{w, t, v, u} C]

/-- The free promotion: loose arrows are strings, loose composition is
concatenation with the empty string as loose identity, and a cell from
`ps` to `qs` is the existence of a covering of `qs` by multicells whose
domains concatenate to `ps`. -/
instance : PseudoDoubleCategoryStruct (FreePromotion C) where
  Loose a b := LoosePath Loose a.un b.un
  Cell ps qs f g := PLift (Nonempty (CellSeq (C := C) qs ps f g))
  vId ps := ⟨⟨idSeq ps⟩⟩
  vComp α β := ⟨β.down.elim fun B => CellSeq.nonempty_vcomp B α.down⟩
  lId _ := .nil
  lComp ps qs := ps.comp qs
  hId f := ⟨⟨CellSeq.nil (C := C) f⟩⟩
  hComp α β := ⟨α.down.elim fun W₁ => β.down.elim fun W₂ => ⟨W₁.append W₂⟩⟩
  lAssoc m n p :=
    ⟨⟨(idSeq (m.comp (n.comp p))).castDom (LoosePath.comp_assoc m n p).symm⟩⟩
  lAssocInv m n p :=
    ⟨⟨(idSeq (m.comp (n.comp p))).castCod (LoosePath.comp_assoc m n p).symm⟩⟩
  lLeftUnitor m := ⟨⟨idSeq m⟩⟩
  lLeftUnitorInv m := ⟨⟨idSeq m⟩⟩
  lRightUnitor m := ⟨⟨(idSeq m).castDom (LoosePath.comp_nil m).symm⟩⟩
  lRightUnitorInv m := ⟨⟨(idSeq m).castCod (LoosePath.comp_nil m).symm⟩⟩

instance {a b c d : FreePromotion C}
    (m : PseudoDoubleCategoryStruct.Loose a b)
    (n : PseudoDoubleCategoryStruct.Loose c d) (f : a ⟶ c) (g : b ⟶ d) :
    Subsingleton (PseudoDoubleCategoryStruct.Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- The free promotion is a pseudo double category: its cells are
proof-irrelevant, so every axiom holds by `Subsingleton.elim`. -/
instance : PseudoDoubleCategory (FreePromotion C) where
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

end Struct

end FreePromotion

end CategoryTheory
