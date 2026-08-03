import DoubleCat.Virtual

/-!
# Functors of virtual double categories

A functor of virtual double categories consists of a functor on the tight
categories, an action on loose arrows, and an action on multicells
preserving frames, identities, and substitution (Cruttwell–Shulman, §3).

There is no lax/pseudo/strong trichotomy here: with no loose composition
in the source or target, there are no comparison cells to direct — a
functor preserves the only operations there are.  Laxity data reappears
exactly when loose composites are freely added to the target (see
`DoubleCat.Virtual.FreePromotion`), which is how the underlying virtual
double category of a pseudo double category mediates between the two
notions.

As in `DoubleCat.Basic`, the preservation laws are stated up to boundary
drift: the tight boundaries of an image multicell agree with the
boundaries of the image only up to `Functor.map_id`/`Functor.map_comp`,
and the loose domain strings agree up to `LoosePath.map_comp`, so the
laws are heterogeneous.  `VirtualDoubleFunctor.ofThin` discharges them
outright when the target's multicells are proof-irrelevant, which is the
case for every instance in this development.
-/

namespace CategoryTheory

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂

section MapSeq

variable {C : Type u₁} [Category.{v₁} C]
  [VirtualDoubleCategoryStruct.{w₁, t₁, v₁, u₁} C]
variable {D : Type u₂} [Category.{v₂} D]
  [VirtualDoubleCategoryStruct.{w₂, t₂, v₂, u₂} D]

/-- The image of a covering sequence under prospective functor data (an
object map, a tight-arrow map, a loose-arrow map, and a multicell map
preserving frames): map each multicell, transporting the domain string
along `LoosePath.map_comp`.  Stated against raw data so that the
substitution-preservation law of `VirtualDoubleFunctor` can refer to it
in its own fields. -/
def mapSeqAux (Fo : C → D) (Fm : ∀ {x y : C}, (x ⟶ y) → (Fo x ⟶ Fo y))
    (Fl : ∀ {x y : C}, Loose x y → Loose (Fo x) (Fo y))
    (Fc : ∀ {a b c d : C} {ps : LoosePath Loose a b} {q : Loose c d}
      {f : a ⟶ c} {g : b ⟶ d}, Cell ps q f g →
      Cell (ps.map Fo fun {_ _} e => Fl e) (Fl q) (Fm f) (Fm g)) :
    ∀ {a b c d : C} {qs : LoosePath Loose c d} {ps : LoosePath Loose a b}
      {u : a ⟶ c} {v : b ⟶ d}, CellSeq qs ps u v →
      CellSeq (qs.map Fo fun {_ _} e => Fl e) (ps.map Fo fun {_ _} e => Fl e)
        (Fm u) (Fm v)
  | _, _, _, _, _, _, _, _, .nil f => .nil (Fm f)
  | _, _, _, _, _, _, _, _, .cons β V =>
      (CellSeq.cons (Fc β) (mapSeqAux Fo Fm Fl Fc V)).castDom
        (LoosePath.map_comp _ _ _ _).symm

end MapSeq

variable (C : Type u₁) [Category.{v₁} C]
  [VirtualDoubleCategoryStruct.{w₁, t₁, v₁, u₁} C]
variable (D : Type u₂) [Category.{v₂} D]
  [VirtualDoubleCategoryStruct.{w₂, t₂, v₂, u₂} D]

/-- A functor of virtual double categories: a functor on tight categories,
an action on loose arrows, and an action on multicells, preserving
identity multicells and substitution (up to the boundary drift absorbed by
`HEq`; see the module docstring). -/
structure VirtualDoubleFunctor extends C ⥤ D where
  /-- The action on loose arrows. -/
  mapLoose : ∀ {a b : C}, Loose a b → Loose (obj a) (obj b)
  /-- The action on multicells.  Frames are preserved: the loose domain
  string maps edgewise, the tight sides map through the functor. -/
  mapCell : ∀ {a b c d : C} {ps : LoosePath Loose a b} {q : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d}, Cell ps q f g →
    Cell (ps.map obj fun {_ _} e => mapLoose e) (mapLoose q) (map f) (map g)
  /-- Identity multicells are preserved. -/
  mapCell_cid : ∀ {a b : C} (q : Loose a b),
    mapCell (cid q) ≍ cid (mapLoose q)
  /-- Substitution is preserved. -/
  mapCell_ccomp : ∀ {a b c d e e' : C} {qs : LoosePath Loose c d}
    {s : Loose e e'} {f : c ⟶ e} {g : d ⟶ e'} {ps : LoosePath Loose a b}
    {u : a ⟶ c} {v : b ⟶ d} (α : Cell qs s f g) (V : CellSeq qs ps u v),
    mapCell (ccomp α V) ≍
      ccomp (mapCell α)
        (mapSeqAux obj (fun {_ _} k => map k) (fun {_ _} e => mapLoose e)
          (fun {_ _ _ _ _ _ _ _} β => mapCell β) V)

namespace VirtualDoubleFunctor

variable {C D}

/-- The image of a covering sequence under a functor of virtual double
categories. -/
def mapSeq (F : VirtualDoubleFunctor C D) {a b c d : C}
    {qs : LoosePath Loose c d} {ps : LoosePath Loose a b} {u : a ⟶ c}
    {v : b ⟶ d} (V : CellSeq qs ps u v) :
    CellSeq (qs.map F.obj fun {_ _} e => F.mapLoose e)
      (ps.map F.obj fun {_ _} e => F.mapLoose e) (F.map u) (F.map v) :=
  mapSeqAux F.obj (fun {_ _} k => F.map k) (fun {_ _} e => F.mapLoose e)
    (fun {_ _ _ _ _ _ _ _} β => F.mapCell β) V

/-- Build a functor of virtual double categories from its data alone when
the target's multicells are proof-irrelevant: the preservation laws hold
by `Subsingleton`.  Every functor constructed in this development is of
this thin kind. -/
def ofThin
    (hD : ∀ {a b c d : D} (ps : LoosePath Loose a b) (q : Loose c d)
      (f : a ⟶ c) (g : b ⟶ d), Subsingleton (Cell ps q f g))
    (F : C ⥤ D)
    (mapLoose : ∀ {a b : C}, Loose a b → Loose (F.obj a) (F.obj b))
    (mapCell : ∀ {a b c d : C} {ps : LoosePath Loose a b} {q : Loose c d}
      {f : a ⟶ c} {g : b ⟶ d}, Cell ps q f g →
      Cell (ps.map F.obj fun {_ _} e => mapLoose e) (mapLoose q)
        (F.map f) (F.map g)) :
    VirtualDoubleFunctor C D where
  toFunctor := F
  mapLoose := mapLoose
  mapCell := mapCell
  mapCell_cid _ := VirtualDoubleCategory.heq_of_subsingleton hD rfl
    (F.map_id _) (F.map_id _) _ _
  mapCell_ccomp _ _ := VirtualDoubleCategory.heq_of_subsingleton hD rfl
    (F.map_comp _ _) (F.map_comp _ _) _ _

end VirtualDoubleFunctor

end CategoryTheory
