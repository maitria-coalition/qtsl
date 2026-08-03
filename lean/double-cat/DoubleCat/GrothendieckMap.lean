import DoubleCat.Grothendieck
import DoubleCat.Dbl
import DoubleCat.Modification

/-!
# Functoriality of the double Grothendieck construction

A tight transformation `σ : F ⟹ G` of span-valued lax double functors
induces a lax double functor `gmap σ : ∫ F → ∫ G` over the identity on
the base: its tight functor is `gmapElements` (mathlib's
`CategoryOfElements.map`, reproved without choice; definitional bridge
`gmapElements_eq_map`), the base of every loose arrow and cell is
unchanged, and the decorations move by `σ`'s cell components read at
elements.  The laxators are `vId`-based cells whose decoration conditions
are `σ`'s compatibility axioms with the laxators of `F` and `G` read at
elements; the five coherence laws reduce through `GCell.heq_ext` to base
chases that are word-for-word those of the strict projection `proj` (both
functors' laxators have `vId` bases, so the base-level content is the
same).

`gmap` is functorial in `σ` (`gmap_id`, `gmap_comp`, by
`LaxDoubleFunctor.ext'` — the underlying data of the two sides agree
definitionally, so only the laxator legs need chases), and the strict
projections are natural with respect to it (`gmap_proj`, the
double-categorical analogue of mathlib's `CategoryOfElements.map_π`).
Packaged: `grothendieckFunctor`, the functor from span-valued lax double
functors on `C` (with tight transformations) to the 1-truncation of the
strict bicategory `Dbl` (the choice-free `Category Dbl` instance defined
in `DoubleCat.Dbl`; mathlib's `StrictBicategory.category` would also be
found but carries `Classical.choice`).

At the 2-cell level there is no further content: the tight-globular
2-cells between tight transformations of span-valued lax double functors
are discrete (`TightTwoCell.discrete`), and `gmapTwoCell` gives the
induced transformation directly nonetheless.

References: Patterson, "Structured and decorated cospans from the
viewpoint of double category theory" (2023), §3; Cruttwell–Lambert–
Pronk–Szyld, "Double fibrations" (2022), §2 (the morphism level of their
construction, restricted to the span-valued case).
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w t v u₁ u

variable {C : Type u₁} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

namespace SpanValued

variable {F G H : SpanValued.{w, t, v, u₁, u} C}

/-- The tight-functor level of `gmap`: the functor `F.Elements ⥤ G.Elements`
induced by the tight components of `σ` (mathlib's
`CategoryOfElements.map`, constructed without choice). -/
def gmapElements (σ : TightTransformation F G) :
    Grothendieck F ⥤ Grothendieck G where
  obj t := ⟨t.1, σ.app t.1 t.2⟩
  map {t₁ t₂} k :=
    ⟨k.1,
      (congrArg (fun m : F.obj t₁.1 ⟶ G.obj t₂.1 => m t₁.2)
          (σ.naturality k.1)).symm.trans (congrArg _ k.2)⟩
  map_id t := rfl
  map_comp k l := rfl

/-- `gmapElements` agrees with mathlib's `CategoryOfElements.map`. -/
theorem gmapElements_eq_map (σ : TightTransformation F G) :
    gmapElements σ = CategoryOfElements.map σ.toNatTrans := rfl

@[reducible] def gmapLoose (σ : TightTransformation F G)
    {p q : Grothendieck F} (M : GLoose p q) :
    GLoose ((gmapElements σ).obj p)
      ((gmapElements σ).obj q) :=
  ⟨M.base, σ.looseApp M.base p.2 q.2 M.dec⟩

@[reducible] def gmapCell (σ : TightTransformation F G)
    {p q r s : Grothendieck F} {M : GLoose p q} {N : GLoose r s}
    {φ : p ⟶ r} {ψ : q ⟶ s} (α : GCell M N φ ψ) :
    GCell (gmapLoose σ M) (gmapLoose σ N)
      ((gmapElements σ).map φ)
      ((gmapElements σ).map ψ) where
  base := α.base
  dec :=
    (DepSpan.FamCell.heq_apply (σ.naturality φ.1).symm (σ.naturality ψ.1).symm
        (σ.looseApp_natural_heq α.base).symm p.2 q.2 M.dec).trans
      (DepSpan.FamCell.apply_congr_heq (σ.looseApp N.base) φ.2 ψ.2 α.dec)

@[reducible] def gmapLaxComp (σ : TightTransformation F G)
    {p q r : Grothendieck F} (M : GLoose p q) (N : GLoose q r) :
    GCell (GLoose.comp (gmapLoose σ M) (gmapLoose σ N))
      (gmapLoose σ (GLoose.comp M N))
      (𝟙 ((gmapElements σ).obj p))
      (𝟙 ((gmapElements σ).obj r)) where
  base := PseudoDoubleCategoryStruct.vId (M.base ⊙ N.base)
  dec :=
    (DepSpan.FamCell.heq_apply (G.map_id p.1) (G.map_id r.1)
        (G.mapCell_vId_heq (M.base ⊙ N.base)) (σ.app p.1 p.2) (σ.app r.1 r.2)
        (GLoose.comp (gmapLoose σ M) (gmapLoose σ N)).dec).trans
      (DepSpan.FamCell.heq_apply (by boundary) (by boundary)
        (σ.looseApp_laxComp_heq M.base N.base).symm p.2 r.2
        ⟨q.2, M.dec, N.dec⟩)

@[reducible] def gmapLaxId (σ : TightTransformation F G)
    (p : Grothendieck F) :
    GCell (GLoose.id ((gmapElements σ).obj p))
      (gmapLoose σ (GLoose.id p))
      (𝟙 ((gmapElements σ).obj p))
      (𝟙 ((gmapElements σ).obj p)) where
  base := PseudoDoubleCategoryStruct.vId (𝟙ˡ p.1)
  dec :=
    (DepSpan.FamCell.heq_apply (G.map_id p.1) (G.map_id p.1)
        (G.mapCell_vId_heq (𝟙ˡ p.1)) (σ.app p.1 p.2) (σ.app p.1 p.2)
        (GLoose.id ((gmapElements σ).obj p)).dec).trans
      (DepSpan.FamCell.heq_apply (by boundary) (by boundary)
        (σ.looseApp_laxId_heq p.1).symm p.2 p.2 ⟨⟨rfl⟩⟩)

/-- The lax double functor `∫ F → ∫ G` induced by a tight transformation of
span-valued lax double functors: bases are unchanged, decorations move by
`σ`'s cell components read at elements. -/
def gmap (σ : TightTransformation F G) :
    LaxDoubleFunctor (Grothendieck F) (Grothendieck G) where
  toFunctor := gmapElements σ
  mapLoose M := gmapLoose σ M
  mapCell α := gmapCell σ α
  mapCell_vId M := rfl
  mapCell_vComp α β := rfl
  laxComp M N := gmapLaxComp σ M N
  laxId p := gmapLaxId σ p
  laxComp_natural α β :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _).symm))
  laxId_natural φ :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        ((PseudoDoubleCategory.vId_vComp_heq _).trans
          (PseudoDoubleCategory.vComp_vId_heq _).symm))
  laxComp_assoc M N P :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        ((((vComp_congr_heq rfl rfl (by boundary) (by boundary)
              (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
              (PseudoDoubleCategory.vId_vComp_heq _)).trans
            (PseudoDoubleCategory.vId_vComp_heq _)).trans
          ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              ((PseudoDoubleCategory.vComp_vId_heq _).trans
                (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _)))).trans
            (PseudoDoubleCategory.vComp_vId_heq _)).symm)))
  laxComp_leftUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        ((vComp_congr_heq rfl rfl (by boundary) (by boundary)
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
            (PseudoDoubleCategory.vId_vComp_heq _)).trans
          (PseudoDoubleCategory.vId_vComp_heq _)))
  laxComp_rightUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        ((vComp_congr_heq rfl rfl (by boundary) (by boundary)
            (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
            (PseudoDoubleCategory.vId_vComp_heq _)).trans
          (PseudoDoubleCategory.vId_vComp_heq _)))

/-- `gmap` preserves identities. -/
theorem gmap_id (F : SpanValued.{w, t, v, u₁, u} C) :
    gmap (TightTransformation.id F) = LaxDoubleFunctor.id :=
  LaxDoubleFunctor.ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun _ _ => HEq.rfl) (fun _ => HEq.rfl)

/-- `gmap` preserves vertical composition. -/
theorem gmap_comp (σ : TightTransformation F G) (τ : TightTransformation G H) :
    gmap (σ.vcomp τ) = (gmap σ).comp (gmap τ) :=
  LaxDoubleFunctor.ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)

    (fun m n =>
      ((Cell.cast_heq _ _ _).trans
        (GCell.heq_ext (by boundary) (by boundary)
          (PseudoDoubleCategory.vId_vComp_heq _))).symm)
    (fun p =>
      ((Cell.cast_heq _ _ _).trans
        (GCell.heq_ext (by boundary) (by boundary)
          (PseudoDoubleCategory.vId_vComp_heq _))).symm)

/-- The strict projections are natural with respect to `gmap`: projecting
after `gmap σ` is projecting. -/
theorem gmap_proj (σ : TightTransformation F G) :
    (gmap σ).comp (proj G) = proj F :=
  LaxDoubleFunctor.ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun m n =>
      (Cell.cast_heq _ _ _).trans
        (PseudoDoubleCategory.vId_vComp_heq
          ((proj G).mapCell ((gmap σ).laxComp m n))))
    (fun p =>

      (Cell.cast_heq _ _ _).trans
        (PseudoDoubleCategory.vId_vComp_heq
          ((proj G).mapCell ((gmap σ).laxId p))))

/-- A tight-globular 2-cell between tight transformations of span-valued lax
double functors: a family of cells at loose identities, compatible with the
cell components.  These turn out to be discrete (`TightTwoCell.discrete`). -/
structure TightTwoCell (σ τ : TightTransformation F G) where

  app : ∀ a : C, Cell (𝟙ˡ (F.obj a)) (𝟙ˡ (G.obj a)) (σ.app a) (τ.app a)

  compat : ∀ {a b : C} (m : Loose a b),
    (σ.looseApp m ⊚ app b) ≫ᵥ
        (lRightUnitor (G.mapLoose m) ≫ᵥ lLeftUnitorInv (G.mapLoose m)) ≍
      (lRightUnitor (F.mapLoose m) ≫ᵥ lLeftUnitorInv (F.mapLoose m)) ≫ᵥ
        (app a ⊚ τ.looseApp m)

variable {σ τ : TightTransformation F G}

namespace TightTwoCell

theorem app_eq (d : TightTwoCell σ τ) (a : C) : σ.app a = τ.app a := by
  ext x
  exact PLift.down (ULift.down (d.app a x x
    (⟨⟨rfl⟩⟩ : DepSpan.Fam.id (F.obj a) x x)))

theorem looseApp_heq (d : TightTwoCell σ τ) {a b : C} (m : Loose a b) :
    σ.looseApp m ≍ τ.looseApp m := by
  refine DepSpan.FamCell.heq_of_apply (d.app_eq a) (d.app_eq b)
    (fun x y s => ?_)
  have h := DepSpan.FamCell.heq_apply (by simp) (by simp) (d.compat m)
    x y ⟨y, s, ⟨⟨rfl⟩⟩⟩
  have h₂ := eq_of_heq h
  have h₃ := DepSpan.comp_snd_heq h₂
  exact (DepSpan.lRightUnitor_apply_heq (G.mapLoose m)
    (σ.looseApp m x y s)
    (d.app b y y (⟨⟨rfl⟩⟩ : DepSpan.Fam.id (F.obj b) y y))).symm.trans h₃

/-- Tight-globular 2-cells are discrete: any such 2-cell forces its boundary
transformations to be equal. -/
theorem discrete (d : TightTwoCell σ τ) : σ = τ :=
  TightTransformation.ext d.app_eq fun m => d.looseApp_heq m

/-- The reflexivity 2-cell. -/
def refl (σ : TightTransformation F G) : TightTwoCell σ σ where
  app a := hId (σ.app a)
  compat {a b} m := by
    refine DepSpan.FamCell.heq_of_apply (by simp) (by simp)
      (fun x y s => ?_)
    obtain ⟨y₀, v, w⟩ := s
    obtain ⟨⟨e⟩⟩ := w
    subst e
    rfl

end TightTwoCell

/-- The transformation of `gmap`s induced by a tight-globular 2-cell (its
content is determined by discreteness, but the construction is direct). -/
def gmapTwoCell (d : TightTwoCell σ τ) :
    TightTransformation (gmap σ) (gmap τ) where
  app p :=
    ⟨𝟙 p.1,
      (congrArg (fun k : G.obj p.1 ⟶ G.obj p.1 => k (σ.app p.1 p.2))
          (G.map_id p.1)).trans
        (congrArg (fun k : F.obj p.1 ⟶ G.obj p.1 => k p.2)
          (d.app_eq p.1))⟩
  naturality _ _ k :=
    Subtype.ext ((Category.comp_id k.1).trans (Category.id_comp k.1).symm)
  looseApp {p q} M :=
    { base := PseudoDoubleCategoryStruct.vId M.base
      dec :=
        (DepSpan.FamCell.heq_apply (G.map_id p.1) (G.map_id q.1)
            (G.mapCell_vId_heq M.base) (σ.app p.1 p.2) (σ.app q.1 q.2)
            (σ.looseApp M.base p.2 q.2 M.dec)).trans
          (DepSpan.FamCell.heq_apply (d.app_eq p.1) (d.app_eq q.1)
            (d.looseApp_heq M.base) p.2 q.2 M.dec) }
  looseApp_natural {a b c d'} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact GCell.heq_ext
      (Subtype.ext ((Category.comp_id f.1).trans (Category.id_comp f.1).symm))
      (Subtype.ext ((Category.comp_id g.1).trans (Category.id_comp g.1).symm))
      ((PseudoDoubleCategory.vComp_vId_heq _).trans
        (PseudoDoubleCategory.vId_vComp_heq _).symm)
  looseApp_laxComp M N := by
    rw [Cell.eq_cast_iff_heq]
    exact GCell.heq_ext (Subtype.ext rfl) (Subtype.ext rfl)
      ((PseudoDoubleCategory.vId_vComp_heq _).trans
        ((heq_of_eq (PseudoDoubleCategory.hComp_vId M.base N.base)).symm.trans
          (PseudoDoubleCategory.vComp_vId_heq _).symm))
  looseApp_laxId p := by
    rw [Cell.eq_cast_iff_heq]
    exact GCell.heq_ext (Subtype.ext rfl) (Subtype.ext rfl)
      ((PseudoDoubleCategory.vId_vComp_heq _).trans
        ((heq_of_eq (PseudoDoubleCategory.hId_id p.1)).symm.trans
          (PseudoDoubleCategory.vComp_vId_heq _).symm))

theorem gmapTwoCell_refl (σ : TightTransformation F G) :
    gmapTwoCell (TightTwoCell.refl σ) = 𝟙 (gmap σ) :=
  TightTransformation.ext (fun _ => Subtype.ext rfl)
    (fun M => GCell.heq_ext (Subtype.ext rfl) (Subtype.ext rfl) HEq.rfl)

def _root_.CategoryTheory.Modification.toTightTwoCell
    {σ τ : TightTransformation F G}
    (μ : Modification (LooseTransformation.id F)
      (LooseTransformation.id G) σ τ) :
    TightTwoCell σ τ where
  app := μ.app
  compat {a b} m := μ.natCell_compat_heq m

theorem discrete_of_modification {σ τ : TightTransformation F G}
    (μ : Modification (LooseTransformation.id F)
      (LooseTransformation.id G) σ τ) :
    σ = τ :=
  μ.toTightTwoCell.discrete

variable (C)

/-- The double Grothendieck construction as a functor: from span-valued lax
double functors on `C` with tight transformations to the 1-truncation of the
strict bicategory `Dbl`. -/
def grothendieckFunctor :
    SpanValued.{w, t, v, u₁, u} C ⥤ Dbl.{max w u, t, v, max u₁ u} where
  obj F := Dbl.of (Grothendieck F)
  map σ := gmap σ
  map_id F := gmap_id F
  map_comp σ τ := gmap_comp σ τ

end SpanValued

end CategoryTheory
