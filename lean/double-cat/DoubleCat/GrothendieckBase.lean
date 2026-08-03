import DoubleCat.Grothendieck
import DoubleCat.Transformation
import DoubleCat.Functor.Composition
import DoubleCat.Functor.Whiskering
import DoubleCat.Opfibration

/-!
# Base change for the double Grothendieck construction

`DoubleCat.GrothendieckMap` develops the fixed-base functoriality of
`∫`: a tight transformation `σ : F ⟹ G` of span-valued lax double
functors **on the same base** induces `gmap σ : ∫ F → ∫ G` over the
identity.  This file develops the base-change level — the object part
of the global 2-functor `∫` on 1-cells `(S, θ)`: given a lax double
functor `S` between the bases and a tight transformation
`θ : F ⟹ S.comp G` (a transformation "over `S`" — the fixed-base
notion already expresses it, taken against the composite), there is a
lax double functor

  `bmap S θ : ∫ F → ∫ G`

sending `⟨a, x⟩` to `⟨S.obj a, θ.app a x⟩`, a decorated loose arrow
`⟨m, d⟩` to `⟨S.mapLoose m, θ.looseApp m ‥ d⟩`, and a cell `⟨α, _⟩` to
`⟨S.mapCell α, _⟩`.  Its laxators have **`S`'s laxators as bases**
(where `gmap`'s had `vId`s), with decoration conditions given by `θ`'s
compatibility axioms read at elements; each of the five coherence laws
of `bmap` reduces through `GCell.heq_ext` to `S`'s corresponding
axiom — the decoration side is propositional throughout.  In
particular no pseudo-ness of `S` is consumed anywhere: `S` may be
genuinely lax.

The projections intertwine (`bmap_proj`): projecting after `bmap S θ`
is `S` after projecting — `bmap S θ` is a functor *over* `S`.  And the
canonical opcartesian lifts of the elements projections
(`DoubleCat.Opfibration`) are preserved on the nose at the loose level
(`bmap_pushGLoose`): at the span-valued stratum every tight
transformation is strictly natural (`looseApp_natural` is a structure
field), so lift preservation carries no strictness hypothesis — the
strictly-natural-iff-lifts-preserved dictionary clause with its
hypothesis absorbed by the ambient structure.

The fixed-base `gmap` is morally the specialization `S = id`; the
comparison is an `eqToHom`-transport statement across
`LaxDoubleFunctor.id_comp` (the composite's laxators carry casts), and
is deliberately not developed here: consumers need `bmap` itself, not
the comparison.

References: Patterson, "Structured and decorated cospans from the
viewpoint of double category theory" (2023); Cruttwell–Lambert–Pronk–
Szyld, "Double fibrations" (2022), the morphism level of the
construction, at the span-valued case with a change of base.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂ u

variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct.{w₁, t₁} C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct.{w₂, t₂} D]
  [PseudoDoubleCategory D]

namespace SpanValued

variable {F : SpanValued.{w₁, t₁, v₁, u₁, u} C}
  {G : SpanValued.{w₂, t₂, v₂, u₂, u} D}

/-- The tight-functor level of `bmap`: the functor on categories of
elements induced by a base change `S` and a transformation `θ` over it. -/
def bmapElements (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G)) :
    Grothendieck F ⥤ Grothendieck G where
  obj t := ⟨S.obj t.1, θ.app t.1 t.2⟩
  map {t₁ t₂} k :=
    ⟨S.map k.1,
      (congrArg (fun m : F.obj t₁.1 ⟶ G.obj (S.obj t₂.1) => m t₁.2)
          (θ.naturality k.1)).symm.trans (congrArg _ k.2)⟩
  map_id t := Subtype.ext (S.map_id t.1)
  map_comp k l := Subtype.ext (S.map_comp k.1 l.1)

variable (S : LaxDoubleFunctor C D) (θ : TightTransformation F (S.comp G)) in
@[reducible] def bmapLoose {p q : Grothendieck F} (M : GLoose p q) :
    GLoose ((bmapElements S θ).obj p) ((bmapElements S θ).obj q) :=
  ⟨S.mapLoose M.base, θ.looseApp M.base p.2 q.2 M.dec⟩

variable (S : LaxDoubleFunctor C D) (θ : TightTransformation F (S.comp G)) in
@[reducible] def bmapCell {p q r s : Grothendieck F} {M : GLoose p q}
    {N : GLoose r s} {φ : p ⟶ r} {ψ : q ⟶ s} (α : GCell M N φ ψ) :
    GCell (bmapLoose S θ M) (bmapLoose S θ N)
      ((bmapElements S θ).map φ) ((bmapElements S θ).map ψ) where
  base := S.mapCell α.base
  dec :=
    (DepSpan.FamCell.heq_apply (θ.naturality φ.1).symm (θ.naturality ψ.1).symm
        (θ.looseApp_natural_heq α.base).symm p.2 q.2 M.dec).trans
      (DepSpan.FamCell.apply_congr_heq (θ.looseApp N.base) φ.2 ψ.2 α.dec)

variable (S : LaxDoubleFunctor C D) (θ : TightTransformation F (S.comp G)) in
@[reducible] def bmapLaxComp {p q r : Grothendieck F} (M : GLoose p q)
    (N : GLoose q r) :
    GCell (GLoose.comp (bmapLoose S θ M) (bmapLoose S θ N))
      (bmapLoose S θ (GLoose.comp M N))
      (𝟙 ((bmapElements S θ).obj p)) (𝟙 ((bmapElements S θ).obj r)) where
  base := S.laxComp M.base N.base
  dec :=
    ((DepSpan.FamCell.heq_apply rfl rfl
        (θ.looseApp_laxComp_heq M.base N.base) p.2 r.2
        ⟨q.2, M.dec, N.dec⟩).trans
      (DepSpan.FamCell.heq_apply (by boundary) (by boundary)
        (Cell.cast_heq _ _
          (G.laxComp (S.mapLoose M.base) (S.mapLoose N.base) ≫ᵥ
            G.mapCell (S.laxComp M.base N.base)))
        (θ.app p.1 p.2) (θ.app r.1 r.2)
        ⟨θ.app q.1 q.2, θ.looseApp M.base p.2 q.2 M.dec,
          θ.looseApp N.base q.2 r.2 N.dec⟩)).symm

variable (S : LaxDoubleFunctor C D) (θ : TightTransformation F (S.comp G)) in
@[reducible] def bmapLaxId (p : Grothendieck F) :
    GCell (GLoose.id ((bmapElements S θ).obj p))
      (bmapLoose S θ (GLoose.id p))
      (𝟙 ((bmapElements S θ).obj p)) (𝟙 ((bmapElements S θ).obj p)) where
  base := S.laxId p.1
  dec :=
    ((DepSpan.FamCell.heq_apply rfl rfl
        (θ.looseApp_laxId_heq p.1) p.2 p.2 ⟨⟨rfl⟩⟩).trans
      (DepSpan.FamCell.heq_apply (by boundary) (by boundary)
        (Cell.cast_heq _ _
          (G.laxId (S.obj p.1) ≫ᵥ G.mapCell (S.laxId p.1)))
        (θ.app p.1 p.2) (θ.app p.1 p.2) ⟨⟨rfl⟩⟩)).symm

/-- `bmapCell` preserves tight-wise identity cells (the `mapCell_vId` law,
proved standalone so its elaboration never sees the under-construction
structure literal). -/
theorem bmapCell_vId (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G)) {p q : Grothendieck F}
    (M : GLoose p q) :
    bmapCell S θ (GCell.vId M) =
      Cell.cast ((bmapElements S θ).map_id p).symm
        ((bmapElements S θ).map_id q).symm (vId (bmapLoose S θ M)) :=
  eq_of_heq ((GCell.heq_ext ((bmapElements S θ).map_id p)
      ((bmapElements S θ).map_id q) (S.mapCell_vId_heq M.base)).trans
    (Cell.cast_heq ((bmapElements S θ).map_id p).symm
      ((bmapElements S θ).map_id q).symm (vId (bmapLoose S θ M))).symm)

/-- `bmapCell` preserves tight-wise composition (the `mapCell_vComp` law,
standalone for the same reason). -/
theorem bmapCell_vComp (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G))
    {p₁ q₁ p₂ q₂ p₃ q₃ : Grothendieck F}
    {M₁ : GLoose p₁ q₁} {M₂ : GLoose p₂ q₂} {M₃ : GLoose p₃ q₃}
    {φ₁ : p₁ ⟶ p₂} {ψ₁ : q₁ ⟶ q₂} {φ₂ : p₂ ⟶ p₃} {ψ₂ : q₂ ⟶ q₃}
    (α : GCell M₁ M₂ φ₁ ψ₁) (β : GCell M₂ M₃ φ₂ ψ₂) :
    bmapCell S θ (GCell.vComp α β) =
      Cell.cast ((bmapElements S θ).map_comp φ₁ φ₂).symm
        ((bmapElements S θ).map_comp ψ₁ ψ₂).symm
        (bmapCell S θ α ≫ᵥ bmapCell S θ β) :=
  eq_of_heq ((GCell.heq_ext ((bmapElements S θ).map_comp φ₁ φ₂)
      ((bmapElements S θ).map_comp ψ₁ ψ₂)
      (S.mapCell_vComp_heq α.base β.base)).trans
    (Cell.cast_heq ((bmapElements S θ).map_comp φ₁ φ₂).symm
      ((bmapElements S θ).map_comp ψ₁ ψ₂).symm
      (bmapCell S θ α ≫ᵥ bmapCell S θ β)).symm)

/-- **Base change for the double Grothendieck construction**: the lax
double functor `∫ F → ∫ G` induced by a base change `S` and a tight
transformation `θ : F ⟹ S.comp G` over it.  Laxator bases are `S`'s
laxators; every coherence law reduces to `S`'s. -/
def bmap (S : LaxDoubleFunctor C D) (θ : TightTransformation F (S.comp G)) :
    LaxDoubleFunctor (Grothendieck F) (Grothendieck G) where
  toFunctor := bmapElements S θ
  mapLoose M := bmapLoose S θ M
  mapCell α := bmapCell S θ α
  mapCell_vId M := bmapCell_vId S θ M
  mapCell_vComp α β := bmapCell_vComp S θ α β
  laxComp M N := bmapLaxComp S θ M N
  laxId p := bmapLaxId S θ p
  laxComp_natural α β :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        (S.laxComp_natural_heq α.base β.base))
  laxId_natural φ :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        (S.laxId_natural_heq φ.1))
  laxComp_assoc M N P :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        (S.laxComp_assoc_heq M.base N.base P.base))
  laxComp_leftUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        (S.laxComp_leftUnitor_heq M.base))
  laxComp_rightUnitor M :=
    Cell.eq_cast_iff_heq.mpr
      (GCell.heq_ext (by boundary) (by boundary)
        (S.laxComp_rightUnitor_heq M.base))

@[simp] theorem bmap_obj (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G)) (p : Grothendieck F) :
    (bmap S θ).obj p = (bmapElements S θ).obj p := rfl

/-- The projections intertwine: `bmap S θ` is a functor over `S`. -/
theorem bmap_proj (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G)) : (bmap S θ).comp (proj G) = (proj F).comp S :=
  LaxDoubleFunctor.ext' rfl (fun _ => HEq.rfl)
    (fun α => by
      show S.mapCell α.base ≍ S.mapCell ((proj F).mapCell α)
      exact HEq.rfl)
    (fun M N =>
      (Cell.cast_heq _ _
          ((proj G).laxComp (bmapLoose S θ M) (bmapLoose S θ N) ≫ᵥ
            (proj G).mapCell (bmapLaxComp S θ M N))).trans <|
        (PseudoDoubleCategory.vId_vComp_heq (S.laxComp M.base N.base)).trans <|
          (PseudoDoubleCategory.vComp_vId_heq (S.laxComp M.base N.base)).symm.trans <|
            (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              (S.mapCell_vId_heq (M.base ⊙ N.base)).symm).trans
              (Cell.cast_heq _ _
                (S.laxComp ((proj F).mapLoose M) ((proj F).mapLoose N) ≫ᵥ
                  S.mapCell ((proj F).laxComp M N))).symm)
    (fun p =>
      (Cell.cast_heq _ _
          ((proj G).laxId ((bmapElements S θ).obj p) ≫ᵥ
            (proj G).mapCell (bmapLaxId S θ p))).trans <|
        (PseudoDoubleCategory.vId_vComp_heq (S.laxId p.1)).trans <|
          (PseudoDoubleCategory.vComp_vId_heq (S.laxId p.1)).symm.trans <|
            (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              (S.mapCell_vId_heq (lId p.1)).symm).trans
              (Cell.cast_heq _ _
                (S.laxId ((proj F).obj p) ≫ᵥ
                  S.mapCell ((proj F).laxId p))).symm)

/-- Heterogeneous extensionality for decorated loose arrows across
propositionally equal endpoints. -/
theorem GLoose.heq_ext' {p p' q q' : Grothendieck G}
    (hp : p = p') (hq : q = q') {M : GLoose p q} {M' : GLoose p' q'}
    (hbase : M.base ≍ M'.base) (hdec : M.dec ≍ M'.dec) : M ≍ M' := by
  subst hp; subst hq
  obtain ⟨b, d⟩ := M
  obtain ⟨b', d'⟩ := M'
  obtain rfl : b = b' := eq_of_heq hbase
  obtain rfl : d = d' := eq_of_heq hdec
  rfl

/-- `bmap` preserves the canonical opcartesian lifts of the elements
projections at the loose level, on the nose: pushing forward then
mapping is mapping then pushing forward.  No strictness hypothesis
appears: at the span-valued stratum, `looseApp_natural` is a structure
field, so every `θ` is strictly natural. -/
theorem bmap_pushGLoose (S : LaxDoubleFunctor C D)
    (θ : TightTransformation F (S.comp G)) {p q : Grothendieck F} (M : GLoose p q)
    {c d : C} {n : Loose c d} {f' : p.1 ⟶ c} {g' : q.1 ⟶ d}
    (γ : Cell M.base n f' g') :
    bmapLoose S θ (pushGLoose M γ) ≍
      pushGLoose (bmapLoose S θ M) (S.mapCell γ) :=
  GLoose.heq_ext'
    (congrArg (fun x => (⟨S.obj c, x⟩ : Grothendieck G))
      (congrArg (fun m : F.obj p.1 ⟶ G.obj (S.obj c) => m p.2)
        (θ.naturality f')))
    (congrArg (fun x => (⟨S.obj d, x⟩ : Grothendieck G))
      (congrArg (fun m : F.obj q.1 ⟶ G.obj (S.obj d) => m q.2)
        (θ.naturality g')))
    HEq.rfl
    (DepSpan.FamCell.heq_apply (θ.naturality f') (θ.naturality g')
      (θ.looseApp_natural_heq γ) p.2 q.2 M.dec)

end SpanValued

end CategoryTheory
