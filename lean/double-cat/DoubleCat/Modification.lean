import DoubleCat.Transformation
import DoubleCat.LooseTransformation

/-!
# Modifications, and the pseudo double category of lax double functors

A modification fills a square of transformations of lax double functors:
given loose transformations `σ : F ⇸ G` and `τ : H ⇸ K` and tight
transformations `t : F ⟹ H` and `u : G ⟹ K`, a modification `μ` assigns
to each object `a` a cell

```
            σ.app a
    F a ------------↛ G a
     |                 |
t.app a       μ      u.app a
     v                 v
    H a ------------↛ K a
            τ.app a
```

compatibly with the cell components of the transformations in both
directions: tight-wise with `cellApp` (over the naturality squares of `t`
and `u`) and loose-wise with the naturality comparisons `natCell` (over
the cell components `looseApp` of `t` and `u`).

This is the 3-cell notion of Grandis–Paré ("Limits in double categories",
1999, §7.4), stated for the lax form of loose transformations.  With it
the four kinds of data assemble into the pseudo double category of lax
double functors of Grandis–Paré's §7.4 closing construction:

* objects: lax double functors `F : C → D`;
* tight arrows: tight transformations (composing strictly — the
  `Category (LaxDoubleFunctor C D)` instance of
  `DoubleCat.Transformation`);
* loose arrows: loose transformations (composing by
  `LooseTransformation.comp`, associatively and unitally only up to
  isomorphism);
* cells: modifications.

The structure cells at each object are the structure cells of the target
double category at the components, so the axioms reduce componentwise;
the instances are `LaxDoubleFunctor.laxDoubleCategoryStruct` and
`LaxDoubleFunctor.laxDoubleCategory`.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]

/-- A modification filling a square of transformations: a cell at each
object, compatible with the cell components of the two tight
transformations (tight-wise) and with the naturality comparisons of the two
loose transformations (loose-wise). -/
structure Modification {F G H K : LaxDoubleFunctor C D}
    (σ : LooseTransformation F G) (τ : LooseTransformation H K)
    (t : TightTransformation F H) (u : TightTransformation G K) where

  app : ∀ a : C, Cell (σ.app a) (τ.app a) (t.app a) (u.app a)

  cellApp_compat : ∀ {a b : C} (f : a ⟶ b),
    σ.cellApp f ≫ᵥ app b =
      (app a ≫ᵥ τ.cellApp f).cast (t.naturality f).symm (u.naturality f).symm

  natCell_compat : ∀ {a b : C} (m : Loose a b),
    (t.looseApp m ⊚ app b) ≫ᵥ τ.natCell m =
      (σ.natCell m ≫ᵥ (app a ⊚ u.looseApp m)).cast (by boundary) (by boundary)

namespace Modification

open PseudoDoubleCategory

variable {F G H K : LaxDoubleFunctor C D}

section Heq

variable {σ : LooseTransformation F G} {τ : LooseTransformation H K}
  {t : TightTransformation F H} {u : TightTransformation G K}
  (μ : Modification σ τ t u)

omit [PseudoDoubleCategory C] [PseudoDoubleCategory D] in
theorem cellApp_compat_heq {a b : C} (f : a ⟶ b) :
    σ.cellApp f ≫ᵥ μ.app b ≍ μ.app a ≫ᵥ τ.cellApp f := by
  rw [μ.cellApp_compat]; exact Cell.cast_heq _ _ _

omit [PseudoDoubleCategory C] [PseudoDoubleCategory D] in
theorem natCell_compat_heq {a b : C} (m : Loose a b) :
    (t.looseApp m ⊚ μ.app b) ≫ᵥ τ.natCell m ≍
      σ.natCell m ≫ᵥ (μ.app a ⊚ u.looseApp m) := by
  rw [μ.natCell_compat]; exact Cell.cast_heq _ _ _

end Heq

omit [PseudoDoubleCategory C] [PseudoDoubleCategory D] in

/-- Modifications are determined by their component cells. -/
theorem ext {σ : LooseTransformation F G} {τ : LooseTransformation H K}
    {t : TightTransformation F H} {u : TightTransformation G K}
    {μ ν : Modification σ τ t u} (h : ∀ a, μ.app a = ν.app a) : μ = ν := by
  obtain ⟨mapp, _, _⟩ := μ
  obtain ⟨napp, _, _⟩ := ν
  have h' : mapp = napp := funext h
  subst h'
  rfl

omit [PseudoDoubleCategory C] [PseudoDoubleCategory D] in

theorem heq_ext {σ : LooseTransformation F G} {τ : LooseTransformation H K}
    {t t' : TightTransformation F H} {u u' : TightTransformation G K}
    {μ : Modification σ τ t u} {ν : Modification σ τ t' u'}
    (ht : t = t') (hu : u = u') (h : ∀ a, μ.app a ≍ ν.app a) : μ ≍ ν := by
  subst ht; subst hu
  exact heq_of_eq (ext fun a => eq_of_heq (h a))

/-- The identity modification on a loose transformation. -/
def id (σ : LooseTransformation F G) :
    Modification σ σ (𝟙 F) (𝟙 G) where
  app a := vId (σ.app a)
  cellApp_compat f := by
    rw [Cell.eq_cast_iff_heq]
    exact (vComp_vId_heq _).trans (vId_vComp_heq _).symm
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    exact (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (hComp_vId (F.mapLoose m) (σ.app b))) HEq.rfl).trans <|
      (vId_vComp_heq _).trans <|
      (vComp_vId_heq _).symm.trans
      (vComp_congr_heq rfl rfl rfl rfl HEq.rfl
        (heq_of_eq (hComp_vId (σ.app a) (G.mapLoose m))).symm)

/-- Tight-wise composition of modifications: components compose tight-wise. -/
def vcomp {F' G' : LaxDoubleFunctor C D}
    {σ : LooseTransformation F G} {τ : LooseTransformation H K}
    {υ : LooseTransformation F' G'}
    {t : TightTransformation F H} {u : TightTransformation G K}
    {t' : TightTransformation H F'} {u' : TightTransformation K G'}
    (μ : Modification σ τ t u) (ν : Modification τ υ t' u') :
    Modification σ υ (t.vcomp t') (u.vcomp u') where
  app a := μ.app a ≫ᵥ ν.app a
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (t.naturality f) (u.naturality f) rfl rfl
        (μ.cellApp_compat_heq f) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (t'.naturality f) (u'.naturality f) HEq.rfl
        (ν.cellApp_compat_heq f)).trans

      (vComp_assoc_heq _ _ _).symm
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (interchange (t.looseApp m) (μ.app b)
          (t'.looseApp m) (ν.app b))) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (ν.natCell_compat_heq m)).trans <|

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (μ.natCell_compat_heq m) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (heq_of_eq (interchange (μ.app a) (u.looseApp m)
          (ν.app a) (u'.looseApp m))).symm)

/-- The loose-identity modification on a tight transformation: the cell
component of `t` at each loose identity, filling the square between the
identity loose transformations. -/
def ofTight {F H : LaxDoubleFunctor C D} (t : TightTransformation F H) :
    Modification (LooseTransformation.id F) (LooseTransformation.id H)
      t t where
  app a := hId (t.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact (heq_of_eq (hId_comp (F.map f) (t.app b))).symm.trans <|
      (hId_congr_heq (t.naturality f)).trans
      (heq_of_eq (hId_comp (t.app a) (H.map f)))
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (lRightUnitor_natural_heq (t.looseApp m)) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (lLeftUnitorInv_natural_heq (t.looseApp m))).trans <|

      (vComp_assoc_heq _ _ _).symm.trans
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl)

end Modification

section HComp

open PseudoDoubleCategory

variable {F G H F' G' H' : LaxDoubleFunctor C D}
  {σ₁ : LooseTransformation F G} {σ₂ : LooseTransformation G H}
  {τ₁ : LooseTransformation F' G'} {τ₂ : LooseTransformation G' H'}
  {t : TightTransformation F F'} {u : TightTransformation G G'}
  {v : TightTransformation H H'}

theorem Modification.hcomp_natCell_aux (μ : Modification σ₁ τ₁ t u)
    (ν : Modification σ₂ τ₂ u v) {a b : C} (m : Loose a b) :
    (t.looseApp m ⊚ (μ.app b ⊚ ν.app b)) ≫ᵥ
        LooseTransformation.compNatCell τ₁ τ₂ m ≍
      LooseTransformation.compNatCell σ₁ σ₂ m ≫ᵥ
        ((μ.app a ⊚ ν.app a) ⊚ v.looseApp m) := by
  exact

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans <|

    (vComp_assoc_heq _ _ _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (lAssocInv_natural_heq (t.looseApp m) (μ.app b) (ν.app b))
      HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (t.looseApp m ⊚ μ.app b) (ν.app b)
          (τ₁.natCell m) (vId (τ₂.app b)))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            (μ.natCell_compat_heq m)
            ((vComp_vId_heq (ν.app b)).trans
              (vId_vComp_heq (ν.app b)).symm)).trans
          (heq_of_eq (interchange (σ₁.natCell m) (vId (σ₂.app b))
            (μ.app a ⊚ u.looseApp m) (ν.app b))))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq (μ.app a) (u.looseApp m) (ν.app b))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (μ.app a) (u.looseApp m ⊚ ν.app b)
          (vId (τ₁.app a)) (τ₂.natCell m))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            ((vComp_vId_heq (μ.app a)).trans
              (vId_vComp_heq (μ.app a)).symm)
            (ν.natCell_compat_heq m)).trans <|
          (heq_of_eq (interchange (vId (σ₁.app a)) (σ₂.natCell m)
            (μ.app a) (ν.app a ⊚ v.looseApp m))))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      lAssocInv_natural_heq (μ.app a) (ν.app a)
        (v.looseApp m)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_assoc_heq _ _ _).symm.trans <|

    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (Cell.cast_heq _ _ _).symm HEq.rfl)

/-- Loose-wise composition of modifications: components compose loose-wise,
compatibly with the composite loose transformations. -/
def Modification.hcomp (μ : Modification σ₁ τ₁ t u)
    (ν : Modification σ₂ τ₂ u v) :
    Modification (σ₁.comp σ₂) (τ₁.comp τ₂) t v where
  app a := μ.app a ⊚ ν.app a
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (heq_of_eq (interchange (σ₁.cellApp f) (σ₂.cellApp f)
        (μ.app b) (ν.app b))).symm.trans <|

      (hComp_congr_heq (t.naturality f) (u.naturality f) (v.naturality f)
        (μ.cellApp_compat_heq f) (ν.cellApp_compat_heq f)).trans

      (heq_of_eq (interchange (μ.app a) (ν.app a)
        (τ₁.cellApp f) (τ₂.cellApp f)))
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    exact μ.hcomp_natCell_aux ν m

end HComp

namespace Modification

open PseudoDoubleCategory

section StructuralTubes

open Bicategory in

theorem assocTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb za zb wa wb : B}
    {fm : xa ⟶ xb} {gm : ya ⟶ yb} {hm : za ⟶ zb} {km : wa ⟶ wb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} {ra : ya ⟶ za} {rb : yb ⟶ zb}
    {pa : za ⟶ wa} {pb : zb ⟶ wb}
    (Sm : fm ≫ sb ⟶ sa ≫ gm) (Rm : gm ≫ rb ⟶ ra ≫ hm)
    (Pm : hm ≫ pb ⟶ pa ≫ km) :
    fm ◁ (α_ sb rb pb).hom ≫
        ((α_ fm sb (rb ≫ pb)).inv ≫ Sm ▷ (rb ≫ pb) ≫
          (α_ sa gm (rb ≫ pb)).hom ≫
          sa ◁ ((α_ gm rb pb).inv ≫ Rm ▷ pb ≫ (α_ ra hm pb).hom ≫
            ra ◁ Pm ≫ (α_ ra pa km).inv) ≫
          (α_ sa (ra ≫ pa) km).inv) =
      ((α_ fm (sb ≫ rb) pb).inv ≫
          ((α_ fm sb rb).inv ≫ Sm ▷ rb ≫ (α_ sa gm rb).hom ≫
            sa ◁ Rm ≫ (α_ sa ra hm).inv) ▷ pb ≫
          (α_ (sa ≫ ra) hm pb).hom ≫ (sa ≫ ra) ◁ Pm ≫
          (α_ (sa ≫ ra) pa km).inv) ≫
        (α_ sa ra pa).hom ▷ km := by
  bicategory

open Bicategory in

theorem assocInvTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb za zb wa wb : B}
    {fm : xa ⟶ xb} {gm : ya ⟶ yb} {hm : za ⟶ zb} {km : wa ⟶ wb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} {ra : ya ⟶ za} {rb : yb ⟶ zb}
    {pa : za ⟶ wa} {pb : zb ⟶ wb}
    (Sm : fm ≫ sb ⟶ sa ≫ gm) (Rm : gm ≫ rb ⟶ ra ≫ hm)
    (Pm : hm ≫ pb ⟶ pa ≫ km) :
    fm ◁ (α_ sb rb pb).inv ≫
        ((α_ fm (sb ≫ rb) pb).inv ≫
          ((α_ fm sb rb).inv ≫ Sm ▷ rb ≫ (α_ sa gm rb).hom ≫
            sa ◁ Rm ≫ (α_ sa ra hm).inv) ▷ pb ≫
          (α_ (sa ≫ ra) hm pb).hom ≫ (sa ≫ ra) ◁ Pm ≫
          (α_ (sa ≫ ra) pa km).inv) =
      ((α_ fm sb (rb ≫ pb)).inv ≫ Sm ▷ (rb ≫ pb) ≫
          (α_ sa gm (rb ≫ pb)).hom ≫
          sa ◁ ((α_ gm rb pb).inv ≫ Rm ▷ pb ≫ (α_ ra hm pb).hom ≫
            ra ◁ Pm ≫ (α_ ra pa km).inv) ≫
          (α_ sa (ra ≫ pa) km).inv) ≫
        (α_ sa ra pa).inv ▷ km := by
  bicategory

open Bicategory in

theorem leftUnitorTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb : B} {fm : xa ⟶ xb} {gm : ya ⟶ yb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} (Sm : fm ≫ sb ⟶ sa ≫ gm) :
    fm ◁ (λ_ sb).hom ≫ Sm =
      ((α_ fm (𝟙 xb) sb).inv ≫ ((ρ_ fm).hom ≫ (λ_ fm).inv) ▷ sb ≫
          (α_ (𝟙 xa) fm sb).hom ≫ 𝟙 xa ◁ Sm ≫ (α_ (𝟙 xa) sa gm).inv) ≫
        (λ_ sa).hom ▷ gm := by
  bicategory

open Bicategory in

theorem leftUnitorInvTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb : B} {fm : xa ⟶ xb} {gm : ya ⟶ yb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} (Sm : fm ≫ sb ⟶ sa ≫ gm) :
    fm ◁ (λ_ sb).inv ≫
        ((α_ fm (𝟙 xb) sb).inv ≫ ((ρ_ fm).hom ≫ (λ_ fm).inv) ▷ sb ≫
          (α_ (𝟙 xa) fm sb).hom ≫ 𝟙 xa ◁ Sm ≫ (α_ (𝟙 xa) sa gm).inv) =
      Sm ≫ (λ_ sa).inv ▷ gm := by
  bicategory

open Bicategory in

theorem rightUnitorTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb : B} {fm : xa ⟶ xb} {gm : ya ⟶ yb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} (Sm : fm ≫ sb ⟶ sa ≫ gm) :
    fm ◁ (ρ_ sb).hom ≫ Sm =
      ((α_ fm sb (𝟙 yb)).inv ≫ Sm ▷ 𝟙 yb ≫ (α_ sa gm (𝟙 yb)).hom ≫
          sa ◁ ((ρ_ gm).hom ≫ (λ_ gm).inv) ≫ (α_ sa (𝟙 ya) gm).inv) ≫
        (ρ_ sa).hom ▷ gm := by
  bicategory

open Bicategory in

theorem rightUnitorInvTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {xa xb ya yb : B} {fm : xa ⟶ xb} {gm : ya ⟶ yb}
    {sa : xa ⟶ ya} {sb : xb ⟶ yb} (Sm : fm ≫ sb ⟶ sa ≫ gm) :
    fm ◁ (ρ_ sb).inv ≫
        ((α_ fm sb (𝟙 yb)).inv ≫ Sm ▷ 𝟙 yb ≫ (α_ sa gm (𝟙 yb)).hom ≫
          sa ◁ ((ρ_ gm).hom ≫ (λ_ gm).inv) ≫ (α_ sa (𝟙 ya) gm).inv) =
      Sm ≫ (ρ_ sa).inv ▷ gm := by
  bicategory

end StructuralTubes

section Structural

variable {F G H K : LaxDoubleFunctor C D}

/-- The associator modification for composition of loose transformations:
componentwise the associator of the target double category. -/
def assoc (σ : LooseTransformation F G) (ρ : LooseTransformation G H)
    (π : LooseTransformation H K) :
    Modification ((σ.comp ρ).comp π) (σ.comp (ρ.comp π)) (𝟙 F) (𝟙 K) where
  app a := lAssoc (σ.app a) (ρ.app a) (π.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lAssoc_natural_heq (σ.cellApp f) (ρ.cellApp f) (π.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := assocTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (hm := show (LooseBicat.mk (H.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj b) from H.mapLoose m)
      (km := show (LooseBicat.mk (K.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj b) from K.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (ra := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj a) from ρ.app a)
      (rb := show (LooseBicat.mk (G.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj b) from ρ.app b)
      (pa := show (LooseBicat.mk (H.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj a) from π.app a)
      (pb := show (LooseBicat.mk (H.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj b) from π.app b)
      (σ.natCell m) (ρ.natCell m) (π.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|
      (Cell.cast_eq_iff_heq.mp h).trans <|
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl)

def assocInv (σ : LooseTransformation F G) (ρ : LooseTransformation G H)
    (π : LooseTransformation H K) :
    Modification (σ.comp (ρ.comp π)) ((σ.comp ρ).comp π) (𝟙 F) (𝟙 K) where
  app a := lAssocInv (σ.app a) (ρ.app a) (π.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lAssocInv_natural_heq (σ.cellApp f) (ρ.cellApp f) (π.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := assocInvTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (hm := show (LooseBicat.mk (H.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj b) from H.mapLoose m)
      (km := show (LooseBicat.mk (K.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj b) from K.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (ra := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj a) from ρ.app a)
      (rb := show (LooseBicat.mk (G.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj b) from ρ.app b)
      (pa := show (LooseBicat.mk (H.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj a) from π.app a)
      (pb := show (LooseBicat.mk (H.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (K.obj b) from π.app b)
      (σ.natCell m) (ρ.natCell m) (π.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|
      (Cell.cast_eq_iff_heq.mp h).trans <|
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl)

/-- The left unitor modification: componentwise the left unitor of the
target. -/
def leftUnitor (σ : LooseTransformation F G) :
    Modification ((LooseTransformation.id F).comp σ) σ (𝟙 F) (𝟙 G) where
  app a := lLeftUnitor (σ.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lLeftUnitor_natural_heq (σ.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := leftUnitorTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (σ.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (Cell.cast_eq_iff_heq.mp h).trans <|
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl)

def leftUnitorInv (σ : LooseTransformation F G) :
    Modification σ ((LooseTransformation.id F).comp σ) (𝟙 F) (𝟙 G) where
  app a := lLeftUnitorInv (σ.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lLeftUnitorInv_natural_heq (σ.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := leftUnitorInvTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (σ.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|
      (Cell.cast_eq_iff_heq.mp h).trans
      (Cell.cast_heq _ _ _)

/-- The right unitor modification: componentwise the right unitor of the
target. -/
def rightUnitor (σ : LooseTransformation F G) :
    Modification (σ.comp (LooseTransformation.id G)) σ (𝟙 F) (𝟙 G) where
  app a := lRightUnitor (σ.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lRightUnitor_natural_heq (σ.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := rightUnitorTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (σ.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (Cell.cast_eq_iff_heq.mp h).trans <|
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl)

def rightUnitorInv (σ : LooseTransformation F G) :
    Modification σ (σ.comp (LooseTransformation.id G)) (𝟙 F) (𝟙 G) where
  app a := lRightUnitorInv (σ.app a)
  cellApp_compat {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact lRightUnitorInv_natural_heq (σ.cellApp f)
  natCell_compat {a b} m := by
    rw [Cell.eq_cast_iff_heq]
    have h := rightUnitorInvTube (B := LooseBicat D)
      (fm := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m)
      (gm := show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m)
      (sa := show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a)
      (sb := show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from σ.app b)
      (σ.natCell m)
    repeat rw [globularComp_def] at h
    simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|
      (Cell.cast_eq_iff_heq.mp h).trans
      (Cell.cast_heq _ _ _)

end Structural

end Modification

section LaxDouble

open PseudoDoubleCategory

/-- The pseudo double category of lax double functors `C → D`: tight arrows
are tight transformations, loose arrows are loose transformations, cells are
modifications (Grandis–Paré, "Limits in double categories", 1999, §7.4). -/
instance LaxDoubleFunctor.laxDoubleCategoryStruct :
    PseudoDoubleCategoryStruct (LaxDoubleFunctor C D) where
  Loose F G := LooseTransformation F G
  Cell σ τ t u := Modification σ τ t u
  vId σ := Modification.id σ
  vComp μ ν := μ.vcomp ν
  lId F := LooseTransformation.id F
  lComp σ τ := σ.comp τ
  hId t := Modification.ofTight t
  hComp μ ν := μ.hcomp ν
  lAssoc σ ρ π := Modification.assoc σ ρ π
  lAssocInv σ ρ π := Modification.assocInv σ ρ π
  lLeftUnitor σ := Modification.leftUnitor σ
  lLeftUnitorInv σ := Modification.leftUnitorInv σ
  lRightUnitor σ := Modification.rightUnitor σ
  lRightUnitorInv σ := Modification.rightUnitorInv σ

/-- The axioms hold componentwise: every equation of modifications reduces to
the corresponding equation in the target double category at each object. -/
instance LaxDoubleFunctor.laxDoubleCategory :
    PseudoDoubleCategory (LaxDoubleFunctor C D) where
  vId_vComp μ := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => vId_vComp_heq (μ.app a)
  vComp_vId μ := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => vComp_vId_heq (μ.app a)
  vComp_assoc α β γ := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => vComp_assoc_heq (α.app a) (β.app a) (γ.app a)
  hId_id F :=
    Modification.ext fun a => PseudoDoubleCategory.hId_id (F.obj a)
  hId_comp f g :=
    Modification.ext fun a =>
      PseudoDoubleCategory.hId_comp (f.app a) (g.app a)
  hComp_vId m n :=
    Modification.ext fun a =>
      PseudoDoubleCategory.hComp_vId (m.app a) (n.app a)
  interchange α₁ α₂ β₁ β₂ :=
    Modification.ext fun a =>
      PseudoDoubleCategory.interchange (α₁.app a) (α₂.app a)
        (β₁.app a) (β₂.app a)
  lAssoc_natural α β γ := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lAssoc_natural_heq (α.app a) (β.app a) (γ.app a)
  lLeftUnitor_natural α := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lLeftUnitor_natural_heq (α.app a)
  lRightUnitor_natural α := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lRightUnitor_natural_heq (α.app a)
  lAssoc_lAssocInv m n p := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lAssoc_lAssocInv_heq (m.app a) (n.app a) (p.app a)
  lAssocInv_lAssoc m n p := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lAssocInv_lAssoc_heq (m.app a) (n.app a) (p.app a)
  lLeftUnitor_lLeftUnitorInv m := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lLeftUnitor_lLeftUnitorInv_heq (m.app a)
  lLeftUnitorInv_lLeftUnitor m := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lLeftUnitorInv_lLeftUnitor_heq (m.app a)
  lRightUnitor_lRightUnitorInv m := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lRightUnitor_lRightUnitorInv_heq (m.app a)
  lRightUnitorInv_lRightUnitor m := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => lRightUnitorInv_lRightUnitor_heq (m.app a)
  pentagon m n p q := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => pentagon_heq (m.app a) (n.app a) (p.app a) (q.app a)
  triangle m n := by
    rw [Cell.eq_cast_iff_heq]
    exact Modification.heq_ext (by simp) (by simp)
      fun a => triangle_heq (m.app a) (n.app a)

end LaxDouble

end CategoryTheory
