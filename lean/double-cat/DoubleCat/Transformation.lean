import DoubleCat.Functor.Lax

/-!
# Tight transformations of lax double functors

A tight transformation `σ : F ⟹ G` between lax double functors assigns to
each object a tight arrow `σ.app a : F.obj a ⟶ G.obj a` (naturally in
tight arrows: the underlying data is a natural transformation of the tight
functors) and to each loose arrow `m` a cell `σ.looseApp m` with tight
sides `σ.app a`, `σ.app b`, naturally in cells and compatibly with the
compositors and unit comparisons of `F` and `G`.

This is the notion Grandis–Paré call a *horizontal* transformation
("Adjoint for double categories", 2004, §2.2 — the 2-cells of their
2-category of weak double categories and lax double functors; their
*vertical* transformations are the loose-component notion,
`CategoryTheory.LooseTransformation`), and Definition 2.12 of
Cruttwell–Lambert–Pronk–Szyld ("Double fibrations", 2022).  Pseudo double
categories, lax double functors, and tight transformations form a strict
2-category; this file provides its hom-categories:
`Category (LaxDoubleFunctor C D)` with tight transformations as morphisms.

The coherence proofs for vertical composition are heterogeneous-equality
chases in the style of `DoubleCat.Functor.Composition` (see the
proof-technique note there; in particular `calc` cannot chain
heterogeneous steps, so the chases are right-nested `HEq.trans` chains).
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

/-- A tight transformation between lax double functors: a natural
transformation of the underlying tight functors, together with a cell
component at every loose arrow, natural in cells and coherent with the
laxators. -/
structure TightTransformation (F G : LaxDoubleFunctor C D) extends
    NatTrans F.toFunctor G.toFunctor where

  /-- The cell component at a loose arrow. -/
  looseApp : ∀ {a b : C} (m : Loose a b),
    Cell (F.mapLoose m) (G.mapLoose m) (app a) (app b)

  /-- Naturality of the cell components in cells. -/
  looseApp_natural : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g),
    F.mapCell α ≫ᵥ looseApp n =
      (looseApp m ≫ᵥ G.mapCell α).cast
        (naturality f).symm (naturality g).symm

  /-- Compatibility with the compositors. -/
  looseApp_laxComp : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    F.laxComp m n ≫ᵥ looseApp (m ⊙ n) =
      ((looseApp m ⊚ looseApp n) ≫ᵥ G.laxComp m n).cast
        (by boundary) (by boundary)

  /-- Compatibility with the unit comparisons. -/
  looseApp_laxId : ∀ (a : C),
    F.laxId a ≫ᵥ looseApp (lId a) =
      (hId (app a) ≫ᵥ G.laxId a).cast (by boundary) (by boundary)

namespace TightTransformation

variable {F G H : LaxDoubleFunctor C D}

section Heq

variable (σ : TightTransformation F G)

theorem looseApp_natural_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) :
    F.mapCell α ≫ᵥ σ.looseApp n ≍ σ.looseApp m ≫ᵥ G.mapCell α := by
  rw [σ.looseApp_natural]; exact Cell.cast_heq _ _ _

theorem looseApp_laxComp_heq {a b c : C} (m : Loose a b) (n : Loose b c) :
    F.laxComp m n ≫ᵥ σ.looseApp (m ⊙ n) ≍
      (σ.looseApp m ⊚ σ.looseApp n) ≫ᵥ G.laxComp m n := by
  rw [σ.looseApp_laxComp]; exact Cell.cast_heq _ _ _

theorem looseApp_laxId_heq (a : C) :
    F.laxId a ≫ᵥ σ.looseApp (lId a) ≍ hId (σ.app a) ≫ᵥ G.laxId a := by
  rw [σ.looseApp_laxId]; exact Cell.cast_heq _ _ _

end Heq

/-- Tight transformations are determined by their tight components and cell
components. -/
theorem ext {σ τ : TightTransformation F G}
    (happ : ∀ a, σ.app a = τ.app a)
    (hloose : ∀ {a b : C} (m : Loose a b), σ.looseApp m ≍ τ.looseApp m) :
    σ = τ := by
  obtain ⟨⟨sapp, snat⟩, sloose, _, _, _⟩ := σ
  obtain ⟨⟨tapp, tnat⟩, tloose, _, _, _⟩ := τ
  have h : sapp = tapp := funext happ
  subst h
  have h' : @sloose = @tloose := by
    funext a b m
    exact eq_of_heq (hloose m)
  subst h'
  rfl

/-- The identity tight transformation. -/
def id (F : LaxDoubleFunctor C D) : TightTransformation F F where
  app a := 𝟙 (F.obj a)
  naturality _ _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
  looseApp m := vId (F.mapLoose m)
  looseApp_natural α := by
    simp [PseudoDoubleCategory.vId_vComp, PseudoDoubleCategory.vComp_vId]
  looseApp_laxComp m n := by
    simp [PseudoDoubleCategory.hComp_vId, PseudoDoubleCategory.vId_vComp,
      PseudoDoubleCategory.vComp_vId]
  looseApp_laxId a := by
    simp [PseudoDoubleCategory.hId_id, PseudoDoubleCategory.vId_vComp,
      PseudoDoubleCategory.vComp_vId]

/-- Vertical composition of tight transformations: components compose
tight-wise. -/
def vcomp (σ : TightTransformation F G) (τ : TightTransformation G H) :
    TightTransformation F H where
  app a := σ.app a ≫ τ.app a
  naturality _ _ f :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ τ.app _) (σ.naturality f)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (σ.app _ ≫ ·) (τ.naturality f)).trans
            (Category.assoc _ _ _).symm
  looseApp m := σ.looseApp m ≫ᵥ τ.looseApp m
  looseApp_natural {a b c d} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (σ.naturality f) (σ.naturality g) rfl rfl
        (σ.looseApp_natural_heq α) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (τ.naturality f) (τ.naturality g) HEq.rfl
        (τ.looseApp_natural_heq α)).trans

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm
  looseApp_laxComp {a b c} m n := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (σ.looseApp_laxComp_heq m n) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (τ.looseApp_laxComp_heq m n)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (heq_of_eq (PseudoDoubleCategory.interchange _ _ _ _)).symm HEq.rfl)
  looseApp_laxId a := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (σ.looseApp_laxId_heq a) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (τ.looseApp_laxId_heq a)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (heq_of_eq (PseudoDoubleCategory.hId_comp _ _)).symm HEq.rfl)

@[simp]
theorem id_app (F : LaxDoubleFunctor C D) (a : C) :
    (TightTransformation.id F).app a = 𝟙 (F.obj a) := rfl

@[simp]
theorem id_looseApp (F : LaxDoubleFunctor C D) {a b : C} (m : Loose a b) :
    (TightTransformation.id F).looseApp m = vId (F.mapLoose m) := rfl

@[simp]
theorem vcomp_app (σ : TightTransformation F G) (τ : TightTransformation G H)
    (a : C) : (σ.vcomp τ).app a = σ.app a ≫ τ.app a := rfl

@[simp]
theorem vcomp_looseApp (σ : TightTransformation F G)
    (τ : TightTransformation G H) {a b : C} (m : Loose a b) :
    (σ.vcomp τ).looseApp m = σ.looseApp m ≫ᵥ τ.looseApp m := rfl

end TightTransformation

/-- Lax double functors and tight transformations form a category: the
hom-categories of the strict 2-category of pseudo double categories. -/
instance : Category (LaxDoubleFunctor C D) where
  Hom F G := TightTransformation F G
  id F := TightTransformation.id F
  comp σ τ := σ.vcomp τ
  id_comp σ :=
    TightTransformation.ext (fun a => by simp)
      (fun m => PseudoDoubleCategory.vId_vComp_heq (σ.looseApp m))
  comp_id σ :=
    TightTransformation.ext (fun a => by simp)
      (fun m => PseudoDoubleCategory.vComp_vId_heq (σ.looseApp m))
  assoc σ τ υ :=
    TightTransformation.ext (fun a => by simp)
      (fun m =>
        PseudoDoubleCategory.vComp_assoc_heq (σ.looseApp m) (τ.looseApp m)
          (υ.looseApp m))

end CategoryTheory
