import DoubleCat.Functor.Lax
import DoubleCat.Functor.Pseudo
import DoubleCat.LooseBicategory
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Loose transformations of lax double functors

A loose transformation `σ : F ⇸ G` between lax double functors assigns to
each object a *loose* arrow `σ.app a : Loose (F.obj a) (G.obj a)`, to each
tight arrow `f : a ⟶ b` a cell `σ.cellApp f` with loose sides `σ.app a`,
`σ.app b` and tight sides `F.map f`, `G.map f` (functorial in `f` up to
`Cell.cast`), and to each loose arrow `m : Loose a b` a globular
*naturality comparison* `σ.natCell m : F.mapLoose m ⊙ σ.app b ⟶
σ.app a ⊙ G.mapLoose m`, natural in cells and coherent with the
compositors and unit comparisons of `F` and `G`.

This is the loose-direction mirror of
`CategoryTheory.TightTransformation`: where the tight notion has tight
components and cell components indexed by loose arrows, the loose notion
has loose components, cell components indexed by tight arrows, and —
because loose composition is weak — an additional layer of comparison
cells in place of the tight notion's naturality *equations*.

It is the notion Grandis–Paré call a *vertical transformation* ("Limits in
double categories", 1999, §7.4 — their vertical direction is the loose one
here).  Grandis–Paré restrict to the *strong* case, requiring the
naturality comparisons to be invertible ("special isocells"), which is the
only case they need; we state the data and axioms without invertibility
(the lax form) and provide strength as a separate predicate
`LooseTransformation.IsStrong`, in the same definitions-with-controls
style as `LaxDoubleFunctor.IsPseudo`.  Restricted to bicategories
(one-object tight direction) the notion is a lax natural transformation of
lax functors; the tight notion restricts to Lack's icons.

Loose transformations compose along the loose direction of their
components (`LooseTransformation.comp`), with naturality comparisons
pasted and corrected by associators — associatively and unitally only up
to isomorphism, which is why they form the loose direction of a pseudo
double category of lax double functors (`DoubleCat.Modification`) rather
than a category.
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

/-- A loose transformation between lax double functors: loose-arrow
components, cell components at tight arrows, and globular naturality
comparison cells at loose arrows, coherent with the laxators of both
functors.

This is Grandis–Paré's *vertical transformation* ("Limits in double
categories", 1999, §7.4), stated laxly: their strong form additionally
requires the naturality comparisons to be invertible, which is
`LooseTransformation.IsStrong` here. -/
structure LooseTransformation (F G : LaxDoubleFunctor C D) where

  /-- The loose-arrow component at an object. -/
  app : ∀ a : C, Loose (F.obj a) (G.obj a)

  /-- The cell component at a tight arrow. -/
  cellApp : ∀ {a b : C} (f : a ⟶ b),
    Cell (app a) (app b) (F.map f) (G.map f)

  /-- The naturality comparison at a loose arrow. -/
  natCell : ∀ {a b : C} (m : Loose a b),
    Cell (F.mapLoose m ⊙ app b) (app a ⊙ G.mapLoose m)
      (𝟙 (F.obj a)) (𝟙 (G.obj b))

  /-- The cell components preserve tight identities. -/
  cellApp_id : ∀ a : C,
    cellApp (𝟙 a) =
      (vId (app a)).cast (F.map_id a).symm (G.map_id a).symm

  /-- The cell components preserve tight composition. -/
  cellApp_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c),
    cellApp (f ≫ g) =
      (cellApp f ≫ᵥ cellApp g).cast
        (F.map_comp f g).symm (G.map_comp f g).symm

  /-- Naturality of the comparison cells in cells. -/
  natCell_natural : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g),
    (F.mapCell α ⊚ cellApp g) ≫ᵥ natCell n =
      (natCell m ≫ᵥ (cellApp f ⊚ G.mapCell α)).cast
        (by boundary) (by boundary)

  /-- Coherence of the comparison cells with the unit comparisons. -/
  natCell_laxId : ∀ a : C,
    (F.laxId a ⊚ vId (app a)) ≫ᵥ natCell (𝟙ˡ a) =
      (lLeftUnitor (app a) ≫ᵥ lRightUnitorInv (app a) ≫ᵥ
        (vId (app a) ⊚ G.laxId a)).cast (by boundary) (by boundary)

  /-- Coherence of the comparison cells with the compositors. -/
  natCell_laxComp : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    (F.laxComp m n ⊚ vId (app c)) ≫ᵥ natCell (m ⊙ n) =
      (lAssoc (F.mapLoose m) (F.mapLoose n) (app c) ≫ᵥ
        (vId (F.mapLoose m) ⊚ natCell n) ≫ᵥ
        lAssocInv (F.mapLoose m) (app b) (G.mapLoose n) ≫ᵥ
        (natCell m ⊚ vId (G.mapLoose n)) ≫ᵥ
        lAssoc (app a) (G.mapLoose m) (G.mapLoose n) ≫ᵥ
        (vId (app a) ⊚ G.laxComp m n)).cast (by boundary) (by boundary)

namespace LooseTransformation

open PseudoDoubleCategory

variable {F G : LaxDoubleFunctor C D}

/-- A loose transformation is *strong* (Grandis–Paré's actual notion) when all
its naturality comparisons are invertible. -/
def IsStrong (σ : LooseTransformation F G) : Prop :=
  ∀ {a b : C} (m : Loose a b), (σ.natCell m).IsInvertible

section Heq

variable (σ : LooseTransformation F G)

theorem cellApp_id_heq (a : C) : σ.cellApp (𝟙 a) ≍ vId (σ.app a) := by
  rw [σ.cellApp_id]; exact Cell.cast_heq _ _ _

theorem cellApp_comp_heq {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    σ.cellApp (f ≫ g) ≍ σ.cellApp f ≫ᵥ σ.cellApp g := by
  rw [σ.cellApp_comp]; exact Cell.cast_heq _ _ _

theorem natCell_natural_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) :
    (F.mapCell α ⊚ σ.cellApp g) ≫ᵥ σ.natCell n ≍
      σ.natCell m ≫ᵥ (σ.cellApp f ⊚ G.mapCell α) := by
  rw [σ.natCell_natural]; exact Cell.cast_heq _ _ _

theorem natCell_laxId_heq (a : C) :
    (F.laxId a ⊚ vId (σ.app a)) ≫ᵥ σ.natCell (𝟙ˡ a) ≍
      lLeftUnitor (σ.app a) ≫ᵥ lRightUnitorInv (σ.app a) ≫ᵥ
        (vId (σ.app a) ⊚ G.laxId a) := by
  rw [σ.natCell_laxId]; exact Cell.cast_heq _ _ _

theorem natCell_laxComp_heq {a b c : C} (m : Loose a b) (n : Loose b c) :
    (F.laxComp m n ⊚ vId (σ.app c)) ≫ᵥ σ.natCell (m ⊙ n) ≍
      lAssoc (F.mapLoose m) (F.mapLoose n) (σ.app c) ≫ᵥ
        (vId (F.mapLoose m) ⊚ σ.natCell n) ≫ᵥ
        lAssocInv (F.mapLoose m) (σ.app b) (G.mapLoose n) ≫ᵥ
        (σ.natCell m ⊚ vId (G.mapLoose n)) ≫ᵥ
        lAssoc (σ.app a) (G.mapLoose m) (G.mapLoose n) ≫ᵥ
        (vId (σ.app a) ⊚ G.laxComp m n) := by
  rw [σ.natCell_laxComp]; exact Cell.cast_heq _ _ _

end Heq

/-- Loose transformations are determined by their loose components, cell
components, and naturality comparisons. -/
theorem ext {σ τ : LooseTransformation F G}
    (happ : ∀ a, σ.app a = τ.app a)
    (hcell : ∀ {a b : C} (f : a ⟶ b), σ.cellApp f ≍ τ.cellApp f)
    (hnat : ∀ {a b : C} (m : Loose a b), σ.natCell m ≍ τ.natCell m) :
    σ = τ := by
  obtain ⟨sapp, scell, snat, _, _, _, _, _⟩ := σ
  obtain ⟨tapp, tcell, tnat, _, _, _, _, _⟩ := τ
  have h : sapp = tapp := funext happ
  subst h
  have h' : @scell = @tcell := by
    funext a b f
    exact eq_of_heq (hcell f)
  subst h'
  have h'' : @snat = @tnat := by
    funext a b m
    exact eq_of_heq (hnat m)
  subst h''
  rfl

open Bicategory in

theorem idTube {B : Type u₁} [Bicategory.{t₁, w₁} B] {a b c : B}
    (p : a ⟶ b) (q : b ⟶ c) :
    (ρ_ (p ≫ q)).hom ≫ (λ_ (p ≫ q)).inv =
      (α_ p q (𝟙 c)).hom ≫
        (p ◁ ((ρ_ q).hom ≫ (λ_ q).inv)) ≫
        (α_ p (𝟙 b) q).inv ≫
        (((ρ_ p).hom ≫ (λ_ p).inv) ▷ q) ≫
        (α_ (𝟙 a) p q).hom := by
  bicategory

theorem id_comp_tube {a b c : D} (m : Loose a b) (n : Loose b c) :
    lRightUnitor (m ⊙ n) ≫ᵥ lLeftUnitorInv (m ⊙ n) ≍
      lAssoc m n (𝟙ˡ c) ≫ᵥ
        (vId m ⊚ (lRightUnitor n ≫ᵥ lLeftUnitorInv n).cast
          (f' := 𝟙 b) (g' := 𝟙 c) (by simp) (by simp)) ≫ᵥ
        lAssocInv m (𝟙ˡ b) n ≫ᵥ
        ((lRightUnitor m ≫ᵥ lLeftUnitorInv m).cast
          (f' := 𝟙 a) (g' := 𝟙 b) (by simp) (by simp) ⊚
          vId n) ≫ᵥ
        lAssoc (𝟙ˡ a) m n := by
  have h := idTube (show (LooseBicat.mk a : LooseBicat D) ⟶ LooseBicat.mk b
    from m) (show (LooseBicat.mk b : LooseBicat D) ⟶ LooseBicat.mk c from n)
  rw [globularComp_def, globularComp_def, globularComp_def,
    globularComp_def, globularComp_def, globularComp_def,
    globularComp_def] at h
  simp only [vComp_cast, Cell.cast_cast] at h
  exact (Cell.cast_eq_iff_heq.mp h).trans (Cell.cast_heq _ _ _)

/-- The identity loose transformation: loose-identity components, with
naturality comparisons built from the unitors. -/
def id (F : LaxDoubleFunctor C D) : LooseTransformation F F where
  app a := 𝟙ˡ (F.obj a)
  cellApp f := hId (F.map f)
  natCell m :=
    (lRightUnitor (F.mapLoose m) ≫ᵥ lLeftUnitorInv (F.mapLoose m)).cast
      (by simp) (by simp)
  cellApp_id a := by
    rw [Cell.eq_cast_iff_heq]
    exact (hId_congr_heq (F.map_id a)).trans
      (heq_of_eq (hId_id (F.obj a)))
  cellApp_comp f g := by
    rw [Cell.eq_cast_iff_heq]
    exact (hId_congr_heq (F.map_comp f g)).trans
      (heq_of_eq (hId_comp _ _))
  natCell_natural {a b c d} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lRightUnitor_natural_heq (F.mapCell α)) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (lLeftUnitorInv_natural_heq (F.mapCell α))).trans <|

      ((vComp_assoc_heq _ _ _).symm.trans
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (Cell.cast_heq _ _ _).symm HEq.rfl))
  natCell_laxId a := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((vComp_congr_heq rfl rfl rfl rfl
          (hComp_congr_heq rfl rfl rfl HEq.rfl
            (heq_of_eq (hId_id (F.obj a)).symm)) HEq.rfl).trans
          (lRightUnitor_natural_heq (F.laxId a))) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        ((lLeftUnitorInv_natural_heq (F.laxId a)).trans
          (vComp_congr_heq rfl rfl rfl rfl HEq.rfl
            (hComp_congr_heq rfl rfl rfl
              (heq_of_eq (hId_id (F.obj a))) HEq.rfl)))).trans <|

      (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (lLeftUnitor_lId_eq_lRightUnitor_lId (F.obj a)).symm)
        (vComp_congr_heq rfl rfl rfl rfl
          (heq_of_eq (lLeftUnitorInv_lId_eq_lRightUnitorInv_lId
            (F.obj a))) HEq.rfl))
  natCell_laxComp {a b c} m n := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (Cell.cast_heq _ _ _)).trans <|

      (vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((vComp_congr_heq rfl rfl rfl rfl
          (hComp_congr_heq rfl rfl rfl HEq.rfl
            (heq_of_eq (hId_id (F.obj c)).symm)) HEq.rfl).trans
          (lRightUnitor_natural_heq (F.laxComp m n))) HEq.rfl).trans <|

      (vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        ((lLeftUnitorInv_natural_heq (F.laxComp m n)).trans
          (vComp_congr_heq rfl rfl rfl rfl HEq.rfl
            (hComp_congr_heq rfl rfl rfl
              (heq_of_eq (hId_id (F.obj a))) HEq.rfl)))).trans <|

      ((vComp_assoc_heq _ _ _).symm.trans <|
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (id_comp_tube (F.mapLoose m) (F.mapLoose n)) HEq.rfl).trans <|
        (vComp_assoc_heq _ _ _).trans <|
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
          (vComp_assoc_heq _ _ _).trans <|
          (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
            (vComp_assoc_heq _ _ _).trans <|
            (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
              (vComp_assoc_heq _ _ _)))))

@[simp]
theorem id_app (F : LaxDoubleFunctor C D) (a : C) :
    (LooseTransformation.id F).app a = 𝟙ˡ (F.obj a) := rfl

@[simp]
theorem id_cellApp (F : LaxDoubleFunctor C D) {a b : C} (f : a ⟶ b) :
    (LooseTransformation.id F).cellApp f = hId (F.map f) := rfl

/-- The identity loose transformation is strong. -/
theorem isStrong_id (F : LaxDoubleFunctor C D) :
    (LooseTransformation.id F).IsStrong := by
  intro a b m
  refine ⟨(lLeftUnitor (F.mapLoose m) ≫ᵥ
    lRightUnitorInv (F.mapLoose m)).cast (by simp) (by simp), ?_, ?_⟩
  · rw [Cell.eq_cast_iff_heq]
    exact (vComp_congr_heq (by simp) (by simp) (by simp) (by simp)
        (Cell.cast_heq _ _ _) (Cell.cast_heq _ _ _)).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
        (vComp_assoc_heq _ _ _).symm.trans <|
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (PseudoDoubleCategory.lLeftUnitorInv_lLeftUnitor_heq _)
          HEq.rfl).trans
        (PseudoDoubleCategory.vId_vComp_heq _)).trans
      (PseudoDoubleCategory.lRightUnitor_lRightUnitorInv_heq _)
  · rw [Cell.eq_cast_iff_heq]
    exact (vComp_congr_heq (by simp) (by simp) (by simp) (by simp)
        (Cell.cast_heq _ _ _) (Cell.cast_heq _ _ _)).trans <|
      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
        (vComp_assoc_heq _ _ _).symm.trans <|
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (PseudoDoubleCategory.lRightUnitorInv_lRightUnitor_heq _)
          HEq.rfl).trans
        (PseudoDoubleCategory.vId_vComp_heq _)).trans
      (PseudoDoubleCategory.lLeftUnitor_lLeftUnitorInv_heq _)

section Comp

variable {H : LaxDoubleFunctor C D}

def compNatCell (σ : LooseTransformation F G) (τ : LooseTransformation G H)
    {a b : C} (m : Loose a b) :
    Cell (F.mapLoose m ⊙ σ.app b ⊙ τ.app b)
      ((σ.app a ⊙ τ.app a) ⊙ H.mapLoose m)
      (𝟙 (F.obj a)) (𝟙 (H.obj b)) :=
  (lAssocInv (F.mapLoose m) (σ.app b) (τ.app b) ≫ᵥ
    (σ.natCell m ⊚ vId (τ.app b)) ≫ᵥ
    lAssoc (σ.app a) (G.mapLoose m) (τ.app b) ≫ᵥ
    (vId (σ.app a) ⊚ τ.natCell m) ≫ᵥ
    lAssocInv (σ.app a) (τ.app a) (H.mapLoose m)).cast
      (f' := 𝟙 (F.obj a)) (g' := 𝟙 (H.obj b)) (by simp) (by simp)

variable (σ : LooseTransformation F G) (τ : LooseTransformation G H)

theorem compNatCell_natural {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (α : Cell m n f g) :
    (F.mapCell α ⊚ (σ.cellApp g ⊚ τ.cellApp g)) ≫ᵥ compNatCell σ τ n ≍
      compNatCell σ τ m ≫ᵥ
        ((σ.cellApp f ⊚ τ.cellApp f) ⊚ H.mapCell α) := by
  exact

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans <|

    (vComp_assoc_heq _ _ _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (lAssocInv_natural_heq (F.mapCell α) (σ.cellApp g) (τ.cellApp g))
      HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (F.mapCell α ⊚ σ.cellApp g) (τ.cellApp g)
          (σ.natCell n) (vId (τ.app d)))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            (σ.natCell_natural_heq α)
            ((vComp_vId_heq (τ.cellApp g)).trans
              (vId_vComp_heq (τ.cellApp g)).symm)).trans
          (heq_of_eq (interchange (σ.natCell m) (vId (τ.app b))
            (σ.cellApp f ⊚ G.mapCell α) (τ.cellApp g))))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq (σ.cellApp f) (G.mapCell α) (τ.cellApp g))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (σ.cellApp f) (G.mapCell α ⊚ τ.cellApp g)
          (vId (σ.app c)) (τ.natCell n))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            ((vComp_vId_heq (σ.cellApp f)).trans
              (vId_vComp_heq (σ.cellApp f)).symm)
            (τ.natCell_natural_heq α)).trans
          (heq_of_eq (interchange (vId (σ.app a)) (τ.natCell m)
            (σ.cellApp f) (τ.cellApp f ⊚ H.mapCell α))))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      lAssocInv_natural_heq (σ.cellApp f) (τ.cellApp f)
        (H.mapCell α)).trans <|

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

open Bicategory in

theorem compIdTube {B : Type u₁} [Bicategory.{t₁, w₁} B] {a b c : B}
    (p : a ⟶ b) (q : b ⟶ c) :
    (α_ (𝟙 a) p q).inv ≫
        ((((λ_ p).hom ≫ (ρ_ p).inv) ▷ q) ≫
          ((α_ p (𝟙 b) q).hom ≫
            ((p ◁ ((λ_ q).hom ≫ (ρ_ q).inv)) ≫
              (α_ p q (𝟙 c)).inv))) =
      (λ_ (p ≫ q)).hom ≫ (ρ_ (p ≫ q)).inv := by
  bicategory

theorem comp_id_tube {a b c : D} (p : Loose a b) (q : Loose b c) :
    lAssocInv (𝟙ˡ a) p q ≫ᵥ
        ((lLeftUnitor p ≫ᵥ lRightUnitorInv p).cast
          (f' := 𝟙 a) (g' := 𝟙 b) (by simp) (by simp) ⊚ vId q) ≫ᵥ
        lAssoc p (𝟙ˡ b) q ≫ᵥ
        (vId p ⊚ (lLeftUnitor q ≫ᵥ lRightUnitorInv q).cast
          (f' := 𝟙 b) (g' := 𝟙 c) (by simp) (by simp)) ≫ᵥ
        lAssocInv p q (𝟙ˡ c) ≍
      lLeftUnitor (p ⊙ q) ≫ᵥ lRightUnitorInv (p ⊙ q) := by
  have h := compIdTube (show (LooseBicat.mk a : LooseBicat D) ⟶
    LooseBicat.mk b from p)
    (show (LooseBicat.mk b : LooseBicat D) ⟶ LooseBicat.mk c from q)
  rw [globularComp_def, globularComp_def, globularComp_def,
    globularComp_def, globularComp_def, globularComp_def,
    globularComp_def] at h
  simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
  exact (Cell.cast_eq_iff_heq.mp h).trans (Cell.cast_heq _ _ _)

theorem compNatCell_laxId (a : C) :
    (F.laxId a ⊚ vId (σ.app a ⊙ τ.app a)) ≫ᵥ compNatCell σ τ (𝟙ˡ a) ≍
      lLeftUnitor (σ.app a ⊙ τ.app a) ≫ᵥ
        lRightUnitorInv (σ.app a ⊙ τ.app a) ≫ᵥ
        (vId (σ.app a ⊙ τ.app a) ⊚ H.laxId a) := by
  exact

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans <|

    (vComp_assoc_heq _ _ _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      ((vComp_congr_heq rfl rfl rfl rfl
        (hComp_congr_heq rfl rfl rfl HEq.rfl
          (heq_of_eq (hComp_vId (σ.app a) (τ.app a)).symm)) HEq.rfl).trans
        (lAssocInv_natural_heq (F.laxId a) (vId (σ.app a))
          (vId (τ.app a))))
      HEq.rfl).trans <|
    (vComp_assoc_heq _ _ _).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (F.laxId a ⊚ vId (σ.app a))
          (vId (τ.app a)) (σ.natCell (𝟙ˡ a)) (vId (τ.app a)))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            ((σ.natCell_laxId_heq a).trans
              (vComp_assoc_heq _ _ _).symm)
            (vComp_vId_heq (vId (τ.app a) ≫ᵥ vId (τ.app a))).symm).trans <|
          (heq_of_eq (interchange
            (lLeftUnitor (σ.app a) ≫ᵥ lRightUnitorInv (σ.app a))
            (vId (τ.app a) ≫ᵥ vId (τ.app a))
            (vId (σ.app a) ⊚ G.laxId a) (vId (τ.app a)))).trans
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            (hComp_congr_heq (by simp) (by simp) (by simp)
              (Cell.cast_heq _ _ _).symm
              (vComp_vId_heq (vId (τ.app a))))
            HEq.rfl))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (lAssoc_natural_heq (vId (σ.app a)) (G.laxId a)
          (vId (τ.app a)))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((heq_of_eq (interchange (vId (σ.app a)) (G.laxId a ⊚ vId (τ.app a))
          (vId (σ.app a)) (τ.natCell (𝟙ˡ a)))).symm.trans <|
          (hComp_congr_heq (by simp) (by simp) (by simp)
            (vComp_vId_heq (vId (σ.app a) ≫ᵥ vId (σ.app a))).symm
            ((τ.natCell_laxId_heq a).trans
              (vComp_assoc_heq _ _ _).symm)).trans <|
          (heq_of_eq (interchange
            (vId (σ.app a) ≫ᵥ vId (σ.app a))
            (lLeftUnitor (τ.app a) ≫ᵥ lRightUnitorInv (τ.app a))
            (vId (σ.app a))
            (vId (τ.app a) ⊚ H.laxId a))).trans
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            (hComp_congr_heq (by simp) (by simp) (by simp)
              (vComp_vId_heq (vId (σ.app a)))
              (Cell.cast_heq _ _ _).symm)
            HEq.rfl))
        HEq.rfl).trans <|
      (vComp_assoc_heq _ _ _)).trans <|

    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl <|
      (lAssocInv_natural_heq (vId (σ.app a)) (vId (τ.app a))
        (H.laxId a)).trans <|
      vComp_congr_heq rfl rfl rfl rfl HEq.rfl
        (hComp_congr_heq rfl rfl rfl
          (heq_of_eq (hComp_vId (σ.app a) (τ.app a))) HEq.rfl)).trans <|

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
      (comp_id_tube (σ.app a) (τ.app a)) HEq.rfl).trans
    (vComp_assoc_heq _ _ _)

open Bicategory in

theorem compLaxTube {B : Type u₁} [Bicategory.{t₁, w₁} B]
    {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : B}
    {fm : x₁ ⟶ x₂} {fn : x₂ ⟶ x₃} {fmn : x₁ ⟶ x₃}
    {gm : y₁ ⟶ y₂} {gn : y₂ ⟶ y₃} {gmn : y₁ ⟶ y₃}
    {hm : z₁ ⟶ z₂} {hn : z₂ ⟶ z₃} {hmn : z₁ ⟶ z₃}
    {sa : x₁ ⟶ y₁} {sb : x₂ ⟶ y₂} {sc : x₃ ⟶ y₃}
    {ta : y₁ ⟶ z₁} {tb : y₂ ⟶ z₂} {tc : y₃ ⟶ z₃}
    {cF : fm ≫ fn ⟶ fmn} {cG : gm ≫ gn ⟶ gmn} {cH : hm ≫ hn ⟶ hmn}
    {Sm : fm ≫ sb ⟶ sa ≫ gm} {Sn : fn ≫ sc ⟶ sb ≫ gn}
    {Smn : fmn ≫ sc ⟶ sa ≫ gmn}
    {Tm : gm ≫ tb ⟶ ta ≫ hm} {Tn : gn ≫ tc ⟶ tb ≫ hn}
    {Tmn : gmn ≫ tc ⟶ ta ≫ hmn}
    (hS : cF ▷ sc ≫ Smn =
      (α_ fm fn sc).hom ≫ fm ◁ Sn ≫ (α_ fm sb gn).inv ≫ Sm ▷ gn ≫
        (α_ sa gm gn).hom ≫ sa ◁ cG)
    (hT : cG ▷ tc ≫ Tmn =
      (α_ gm gn tc).hom ≫ gm ◁ Tn ≫ (α_ gm tb hn).inv ≫ Tm ▷ hn ≫
        (α_ ta hm hn).hom ≫ ta ◁ cH) :
    cF ▷ (sc ≫ tc) ≫
        ((α_ fmn sc tc).inv ≫ Smn ▷ tc ≫ (α_ sa gmn tc).hom ≫
          sa ◁ Tmn ≫ (α_ sa ta hmn).inv) =
      (α_ fm fn (sc ≫ tc)).hom ≫
        fm ◁ ((α_ fn sc tc).inv ≫ Sn ▷ tc ≫ (α_ sb gn tc).hom ≫
          sb ◁ Tn ≫ (α_ sb tb hn).inv) ≫
        (α_ fm (sb ≫ tb) hn).inv ≫
        ((α_ fm sb tb).inv ≫ Sm ▷ tb ≫ (α_ sa gm tb).hom ≫
          sa ◁ Tm ≫ (α_ sa ta hm).inv) ▷ hn ≫
        (α_ (sa ≫ ta) hm hn).hom ≫
        (sa ≫ ta) ◁ cH :=
  calc
    _ = 𝟙 _ ⊗≫ (cF ▷ sc ≫ Smn) ▷ tc ⊗≫ sa ◁ Tmn ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (fm ◁ Sn ⊗≫ Sm ▷ gn) ▷ tc ⊗≫
          sa ◁ (cG ▷ tc ≫ Tmn) ⊗≫ 𝟙 _ := by
      rw [hS]
      bicategory
    _ = 𝟙 _ ⊗≫ fm ◁ Sn ▷ tc ⊗≫
          (Sm ▷ (gn ≫ tc) ≫ (sa ≫ gm) ◁ Tn) ⊗≫
          sa ◁ (Tm ▷ hn ⊗≫ ta ◁ cH) ⊗≫ 𝟙 _ := by
      rw [hT]
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

open Bicategory in

theorem compNatCell_laxComp {a b c : C} (m : Loose a b) (n : Loose b c) :
    (F.laxComp m n ⊚ vId (σ.app c ⊙ τ.app c)) ≫ᵥ
        compNatCell σ τ (m ⊙ n) ≍
      lAssoc (F.mapLoose m) (F.mapLoose n) (σ.app c ⊙ τ.app c) ≫ᵥ
        (vId (F.mapLoose m) ⊚ compNatCell σ τ n) ≫ᵥ
        lAssocInv (F.mapLoose m) (σ.app b ⊙ τ.app b) (H.mapLoose n) ≫ᵥ
        (compNatCell σ τ m ⊚ vId (H.mapLoose n)) ≫ᵥ
        lAssoc (σ.app a ⊙ τ.app a) (H.mapLoose m) (H.mapLoose n) ≫ᵥ
        (vId (σ.app a ⊙ τ.app a) ⊚ H.laxComp m n) := by
  have hS : F.laxComp m n ▷
      (show (LooseBicat.mk (F.obj c) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj c) from σ.app c) ≫ σ.natCell (m ⊙ n) =
      (α_ (show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (F.obj b) from F.mapLoose m)
        (F.mapLoose n) (σ.app c)).hom ≫
      (show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (F.obj b) from F.mapLoose m) ◁ σ.natCell n ≫
      (α_ (show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (F.obj b) from F.mapLoose m)
        (show (LooseBicat.mk (F.obj b) : LooseBicat D) ⟶
          LooseBicat.mk (G.obj b) from σ.app b) (G.mapLoose n)).inv ≫
      σ.natCell m ▷ (show (LooseBicat.mk (G.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj c) from G.mapLoose n) ≫
      (α_ (show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (G.obj a) from σ.app a)
        (G.mapLoose m) (G.mapLoose n)).hom ≫
      (show (LooseBicat.mk (F.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj a) from σ.app a) ◁ G.laxComp m n := by
    repeat rw [globularComp_def]
    simp only [vComp_cast, cast_vComp, Cell.cast_cast]
    rw [Cell.cast_eq_iff_heq]
    exact (σ.natCell_laxComp_heq m n).trans <|
      ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm)
  have hT : G.laxComp m n ▷
      (show (LooseBicat.mk (G.obj c) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj c) from τ.app c) ≫ τ.natCell (m ⊙ n) =
      (α_ (show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (G.obj b) from G.mapLoose m)
        (G.mapLoose n) (τ.app c)).hom ≫
      (show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (G.obj b) from G.mapLoose m) ◁ τ.natCell n ≫
      (α_ (show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (G.obj b) from G.mapLoose m)
        (show (LooseBicat.mk (G.obj b) : LooseBicat D) ⟶
          LooseBicat.mk (H.obj b) from τ.app b) (H.mapLoose n)).inv ≫
      τ.natCell m ▷ (show (LooseBicat.mk (H.obj b) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj c) from H.mapLoose n) ≫
      (α_ (show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
          LooseBicat.mk (H.obj a) from τ.app a)
        (H.mapLoose m) (H.mapLoose n)).hom ≫
      (show (LooseBicat.mk (G.obj a) : LooseBicat D) ⟶
        LooseBicat.mk (H.obj a) from τ.app a) ◁ H.laxComp m n := by
    repeat rw [globularComp_def]
    simp only [vComp_cast, cast_vComp, Cell.cast_cast]
    rw [Cell.cast_eq_iff_heq]
    exact (τ.natCell_laxComp_heq m n).trans <|
      ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl <|
        (Cell.cast_heq _ _ _).symm).trans
      (Cell.cast_heq _ _ _).symm)
  have h := compLaxTube hS hT
  repeat rw [globularComp_def] at h
  simp only [vComp_cast, cast_vComp, Cell.cast_cast] at h
  exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans <|
    (Cell.cast_eq_iff_heq.mp h).trans (Cell.cast_heq _ _ _)

def comp (σ : LooseTransformation F G) (τ : LooseTransformation G H) :
    LooseTransformation F H where
  app a := σ.app a ⊙ τ.app a
  cellApp f := σ.cellApp f ⊚ τ.cellApp f
  natCell m := compNatCell σ τ m
  cellApp_id a := by
    rw [Cell.eq_cast_iff_heq]
    exact (hComp_congr_heq (F.map_id a) (G.map_id a) (H.map_id a)
        (σ.cellApp_id_heq a) (τ.cellApp_id_heq a)).trans
      (heq_of_eq (PseudoDoubleCategory.hComp_vId _ _))
  cellApp_comp {a b c} f g := by
    rw [Cell.eq_cast_iff_heq]
    exact (hComp_congr_heq (F.map_comp f g) (G.map_comp f g)
        (H.map_comp f g)
        (σ.cellApp_comp_heq f g) (τ.cellApp_comp_heq f g)).trans
      (heq_of_eq (PseudoDoubleCategory.interchange (σ.cellApp f)
        (τ.cellApp f) (σ.cellApp g) (τ.cellApp g)))
  natCell_natural {a b c d} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact compNatCell_natural σ τ α
  natCell_laxId a := by
    rw [Cell.eq_cast_iff_heq]
    exact compNatCell_laxId σ τ a
  natCell_laxComp {a b c} m n := by
    rw [Cell.eq_cast_iff_heq]
    exact compNatCell_laxComp σ τ m n

@[simp]
theorem comp_app (a : C) : (σ.comp τ).app a = σ.app a ⊙ τ.app a := rfl

@[simp]
theorem comp_cellApp {a b : C} (f : a ⟶ b) :
    (σ.comp τ).cellApp f = σ.cellApp f ⊚ τ.cellApp f := rfl

theorem comp_natCell {a b : C} (m : Loose a b) :
    (σ.comp τ).natCell m = compNatCell σ τ m := rfl

end Comp

end LooseTransformation

end CategoryTheory
