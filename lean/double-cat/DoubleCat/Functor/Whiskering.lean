import DoubleCat.Functor.Composition
import DoubleCat.Transformation

/-!
# Whiskering of tight transformations

Given a tight transformation `σ : F ⟶ G` between lax double functors
`C → D` and lax double functors `H : D → E` (resp. `B → C`), this file
constructs the whiskered transformations
`σ.whiskerRight H : F.comp H ⟶ G.comp H` and
`whiskerLeft H σ : H.comp F ⟶ H.comp G`, proves that both whiskerings are
functorial (they preserve identities and vertical composition), and proves
the exchange law relating them.  Together with the hom-categories of
`DoubleCat.Transformation` and the composition laws for lax double functors
proved here (`LaxDoubleFunctor.comp_id`, `id_comp`, `assoc`, via the
extensionality lemma `LaxDoubleFunctor.ext'`), this is the strict
2-category of pseudo double categories, lax double functors, and tight
transformations (Grandis–Paré, "Adjoint for double categories", 2004;
Cruttwell–Lambert–Pronk–Szyld, "Double fibrations", 2022, §2.2), presented
at the level of its operations; the bundled bicategory is in
`DoubleCat.Dbl`.

## Proof technique

The coherence chases are heterogeneous-equality chases in the style of
`DoubleCat.Functor.Composition` (see the technique note there: `calc`
cannot chain heterogeneous steps, so chains are right-nested `HEq.trans`;
casts are stripped and reintroduced only where a boundary is
re-normalized).  The equality of lax double functors asserted by the
composition laws is legitimate here despite functor-equality being evil in
general: the underlying tight functors of the two sides are definitionally
equal (`Functor.comp_id` and friends are `rfl`), and only the laxator
fields differ, propositionally; `LaxDoubleFunctor.ext'` reduces the
equality to componentwise heterogeneous equalities.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w₀ t₀ v₀ u₀ w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂ w₃ t₃ v₃ u₃

variable {B : Type u₀} [Category.{v₀} B] [PseudoDoubleCategoryStruct B]
  [PseudoDoubleCategory B]
variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]
variable {E : Type u₃} [Category.{v₃} E] [PseudoDoubleCategoryStruct E]
  [PseudoDoubleCategory E]

namespace TightTransformation

variable {F G K : LaxDoubleFunctor C D}

/-- Whisker a tight transformation on the right by a lax double functor:
`(σ.whiskerRight H).app a = H.map (σ.app a)` and
`(σ.whiskerRight H).looseApp m = H.mapCell (σ.looseApp m)`. -/
def whiskerRight (σ : TightTransformation F G) (H : LaxDoubleFunctor D E) :
    TightTransformation (F.comp H) (G.comp H) where
  app a := H.map (σ.app a)
  naturality {a b} f := by
    show H.map (F.map f) ≫ H.map (σ.app b) = H.map (σ.app a) ≫ H.map (G.map f)
    rw [← H.map_comp, ← H.map_comp, σ.naturality]
  looseApp m := H.mapCell (σ.looseApp m)
  looseApp_natural {a b c d} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (H.mapCell_vComp_heq (F.mapCell α) (σ.looseApp n)).symm.trans <|

      (H.mapCell_congr_heq (σ.naturality f) (σ.naturality g)
        (σ.looseApp_natural_heq α)).trans

      (H.mapCell_vComp_heq (σ.looseApp m) (G.mapCell α))
  looseApp_laxComp {a b c} m n := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_congr_heq (by boundary) (by boundary)
          (σ.looseApp_laxComp_heq m n))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (H.laxComp_natural_heq (σ.looseApp m) (σ.looseApp n)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)
  looseApp_laxId a := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_congr_heq (by boundary) (by boundary)
          (σ.looseApp_laxId_heq a))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (H.laxId_natural_heq (σ.app a)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)

/-- Whisker a tight transformation on the left by a lax double functor:
`(whiskerLeft H σ).app a = σ.app (H.obj a)` and
`(whiskerLeft H σ).looseApp m = σ.looseApp (H.mapLoose m)`. -/
def whiskerLeft (H : LaxDoubleFunctor B C) (σ : TightTransformation F G) :
    TightTransformation (H.comp F) (H.comp G) where
  app a := σ.app (H.obj a)
  naturality {a b} f := σ.naturality (H.map f)
  looseApp m := σ.looseApp (H.mapLoose m)
  looseApp_natural {a b c d} {m n} {f g} α := by
    rw [Cell.eq_cast_iff_heq]
    exact σ.looseApp_natural_heq (H.mapCell α)
  looseApp_laxComp {a b c} m n := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (σ.looseApp_natural_heq (H.laxComp m n))).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (σ.looseApp_laxComp_heq (H.mapLoose m) (H.mapLoose n)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)
  looseApp_laxId a := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (σ.looseApp_natural_heq (H.laxId a))).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (σ.looseApp_laxId_heq (H.obj a)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)

@[simp]
theorem whiskerRight_app (σ : TightTransformation F G)
    (H : LaxDoubleFunctor D E) (a : C) :
    (σ.whiskerRight H).app a = H.map (σ.app a) := rfl

@[simp]
theorem whiskerRight_looseApp (σ : TightTransformation F G)
    (H : LaxDoubleFunctor D E) {a b : C} (m : Loose a b) :
    (σ.whiskerRight H).looseApp m = H.mapCell (σ.looseApp m) := rfl

@[simp]
theorem whiskerLeft_app (H : LaxDoubleFunctor B C)
    (σ : TightTransformation F G) (a : B) :
    (whiskerLeft H σ).app a = σ.app (H.obj a) := rfl

@[simp]
theorem whiskerLeft_looseApp (H : LaxDoubleFunctor B C)
    (σ : TightTransformation F G) {a b : B} (m : Loose a b) :
    (whiskerLeft H σ).looseApp m = σ.looseApp (H.mapLoose m) := rfl

theorem id_whiskerRight (F : LaxDoubleFunctor C D)
    (H : LaxDoubleFunctor D E) :
    (TightTransformation.id F).whiskerRight H =
      TightTransformation.id (F.comp H) :=
  ext (fun a => by simp) (fun m => H.mapCell_vId_heq (F.mapLoose m))

theorem vcomp_whiskerRight (σ : TightTransformation F G)
    (τ : TightTransformation G K) (H : LaxDoubleFunctor D E) :
    (σ.vcomp τ).whiskerRight H =
      (σ.whiskerRight H).vcomp (τ.whiskerRight H) :=
  ext (fun a => by simp) (fun m => H.mapCell_vComp_heq _ _)

theorem whiskerLeft_id (H : LaxDoubleFunctor B C) (F : LaxDoubleFunctor C D) :
    whiskerLeft H (TightTransformation.id F) =
      TightTransformation.id (H.comp F) :=
  ext (fun _ => rfl) (fun _ => HEq.rfl)

theorem whiskerLeft_vcomp (H : LaxDoubleFunctor B C)
    (σ : TightTransformation F G) (τ : TightTransformation G K) :
    whiskerLeft H (σ.vcomp τ) =
      (whiskerLeft H σ).vcomp (whiskerLeft H τ) :=
  ext (fun _ => rfl) (fun _ => HEq.rfl)

/-- The exchange law: whiskering a transformation on the left and on the right
in either order gives the same composite. -/
theorem whisker_exchange {H K : LaxDoubleFunctor D E}
    (σ : TightTransformation F G) (τ : TightTransformation H K) :
    (σ.whiskerRight H).vcomp (whiskerLeft G τ) =
      (whiskerLeft F τ).vcomp (σ.whiskerRight K) :=
  ext (fun a => τ.naturality (σ.app a))
    (fun m => τ.looseApp_natural_heq (σ.looseApp m))

@[simp]
theorem cat_id_app (F : LaxDoubleFunctor C D) (a : C) :
    (𝟙 F : TightTransformation F F).app a = 𝟙 (F.obj a) := rfl

@[simp]
theorem cat_id_looseApp (F : LaxDoubleFunctor C D) {a b : C}
    (m : Loose a b) :
    (𝟙 F : TightTransformation F F).looseApp m = vId (F.mapLoose m) := rfl

@[simp]
theorem cat_comp_app (σ : F ⟶ G) (τ : G ⟶ K) (a : C) :
    (σ ≫ τ).app a = σ.app a ≫ τ.app a := rfl

@[simp]
theorem cat_comp_looseApp (σ : F ⟶ G) (τ : G ⟶ K) {a b : C}
    (m : Loose a b) :
    (σ ≫ τ).looseApp m = σ.looseApp m ≫ᵥ τ.looseApp m := rfl

end TightTransformation

namespace LaxDoubleFunctor

omit [PseudoDoubleCategory C] [PseudoDoubleCategory D] in

/-- Extensionality for lax double functors: two lax double functors are equal
as soon as their underlying functors, loose actions, and cell actions agree
definitionally and their laxators agree heterogeneously.  This is the
workhorse for the strict composition laws: the sides agree on all data and
differ only propositionally in the laxator proofs. -/
theorem ext' {F G : LaxDoubleFunctor C D}
    (hFun : F.toFunctor = G.toFunctor)
    (hLoose : ∀ {a b : C} (m : Loose a b), F.mapLoose m ≍ G.mapLoose m)
    (hCell : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d} {f : a ⟶ c}
      {g : b ⟶ d} (α : Cell m n f g), F.mapCell α ≍ G.mapCell α)
    (hComp : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
      F.laxComp m n ≍ G.laxComp m n)
    (hId : ∀ a : C, F.laxId a ≍ G.laxId a) : F = G := by
  obtain ⟨tf, ml, mc, _, _, lc, li, _, _, _, _, _⟩ := F
  obtain ⟨tf', ml', mc', _, _, lc', li', _, _, _, _, _⟩ := G
  subst hFun
  have hml : @ml = @ml' := by
    funext a b m
    exact eq_of_heq (hLoose m)
  subst hml
  have hmc : @mc = @mc' := by
    funext a b c d m n f g α
    exact eq_of_heq (hCell α)
  subst hmc
  have hlc : @lc = @lc' := by
    funext a b c m n
    exact eq_of_heq (hComp m n)
  subst hlc
  have hli : li = li' := by
    funext a
    exact eq_of_heq (hId a)
  subst hli
  rfl

theorem comp_id (F : LaxDoubleFunctor C D) :
    F.comp (LaxDoubleFunctor.id) = F :=
  ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun m n =>
      (Cell.cast_heq _ _ _).trans
        (PseudoDoubleCategory.vId_vComp_heq (F.laxComp m n)))
    (fun a =>
      (Cell.cast_heq _ _ _).trans
        (PseudoDoubleCategory.vId_vComp_heq (F.laxId a)))

theorem id_comp (F : LaxDoubleFunctor C D) :
    (LaxDoubleFunctor.id).comp F = F :=
  ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun m n =>
      (Cell.cast_heq _ _ _).trans <|
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (F.mapCell_vId_heq (m ⊙ n))).trans
        (PseudoDoubleCategory.vComp_vId_heq (F.laxComp m n)))
    (fun a =>
      (Cell.cast_heq _ _ _).trans <|
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (F.mapCell_vId_heq (lId a))).trans
        (PseudoDoubleCategory.vComp_vId_heq (F.laxId a)))

theorem comp_assoc (F : LaxDoubleFunctor B C) (G : LaxDoubleFunctor C D)
    (H : LaxDoubleFunctor D E) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  ext' rfl (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun m n =>

      (Cell.cast_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_congr_heq (by boundary) (by boundary)
          (Cell.cast_heq _ _ _))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl).trans

      (Cell.cast_heq _ _ _).symm)
    (fun a =>
      (Cell.cast_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_congr_heq (by boundary) (by boundary)
          (Cell.cast_heq _ _ _))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (H.mapCell_vComp_heq _ _)).trans <|
      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _).symm HEq.rfl).trans
      (Cell.cast_heq _ _ _).symm)

end LaxDoubleFunctor

end CategoryTheory
