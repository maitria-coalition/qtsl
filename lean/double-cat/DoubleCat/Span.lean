import DoubleCat.Basic
import DoubleCat.Companion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The double category of spans

For a category `C` with pullbacks, the pseudo double category `Span C` has
the objects of `C` as objects, the morphisms of `C` as tight arrows, spans
`a ⟵ s ⟶ b` in `C` as loose arrows (composing by chosen pullback), and
morphisms of apexes compatible with the tight boundaries as cells.  This is
the motivating example of a pseudo double category (Grandis–Paré, "Limits
in double categories", 1999): loose composition is associative and unital
only up to the coherent isomorphisms provided by the universal property of
the pullback.

It is also the fundamental example of a proarrow equipment (Shulman,
"Framed bicategories and monoidal fibrations", 2008, Example 2.8): every
tight arrow `f : a ⟶ b` has a companion (the graph span `a ⟵ a ⟶ b` with
legs `𝟙 a` and `f`) and a conjoint (the cograph span `b ⟵ a ⟶ a`) — in
contrast to the double category of commutative squares, where conjoints
exist only for isomorphisms.

## Main definitions

* `CategoryTheory.Span`: a type synonym for `C` carrying the double
  category structure.
* `CategoryTheory.SpanArrow`: spans `a ⟵ s ⟶ b`, the loose arrows.
* `CategoryTheory.SpanCell`: morphisms of apexes commuting with the legs
  up to the tight boundary arrows, the cells.
* `CategoryTheory.Span.instPseudoDoubleCategory`: the pseudo double
  category axioms.  Unlike in the double category of commutative squares,
  the cells of `Span C` carry data (the apex morphism), so the axioms are
  genuine equations, proved by the universal property of the pullback.
* `CategoryTheory.Span.instEquipment`: the equipment structure.

## Implementation notes

Cell equations are proved by reducing heterogeneous equality of cells to
equality of apex morphisms (`SpanCell.heq_of_hom`) and then applying the
uniqueness clause of the pullback's universal property.  The section is
`noncomputable` because loose composition chooses pullbacks.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct Limits

noncomputable section

universe v u

variable (C : Type u) [Category.{v} C]

/-- The double category of spans in `C`: a type synonym for `C` carrying the
`PseudoDoubleCategory` instance whose loose arrows are spans and whose cells
are morphisms of apexes. -/
def Span (C : Type u) := C

namespace Span

instance : Category.{v} (Span C) := inferInstanceAs (Category C)

variable {C}

/-- Interpret an object of `C` as an object of `Span C`. -/
def mk (a : C) : Span C := a

/-- Interpret an object of `Span C` as an object of `C`. -/
def unmk (a : Span C) : C := a

instance [HasPullbacks C] : HasPullbacks (Span C) :=
  inferInstanceAs (HasPullbacks C)

end Span

variable {C}

/-- A span `a ⟵ s ⟶ b` in `C`: the loose arrows of the double category of
spans. -/
structure SpanArrow (a b : Span C) : Type (max u v) where

  apex : Span C

  l : apex ⟶ a

  r : apex ⟶ b

namespace SpanArrow

/-- The identity span `a ⟵ a ⟶ a`. -/
@[reducible, simps l r]
def id (a : Span C) : SpanArrow a a where
  apex := a
  l := 𝟙 a
  r := 𝟙 a

/-- The graph span of a tight arrow: `a ⟵ a ⟶ b` with legs `𝟙 a` and `f`.
This is the companion of `f`. -/
@[reducible, simps l r]
def graph {a b : Span C} (f : a ⟶ b) : SpanArrow a b where
  apex := a
  l := 𝟙 a
  r := f

/-- The cograph span of a tight arrow: `b ⟵ a ⟶ a` with legs `f` and `𝟙 a`.
This is the conjoint of `f`. -/
@[reducible, simps l r]
def cograph {a b : Span C} (f : a ⟶ b) : SpanArrow b a where
  apex := a
  l := f
  r := 𝟙 a

variable [HasPullbacks C]

/-- Composition of spans by (chosen) pullback. -/
@[reducible, simps l r]
def comp {a b c : Span C} (m : SpanArrow a b) (n : SpanArrow b c) :
    SpanArrow a c where
  apex := pullback m.r n.l
  l := pullback.fst m.r n.l ≫ m.l
  r := pullback.snd m.r n.l ≫ n.r

@[reassoc (attr := simp)]
theorem snd_id_l {a b : Span C} (m : SpanArrow a b) :
    pullback.snd (𝟙 a) m.l ≫ m.l = pullback.fst (𝟙 a) m.l :=
  pullback.condition.symm.trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem fst_id_r {a b : Span C} (m : SpanArrow a b) :
    pullback.fst m.r (𝟙 b) ≫ m.r = pullback.snd m.r (𝟙 b) :=
  pullback.condition.trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem condition_comp_left {a b c d : Span C} (m : SpanArrow a b)
    (n : SpanArrow b c) (p : SpanArrow c d) :
    pullback.fst (m.comp n).r p.l ≫ (pullback.snd m.r n.l ≫ n.r) =
      pullback.snd (m.comp n).r p.l ≫ p.l :=
  pullback.condition

@[reassoc (attr := simp)]
theorem condition_comp_right {a b c d : Span C} (m : SpanArrow a b)
    (n : SpanArrow b c) (p : SpanArrow c d) :
    pullback.fst m.r (n.comp p).l ≫ m.r =
      pullback.snd m.r (n.comp p).l ≫ (pullback.fst n.r p.l ≫ n.l) :=
  pullback.condition

end SpanArrow

/-- A cell between spans: a morphism of apexes whose leg composites commute
with the tight boundary arrows. -/
structure SpanCell {a b c d : Span C} (m : SpanArrow a b) (n : SpanArrow c d)
    (f : a ⟶ c) (g : b ⟶ d) : Type v where

  hom : m.apex ⟶ n.apex

  hom_l : hom ≫ n.l = m.l ≫ f

  hom_r : hom ≫ n.r = m.r ≫ g

attribute [reassoc (attr := simp)] SpanCell.hom_l SpanCell.hom_r

namespace SpanCell

@[ext]
theorem ext {a b c d : Span C} {m : SpanArrow a b} {n : SpanArrow c d}
    {f : a ⟶ c} {g : b ⟶ d} {α β : SpanCell m n f g}
    (h : α.hom = β.hom) : α = β := by
  cases α; cases β; cases h; rfl

/-- Cells between spans are heterogeneously equal as soon as their apex
morphisms are (with equal boundaries); the workhorse for the axiom proofs. -/
theorem heq_of_hom {a b c d : Span C} {m : SpanArrow a b}
    {n : SpanArrow c d} {f f' : a ⟶ c} {g g' : b ⟶ d}
    {α : SpanCell m n f g} {β : SpanCell m n f' g'}
    (hf : f = f') (hg : g = g') (h : α.hom = β.hom) : α ≍ β := by
  subst hf; subst hg
  exact heq_of_eq (SpanCell.ext h)

local macro "span_simp" : tactic =>
  `(tactic| (simp [pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      pullback.condition, pullback.condition_assoc,
      SpanArrow.snd_id_l, SpanArrow.fst_id_r,
      SpanArrow.snd_id_l_assoc, SpanArrow.fst_id_r_assoc]) <;> try rfl)

variable {a b c d : Span C}

@[simps hom]
def vId (m : SpanArrow a b) : SpanCell m m (𝟙 a) (𝟙 b) where
  hom := 𝟙 m.apex
  hom_l := by simp
  hom_r := by simp

@[simps hom]
def vComp {a₁ b₁ a₂ b₂ a₃ b₃ : Span C}
    {m₁ : SpanArrow a₁ b₁} {m₂ : SpanArrow a₂ b₂} {m₃ : SpanArrow a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (α : SpanCell m₁ m₂ f₁ g₁) (β : SpanCell m₂ m₃ f₂ g₂) :
    SpanCell m₁ m₃ (f₁ ≫ f₂) (g₁ ≫ g₂) where
  hom := α.hom ≫ β.hom
  hom_l := by simp
  hom_r := by simp

@[simps hom]
def hId {a b : Span C} (f : a ⟶ b) :
    SpanCell (SpanArrow.id a) (SpanArrow.id b) f f where
  hom := f
  hom_l := by simp
  hom_r := by simp

variable [HasPullbacks C]

@[simps hom]
def hComp {a₁ a₂ a₃ b₁ b₂ b₃ : Span C}
    {m₁ : SpanArrow a₁ a₂} {m₂ : SpanArrow a₂ a₃}
    {n₁ : SpanArrow b₁ b₂} {n₂ : SpanArrow b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : SpanCell m₁ n₁ f g) (β : SpanCell m₂ n₂ g h) :
    SpanCell (m₁.comp m₂) (n₁.comp n₂) f h where
  hom := pullback.lift (pullback.fst m₁.r m₂.l ≫ α.hom)
    (pullback.snd m₁.r m₂.l ≫ β.hom) (by span_simp)
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def assoc {a b c d : Span C} (m : SpanArrow a b) (n : SpanArrow b c)
    (p : SpanArrow c d) :
    SpanCell ((m.comp n).comp p) (m.comp (n.comp p)) (𝟙 a) (𝟙 d) where
  hom := pullback.lift
    (pullback.fst (m.comp n).r p.l ≫ pullback.fst m.r n.l)
    (pullback.lift
      (pullback.fst (m.comp n).r p.l ≫ pullback.snd m.r n.l)
      (pullback.snd (m.comp n).r p.l)
      (by span_simp))
    (by span_simp)
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def assocInv {a b c d : Span C} (m : SpanArrow a b) (n : SpanArrow b c)
    (p : SpanArrow c d) :
    SpanCell (m.comp (n.comp p)) ((m.comp n).comp p) (𝟙 a) (𝟙 d) where
  hom := pullback.lift
    (pullback.lift
      (pullback.fst m.r (n.comp p).l)
      (pullback.snd m.r (n.comp p).l ≫ pullback.fst n.r p.l)
      (by span_simp))
    (pullback.snd m.r (n.comp p).l ≫ pullback.snd n.r p.l)
    (by span_simp)
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def leftUnitor {a b : Span C} (m : SpanArrow a b) :
    SpanCell ((SpanArrow.id a).comp m) m (𝟙 a) (𝟙 b) where
  hom := pullback.snd (𝟙 a) m.l
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def leftUnitorInv {a b : Span C} (m : SpanArrow a b) :
    SpanCell m ((SpanArrow.id a).comp m) (𝟙 a) (𝟙 b) where
  hom := pullback.lift m.l (𝟙 m.apex) (by simp)
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def rightUnitor {a b : Span C} (m : SpanArrow a b) :
    SpanCell (m.comp (SpanArrow.id b)) m (𝟙 a) (𝟙 b) where
  hom := pullback.fst m.r (𝟙 b)
  hom_l := by span_simp
  hom_r := by span_simp

@[simps hom]
def rightUnitorInv {a b : Span C} (m : SpanArrow a b) :
    SpanCell m (m.comp (SpanArrow.id b)) (𝟙 a) (𝟙 b) where
  hom := pullback.lift (𝟙 m.apex) m.r (by simp)
  hom_l := by span_simp
  hom_r := by span_simp

end SpanCell

namespace Span

variable [HasPullbacks C]

/-- The double category structure on `Span C`: loose composition by pullback,
structure cells from the universal property. -/
instance instPseudoDoubleCategoryStruct : PseudoDoubleCategoryStruct (Span C) where
  Loose := SpanArrow
  Cell := SpanCell
  vId := fun m => SpanCell.vId m
  vComp := fun α β => SpanCell.vComp α β
  lId := fun a => SpanArrow.id a
  lComp := fun m n => SpanArrow.comp m n
  hId := fun f => SpanCell.hId f
  hComp := fun α β => SpanCell.hComp α β
  lAssoc := fun m n p => SpanCell.assoc m n p
  lAssocInv := fun m n p => SpanCell.assocInv m n p
  lLeftUnitor := fun m => SpanCell.leftUnitor m
  lLeftUnitorInv := fun m => SpanCell.leftUnitorInv m
  lRightUnitor := fun m => SpanCell.rightUnitor m
  lRightUnitorInv := fun m => SpanCell.rightUnitorInv m

@[simp]
theorem lId_def (a : Span C) : 𝟙ˡ a = SpanArrow.id a := rfl

@[simp]
theorem lComp_def {a b c : Span C} (m : Loose a b) (n : Loose b c) :
    m ⊙ n = SpanArrow.comp m n := rfl

@[simp]
theorem vId_def {a b : Span C} (m : Loose a b) :
    vId m = SpanCell.vId m := rfl

@[simp]
theorem vComp_def {a₁ b₁ a₂ b₂ a₃ b₃ : Span C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) :
    α ≫ᵥ β = SpanCell.vComp α β := rfl

@[simp]
theorem hId_def {a b : Span C} (f : a ⟶ b) : hId f = SpanCell.hId f := rfl

@[simp]
theorem hComp_def {a₁ a₂ a₃ b₁ b₂ b₃ : Span C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃}
    {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h) :
    α ⊚ β = SpanCell.hComp α β := rfl

@[simp]
theorem lAssoc_def {a b c d : Span C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) : lAssoc m n p = SpanCell.assoc m n p := rfl

@[simp]
theorem lAssocInv_def {a b c d : Span C} (m : Loose a b)
    (n : Loose b c) (p : Loose c d) :
    lAssocInv m n p = SpanCell.assocInv m n p := rfl

@[simp]
theorem lLeftUnitor_def {a b : Span C} (m : Loose a b) :
    lLeftUnitor m = SpanCell.leftUnitor m := rfl

@[simp]
theorem lLeftUnitorInv_def {a b : Span C} (m : Loose a b) :
    lLeftUnitorInv m = SpanCell.leftUnitorInv m := rfl

@[simp]
theorem lRightUnitor_def {a b : Span C} (m : Loose a b) :
    lRightUnitor m = SpanCell.rightUnitor m := rfl

@[simp]
theorem lRightUnitorInv_def {a b : Span C} (m : Loose a b) :
    lRightUnitorInv m = SpanCell.rightUnitorInv m := rfl

local macro "span_disch" : tactic =>
  `(tactic| (repeat' apply pullback.hom_ext) <;>
      first
        | rfl
        | (simp [pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc,
            pullback.condition, pullback.condition_assoc,
            SpanArrow.snd_id_l, SpanArrow.fst_id_r,
            SpanArrow.snd_id_l_assoc, SpanArrow.fst_id_r_assoc]
           <;> try rfl))

instance instPseudoDoubleCategory : PseudoDoubleCategory (Span C) where
  vId_vComp α := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  vComp_vId α := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  vComp_assoc α β γ := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  hId_id a := by
    apply SpanCell.ext
    span_disch
  hId_comp f g := by
    apply SpanCell.ext
    span_disch
  hComp_vId m n := by
    apply SpanCell.ext
    span_disch
  interchange α₁ α₂ β₁ β₂ := by
    apply SpanCell.ext
    span_disch
  lAssoc_natural α β γ := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lLeftUnitor_natural α := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lRightUnitor_natural α := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lAssoc_lAssocInv m n p := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lAssocInv_lAssoc m n p := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lLeftUnitor_lLeftUnitorInv m := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lLeftUnitorInv_lLeftUnitor m := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lRightUnitor_lRightUnitorInv m := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  lRightUnitorInv_lRightUnitor m := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  pentagon m n p q := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  triangle m n := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)

variable {a b : Span C}

def companion (f : a ⟶ b) : Companion f where
  loose := SpanArrow.graph f
  eta :=
    { hom := 𝟙 a
      hom_l := by simp
      hom_r := by simp }
  eps :=
    { hom := f
      hom_l := by simp
      hom_r := by simp }
  eta_vComp_eps := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  eta_hComp_eps := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)

def conjoint (f : a ⟶ b) : Conjoint f where
  loose := SpanArrow.cograph f
  eta :=
    { hom := 𝟙 a
      hom_l := by simp
      hom_r := by simp }
  eps :=
    { hom := f
      hom_l := by simp
      hom_r := by simp }
  eta_vComp_eps := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)
  eps_hComp_eta := by
    rw [Cell.eq_cast_iff_heq]
    exact SpanCell.heq_of_hom (by simp) (by simp) (by span_disch)

instance instEquipment : Equipment (Span C) where
  companion := fun f => companion f
  conjoint := fun f => conjoint f

end Span

end

end CategoryTheory
