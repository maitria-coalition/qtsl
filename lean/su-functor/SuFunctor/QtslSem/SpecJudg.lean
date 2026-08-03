import SuFunctor.Plain.SpecFunctor
import DoubleCat.JudgLayer

/-!
# The semantic universe's inclusion-ordered judgment layer

The judgment layer (`DoubleCat.JudgLayer`) instantiated at the spec
tier: over the wiring base in state-family presentation, decorate each
wiring pattern with an apex penalty class (`SuFunctor.Plain.Cpl`),
order the fibres by inclusion, transport by the image of penalty
pullback along a cell's apex map, compose by the image of
pushforward-then-add, and take the singleton austere unit.  The
coherence obligations are exactly the element-level cores already
proved for the spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`, section Cores) — the judgment layer is
what remains of that functor when the dependent-span bookkeeping is
subtracted: same coherence content, no heterogeneous equality.

`SpecJudgLayer` is thereby a **thin** pseudo double category over the
wiring base — the carrier the semantic-universe totals' own docstrings
call "the judgment layer, carried on top of this total", now a pseudo
double category in its own right, eligible as a target of the
free-promotion transpose (`VirtualDoubleFunctor.promoteThin`), which
the totals themselves are not (their Grothendieck cells carry the
wiring base's state-map cells as data).

`cellOfSubset` records the entry point for the System-judgment
component stock: a class inclusion over a fixed pattern — the directed
adequacy-square shape (region inclusion to judgment-class inclusion) —
is a cell of the judgment layer over identity boundaries.
-/

namespace SuFunctor

namespace QtslSem

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain

universe u

/-- The spec-class judgment order over the wiring base: apex penalty
classes ordered by inclusion, with image transport, image-of-boxplus
composition, and the singleton austere unit.  Every coherence field is
one of `SuFunctor.Plain.SpecFunctor`'s element-level cores, read at
`Set` level. -/
def specJudgOrder (El : Type u) : JudgmentOrder.{u} (WireSpan El) where
  Dec M := Cpl M
  le 𝒰 𝒱 := 𝒰 ⊆ 𝒱
  le_refl _ := subset_rfl
  le_trans h₁ h₂ := h₁.trans h₂
  pull γ 𝒰 := Pen.pull (PatCell.tot γ) '' 𝒰
  dcomp 𝒰 𝒱 := Set.image2 boxplus 𝒰 𝒱
  dunit A := {unitPen A}
  pull_vId := by
    intro A B M 𝒰
    have h : Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M)) = id :=
      funext fun u => Pen.pull_id u
    rw [h, Set.image_id]
  pull_vComp := by
    intro A₁ B₁ A₂ B₂ A₃ B₃ M₁ M₂ M₃ f₁ g₁ f₂ g₂ α β 𝒰
    rw [← Set.image_comp]
    congr 1
    funext u
    exact (Pen.pull_pull (PatCell.tot α) (PatCell.tot β) u).symm
  pull_mono := by
    intro A B C D M N f g γ 𝒰 𝒱 h
    exact Set.image_mono h
  dcomp_mono := by
    intro A B C M N 𝒰 𝒰' 𝒱 𝒱' h₁ h₂
    exact Set.image2_subset h₁ h₂
  pull_hId := by
    intro A B f
    rw [Set.image_singleton]
    exact rfl
  pull_hComp := by
    intro A₁ A₂ A₃ B₁ B₂ B₃ M₁ M₂ N₁ N₂ f g h α β 𝒰₁ 𝒰₂
    rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
    exact Set.image2_congr fun u₁ _ u₂ _ => pull_tot_hComp_boxplus α β u₁ u₂
  pull_lAssoc := by
    intro A B C D M N P 𝒰₁ 𝒰₂ 𝒰₃
    rw [Set.image_image2]
    exact Set.image2_assoc fun u₁ u₂ u₃ =>
      pull_tot_lAssoc_boxplus M N P u₁ u₂ u₃
  pull_lLeftUnitor := by
    intro A B M 𝒰
    rw [Set.image2_singleton_left, ← Set.image_comp]
    have h : Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ∘
          boxplus (unitPen _) = id :=
      funext fun u => pull_tot_lLeftUnitor_boxplus M u
    rw [h, Set.image_id]
  pull_lRightUnitor := by
    intro A B M 𝒰
    rw [Set.image2_singleton_right, ← Set.image_comp]
    have h : Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)) ∘
          (fun u => boxplus u (unitPen _)) = id :=
      funext fun u => pull_tot_lRightUnitor_boxplus M u
    rw [h, Set.image_id]

/-- **The semantic universe's inclusion-ordered judgment layer**: the
judgment layer of the spec-class judgment order over the wiring base —
a thin pseudo double category (both by the generic instances). -/
abbrev SpecJudgLayer (El : Type u) :=
  JudgLayer (WireSpan El) (specJudgOrder El)

/-- The judgment layer is a pseudo double category, by instance
search — the generic construction consumes the datum as-is. -/
theorem specJudgLayer_pseudoDoubleCategory (El : Type u) :
    ∃ _ : PseudoDoubleCategory (SpecJudgLayer El), True :=
  ⟨inferInstance, trivial⟩

/-- Thinness at the instantiated carrier, in the form the
free-promotion transpose consumes. -/
theorem specJudgLayer_cell_subsingleton (El : Type u)
    {a b c d : SpecJudgLayer El} (M : Loose a b) (N : Loose c d)
    (f : a ⟶ c) (g : b ⟶ d) : Subsingleton (Cell M N f g) :=
  JudgLayer.cell_subsingleton M N f g

/-- A class inclusion over a fixed pattern is a cell of the judgment
layer over identity boundaries — the directed adequacy-square shape
(region inclusion to judgment-class inclusion), entering the carrier
through the generic fibre-order constructor. -/
def cellOfSubset {El : Type u} {a b : SpecJudgLayer El}
    {M : Pat a.un b.un} {𝒰 𝒱 : Cpl M} (h : 𝒰 ⊆ 𝒱) :
    Cell (C := SpecJudgLayer El)
      (⟨M, 𝒰⟩ : JudgLayer.JLoose (specJudgOrder El) a b) ⟨M, 𝒱⟩
      (𝟙 a) (𝟙 b) :=
  JudgLayer.cellOfLe h

end

end QtslSem

end SuFunctor
