import DoubleCat.Functor.Lax

/-!
# Composition of lax double functors

The composite of two lax double functors is a lax double functor: the
underlying functors compose, the actions on loose arrows and cells compose,
and the comparison cells of the composite are the comparisons of the outer
functor composed with the outer functor's image of the inner functor's
comparisons (Grandis–Paré, "Adjoint for double categories", 2004, §2.2).

## Proof technique

The coherence proofs are chases in the heterogeneous-equality calculus of
`DoubleCat.Basic`: each goal `lhs = Cell.cast _ _ rhs` is converted to
`lhs ≍ rhs` by `Cell.eq_cast_iff_heq` and then chased as a right-nested
`HEq.trans` chain, using the congruence lemmas (`vComp_congr_heq`,
`hComp_congr_heq`, `mapCell_congr_heq`) to rewrite in context, the `_heq`
forms of the functor axioms, and the interchange law — which holds on the
nose, so it enters by `heq_of_eq`.  (`calc` is not usable here: its
step-chaining reads the last two explicit arguments of the relation as the
step's sides, which for `HEq` picks up the right-hand *type* — so
heterogeneous steps whose types change cannot be chained.  Term-mode
`HEq.trans` has no such restriction.)

A heterogeneous chase may not strip casts freely, because every
intermediate term must still typecheck: where a loose-wise composite needs
boundaries merged, the identity column is split as
`vId (G.mapLoose _) ≫ᵥ G.mapCell (vId _)` (whose tight sides are
`𝟙 ≫ G.map 𝟙`, matching the uncast composite exactly), and casts are
reintroduced on a factor exactly where a boundary must be re-normalized.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂ w₃ t₃ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]
variable {E : Type u₃} [Category.{v₃} E] [PseudoDoubleCategoryStruct E]
  [PseudoDoubleCategory E]

namespace LaxDoubleFunctor

/-- The composite of two lax double functors: underlying data composes
componentwise, and each laxator of the composite is the outer functor's
laxator followed by the outer functor's image of the inner functor's
laxator. -/
def comp (F : LaxDoubleFunctor C D) (G : LaxDoubleFunctor D E) :
    LaxDoubleFunctor C E where

  toFunctor :=
    { obj := fun a => G.obj (F.obj a)
      map := fun f => G.map (F.map f)
      map_id := fun a => (congrArg G.map (F.map_id a)).trans (G.map_id _)
      map_comp := fun f g =>
        (congrArg G.map (F.map_comp f g)).trans (G.map_comp _ _) }
  mapLoose m := G.mapLoose (F.mapLoose m)
  mapCell α := G.mapCell (F.mapCell α)
  mapCell_vId m := by boundary
  mapCell_vComp α β := by boundary
  laxComp m n :=
    (G.laxComp (F.mapLoose m) (F.mapLoose n) ≫ᵥ
      G.mapCell (F.laxComp m n)).cast (by boundary) (by boundary)
  laxId a :=
    (G.laxId (F.obj a) ≫ᵥ G.mapCell (F.laxId a)).cast (by boundary) (by boundary)
  laxComp_natural {a₁ a₂ a₃ b₁ b₂ b₃} {m₁ m₂ n₁ n₂} {f g h} α β := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_vComp_heq _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_congr_heq (by boundary) (by boundary)
          (F.laxComp_natural_heq α β))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_vComp_heq _ _)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (G.laxComp_natural_heq (F.mapCell α) (F.mapCell β)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)
  laxId_natural {a b} f := by
    rw [Cell.eq_cast_iff_heq]
    exact

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (Cell.cast_heq _ _ _) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_vComp_heq _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_congr_heq (by boundary) (by boundary)
          (F.laxId_natural_heq f))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (G.mapCell_vComp_heq _ _)).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (G.laxId_natural_heq (F.map f)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (Cell.cast_heq _ _ _).symm)
  laxComp_assoc {a b c d} m n p := by
    rw [Cell.eq_cast_iff_heq]

    have h₁ :
        ((G.laxComp (F.mapLoose m) (F.mapLoose n) ≫ᵥ
              G.mapCell (F.laxComp m n)).cast
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj c)))
            (by boundary) (by boundary) ⊚
            vId (G.mapLoose (F.mapLoose p))) ≫ᵥ
          (G.laxComp (F.mapLoose (m ⊙ n)) (F.mapLoose p) ≫ᵥ
              G.mapCell (F.laxComp (m ⊙ n) p)).cast
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj d)))
            (by boundary) (by boundary) ≫ᵥ
          G.mapCell (F.mapCell (lAssoc m n p)) ≍
        ((G.laxComp (F.mapLoose m) (F.mapLoose n) ≫ᵥ
            G.mapCell (F.laxComp m n)) ⊚
          (vId (G.mapLoose (F.mapLoose p)) ≫ᵥ
            G.mapCell (vId (F.mapLoose p)))) ≫ᵥ
        (G.laxComp (F.mapLoose (m ⊙ n)) (F.mapLoose p) ≫ᵥ
            G.mapCell (F.laxComp (m ⊙ n) p)) ≫ᵥ
        G.mapCell (F.mapCell (lAssoc m n p)) :=
      vComp_congr_heq (by boundary) (by boundary) (by boundary) (by boundary)
        (hComp_congr_heq (by boundary) (by boundary) (by boundary)
          (Cell.cast_heq _ _ _)
          ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              (G.mapCell_vId_heq (F.mapLoose p))).trans
            (PseudoDoubleCategory.vComp_vId_heq _)).symm)
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (Cell.cast_heq _ _ _) HEq.rfl)
    exact h₁.trans <|

      (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (PseudoDoubleCategory.interchange _ _ _ _)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (PseudoDoubleCategory.vComp_assoc_heq _ _ _))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (G.laxComp_natural_heq (F.laxComp m n)
            (vId (F.mapLoose p))).symm HEq.rfl)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _)).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (G.mapCell_vComp_heq _ _).symm))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_vComp_heq _ _).symm)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_congr_heq (by boundary) (by boundary)
            (F.laxComp_assoc_heq m n p)))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_vComp_heq _ _))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (G.mapCell_vComp_heq _ _)))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm).trans <|
      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm.trans <|

      (vComp_congr_heq (by boundary) (by boundary) rfl rfl
        (G.laxComp_assoc_heq (F.mapLoose m) (F.mapLoose n)
          (F.mapLoose p)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        ((PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans
          (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (vComp_congr_heq (by boundary) (by boundary) rfl rfl
            (G.laxComp_natural_heq (vId (F.mapLoose m))
              (F.laxComp n p)) HEq.rfl))).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (PseudoDoubleCategory.vComp_assoc_heq _ _ _)).trans
          (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm)).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (heq_of_eq (PseudoDoubleCategory.interchange _ _ _ _)).symm
          HEq.rfl)).trans

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq (by boundary) (by boundary) (by boundary) (by boundary)
          (hComp_congr_heq (by boundary) (by boundary) (by boundary)
            ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
                (G.mapCell_vId_heq (F.mapLoose m))).trans
              (PseudoDoubleCategory.vComp_vId_heq _))
            (Cell.cast_heq
              (f' := 𝟙 (G.obj (F.obj b))) (g' := 𝟙 (G.obj (F.obj d)))
              (by boundary) (by boundary) _).symm)
          (Cell.cast_heq
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj d)))
            (by boundary) (by boundary) _).symm))
  laxComp_leftUnitor {a b} m := by
    rw [Cell.eq_cast_iff_heq]

    have h₁ :
        ((G.laxId (F.obj a) ≫ᵥ G.mapCell (F.laxId a)).cast
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj a)))
            (by boundary) (by boundary) ⊚
            vId (G.mapLoose (F.mapLoose m))) ≫ᵥ
          (G.laxComp (F.mapLoose (lId a)) (F.mapLoose m) ≫ᵥ
              G.mapCell (F.laxComp (lId a) m)).cast
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj b)))
            (by boundary) (by boundary) ≫ᵥ
          G.mapCell (F.mapCell (lLeftUnitor m)) ≍
        ((G.laxId (F.obj a) ≫ᵥ G.mapCell (F.laxId a)) ⊚
          (vId (G.mapLoose (F.mapLoose m)) ≫ᵥ
            G.mapCell (vId (F.mapLoose m)))) ≫ᵥ
        (G.laxComp (F.mapLoose (lId a)) (F.mapLoose m) ≫ᵥ
            G.mapCell (F.laxComp (lId a) m)) ≫ᵥ
        G.mapCell (F.mapCell (lLeftUnitor m)) :=
      vComp_congr_heq (by boundary) (by boundary) (by boundary) (by boundary)
        (hComp_congr_heq (by boundary) (by boundary) (by boundary)
          (Cell.cast_heq _ _ _)
          ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              (G.mapCell_vId_heq (F.mapLoose m))).trans
            (PseudoDoubleCategory.vComp_vId_heq _)).symm)
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (Cell.cast_heq _ _ _) HEq.rfl)
    exact h₁.trans <|

      (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (PseudoDoubleCategory.interchange _ _ _ _)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (PseudoDoubleCategory.vComp_assoc_heq _ _ _))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (G.laxComp_natural_heq (F.laxId a) (vId (F.mapLoose m))).symm
          HEq.rfl)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _)).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (G.mapCell_vComp_heq _ _).symm))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_vComp_heq _ _).symm)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_congr_heq (by boundary) (by boundary)
            (F.laxComp_leftUnitor_heq m)))).trans

      (G.laxComp_leftUnitor_heq (F.mapLoose m))
  laxComp_rightUnitor {a b} m := by
    rw [Cell.eq_cast_iff_heq]

    have h₁ :
        (vId (G.mapLoose (F.mapLoose m)) ⊚
            (G.laxId (F.obj b) ≫ᵥ G.mapCell (F.laxId b)).cast
            (f' := 𝟙 (G.obj (F.obj b))) (g' := 𝟙 (G.obj (F.obj b)))
            (by boundary) (by boundary)) ≫ᵥ
          (G.laxComp (F.mapLoose m) (F.mapLoose (lId b)) ≫ᵥ
              G.mapCell (F.laxComp m (lId b))).cast
            (f' := 𝟙 (G.obj (F.obj a))) (g' := 𝟙 (G.obj (F.obj b)))
            (by boundary) (by boundary) ≫ᵥ
          G.mapCell (F.mapCell (lRightUnitor m)) ≍
        ((vId (G.mapLoose (F.mapLoose m)) ≫ᵥ
            G.mapCell (vId (F.mapLoose m))) ⊚
          (G.laxId (F.obj b) ≫ᵥ G.mapCell (F.laxId b))) ≫ᵥ
        (G.laxComp (F.mapLoose m) (F.mapLoose (lId b)) ≫ᵥ
            G.mapCell (F.laxComp m (lId b))) ≫ᵥ
        G.mapCell (F.mapCell (lRightUnitor m)) :=
      vComp_congr_heq (by boundary) (by boundary) (by boundary) (by boundary)
        (hComp_congr_heq (by boundary) (by boundary) (by boundary)
          ((vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
              (G.mapCell_vId_heq (F.mapLoose m))).trans
            (PseudoDoubleCategory.vComp_vId_heq _)).symm
          (Cell.cast_heq _ _ _))
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (Cell.cast_heq _ _ _) HEq.rfl)
    exact h₁.trans <|

      (vComp_congr_heq rfl rfl rfl rfl
        (heq_of_eq (PseudoDoubleCategory.interchange _ _ _ _)) HEq.rfl).trans <|

      (PseudoDoubleCategory.vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (PseudoDoubleCategory.vComp_assoc_heq _ _ _))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq (by boundary) (by boundary) rfl rfl
          (G.laxComp_natural_heq (vId (F.mapLoose m)) (F.laxId b)).symm
          HEq.rfl)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (PseudoDoubleCategory.vComp_assoc_heq _ _ _)).trans <|

      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
            (G.mapCell_vComp_heq _ _).symm))).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_vComp_heq _ _).symm)).trans <|
      (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
        (vComp_congr_heq rfl rfl (by boundary) (by boundary) HEq.rfl
          (G.mapCell_congr_heq (by boundary) (by boundary)
            (F.laxComp_rightUnitor_heq m)))).trans

      (G.laxComp_rightUnitor_heq (F.mapLoose m))

@[simp]
theorem comp_obj (F : LaxDoubleFunctor C D) (G : LaxDoubleFunctor D E)
    (a : C) : (F.comp G).obj a = G.obj (F.obj a) := rfl

@[simp]
theorem comp_map (F : LaxDoubleFunctor C D) (G : LaxDoubleFunctor D E)
    {a b : C} (f : a ⟶ b) : (F.comp G).map f = G.map (F.map f) := rfl

@[simp]
theorem comp_mapLoose (F : LaxDoubleFunctor C D) (G : LaxDoubleFunctor D E)
    {a b : C} (m : Loose a b) :
    (F.comp G).mapLoose m = G.mapLoose (F.mapLoose m) := rfl

@[simp]
theorem comp_mapCell (F : LaxDoubleFunctor C D) (G : LaxDoubleFunctor D E)
    {a b c d : C} {m : Loose a b} {n : Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (α : Cell m n f g) :
    (F.comp G).mapCell α = G.mapCell (F.mapCell α) := rfl

end LaxDoubleFunctor

end CategoryTheory
