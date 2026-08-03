import DoubleCat.Virtual.FreePromotion
import DoubleCat.Virtual.Functor
import DoubleCat.Virtual.OfPseudo
import DoubleCat.Functor.Pseudo
import DoubleCat.Functor.Composition

/-!
# The transpose across the free promotion (thin case)

The free promotion is the object part of a left adjoint: functors of
virtual double categories from `C` into the underlying virtual double
category of a pseudo double category `D` correspond to
(structure-preserving) functors of pseudo double categories from
`FreePromotion C` to `D` (Cruttwell–Shulman, "A unified framework for
generalized multicategories", 2010, §7).  This file mechanizes the
*existence direction* of that correspondence in the thin case — the case
every instance in this development inhabits:

* `CategoryTheory.VirtualDoubleFunctor.promoteThin`: the transpose of a
  functor of virtual double categories `G : C ⥤ᵥ D` (with `D` the
  underlying virtual double category of a pseudo double category whose
  cells are proof-irrelevant) across the promotion — a lax double functor
  `FreePromotion C ⥤ D` sending a string to the fold of its mapped edges
  and a covering to the fold of its mapped multicells;
* `CategoryTheory.VirtualDoubleFunctor.promoteThin_isPseudo`: the
  transpose is pseudo, not merely lax — its compositor is the canonical
  re-association of folds, which is invertible (`foldCompCell` and
  `foldCompCellInv` below are the two directions).

Restriction remark (not mechanized; Cruttwell–Shulman §5 and §7): the
virtual double categories in the image of the underlying-virtual functor
are, up to equivalence, exactly the *representable* ones — those with
units and all composites — so the adjunction restricts to the classical
equivalence between representable virtual double categories and pseudo
double categories.  Nothing downstream consumes the full adjunction
(uniqueness direction, triangle identities); this file carries only the
transpose that the applications use.

Also here, and generically useful for thin targets:

* `CategoryTheory.LoosePath.foldCompCellInv`: the inverse canonical
  comparison `fold ps ⊙ fold rs ⟶ fold (ps.comp rs)`, mirroring
  `LoosePath.foldCompCell` with the co-directed structure cells;
* `CategoryTheory.LaxDoubleFunctor.ext_of_thin`: two lax double functors
  into a thin pseudo double category are equal as soon as their
  underlying functors and loose actions agree — the cell actions and
  laxators are then forced by proof irrelevance.
-/

namespace CategoryTheory

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct
  PseudoDoubleCategoryStruct

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂

namespace LoosePath

variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]

/-- The canonical globular comparison from the loose composite of the folds
to the fold of a concatenation, built from unitors and associators: the
inverse direction of `LoosePath.foldCompCell`.  In a thin pseudo double
category this is the only such cell; in general it is the canonical one. -/
def foldCompCellInv : ∀ {a b c : D}
    (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := D)) a b)
    (rs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := D)) b c),
    Cell (ps.fold ⊙ rs.fold) ((ps.comp rs).fold) (𝟙 a) (𝟙 c)
  | _, _, _, .nil, rs => lLeftUnitor rs.fold
  | _, _, _, .cons q ps, rs =>
      Cell.cast (Category.id_comp _) (Category.id_comp _)
        (lAssoc q ps.fold rs.fold ≫ᵥ (vId q ⊚ foldCompCellInv ps rs))

end LoosePath

namespace FreePromotion

variable {C : Type u₁} [Category.{v₁} C]

/-- The underlying-object functor of the free promotion: it unwraps.  The
tight category of `FreePromotion C` is that of `C` on the nose. -/
def unFunctor : FreePromotion C ⥤ C where
  obj := FreePromotion.un
  map f := f

end FreePromotion

section PromoteThin

variable {C : Type u₁} [Category.{v₁} C]
  [VirtualDoubleCategoryStruct.{w₁, t₁, v₁, u₁} C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]

attribute [local instance] VirtualDoubleCategoryStruct.ofPseudo

/-- **The transpose across the free promotion** (existence direction of the
promotion's universal property, thin case).  A functor of virtual double
categories from `C` to the underlying virtual double category of a pseudo
double category `D` with proof-irrelevant cells induces a lax double
functor `FreePromotion C ⥤ D`:

* a string of loose arrows maps to the fold of its mapped edges;
* a cell of the promotion — a covering — maps to the fold of its mapped
  multicells (`seqFoldAux`, the same fold that interprets substitution in
  `VirtualDoubleCategoryStruct.ofPseudo`);
* the compositor is the canonical re-association of folds.

The coherence laws hold by proof irrelevance in `D`.  The transpose is in
fact pseudo (`promoteThin_isPseudo`): freely added composites map to
composites of images up to the invertible canonical comparison, never up
to a genuinely one-directed cell. -/
noncomputable def VirtualDoubleFunctor.promoteThin
    (hD : ∀ {a b c d : D} (m : PseudoDoubleCategoryStruct.Loose a b)
      (n : PseudoDoubleCategoryStruct.Loose c d) (f : a ⟶ c) (g : b ⟶ d),
      Subsingleton (PseudoDoubleCategoryStruct.Cell m n f g))
    (G : VirtualDoubleFunctor C D) :
    LaxDoubleFunctor (FreePromotion C) D where
  toFunctor := FreePromotion.unFunctor ⋙ G.toFunctor
  mapLoose ps := (ps.map G.obj fun {_ _} e => G.mapLoose e).fold
  mapCell α :=
    VirtualDoubleCategoryData.seqFoldAux (G.mapSeq (Classical.choice α.down))
  mapCell_vId _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  mapCell_vComp _ _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  laxComp ps qs :=
    (LoosePath.map_comp G.obj (fun {_ _} e => G.mapLoose e) ps qs).symm ▸
      LoosePath.foldCompCellInv (ps.map G.obj fun {_ _} e => G.mapLoose e)
        (qs.map G.obj fun {_ _} e => G.mapLoose e)
  laxId a := vId (lId (G.obj a.un))
  laxComp_natural _ _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  laxId_natural _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  laxComp_assoc _ _ _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  laxComp_leftUnitor _ := @Subsingleton.elim _ (hD _ _ _ _) _ _
  laxComp_rightUnitor _ := @Subsingleton.elim _ (hD _ _ _ _) _ _

/-- The transpose is pseudo: its compositor and unit comparison are the
canonical fold re-associations, invertible by construction (the two
directions are `foldCompCellInv` and `foldCompCell`; the roundtrips are
proof irrelevance). -/
theorem VirtualDoubleFunctor.promoteThin_isPseudo
    (hD : ∀ {a b c d : D} (m : PseudoDoubleCategoryStruct.Loose a b)
      (n : PseudoDoubleCategoryStruct.Loose c d) (f : a ⟶ c) (g : b ⟶ d),
      Subsingleton (PseudoDoubleCategoryStruct.Cell m n f g))
    (G : VirtualDoubleFunctor C D) :
    (G.promoteThin hD).IsPseudo where
  laxComp_isInvertible ps qs := by
    have β : PseudoDoubleCategoryStruct.Cell
        (((ps.comp qs).map G.obj fun {_ _} e => G.mapLoose e).fold)
        ((ps.map G.obj fun {_ _} e => G.mapLoose e).fold ⊙
          (qs.map G.obj fun {_ _} e => G.mapLoose e).fold)
        (𝟙 _) (𝟙 _) := by
      rw [LoosePath.map_comp]
      exact LoosePath.foldCompCell _ _
    exact ⟨β, @Subsingleton.elim _ (hD _ _ _ _) _ _,
      @Subsingleton.elim _ (hD _ _ _ _) _ _⟩
  laxId_isInvertible a :=
    ⟨vId (lId (G.obj a.un)),
      @Subsingleton.elim _ (hD _ _ _ _) _ _,
      @Subsingleton.elim _ (hD _ _ _ _) _ _⟩

end PromoteThin

section ExtThin

variable {C : Type u₁} [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct D]

/-- Two lax double functors into a thin pseudo double category are equal as
soon as their underlying functors and their actions on loose arrows agree:
the cell actions and the laxators land in proof-irrelevant types indexed
by the agreeing data, so they carry no further information.  (The loose
agreement is heterogeneous only because it is stated before the underlying
functors are identified.) -/
theorem LaxDoubleFunctor.ext_of_thin
    (hD : ∀ {a b c d : D} (m : Loose a b) (n : Loose c d) (f : a ⟶ c)
      (g : b ⟶ d), Subsingleton (Cell m n f g))
    {F G : LaxDoubleFunctor C D}
    (hFun : F.toFunctor = G.toFunctor)
    (hLoose : ∀ {a b : C} (m : Loose a b), F.mapLoose m ≍ G.mapLoose m) :
    F = G := by
  obtain ⟨F₀, FL, FC, _, _, FlC, FlI, _, _, _, _, _⟩ := F
  obtain ⟨G₀, GL, GC, _, _, GlC, GlI, _, _, _, _, _⟩ := G
  obtain rfl : F₀ = G₀ := hFun
  obtain rfl : @FL = @GL := by
    funext a b m
    exact eq_of_heq (hLoose m)
  obtain rfl : @FC = @GC := by
    funext a b c d m n f g α
    exact @Subsingleton.elim _ (hD _ _ _ _) _ _
  obtain rfl : @FlC = @GlC := by
    funext a b c m n
    exact @Subsingleton.elim _ (hD _ _ _ _) _ _
  obtain rfl : @FlI = @GlI := by
    funext a
    exact @Subsingleton.elim _ (hD _ _ _ _) _ _
  rfl

end ExtThin

end CategoryTheory
