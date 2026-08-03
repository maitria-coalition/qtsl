import DoubleCat
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Axiom receipts

Witnesses that the principal instances and constructions of the library
are found by instance search and are lawful, together with `#print axioms`
receipts for the core definitions and theorems, so that the axiom
footprint of each part of the library is inspectable at build time.
-/

open CategoryTheory

/-- A one-object category, for witness purposes. -/
inductive PtCat : Type where | star

instance : Category PtCat where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- Witness: the `Sq` double category structure is found by instance search. -/
@[reducible] def sqStructWitness : PseudoDoubleCategoryStruct (Sq PtCat) := inferInstance
/-- Witness: the `Sq` instance is lawful. -/
theorem sqLawfulWitness : PseudoDoubleCategory (Sq PtCat) := inferInstance

/-- Witness: the identity lax double functor. -/
def idWitness : LaxDoubleFunctor (Sq PtCat) (Sq PtCat) := LaxDoubleFunctor.id

/-- Witness: composition of lax double functors. -/
def compWitness : LaxDoubleFunctor (Sq PtCat) (Sq PtCat) :=
  LaxDoubleFunctor.id.comp LaxDoubleFunctor.id

/-- Witness: the hom-category of tight transformations. -/
@[reducible] def homCatWitness : Category (LaxDoubleFunctor (Sq PtCat) (Sq PtCat)) :=
  inferInstance

/-- Witness: an identity tight transformation, as a morphism. -/
def idTransWitness :
    (LaxDoubleFunctor.id : LaxDoubleFunctor (Sq PtCat) (Sq PtCat)) ⟶
      LaxDoubleFunctor.id :=
  𝟙 _

/-- Witness: companions in `Sq`. -/
def companionWitness : Companion (𝟙 (Sq.mk PtCat.star)) :=
  Sq.companion PtCat (𝟙 _)

/-- Witness: conjoints of isomorphisms in `Sq`. -/
def conjointWitness : Conjoint (Iso.refl (Sq.mk PtCat.star)).hom :=
  Sq.conjointOfIso (Iso.refl _)

#print axioms CategoryTheory.PseudoDoubleCategoryStruct.Cell.cast
#print axioms CategoryTheory.PseudoDoubleCategoryStruct.cast_vComp
#print axioms CategoryTheory.PseudoDoubleCategoryStruct.vComp_congr_heq
#print axioms CategoryTheory.PseudoDoubleCategoryStruct.hComp_congr_heq
#print axioms CategoryTheory.LoosePair.hom_ext
#print axioms CategoryTheory.LoosePair.instCategory
#print axioms CategoryTheory.LoosePair.lIdFunctor
#print axioms CategoryTheory.LoosePair.lIdFunctor_srcFunctor
#print axioms CategoryTheory.LaxDoubleFunctor.comp
#print axioms CategoryTheory.TightTransformation.ext
#print axioms CategoryTheory.TightTransformation.vcomp
#print axioms CategoryTheory.instCategoryLaxDoubleFunctor
#print axioms sqStructWitness
#print axioms sqLawfulWitness
#print axioms idWitness
#print axioms compWitness
#print axioms homCatWitness
#print axioms idTransWitness
#print axioms companionWitness
#print axioms conjointWitness

/-- Witness: a bundled object of the 2-category of double categories. -/
def dblWitness : Dbl := Dbl.of (Sq PtCat)

/-- Witness: right whiskering of a tight transformation. -/
def whiskerWitness :
    TightTransformation
      ((LaxDoubleFunctor.id : LaxDoubleFunctor (Sq PtCat) (Sq PtCat)).comp
        LaxDoubleFunctor.id)
      (LaxDoubleFunctor.id.comp LaxDoubleFunctor.id) :=
  (TightTransformation.id LaxDoubleFunctor.id).whiskerRight LaxDoubleFunctor.id

#print axioms CategoryTheory.TightTransformation.whiskerRight
#print axioms CategoryTheory.TightTransformation.whiskerLeft
#print axioms CategoryTheory.TightTransformation.whisker_exchange
#print axioms CategoryTheory.LaxDoubleFunctor.ext'
#print axioms CategoryTheory.LaxDoubleFunctor.comp_id
#print axioms CategoryTheory.LaxDoubleFunctor.id_comp
#print axioms CategoryTheory.LaxDoubleFunctor.comp_assoc
#print axioms CategoryTheory.Dbl.bicategory
#print axioms dblWitness
#print axioms whiskerWitness

#print axioms CategoryTheory.MonoidalDoubleCategory.GradedCounterexample.not_m9AssociatorInterchanger
#print axioms CategoryTheory.MonoidalDoubleCategory.GradedCounterexample.chi_isInvertible
#print axioms CategoryTheory.MonoidalDoubleCategory.GradedCounterexample.mu_isInvertible

#print axioms CategoryTheory.LaxDoubleFunctor.isPseudo_id
#print axioms CategoryTheory.NatGraded.not_isPseudo_laxWeight

#print axioms CategoryTheory.Companion.id
#print axioms CategoryTheory.Companion.theta_vComp_theta
#print axioms CategoryTheory.Companion.isoLoose

/-- Witness: composition of companions. -/
def companionCompWitness :
    Companion (𝟙 (Sq.mk PtCat.star) ≫ 𝟙 (Sq.mk PtCat.star)) :=
  (Sq.companion PtCat (𝟙 _)).comp (Sq.companion PtCat (𝟙 _))
#print axioms CategoryTheory.Companion.tube
#print axioms CategoryTheory.Companion.comp_tube
#print axioms CategoryTheory.Companion.comp
#print axioms companionCompWitness

/-- Witness: an identity loose transformation. -/
def looseTransIdWitness :
    LooseTransformation
      (LaxDoubleFunctor.id : LaxDoubleFunctor (Sq PtCat) (Sq PtCat))
      LaxDoubleFunctor.id :=
  LooseTransformation.id LaxDoubleFunctor.id

/-- Witness: composition of loose transformations. -/
def looseTransCompWitness :
    LooseTransformation
      (LaxDoubleFunctor.id : LaxDoubleFunctor (Sq PtCat) (Sq PtCat))
      LaxDoubleFunctor.id :=
  looseTransIdWitness.comp looseTransIdWitness
#print axioms CategoryTheory.LooseTransformation.ext
#print axioms CategoryTheory.LooseTransformation.id
#print axioms CategoryTheory.LooseTransformation.isStrong_id
#print axioms CategoryTheory.LooseTransformation.idTube
#print axioms CategoryTheory.LooseTransformation.id_comp_tube
#print axioms CategoryTheory.LooseTransformation.compNatCell_natural
#print axioms CategoryTheory.LooseTransformation.compIdTube
#print axioms CategoryTheory.LooseTransformation.comp_id_tube
#print axioms CategoryTheory.LooseTransformation.compNatCell_laxId
#print axioms CategoryTheory.LooseTransformation.compLaxTube
#print axioms CategoryTheory.LooseTransformation.compNatCell_laxComp
#print axioms CategoryTheory.LooseTransformation.comp
#print axioms looseTransIdWitness
#print axioms looseTransCompWitness

#print axioms CategoryTheory.PseudoDoubleCategoryStruct.globularCategory
#print axioms CategoryTheory.LooseBicat.bicategory
#print axioms CategoryTheory.PseudoDoubleCategoryStruct.lLeftUnitor_lId_eq_lRightUnitor_lId
#print axioms CategoryTheory.PseudoDoubleCategoryStruct.lLeftUnitorInv_lId_eq_lRightUnitorInv_lId

#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.instStrong
#print axioms CategoryTheory.NatGraded.not_strong

#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.instLaws
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.instBraidedLaws

#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.m1Pentagon_iff
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.m4InterchangerAssoc_iff
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.m9AssociatorInterchanger_iff

#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m4InterchangerAssoc
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m2Triangle
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m6BraidingInterchanger

#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m1Pentagon
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m3_hexagonForward
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m3_hexagonReverse
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m3_involutive
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m5InterchangerUnit
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m7UnitorUnit
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m10UnitorInterchanger
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m11aAssociatorUnit
#print axioms CategoryTheory.MonoidalDoubleCategory.Graded.not_m11bBraidingUnit

/-- Witness: an identity modification. -/
def modIdWitness :
    Modification (LooseTransformation.id (LaxDoubleFunctor.id :
        LaxDoubleFunctor (Sq PtCat) (Sq PtCat)))
      (LooseTransformation.id LaxDoubleFunctor.id)
      (TightTransformation.id _) (TightTransformation.id _) :=
  Modification.id _

/-- Witness: loose-wise composition of modifications. -/
def modHCompWitness :
    Modification
      ((LooseTransformation.id (LaxDoubleFunctor.id :
          LaxDoubleFunctor (Sq PtCat) (Sq PtCat))).comp
        (LooseTransformation.id LaxDoubleFunctor.id))
      ((LooseTransformation.id LaxDoubleFunctor.id).comp
        (LooseTransformation.id LaxDoubleFunctor.id))
      (TightTransformation.id _) (TightTransformation.id _) :=
  modIdWitness.hcomp modIdWitness
#print axioms CategoryTheory.Modification.ext
#print axioms CategoryTheory.Modification.heq_ext
#print axioms CategoryTheory.Modification.id
#print axioms CategoryTheory.Modification.vcomp
#print axioms CategoryTheory.Modification.ofTight
#print axioms CategoryTheory.Modification.hcomp_natCell_aux
#print axioms CategoryTheory.Modification.hcomp
#print axioms CategoryTheory.Modification.assocTube
#print axioms CategoryTheory.Modification.assocInvTube
#print axioms CategoryTheory.Modification.leftUnitorTube
#print axioms CategoryTheory.Modification.leftUnitorInvTube
#print axioms CategoryTheory.Modification.rightUnitorTube
#print axioms CategoryTheory.Modification.rightUnitorInvTube
#print axioms CategoryTheory.Modification.assoc
#print axioms CategoryTheory.Modification.assocInv
#print axioms CategoryTheory.Modification.leftUnitor
#print axioms CategoryTheory.Modification.leftUnitorInv
#print axioms CategoryTheory.Modification.rightUnitor
#print axioms CategoryTheory.Modification.rightUnitorInv
#print axioms modIdWitness
#print axioms modHCompWitness

@[reducible] def laxStructWitness :
    PseudoDoubleCategoryStruct (LaxDoubleFunctor (Sq PtCat) (Sq PtCat)) :=
  inferInstance

/-- Witness: the pseudo double category of lax double functors is lawful. -/
theorem laxLawfulWitness :
    PseudoDoubleCategory (LaxDoubleFunctor (Sq PtCat) (Sq PtCat)) :=
  inferInstance

theorem laxLaxWitness :
    PseudoDoubleCategory
      (LaxDoubleFunctor (LaxDoubleFunctor (Sq PtCat) (Sq PtCat))
        (Sq PtCat)) :=
  inferInstance

@[reducible] def laxLooseBicatWitness :
    Bicategory (LooseBicat (LaxDoubleFunctor (Sq PtCat) (Sq PtCat))) :=
  inferInstance
#print axioms CategoryTheory.LaxDoubleFunctor.laxDoubleCategoryStruct
#print axioms CategoryTheory.LaxDoubleFunctor.laxDoubleCategory
#print axioms laxStructWitness
#print axioms laxLawfulWitness
#print axioms laxLaxWitness
#print axioms laxLooseBicatWitness

@[reducible] noncomputable def spanStructWitness :
    PseudoDoubleCategoryStruct (Span (Type 0)) :=
  inferInstance

/-- Witness: the double category of spans of types is lawful. -/
theorem spanLawfulWitness : PseudoDoubleCategory (Span (Type 0)) :=
  inferInstance

@[reducible] def spanEquipmentWitness : Equipment (Span (Type 0)) := inferInstance

/-- Witness: companions in `Span`. -/
noncomputable def spanCompanionWitness : Companion (𝟙 (Span.mk Bool)) :=
  Equipment.companion (𝟙 _)

noncomputable def spanConjointWitness : Conjoint (𝟙 (Span.mk Bool)) :=
  Equipment.conjoint (𝟙 _)

noncomputable def spanCompanionCompWitness :
    Companion (𝟙 (Span.mk Bool) ≫ 𝟙 (Span.mk Bool)) :=
  (Span.companion (𝟙 _)).comp (Span.companion (𝟙 _))

@[reducible] noncomputable def spanLooseBicatWitness :
    Bicategory (LooseBicat (Span (Type 0))) :=
  inferInstance
#print axioms CategoryTheory.SpanCell.heq_of_hom
#print axioms CategoryTheory.Span.instPseudoDoubleCategoryStruct
#print axioms CategoryTheory.Span.instPseudoDoubleCategory
#print axioms CategoryTheory.Span.companion
#print axioms CategoryTheory.Span.conjoint
#print axioms CategoryTheory.Span.instEquipment
#print axioms spanStructWitness
#print axioms spanLawfulWitness
#print axioms spanEquipmentWitness
#print axioms spanCompanionWitness
#print axioms spanConjointWitness
#print axioms spanCompanionCompWitness
#print axioms spanLooseBicatWitness

@[reducible] def depSpanStructWitness :
    PseudoDoubleCategoryStruct (Type 0) :=
  inferInstance

theorem depSpanLawfulWitness : PseudoDoubleCategory (Type 0) :=
  inferInstance

@[reducible] def depSpanEquipmentWitness : Equipment (Type 0) :=
  inferInstance

def depSpanCompanionWitness : Companion (𝟙 (Bool : Type 0)) :=
  Equipment.companion (𝟙 _)

def depSpanConjointWitness : Conjoint (𝟙 (Bool : Type 0)) :=
  Equipment.conjoint (𝟙 _)

def depSpanCompanionCompWitness :
    Companion (𝟙 (Bool : Type 0) ≫ 𝟙 (Bool : Type 0)) :=
  (DepSpan.companion (𝟙 _)).comp (DepSpan.companion (𝟙 _))

@[reducible] def depSpanLooseBicatWitness :
    Bicategory (LooseBicat (Type 0)) :=
  inferInstance
#print axioms CategoryTheory.DepSpan.instPseudoDoubleCategoryStruct
#print axioms CategoryTheory.DepSpan.instPseudoDoubleCategory
#print axioms CategoryTheory.DepSpan.companion
#print axioms CategoryTheory.DepSpan.conjoint
#print axioms CategoryTheory.DepSpan.instEquipment
#print axioms depSpanStructWitness
#print axioms depSpanLawfulWitness
#print axioms depSpanEquipmentWitness
#print axioms depSpanCompanionWitness
#print axioms depSpanConjointWitness
#print axioms depSpanCompanionCompWitness
#print axioms depSpanLooseBicatWitness

#print axioms CategoryTheory.SpanValued.GLoose.id
#print axioms CategoryTheory.SpanValued.GLoose.comp
#print axioms CategoryTheory.SpanValued.GCell.ext
#print axioms CategoryTheory.SpanValued.GCell.vId
#print axioms CategoryTheory.SpanValued.GCell.vComp
#print axioms CategoryTheory.SpanValued.GCell.hId

#print axioms CategoryTheory.DepSpan.comp_heq
#print axioms CategoryTheory.SpanValued.GCell.hComp
#print axioms CategoryTheory.SpanValued.GCell.dec_inv
#print axioms CategoryTheory.SpanValued.GCell.lAssoc
#print axioms CategoryTheory.SpanValued.GCell.lAssocInv
#print axioms CategoryTheory.SpanValued.GCell.lLeftUnitor
#print axioms CategoryTheory.SpanValued.GCell.lLeftUnitorInv
#print axioms CategoryTheory.SpanValued.GCell.lRightUnitor
#print axioms CategoryTheory.SpanValued.GCell.lRightUnitorInv
#print axioms CategoryTheory.SpanValued.GCell.heq_ext
#print axioms CategoryTheory.SpanValued.instPseudoDoubleCategoryStruct
#print axioms CategoryTheory.SpanValued.instPseudoDoubleCategory
#print axioms CategoryTheory.SpanValued.proj
#print axioms CategoryTheory.SpanValued.proj_isPseudo

@[reducible] def grothStructWitness :
    PseudoDoubleCategoryStruct
      (SpanValued.Grothendieck
        (LaxDoubleFunctor.id : SpanValued (Type 0))) :=
  inferInstance

theorem grothLawfulWitness :
    PseudoDoubleCategory
      (SpanValued.Grothendieck
        (LaxDoubleFunctor.id : SpanValued (Type 0))) :=
  inferInstance

def grothProjWitness :
    LaxDoubleFunctor
      (SpanValued.Grothendieck
        (LaxDoubleFunctor.id : SpanValued (Type 0))) (Type 0) :=
  SpanValued.proj _

theorem grothProjPseudoWitness :
    (SpanValued.proj (LaxDoubleFunctor.id : SpanValued (Type 0))).IsPseudo :=
  SpanValued.proj_isPseudo _

def grothLooseCompWitness :
    SpanValued.GLoose
      (F := (LaxDoubleFunctor.id : SpanValued (Type 0)))
      ⟨Bool, true⟩ ⟨Bool, true⟩ :=
  (SpanValued.GLoose.id _).comp (SpanValued.GLoose.id _)
#print axioms grothStructWitness
#print axioms grothLawfulWitness
#print axioms grothProjWitness
#print axioms grothProjPseudoWitness
#print axioms grothLooseCompWitness

def gmapWitness :
    LaxDoubleFunctor
      (SpanValued.Grothendieck
        (LaxDoubleFunctor.id : SpanValued (Type 0)))
      (SpanValued.Grothendieck
        (LaxDoubleFunctor.id : SpanValued (Type 0))) :=
  SpanValued.gmap (TightTransformation.id _)

def grothFunctorWitness : SpanValued (Type 0) ⥤ Dbl :=
  SpanValued.grothendieckFunctor (Type 0)
#print axioms CategoryTheory.SpanValued.gmapElements

#print axioms CategoryTheory.SpanValued.gmapElements_eq_map
#print axioms CategoryTheory.SpanValued.gmapLoose
#print axioms CategoryTheory.SpanValued.gmapCell
#print axioms CategoryTheory.SpanValued.gmapLaxComp
#print axioms CategoryTheory.SpanValued.gmapLaxId
#print axioms CategoryTheory.SpanValued.gmap
#print axioms CategoryTheory.SpanValued.gmap_id
#print axioms CategoryTheory.SpanValued.gmap_comp
#print axioms CategoryTheory.SpanValued.gmap_proj
#print axioms CategoryTheory.SpanValued.grothendieckFunctor
#print axioms gmapWitness
#print axioms grothFunctorWitness

def tightTwoCellReflWitness :
    SpanValued.TightTwoCell
      (TightTransformation.id (LaxDoubleFunctor.id : SpanValued (Type 0)))
      (TightTransformation.id LaxDoubleFunctor.id) :=
  SpanValued.TightTwoCell.refl _

def gmapTwoCellWitness :
    TightTransformation
      (SpanValued.gmap
        (TightTransformation.id (LaxDoubleFunctor.id : SpanValued (Type 0))))
      (SpanValued.gmap (TightTransformation.id LaxDoubleFunctor.id)) :=
  SpanValued.gmapTwoCell tightTwoCellReflWitness
#print axioms CategoryTheory.DepSpan.lRightUnitor_apply_heq
#print axioms CategoryTheory.DepSpan.comp_snd_heq
#print axioms CategoryTheory.SpanValued.TightTwoCell.app_eq
#print axioms CategoryTheory.SpanValued.TightTwoCell.looseApp_heq
#print axioms CategoryTheory.SpanValued.TightTwoCell.discrete
#print axioms CategoryTheory.SpanValued.TightTwoCell.refl
#print axioms CategoryTheory.SpanValued.gmapTwoCell
#print axioms CategoryTheory.SpanValued.gmapTwoCell_refl
#print axioms CategoryTheory.Modification.toTightTwoCell
#print axioms CategoryTheory.SpanValued.discrete_of_modification
#print axioms tightTwoCellReflWitness
#print axioms gmapTwoCellWitness

@[reducible] def dblCatWitness : Category Dbl.{0, 0, 0, 0} := inferInstance
#print axioms dblCatWitness

/-! ### Virtual double categories -/

/-- Witness: the underlying virtual double category structure of the
double category of commutative squares. -/
def sqVirtualStructWitness : VirtualDoubleCategoryStruct (Sq PtCat) :=
  VirtualDoubleCategoryStruct.ofPseudo

/-- Witness: the underlying virtual double category of a thin pseudo
double category is lawful. -/
theorem sqVirtualLawfulWitness :
    @VirtualDoubleCategory (Sq PtCat) _ sqVirtualStructWitness :=
  VirtualDoubleCategoryStruct.ofPseudo_lawful fun _ _ _ _ => inferInstance

section
attribute [local instance] sqVirtualStructWitness

/-- Witness: the free promotion of a virtual double category is a pseudo
double category by instance search. -/
def freePromotionStructWitness :
    PseudoDoubleCategoryStruct (FreePromotion (Sq PtCat)) := inferInstance

/-- Witness: the free promotion's axioms hold. -/
theorem freePromotionLawfulWitness :
    PseudoDoubleCategory (FreePromotion (Sq PtCat)) := inferInstance

end

#print axioms CategoryTheory.LoosePath.comp_assoc
#print axioms CategoryTheory.VirtualDoubleCategory.of_subsingleton
#print axioms CategoryTheory.VirtualDoubleCategoryStruct.compUnder
#print axioms CategoryTheory.VirtualDoubleCategoryData.CellSeq.split
#print axioms CategoryTheory.VirtualDoubleCategoryData.CellSeq.nonempty_vcomp
#print axioms CategoryTheory.VirtualDoubleCategoryStruct.ofPseudo
#print axioms CategoryTheory.VirtualDoubleFunctor.ofThin
#print axioms sqVirtualStructWitness
#print axioms sqVirtualLawfulWitness
#print axioms freePromotionStructWitness
#print axioms freePromotionLawfulWitness
#print axioms CategoryTheory.VSpanValued.vproj_isDiscreteOpfibration
#print axioms CategoryTheory.SpanValued.restrictVirtual
#print axioms CategoryTheory.SpanValued.stratum1CellEquiv
#print axioms CategoryTheory.SpanValued.foldGLoose_dec
#print axioms CategoryTheory.SpanValued.restrictVirtual_vproj_isDiscreteOpfibration

/-! ## The wiring base and the plain-side opfibration -/

section

open CategoryTheory.WireSpan

/-- Witness: the wiring base's double category structure is found by
instance search. -/
@[reducible] def wireSpanStructWitness :
    PseudoDoubleCategoryStruct (WireSpan PUnit.{1}) := inferInstance

/-- Witness: the wiring base's axioms hold. -/
theorem wireSpanLawfulWitness : PseudoDoubleCategory (WireSpan PUnit.{1}) :=
  inferInstance

end

#print axioms CategoryTheory.WireSpan.instPseudoDoubleCategory
#print axioms CategoryTheory.WireSpan.compFst_compFst_tot_lAssoc
#print axioms CategoryTheory.SpanValued.proj_isDiscreteOpfibration
#print axioms wireSpanStructWitness
#print axioms wireSpanLawfulWitness
#print axioms CategoryTheory.SpanValued.bmap
#print axioms CategoryTheory.SpanValued.bmap_proj
#print axioms CategoryTheory.SpanValued.bmap_pushGLoose
