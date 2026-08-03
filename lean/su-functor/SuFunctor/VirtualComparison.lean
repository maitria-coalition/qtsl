import SuFunctor.Virtual
import DoubleCat.Virtual.FreePromotion

/-! # The two repaired presentations, compared

Two architectural repairs of the refuted loose composition were on the
table (recorded with the countermodels): *composition as formal
conjunction* — loose arrows become finite lists of judgments, loose
composition is concatenation — and *virtual double category source* —
loose composition is dropped and cells take lists of judgments as loose
domains.  This module makes their relationship a theorem shape: **the
formal-conjunction presentation is the free promotion of the virtual
one.**

Concretely, `FreePromotion (BLV H F)` (the general construction of
`DoubleCat.Virtual.FreePromotion`, instantiated at the source virtual
double category) *is* a formal-conjunction double category:

* its loose arrows are strings over the single object, equivalent to
  `List Judgment` (`loosePathEquivList`), carrying loose composition to
  concatenation (`BLV.pathToList_comp`) and the loose identity to the
  empty list (`BLV.pathToList_nil`);
* its cells from `ps` to `qs` are inhabited exactly when the judgment
  list of `qs` is derivable *blockwise* from a partition of the judgment
  list of `ps` (`freePromotion_cell_iff`), the relation `ListDeriv` —
  formal-conjunction entailment generated pointwise by the virtual
  cells.

A formal-conjunction presentation built independently (lists as loose
arrows, concatenation as composition, a list-level entailment calculus
as cells) therefore agrees with the free promotion of this one exactly
when its cell relation is inter-derivable with `ListDeriv`; that
inter-derivability is the precise, checkable content of "the list
presentation is the free promotion of the virtual presentation", stated
here entirely on this development's side of the comparison.  (For the
repaired presentation of `SuFunctorLegacy.Source` the inter-derivability is
proven: `listDeriv_iff_jderiv` in `SuFunctorLegacy.Transpose`.)

Of the promotion's universal property, the existence direction — a
functor of virtual double categories into an underlying pseudo double
category induces one out of the promotion — is mechanized for thin
targets in `DoubleCat.Virtual.Promote` and instantiated in
`SuFunctorLegacy.Transpose`; the full adjunction (uniqueness, triangle
identities) remains deliberately unmechanized, per the module docstring
of `DoubleCat.Virtual.FreePromotion`.
-/

namespace SuFunctor

namespace Virtual

open PPLC CategoryTheory VirtualDoubleCategoryData VirtualDoubleCategoryStruct

namespace BLV

variable {H : Hypernet} {F : RuleFamily H}

/-- Read a list of judgments as a string of loose arrows over the single
object. -/
def listToPath : List Judgment → LoosePath (fun _ _ => Judgment)
    (BLV.mk' : BLV H F) BLV.mk'
  | [] => .nil
  | j :: js => .cons j (listToPath js)

@[simp] theorem listToPath_nil :
    listToPath ([] : List Judgment) = (.nil : LoosePath _ (BLV.mk' : BLV H F) _) :=
  rfl

@[simp] theorem listToPath_cons (j : Judgment) (js : List Judgment) :
    (listToPath (j :: js) : LoosePath _ (BLV.mk' : BLV H F) _) =
      .cons j (listToPath js) := rfl

@[simp] theorem pathToList_listToPath :
    ∀ js : List Judgment,
      pathToList (listToPath js : LoosePath _ (BLV.mk' : BLV H F) _) = js
  | [] => rfl
  | j :: js => congrArg (j :: ·) (pathToList_listToPath js)

@[simp] theorem listToPath_pathToList :
    ∀ {a b : BLV H F} (ps : LoosePath (fun _ _ => Judgment) a b),
      listToPath (pathToList ps) = ps := by
  intro a b ps
  induction ps with
  | nil => rfl
  | cons j ps ih =>
      show LoosePath.cons j (listToPath (pathToList ps)) = LoosePath.cons j ps
      rw [ih]

theorem listToPath_append : ∀ (l₁ l₂ : List Judgment),
    (listToPath (l₁ ++ l₂) : LoosePath _ (BLV.mk' : BLV H F) _) =
      (listToPath l₁).comp (listToPath l₂) := by
  intro l₁ l₂
  induction l₁ with
  | nil => rfl
  | cons j l₁ ih =>
      show LoosePath.cons j (listToPath (l₁ ++ l₂)) =
        LoosePath.cons j ((listToPath l₁).comp (listToPath l₂))
      rw [ih]

/-- Strings over the single object are lists of judgments; under this
equivalence, loose composition of the free promotion is concatenation
(`pathToList_comp`) and the loose identity is the empty list
(`pathToList_nil`). -/
def loosePathEquivList {a b : BLV H F} :
    LoosePath (fun _ _ => Judgment) a b ≃ List Judgment where
  toFun := pathToList
  invFun := listToPath
  left_inv := listToPath_pathToList
  right_inv := pathToList_listToPath

end BLV

variable {H : Hypernet} {F : RuleFamily H}

/-- Formal-conjunction entailment between judgment lists, generated
pointwise by the virtual cells: `qs` is derivable blockwise from a
partition of `ps`.  This is the cell relation the formal-conjunction
(list) presentation carries when it is the free promotion of the
virtual presentation. -/
def ListDeriv (H : Hypernet) (F : RuleFamily H)
    (ps qs : List Judgment) : Prop :=
  ∃ pss : List (List Judgment),
    List.Forall₂ (Deriv H F) pss qs ∧ pss.flatten = ps

/-- Blockwise derivations assemble into a covering sequence (over
canonical strings). -/
theorem cellSeq_of_forall₂ {qs : List Judgment}
    {pss : List (List Judgment)}
    (hf : List.Forall₂ (Deriv H F) pss qs) :
    Nonempty (CellSeq (BLV.listToPath qs)
      (BLV.listToPath pss.flatten : LoosePath _ (BLV.mk' : BLV H F) _)
      (⟨⟩ : PUnit) (⟨⟩ : PUnit)) := by
  induction hf with
  | nil => exact ⟨.nil _⟩
  | @cons ps q pss' qs' h _ ih =>
      obtain ⟨V⟩ := ih
      have hcell : Deriv H F (BLV.pathToList
          (BLV.listToPath ps : LoosePath _ (BLV.mk' : BLV H F) _)) q := by
        rw [BLV.pathToList_listToPath]; exact h
      have W : CellSeq (BLV.listToPath (q :: qs'))
          ((BLV.listToPath ps : LoosePath _ (BLV.mk' : BLV H F) _).comp
            (BLV.listToPath pss'.flatten)) (⟨⟩ : PUnit) (⟨⟩ : PUnit) :=
        .cons (PLift.up hcell) V
      exact ⟨W.castDom (BLV.listToPath_append ps pss'.flatten).symm⟩

/-- **The comparison theorem at the instance**: a cell of the free
promotion of the virtual presentation — a covering of `qs` by multicells
whose domains concatenate to `ps` — exists exactly when the judgment
list of `qs` is blockwise derivable from a partition of the judgment
list of `ps`.  Together with `BLV.loosePathEquivList` (strings are
lists, concatenation is composition), this says `FreePromotion (BLV H F)`
*is* the formal-conjunction double category over the virtual cells: the
checkable form of "the list presentation is the free promotion of the
virtual one". -/
theorem freePromotion_cell_iff {a b c d : BLV H F}
    {qs : LoosePath Loose c d} {ps : LoosePath Loose a b}
    {u : a ⟶ c} {v : b ⟶ d} :
    Nonempty (CellSeq qs ps u v) ↔
      ListDeriv H F (BLV.pathToList ps) (BLV.pathToList qs) := by
  constructor
  · rintro ⟨V⟩
    exact BLV.cellSeq_deriv V
  · rintro ⟨pss, hf, hflat⟩
    obtain ⟨V⟩ := cellSeq_of_forall₂ hf
    cases u; cases v
    have hq : (BLV.listToPath (BLV.pathToList qs) : LoosePath _ _ _) = qs :=
      BLV.listToPath_pathToList qs
    have hp : (BLV.listToPath pss.flatten : LoosePath _ _ _) = ps := by
      rw [hflat]; exact BLV.listToPath_pathToList ps
    exact ⟨(V.castDom hp).castCod hq⟩

/-- The free promotion of the source virtual double category is a pseudo
double category, by instance search: the comparison object exists as a
term of the library's own class. -/
example : PseudoDoubleCategory (FreePromotion (BLV H F)) := inferInstance

end Virtual

end SuFunctor
