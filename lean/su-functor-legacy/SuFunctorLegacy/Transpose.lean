/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the route-agreement theorem (`transpose_eq_semFunctor`)
together with conservativity (`unit_fullyFaithful`) and the calculus
dictionary (`listDeriv_iff_jderiv`) for the two presentations of the
retired routes.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.VirtualFunctor
import SuFunctor.VirtualComparison
import DoubleCat.Virtual.Promote

/-! # The transpose at the instance: the two repairs are one structure

`SuFunctorLegacy.Source` and `SuFunctor.Virtual` are the two architectural
repairs of the refuted kind-table composition: *formal conjunction*
(loose arrows are judgment lists, composing by concatenation, cells the
entailment calculus `JDeriv`) and the *virtual presentation* (loose
arrows stay single judgments, cells take premise lists, no composition
exists).  `SuFunctor.VirtualComparison` made their relationship a
theorem shape — the formal-conjunction presentation should be the free
promotion of the virtual one — and proved the cell condition
(`freePromotion_cell_iff`).  This module finishes the comparison and
transports the semantics across it:

* **the family dictionary**: a virtual rule family reads as a
  formal-conjunction family (`RuleFamily.toConj` — premises verbatim,
  the conclusion as a singleton list; `SemRuleFamily.toConj` carries the
  squares), inverse in shape to `SuFunctor.Virtual.ofConj`;
* **conservativity** (`unit_fullyFaithful`): promotion cells into a
  *singleton* string are exactly the virtual multicells — the unit of
  the promotion is fully faithful on multicells.  Both sides are
  subsingleton propositions, so the iff is the bijection.  The edge
  case beside it (`listDeriv_nil_iff`): the only cell into the *empty*
  string is the identity at the empty string — codomain `[j]` is the
  faithful stratum, codomain `[]` is trivial;
* **the calculus dictionary** (`listDeriv_iff_jderiv`): blockwise
  derivability over a virtual family is exactly `JDeriv` over its
  conjunctified family — the inter-derivability that
  `SuFunctor.VirtualComparison` names as the checkable content of the
  comparison, both directions.  (`JDeriv`'s structure cells map to
  identity partitions; transitivity of blockwise derivability is the
  promotion's own vertical composition, `CellSeq.nonempty_vcomp`.)
* **the transpose** (`transposeSemFunctor`): the pseudo double functor
  `FreePromotion (BLV H F.rules) ⥤ Crd (AdmVal H)` induced by
  `semVirtualFunctor` through the promotion's universal property
  (`VirtualDoubleFunctor.promoteThin`, the existence direction,
  mechanized for thin targets in `DoubleCat.Virtual.Promote`);
* **the crown** (`transpose_eq_semFunctor`): the transpose *is*
  `semFunctor` — equal, as lax double functors, to the composite of the
  comparison functor `FreePromotion (BLV H F.rules) ⥤ BLD H
  F.rules.toConj` (strings to lists, coverings to derivations) with
  `semFunctor H F.toConj`.  The proof is exactly the thin-case
  bookkeeping the statement deserves: the underlying functors agree
  definitionally, the loose actions agree because folding a mapped
  string computes pointwise satisfaction (`foldMap_sat`; `SatList` and
  `SatConj` are one definition), and the cell actions then agree by
  proof irrelevance (`LaxDoubleFunctor.ext_of_thin`);
* **soundness, inherited** (`soundness_inherited`): the composed
  statement — a proof object's sequent is semantically valid — through
  the virtual route and the dictionary, with `satCoherence` and
  `JDeriv.sem` nowhere in the derivation.  Soundness is proven once,
  virtually (`Deriv.sem`), and the formal-conjunction presentation
  inherits it across the promotion; `semFunctor_cell_inherited` is the
  cell-level form (the transpose's action on any promotion cell, in
  list vocabulary).

Restriction remark (prose only, mechanization deliberately not
undertaken; Cruttwell–Shulman, "A unified framework for generalized
multicategories", 2010, §5, §7): the promotion is the left adjoint to
the underlying-virtual-double-category functor, and the adjunction
restricts to an equivalence between *representable* virtual double
categories — those with units and all composites — and pseudo double
categories.  `FreePromotion (BLV H F)` is representable by
construction; `BLV H F` itself is not (that is the point: cut's premise
pair has no composite to be represented by). -/

namespace SuFunctor

namespace Virtual

open PPLC CategoryTheory VirtualDoubleCategoryData VirtualDoubleCategoryStruct

variable {H : Hypernet}

/-! ## The family dictionary -/

/-- A virtual rule family, read as a formal-conjunction family: premises
verbatim, the conclusion as a singleton list.  Inverse in shape to
`SuFunctor.Virtual.ofConj` (which reads a formal-conjunction family
blockwise, one virtual instance per conclusion judgment); on families
with singleton conclusions the two translations are mutually inverse up
to tag bookkeeping. -/
def RuleFamily.toConj (F : RuleFamily H) : SuFunctor.RuleFamily H where
  Tag := F.Tag
  gate := F.gate
  top := F.tops
  bot := fun t => [F.bot t]

/-- The semantic form of the dictionary: squares carry over on the nose
(`SatList` and `SatConj` are one definition; only the singleton wrapper
on the conclusion moves). -/
def SemRuleFamily.toConj (F : SemRuleFamily H) : SuFunctor.SemRuleFamily H where
  rules := F.rules.toConj
  square := fun t ht μ h => satConj_singleton.mpr (F.square t ht μ h)

/-- The two loose semantic readings are one definition. -/
theorem satList_eq_satConj (js : List Judgment) :
    SatList H js = SatConj H js := rfl

/-! ## The `ListDeriv` calculus

`ListDeriv` (blockwise derivability, `SuFunctor.VirtualComparison`) is
the cell relation of the free promotion in list vocabulary
(`freePromotion_cell_iff`).  The promotion is a pseudo double category,
so the relation is reflexive, transitive, and monoidal; reflexivity and
monoidality are direct, and transitivity is inherited from the
promotion's vertical composition rather than re-proved by list
surgery. -/

variable {F : RuleFamily H}

private theorem forall₂_append {α β : Type _} {R : α → β → Prop}
    {l₁ l₂ : List α} {u₁ u₂ : List β}
    (h₁ : List.Forall₂ R l₁ u₁) (h₂ : List.Forall₂ R l₂ u₂) :
    List.Forall₂ R (l₁ ++ l₂) (u₁ ++ u₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

/-- Blockwise derivability is reflexive: the identity partition. -/
theorem ListDeriv.refl (l : List Judgment) : ListDeriv H F l l := by
  refine ⟨l.map fun j => [j], ?_, ?_⟩
  · induction l with
    | nil => exact .nil
    | cons j l ih => exact .cons (Deriv.refl j) ih
  · induction l with
    | nil => rfl
    | cons j l ih => simp [ih]

/-- `freePromotion_cell_iff`, read at canonical strings: the cells of the
free promotion between the strings of two lists are exactly blockwise
derivability between the lists. -/
theorem nonempty_cellSeq_iff_listDeriv {ps qs : List Judgment} :
    Nonempty (CellSeq (BLV.listToPath qs : LoosePath _ (BLV.mk' : BLV H F) _)
      (BLV.listToPath ps) (⟨⟩ : PUnit) (⟨⟩ : PUnit)) ↔
      ListDeriv H F ps qs := by
  rw [freePromotion_cell_iff, BLV.pathToList_listToPath,
    BLV.pathToList_listToPath]

/-- Blockwise derivability is transitive — by the promotion's own
vertical composition (`CellSeq.nonempty_vcomp`), not by list surgery. -/
theorem ListDeriv.trans {l₁ l₂ l₃ : List Judgment}
    (h₁ : ListDeriv H F l₁ l₂) (h₂ : ListDeriv H F l₂ l₃) :
    ListDeriv H F l₁ l₃ := by
  rw [← nonempty_cellSeq_iff_listDeriv] at h₁ h₂ ⊢
  obtain ⟨B⟩ := h₂
  exact CellSeq.nonempty_vcomp B h₁

/-- Blockwise derivability is monoidal: partitions concatenate. -/
theorem ListDeriv.hcomp {m₁ n₁ m₂ n₂ : List Judgment}
    (h₁ : ListDeriv H F m₁ n₁) (h₂ : ListDeriv H F m₂ n₂) :
    ListDeriv H F (m₁ ++ m₂) (n₁ ++ n₂) := by
  obtain ⟨pss₁, hf₁, rfl⟩ := h₁
  obtain ⟨pss₂, hf₂, rfl⟩ := h₂
  exact ⟨pss₁ ++ pss₂, forall₂_append hf₁ hf₂, by simp⟩

/-- Blockwise derivability into a singleton is one virtual multicell: a
partition covering one judgment has exactly one block, and that block is
everything. -/
theorem listDeriv_singleton_iff {ps : List Judgment} {j : Judgment} :
    ListDeriv H F ps [j] ↔ Deriv H F ps j := by
  constructor
  · rintro ⟨pss, hf, hflat⟩
    cases hf with
    | cons h hf' =>
        cases hf'
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
          at hflat
        exact hflat ▸ h
  · intro d
    exact ⟨[ps], .cons d .nil, by simp⟩

/-- The edge case beside conservativity: the only string with a cell
into the *empty* string is the empty string itself (a partition indexed
by nothing flattens to nothing).  Cells into the loose identity are
trivial; the faithful stratum is the singleton codomain. -/
theorem listDeriv_nil_iff {ps : List Judgment} :
    ListDeriv H F ps [] ↔ ps = [] := by
  constructor
  · rintro ⟨pss, hf, hflat⟩
    cases hf
    simpa using hflat.symm
  · rintro rfl
    exact ListDeriv.refl []

/-! ## Conservativity: the unit is fully faithful on multicells -/

/-- **Conservativity of the promotion.**  A cell of the free promotion
from a string `ps` into a *singleton* string is exactly a multicell of
the virtual presentation: the unit `BLV H F ⥤ᵥ FreePromotion (BLV H F)`
(judgments to singleton strings, multicells to one-block coverings) is
fully faithful on multicells.  Both sides are subsingleton propositions
— `Deriv` is a `Prop` and the promotion's cells are the existence of a
covering — so this iff *is* the bijection on cell sets.  Nothing is
gained and nothing is lost in the promotion: new cells appear only
between genuinely composite strings, where the virtual presentation had
no boundary to write. -/
theorem unit_fullyFaithful {a b c d : BLV H F} {ps : LoosePath Loose a b}
    {j : Loose c d} {u : a ⟶ c} {v : b ⟶ d} :
    Nonempty (CellSeq (.single j) ps u v) ↔
      Deriv H F (BLV.pathToList ps) j := by
  rw [freePromotion_cell_iff]
  exact listDeriv_singleton_iff

/-! ## The calculus dictionary: `ListDeriv` is `JDeriv`, conjunctified -/

/-- A virtual multicell is a one-conclusion derivation of the
formal-conjunction calculus over the conjunctified family.  Generators
map to generators; splicing is horizontal pasting against identities,
one associator to regroup, and transitivity. -/
theorem Deriv.toJDeriv {ps : List Judgment} {q : Judgment}
    (d : Deriv H F ps q) : JDeriv H F.toConj ps [q] := by
  induction d with
  | ofRule t ht => exact JDeriv.ofRule (F := F.toConj) t ht
  | ofProof po => exact .ofProof po
  | refl j => exact .refl [j]
  | @splice as cs ps' b r _ _ ihmain ihinner =>
      exact JDeriv.trans
        (JDeriv.trans
          (JDeriv.hcomp (JDeriv.hcomp (JDeriv.refl as) ihinner)
            (JDeriv.refl cs))
          (JDeriv.assoc as [b] cs))
        ihmain

/-- Blockwise derivability maps into the formal-conjunction calculus:
concatenate the blocks' one-conclusion derivations horizontally. -/
theorem ListDeriv.toJDeriv {ps qs : List Judgment}
    (ld : ListDeriv H F ps qs) : JDeriv H F.toConj ps qs := by
  obtain ⟨pss, hf, rfl⟩ := ld
  induction hf with
  | nil => exact .refl []
  | cons h _ ih =>
      rw [List.flatten_cons]
      exact JDeriv.hcomp (Deriv.toJDeriv h) ih

/-- The formal-conjunction calculus over a conjunctified family maps
back to blockwise derivability: generators become one-block partitions,
the categorical closure becomes the promotion's own composition, and the
structure cells become identity partitions along list identities. -/
theorem JDeriv.toListDeriv {l l' : List Judgment}
    (d : JDeriv H F.toConj l l') : ListDeriv H F l l' := by
  induction d with
  | ofRule t ht =>
      exact ⟨[F.tops t], .cons (.ofRule t ht) .nil,
        by simp [RuleFamily.toConj]⟩
  | ofProof po => exact ⟨[[]], .cons (.ofProof po) .nil, by simp⟩
  | refl l => exact ListDeriv.refl l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | hcomp _ _ ih₁ ih₂ => exact ih₁.hcomp ih₂
  | assoc m n p => rw [List.append_assoc]; exact ListDeriv.refl _
  | assocInv m n p => rw [List.append_assoc]; exact ListDeriv.refl _
  | unitL m => exact ListDeriv.refl m
  | unitLInv m => exact ListDeriv.refl m
  | unitR m => rw [List.append_nil]; exact ListDeriv.refl m
  | unitRInv m => rw [List.append_nil]; exact ListDeriv.refl m

/-- **The calculus dictionary**: blockwise derivability over a virtual
family is inter-derivable with the formal-conjunction calculus over its
conjunctified family — the checkable content of "the list presentation
is the free promotion of the virtual one", now proved for the repaired
presentation of `SuFunctorLegacy.Source` (not merely stated against a
hypothetical list presentation). -/
theorem listDeriv_iff_jderiv {l l' : List Judgment} :
    ListDeriv H F l l' ↔ JDeriv H F.toConj l l' :=
  ⟨ListDeriv.toJDeriv, JDeriv.toListDeriv⟩

/-- **Cell agreement**: the cells of the free promotion are the cells of
the formal-conjunction double category, across strings-are-lists.  With
`BLV.loosePathEquivList` (loose arrows and their composition) and the
trivial object/tight agreement, this is the equivalence
`FreePromotion (BLV H F) ≃ BLD H F.toConj` stated componentwise. -/
theorem cell_agreement {a b c d : BLV H F} {ps : LoosePath Loose a b}
    {qs : LoosePath Loose c d} {u : a ⟶ c} {v : b ⟶ d} :
    Nonempty (CellSeq qs ps u v) ↔
      JDeriv H F.toConj (BLV.pathToList ps) (BLV.pathToList qs) :=
  freePromotion_cell_iff.trans listDeriv_iff_jderiv

/-! ## The comparison functor and the transpose -/

/-- The compositor content of the comparison functor: reading a
concatenated string is concatenating the read lists, so the comparison
cell is an identity derivation along `pathToList_comp`. -/
theorem jderiv_concat_refl (F : RuleFamily H) {a b c : BLV H F}
    (ps : LoosePath Loose a b) (qs : LoosePath Loose b c) :
    JDeriv H F.toConj (BLV.pathToList ps ++ BLV.pathToList qs)
      (BLV.pathToList (ps.comp qs)) := by
  rw [BLV.pathToList_comp]
  exact JDeriv.refl _

/-- The comparison functor `FreePromotion (BLV H F) ⥤ BLD H F.toConj`:
strings to lists (`BLV.pathToList`), coverings to derivations (the
forward direction of `cell_agreement`).  Its compositor and unit
comparison are identities along `pathToList_comp` and `pathToList_nil` —
strings-are-lists is loose-structure-preserving on the nose. -/
def comparisonFunctor (H : Hypernet) (F : RuleFamily H) :
    LaxDoubleFunctor (FreePromotion (BLV H F)) (BLD H F.toConj) where
  toFunctor :=
    { obj := fun _ => BLD.mk'
      map := fun _ => ⟨⟩ }
  mapLoose := fun {_ _} ps => BLV.pathToList ps
  mapCell α := ⟨ListDeriv.toJDeriv (freePromotion_cell_iff.mp α.down)⟩
  mapCell_vId _ := Subsingleton.elim _ _
  mapCell_vComp _ _ := Subsingleton.elim _ _
  laxComp ps qs := ⟨jderiv_concat_refl F ps qs⟩
  laxId _ := ⟨JDeriv.refl []⟩
  laxComp_natural _ _ := Subsingleton.elim _ _
  laxId_natural _ := Subsingleton.elim _ _
  laxComp_assoc _ _ _ := Subsingleton.elim _ _
  laxComp_leftUnitor _ := Subsingleton.elim _ _
  laxComp_rightUnitor _ := Subsingleton.elim _ _

/-- **The transpose**: the pseudo double functor
`FreePromotion (BLV H F.rules) ⥤ Crd (AdmVal H)` induced by the
semantic functor of virtual double categories through the promotion's
universal property (existence direction, `promoteThin`). -/
noncomputable def transposeSemFunctor (H : Hypernet) (F : SemRuleFamily H) :
    LaxDoubleFunctor (FreePromotion (BLV H F.rules)) (Crd (AdmVal H)) :=
  (semVirtualFunctor H F).promoteThin fun _ _ _ _ =>
    inferInstanceAs (Subsingleton (PLift _))

/-- The transpose is pseudo, inherited from `promoteThin_isPseudo`. -/
theorem transposeSemFunctor_isPseudo (H : Hypernet) (F : SemRuleFamily H) :
    (transposeSemFunctor H F).IsPseudo :=
  VirtualDoubleFunctor.promoteThin_isPseudo _ _

/-- **Loose agreement**: the transpose reads a string as the fold of its
judgments' satisfaction constraints, and that fold *is* conjunctive
satisfaction of the underlying list (`foldMap_sat`, plus propositional
and functional extensionality). -/
theorem transpose_mapLoose (H : Hypernet) (F : SemRuleFamily H)
    {a b : FreePromotion (BLV H F.rules)}
    (ps : PseudoDoubleCategoryStruct.Loose a b) :
    (transposeSemFunctor H F).mapLoose ps = SatConj H (BLV.pathToList ps) := by
  funext μ
  exact propext (foldMap_sat ps μ)

/-- **The crown: the adjoint transpose of the virtual semantic functor
is the semantic functor of the formal-conjunction presentation.**  As
lax double functors out of the free promotion,

`transposeSemFunctor H F = comparisonFunctor H F.rules ⋙ semFunctor H F.toConj`.

Soundness content and coherence content coincide across the promotion:
the underlying functors agree definitionally (both constant at the
single scene), the loose actions agree because folding a mapped string
computes pointwise satisfaction of the underlying list
(`transpose_mapLoose`), and the cell actions agree by proof irrelevance
in the thin target — which is exactly where `cell_agreement` has already
matched the cells one-to-one. -/
theorem transpose_eq_semFunctor (H : Hypernet) (F : SemRuleFamily H) :
    transposeSemFunctor H F =
      (comparisonFunctor H F.rules).comp (semFunctor H F.toConj) := by
  refine LaxDoubleFunctor.ext_of_thin
    (fun _ _ _ _ => inferInstanceAs (Subsingleton (PLift _))) rfl ?_
  intro a b ps
  exact heq_of_eq (transpose_mapLoose H F ps)

/-! ## Soundness, inherited -/

/-- Blockwise semantic reading: the transpose's action on a promotion
cell, in list vocabulary — each block enters through `Deriv.sem`, the
*virtual* semantic reading, and the blocks conjoin.  No coherence bundle
appears. -/
theorem ListDeriv.sem (F : SemRuleFamily H) {ps qs : List Judgment}
    (ld : ListDeriv H F.rules ps qs) :
    ∀ μ : SubPMF (AdmVal H), SatList H ps μ → SatList H qs μ := by
  obtain ⟨pss, hf, rfl⟩ := ld
  induction hf with
  | nil => exact fun μ _ => satList_nil μ
  | @cons ps' q pss' qs' h _ ih =>
      intro μ hsat
      rw [List.flatten_cons] at hsat
      have h₁ : SatList H ps' μ := fun j hj =>
        hsat j (List.mem_append.mpr (Or.inl hj))
      have h₂ : SatList H pss'.flatten μ := fun j hj =>
        hsat j (List.mem_append.mpr (Or.inr hj))
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Deriv.sem F.square h μ h₁
      · exact ih μ h₂ j hj

/-- **Cell-level inheritance**: every semantic square of the
formal-conjunction presentation — the entailment `semFunctor` assigns to
a `JDeriv` cell — is derivable through the virtual route: dictionary
backward (`JDeriv.toListDeriv`), then blockwise `Deriv.sem`.  Neither
`satCoherence` nor `JDeriv.sem` is consumed: the structure cells cost
nothing because the dictionary sends them to identity partitions, which
is the formal content of "the refuted obligations were list bookkeeping
all along". -/
theorem semFunctor_cell_inherited (H : Hypernet) (F : SemRuleFamily H)
    {l l' : List Judgment} (d : JDeriv H F.rules.toConj l l') :
    ∀ μ : SubPMF (AdmVal H), SatConj H l μ → SatConj H l' μ :=
  fun μ hμ => ListDeriv.sem F (JDeriv.toListDeriv d) μ hμ

/-- **Soundness, inherited across the promotion**: the composed
statement — a proof object of the certificate calculus asserts its
sequent's semantic validity — obtained through the virtual route: the
proof object is a nullary multicell, its transpose is the cell from the
empty conjunction, and the anchor equivalence lands the calculus's own
validity notion.  Statement-identical to `semFunctor_sound`; proof
disjoint from it — soundness is proven once, virtually, and inherited
pseudo-ly. -/
theorem soundness_inherited (H : Hypernet) (F : SemRuleFamily H)
    {seq : Sequent} (po : ProofObject H seq) : seq.semanticallyValid H :=
  (satAll_ofSequent_iff H seq).mp fun μ =>
    satConj_singleton.mp
      (semFunctor_cell_inherited H F (JDeriv.ofProof po) μ (satConj_nil H μ))

end Virtual

end SuFunctor
