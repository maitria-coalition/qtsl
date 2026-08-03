/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the thin formal-conjunction presentation of the derivation
calculus (`BLD`, `JDeriv`).  The presentation of record is the virtual
one (`SuFunctor.Virtual`), of which this is the free promotion
(`SuFunctorLegacy.Transpose`).

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctor.Judgment
import DoubleCat.Functor.Lax

/-! # The source: the proof calculus as a thin double category

The proof calculus enters the double-categorical picture at the
*judgment* level: loose arrows are **formal conjunctions** — finite
lists of graded satisfaction judgments, composing by concatenation,
with the empty list as loose identity — and a cell from `l` to `l'` is
derivability of `l'` from `l` in a small entailment calculus `JDeriv`
over a **parametric rule family**.

Three design decisions are load-bearing:

* **Composition is free.**  The loose composite of two judgment lists
  is their concatenation: a formal object retaining both factors.
  Nothing about the judgments' kinds enters the composition — the
  informative combination rows of the semantics (Fréchet, Boole, the
  conjunct sequent) act as *cells out of formal pairs*, supplied by
  rule families (`SuFunctorLegacy.Squares`), never as the composition
  itself.  (An earlier kind-table composition was refuted on exactly
  this point; `SuFunctorLegacy.Refute` keeps the pins.)  The structure cells
  of the loose direction are correspondingly list identities: the left
  unitors are definitional, the associators and right unitors are
  `List.append_assoc` and `List.append_nil` read as derivations.

* **Rule families are parameters.**  Which rules generate entailment
  cells — and which of a calculus's rules count as core rather than
  admissible or alias — is data (`RuleFamily`), never hardcoded: moving
  a rule between tiers changes a family instance, not this module.
  Eliminable rules do not enter a family at all; their derivations are
  expanded through core cells before reaching this layer (recipe
  expansion), so only core rules ever owe a semantic square.  A
  multi-premise rule presents its premises as its top *list* — the
  premises are retained individually, so mixed-kind premise shapes (a
  risk bound beside a mass premise, a verdict bound beside an escape
  bound) are stated verbatim.

* **Theorems are cells from the empty conjunction.**  A proof object of
  the certificate calculus proves a sequent from *no* judgment-level
  premises; it enters as a cell whose top is the loose identity `[]`
  (`ofProof`).  The internal derivation engine of the sequent
  calculus — cut, weakening, the whole proof search — lives inside the
  proof-object calculus and surfaces here only through completed
  proofs; the double category presents the entailment structure among
  judgments, not the search.  (Under formal conjunction, cut's
  judgment-level face is also expressible directly as a two-premise
  family cell — `SuFunctorLegacy.Squares` records it — but the engine's home
  is unchanged.)

The resulting double category `BLD H F` is thin (cells are
propositions), single-object (one hypernet per component; assembling
the components over a wiring base with hypernet morphisms as tight
arrows is the named successor), and free on the family's generators
together with the structure cells.
-/

namespace SuFunctor

open PPLC

/-- A syntactic rule family: a type of rule instances, a gate selecting
the enabled ones (tier membership as a parameter), and the boundary of
each instance's entailment cell — the premise judgments as a list on
top, the conclusion judgments below.  A multi-premise rule instance
presents its premises verbatim: the top list retains each premise
separately, whatever its kind. -/
structure RuleFamily (H : Hypernet) : Type 1 where
  /-- Rule instances (typically: a rule tag together with its
  side-condition data). -/
  Tag : Type
  /-- Which instances are enabled — tier membership as a parameter
  (re-tiering a rule changes the gate, not the calculus), and the
  natural home of a rule's semantic side conditions, which may consult
  the ambient hypernet. -/
  gate : Tag → Prop
  /-- The premise judgments of an instance, as a formal conjunction. -/
  top : Tag → List Judgment
  /-- The conclusion judgments of an instance. -/
  bot : Tag → List Judgment

/-- The empty rule family: no generators beyond the structure cells and
the proof-object import. -/
def RuleFamily.empty (H : Hypernet) : RuleFamily H where
  Tag := Empty
  gate := fun t => t.elim
  top := fun t => t.elim
  bot := fun t => t.elim

/-- Judgment-level derivability over a hypernet `H` and a rule family
`F`: the thin cell structure of the source double category.

Constructors sort into three groups: the two generator imports
(`ofRule` — the family's entailment cells; `ofProof` — checker theorems
as cells from the empty conjunction), the categorical closure (`refl`,
`trans`, `hcomp`), and the structure cells of the loose direction
(associators and unitors).  Every constructor owes the semantic functor
a square; under formal conjunction the structure-cell squares are list
identities, proved once in the coherence bundle. -/
inductive JDeriv (H : Hypernet) (F : RuleFamily H) :
    List Judgment → List Judgment → Prop
  | ofRule (t : F.Tag) (ht : F.gate t) : JDeriv H F (F.top t) (F.bot t)
  | ofProof {seq : Sequent} (po : ProofObject H seq) :
      JDeriv H F [] [Judgment.ofSequent seq]
  | refl (l : List Judgment) : JDeriv H F l l
  | trans {l₁ l₂ l₃ : List Judgment} :
      JDeriv H F l₁ l₂ → JDeriv H F l₂ l₃ → JDeriv H F l₁ l₃
  | hcomp {m₁ n₁ m₂ n₂ : List Judgment} :
      JDeriv H F m₁ n₁ → JDeriv H F m₂ n₂ →
      JDeriv H F (m₁ ++ m₂) (n₁ ++ n₂)
  | assoc (m n p : List Judgment) :
      JDeriv H F ((m ++ n) ++ p) (m ++ (n ++ p))
  | assocInv (m n p : List Judgment) :
      JDeriv H F (m ++ (n ++ p)) ((m ++ n) ++ p)
  | unitL (m : List Judgment) : JDeriv H F ([] ++ m) m
  | unitLInv (m : List Judgment) : JDeriv H F m ([] ++ m)
  | unitR (m : List Judgment) : JDeriv H F (m ++ []) m
  | unitRInv (m : List Judgment) : JDeriv H F m (m ++ [])

/-- The source double category: single-object (the hypernet and family
are phantom parameters), loose arrows the formal conjunctions of
judgments, cells derivability. -/
structure BLD (H : Hypernet) (F : RuleFamily H) : Type where
  mk' ::

namespace BLD

open CategoryTheory PseudoDoubleCategoryStruct

variable {H : Hypernet} {F : RuleFamily H}

instance : CategoryTheory.Category.{0} (BLD H F) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance : PseudoDoubleCategoryStruct (BLD H F) where
  Loose _ _ := List Judgment
  Cell m n _ _ := PLift (JDeriv H F m n)
  vId m := ⟨.refl m⟩
  vComp α β := ⟨.trans α.down β.down⟩
  lId _ := []
  lComp m n := m ++ n
  hId _ := ⟨.refl []⟩
  hComp α β := ⟨.hcomp α.down β.down⟩
  lAssoc m n p := ⟨.assoc m n p⟩
  lAssocInv m n p := ⟨.assocInv m n p⟩
  lLeftUnitor m := ⟨.unitL m⟩
  lLeftUnitorInv m := ⟨.unitLInv m⟩
  lRightUnitor m := ⟨.unitR m⟩
  lRightUnitorInv m := ⟨.unitRInv m⟩

instance {a b c d : BLD H F} (m : Loose a b) (n : Loose c d) (f : a ⟶ c)
    (g : b ⟶ d) : Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

instance : PseudoDoubleCategory (BLD H F) where
  vId_vComp _ := Subsingleton.elim _ _
  vComp_vId _ := Subsingleton.elim _ _
  vComp_assoc _ _ _ := Subsingleton.elim _ _
  hId_id _ := Subsingleton.elim _ _
  hId_comp _ _ := Subsingleton.elim _ _
  hComp_vId _ _ := Subsingleton.elim _ _
  interchange _ _ _ _ := Subsingleton.elim _ _
  lAssoc_natural _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_natural _ := Subsingleton.elim _ _
  lRightUnitor_natural _ := Subsingleton.elim _ _
  lAssoc_lAssocInv _ _ _ := Subsingleton.elim _ _
  lAssocInv_lAssoc _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_lLeftUnitorInv _ := Subsingleton.elim _ _
  lLeftUnitorInv_lLeftUnitor _ := Subsingleton.elim _ _
  lRightUnitor_lRightUnitorInv _ := Subsingleton.elim _ _
  lRightUnitorInv_lRightUnitor _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

end BLD

end SuFunctor
