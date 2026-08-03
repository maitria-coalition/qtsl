import SuFunctor.Judgment
import DoubleCat.Virtual

/-! # The proof calculus as a virtual double category

The refutations in `SuFunctorLegacy.Refute` show that no sound, unital,
syntactic loose composition of *single* judgments can support the
structure squares a pseudo double category presentation owes: the
one-slot composite provably forgets the premise *pair* (a two-premise
implication can be semantically sound while the composite of its
premises is a tautology — the mixed-row funnel, kept as a type-error pin
in `SuFunctorLegacy.Refute`).  Two repairs coexist in this package.  The
formal-conjunction repair (`SuFunctorLegacy.Source`) keeps a pseudo
presentation and replaces the composite by list concatenation.  The
virtual presentation here removes the composite instead: loose arrows
are still single graded judgments, but a cell now has a *list* of
judgments as its loose domain, so multi-premise entailments are ordinary
multicells and no composition table exists to owe anything.
(`SuFunctorLegacy.Transpose` proves the two repairs are the same structure:
the formal-conjunction presentation is the free promotion of this
one.)

Concretely, over a hypernet `H` and a parametric rule family `F`:

* rule instances present their premises as a list (`Virtual.RuleFamily`,
  with `tops : Tag → List Judgment` where the retired kind-table
  presentation's family had a single composite top; the repaired
  `SuFunctor.RuleFamily` likewise carries its premises as a list, and
  additionally allows a list of conclusions where `bot` here is a single
  judgment — the multicategorical codomain);
* derivability (`Virtual.Deriv`) is a small multicategorical calculus:
  family generators, checker theorems as *nullary* cells (`ofProof` — a
  proof object proves its sequent from no judgment-level premises; the
  retired kind-table presentation encoded this as a cell topped by the
  unit judgment, where formal conjunction uses the empty list and the
  virtual presentation the empty premise string), identities,
  and single-position substitution (`splice`), from which simultaneous
  substitution is derived (`Deriv.subst`);
* the single-object carrier `Virtual.BLV H F` then carries a
  `VirtualDoubleCategoryStruct` whose multicells are `Deriv`
  propositions, lawful by proof irrelevance.

Cut is the flagship example: from `Φ ⊢ χ` and `Φ ∧ χ ⊢ Ψ` conclude
`Φ ⊢ Ψ`.  Its premise pair is strictly stronger than the conjunct
composite the kind table would have formed (`SuFunctorLegacy.Refute`'s module
docstring records the countermodel), so the retired presentation had to
keep cut inside the proof-object calculus.  Here it is an ordinary
2-ary multicell; its semantic square lives in
`SuFunctorLegacy.VirtualFunctor`.  (Formal conjunction admits it as a cell
out of the two-element list, `SuFunctorLegacy.Squares.cutFamily`.) -/

namespace SuFunctor

namespace Virtual

open PPLC CategoryTheory

/-- A syntactic rule family with multi-ary premises: a type of rule
instances, a gate selecting the enabled ones (tier membership as a
parameter, exactly as in `SuFunctor.RuleFamily`), and the boundary of
each instance's entailment cell — a *list* of premise judgments on top,
one conclusion judgment below.  Where the retired kind-table
presentation forced a multi-premise rule through the loose composite of
its premises (losing the pair), the list survives to the cell boundary
here. -/
structure RuleFamily (H : Hypernet) : Type 1 where
  /-- Rule instances (typically: a rule tag together with its
  side-condition data). -/
  Tag : Type
  /-- Which instances are enabled — tier membership as a parameter. -/
  gate : Tag → Prop
  /-- The premise judgments of an instance, in order. -/
  tops : Tag → List Judgment
  /-- The conclusion judgment of an instance. -/
  bot : Tag → Judgment

/-- The empty rule family: no generators beyond identities, substitution,
and the proof-object import. -/
def RuleFamily.empty (H : Hypernet) : RuleFamily H where
  Tag := Empty
  gate := fun t => t.elim
  tops := fun t => t.elim
  bot := fun t => t.elim

/-- Judgment-level derivability with multi-ary premises: the thin
multicell structure of the source virtual double category.

Constructors: the two generator imports (`ofRule` — the family's
entailment cells, with their premise lists intact; `ofProof` — checker
theorems as nullary cells), the identity cell (`refl`), and
single-position substitution (`splice`).  Simultaneous substitution and
tight-wise transitivity are derived (`Deriv.subst`, `Deriv.trans`).

There are no structure-cell constructors: the virtual presentation has
no loose composition, hence no associators, no unitors, and no
horizontal-composition closure — the constructors whose semantic squares
`SuFunctorLegacy.Refute` refutes simply do not exist here. -/
inductive Deriv (H : Hypernet) (F : RuleFamily H) :
    List Judgment → Judgment → Prop
  /-- A family generator: premises as a list, gate as a hypothesis. -/
  | ofRule (t : F.Tag) (ht : F.gate t) : Deriv H F (F.tops t) (F.bot t)
  /-- A checker theorem enters as a nullary multicell: its sequent's
  judgment is derivable from no judgment-level premises. -/
  | ofProof {seq : Sequent} (po : ProofObject H seq) :
      Deriv H F [] (Judgment.ofSequent seq)
  /-- The identity multicell on a judgment. -/
  | refl (j : Judgment) : Deriv H F [j] j
  /-- Single-position substitution: a derivation of one premise splices
  into a derivation using it. -/
  | splice {as cs ps : List Judgment} {b r : Judgment} :
      Deriv H F (as ++ b :: cs) r → Deriv H F ps b →
      Deriv H F (as ++ ps ++ cs) r

namespace Deriv

variable {H : Hypernet} {F : RuleFamily H}

/-- Simultaneous substitution, prefix-generalized form: splicing a
derivation into each premise beyond a fixed prefix. -/
theorem subst_aux {r : Judgment} {qs : List Judgment}
    {pss : List (List Judgment)} (hf : List.Forall₂ (Deriv H F) pss qs) :
    ∀ {done : List Judgment}, Deriv H F (done ++ qs) r →
      Deriv H F (done ++ pss.flatten) r := by
  induction hf with
  | nil => intro done d; simpa using d
  | @cons ps q pss' qs' h _ ih =>
      intro done d
      have d' : Deriv H F (done ++ ps ++ qs') r := d.splice h
      rw [List.append_assoc] at d'
      have d'' : Deriv H F ((done ++ ps) ++ pss'.flatten) r := by
        apply ih
        rw [List.append_assoc]
        exact d'
      rw [List.append_assoc] at d''
      simpa using d''

/-- Simultaneous substitution: a derivation of `r` from `qs`, together
with derivations of each `qᵢ` from `psᵢ`, yields a derivation of `r`
from the concatenation of the `psᵢ`. -/
theorem subst {r : Judgment} {qs : List Judgment}
    {pss : List (List Judgment)} (d : Deriv H F qs r)
    (hf : List.Forall₂ (Deriv H F) pss qs) :
    Deriv H F pss.flatten r :=
  subst_aux hf (done := []) d

/-- Tight-wise transitivity: pasting a unary cell below a cell is the
singleton case of substitution. -/
theorem trans {ps : List Judgment} {q r : Judgment}
    (h : Deriv H F ps q) (h' : Deriv H F [q] r) : Deriv H F ps r := by
  simpa using h'.splice (as := []) (cs := []) h

end Deriv

/-- The source virtual double category's carrier: single-object (the
hypernet and family are phantom parameters, exactly as in
`SuFunctor.BLD`). -/
structure BLV (H : Hypernet) (F : RuleFamily H) : Type where
  mk' ::

namespace BLV

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

variable {H : Hypernet} {F : RuleFamily H}

instance : CategoryTheory.Category.{0} (BLV H F) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- Read a string of loose arrows over the single object as a list of
judgments. -/
def pathToList : ∀ {a b : BLV H F},
    LoosePath (fun _ _ => Judgment) a b → List Judgment
  | _, _, .nil => []
  | _, _, .cons j ps => j :: pathToList ps

@[simp] theorem pathToList_nil {a : BLV H F} :
    pathToList (.nil : LoosePath (fun _ _ => Judgment) a a) = [] := rfl

@[simp] theorem pathToList_cons {a b c : BLV H F} (j : Judgment)
    (ps : LoosePath (fun _ _ => Judgment) b c) :
    pathToList (.cons (a := a) j ps) = j :: pathToList ps := rfl

@[simp] theorem pathToList_comp : ∀ {a b c : BLV H F}
    (ps : LoosePath (fun _ _ => Judgment) a b)
    (qs : LoosePath (fun _ _ => Judgment) b c),
    pathToList (ps.comp qs) = pathToList ps ++ pathToList qs
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons j ps, qs => congrArg (j :: ·) (pathToList_comp ps qs)

instance : VirtualDoubleCategoryData (BLV H F) where
  Loose _ _ := Judgment
  Cell ps q _ _ := PLift (Deriv H F (pathToList ps) q)

instance {a b c d : BLV H F} (ps : LoosePath Loose a b) (q : Loose c d)
    (f : a ⟶ c) (g : b ⟶ d) : Subsingleton (Cell ps q f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- A covering sequence of derivability cells yields blockwise
derivations: the premise lists of the blocks, their pointwise
derivations of the covered judgments, and the concatenation identity. -/
theorem cellSeq_deriv : ∀ {a b c d : BLV H F}
    {qs : LoosePath Loose c d} {ps : LoosePath Loose a b}
    {u : a ⟶ c} {v : b ⟶ d}, CellSeq qs ps u v →
    ∃ pss : List (List Judgment),
      List.Forall₂ (Deriv H F) pss (pathToList qs) ∧
        pss.flatten = pathToList ps
  | _, _, _, _, _, _, _, _, .nil _ => ⟨[], .nil, rfl⟩
  | _, _, _, _, _, _, _, _, .cons β V => by
      obtain ⟨pss, hf, hflat⟩ := cellSeq_deriv V
      exact ⟨_ :: pss, .cons β.down hf, by simp [hflat]⟩

instance : VirtualDoubleCategoryStruct (BLV H F) where
  cid j := ⟨Deriv.refl j⟩
  ccomp α V := ⟨by
    obtain ⟨pss, hf, hflat⟩ := cellSeq_deriv V
    exact hflat ▸ Deriv.subst α.down hf⟩

/-- The source virtual double category is lawful: its multicells are
propositions. -/
instance : VirtualDoubleCategory (BLV H F) :=
  .of_subsingleton fun _ _ _ _ => inferInstance

end BLV

end Virtual

end SuFunctor
