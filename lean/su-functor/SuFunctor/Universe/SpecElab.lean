import SuFunctor.Universe.SpecDnf

/-! # The specification surface: formation, normal forms, and the exact
compile into coupled-DNF presentations

The state-formula fragment of the specification language, compiled into
the coupled-DNF presentations of `SpecDnf`.  The architecture is
*interface resolution, then structural recursion*: a record resolves its
positional geometry first (refusing non-conformant records with the
failure's geometry attached, before any recursion), and the compile is
then a fold of rule-indexed cells over the formula's formation
structure.  Carrier-generic (`K` an arbitrary type), so the results
instantiate at every fibre of the DNF spec decoration (`DnfSpec`).

Contents, cell by cell:

* **Walls and properness** (`wallOn`, `permitted`, `safeProper`): the
  carrier-generic wall (`0` inside, `⊤` outside; the belief-carrier
  instance is `SuFunctor.Universe.wall`), and the two faces of the
  crisp judgment — safety is wall domination (`wallOn_le_iff`: the
  permitted region is contained), properness is a dip under the top
  mark (`dip_top_iff`: some point is permitted at finite penalty).
  Their conjunction is the satisfaction of a *safety atom*
  (`coupledSat_safetyAtom_iff`): to satisfy anything, first exist — the
  presupposition is a theorem of the judgment, not a formula anyone
  writes.  In particular the true constant is not vacuous: its class is
  exactly the proper systems (`SpecDnf.modelClass_top` — the bare
  feasibility claim, distinguishing an inconsistent system from a
  working one).
* **The fibre lattice cells** (`SpecAtom.merge`, `SpecDnf.conj`,
  `SpecDnf.disj`): conjunction is the atom merge — floors join by
  pointwise max, mark families union — and it is *exact*
  (`SpecAtom.modelClass_merge`: the merged class is the intersection;
  the safety face is the conjunction-is-max universal property, the
  order-theoretic kin of `sat_sup_iff`).  Disjunction of presentations
  is the disjunct union, and its class is the plain union
  (`SpecDnf.modelClass_disj`).  The properness mark rides every merge
  by construction.
* **Formation and negation normal form** (`StateFormula`, `NnfForm`,
  `StateFormula.nnf`): negation is a surface former, resolved by
  polarity recursion into a normal form whose grammar has *no negation
  node* — the unconsumable residues have no clause because they have no
  constructor.  On the state fragment the resolution is total and
  exact: `den_nnf` says the region semantics is preserved on the nose
  (De Morgan and double negation), with the closed/strict swap entering
  at literals (`den_compl_le`).
* **The compile and its adequacy fold** (`NnfForm.elabNnf`,
  `NnfForm.classSem`, `NnfForm.elabNnf_modelClass`): one compile clause
  per formation rule — literals to safety atoms, conjunction to the
  merge, disjunction to the union — and the record-level adequacy
  statement is the fold of the per-rule cells over the formation
  derivation: the compiled presentation's model class *equals* the
  recursively-read class semantics.  Every compiled atom carries the
  properness mark (`elabNnf_top_mem` — one line, because the fence is
  structural: `SpecAtom.top_mem` is a field).
* **Where the region reading is honest, and where it is not**: on the
  disjunction-free fragment the class semantics collapses to
  safe-and-proper against the denoted region
  (`elabNnf_modelClass_disjFree`).  Across a disjunction it does not,
  and the gap is a theorem (`exists_hedging_gap`): a proper system can
  hold its permitted region inside a union of two regions while
  belonging to neither disjunct's class — models of a disjunction may
  hedge, and the presentation semantics deliberately excludes hedging
  (the disjunct union is the constructible normal form's union of
  classes, not the pointwise-min coproduct of penalties).
* **Records, interfaces, conformance** (`SpecRecord`,
  `SpecRecord.resolveArity`, `SpecRecord.elabSpec`): the record former's
  premises as executable conformance — root atoms at the guarantee
  arity, assumption atoms at the input arity, assumptions in the base
  stratum (`Theta0`).  An assumption-carrying record carries an
  interface *by type* (the assumption slot lives inside the interface
  option).  Resolution is total on conformant records and refuses
  otherwise with the offender's geometry
  (`resolveArity_isOk_iff`, `resolveArity_error_names_offender`); the
  compile factors through resolution (`elabSpec_isOk_iff`,
  `elabSpec_ok_modelClass`, `elabSpec_top_mem`).  The compile reads the
  guarantee only: an assumption is carried as data, its conditional
  semantics deferred — never silently read as an unconditional
  strengthening.

Axiom receipts at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx.
-/

namespace SuFunctor.Universe

open scoped ENNReal

universe u v

variable {K : Type u} {α : Type v}

/-! ## Walls and properness: the crisp judgment's two faces -/

/-- The permitted region of a system: the points it does not forbid
outright. -/
def permitted (σ : K → ℝ≥0∞) : Set K := {μ | σ μ ≠ ⊤}

theorem mem_permitted_iff {σ : K → ℝ≥0∞} {μ : K} :
    μ ∈ permitted σ ↔ σ μ ≠ ⊤ :=
  Iff.rfl

open Classical in
/-- The carrier-generic wall: `0` on the set, `⊤` off it.  (On the
belief carrier this is `SuFunctor.Universe.wall`.) -/
noncomputable def wallOn (C : Set K) : K → ℝ≥0∞ :=
  fun μ => if μ ∈ C then 0 else ⊤

theorem wallOn_apply_of_mem {C : Set K} {μ : K} (h : μ ∈ C) :
    wallOn C μ = 0 := by simp [wallOn, h]

theorem wallOn_apply_of_not_mem {C : Set K} {μ : K} (h : μ ∉ C) :
    wallOn C μ = ⊤ := by simp [wallOn, h]

@[simp] theorem wallOn_univ : wallOn (Set.univ : Set K) = 0 :=
  funext fun μ => wallOn_apply_of_mem (Set.mem_univ μ)

/-- **The safety face**: wall domination says exactly that the permitted
region is contained in the wall's set. -/
theorem wallOn_le_iff {C : Set K} {σ : K → ℝ≥0∞} :
    wallOn C ≤ σ ↔ permitted σ ⊆ C := by
  constructor
  · intro h μ hμ
    by_contra hC
    exact hμ (top_le_iff.mp (wallOn_apply_of_not_mem hC ▸ h μ))
  · intro h μ
    by_cases hC : μ ∈ C
    · rw [wallOn_apply_of_mem hC]
      exact zero_le
    · rw [wallOn_apply_of_not_mem hC]
      have hσ : ¬ σ μ ≠ ⊤ := fun hne => hC (h hne)
      rw [not_not] at hσ
      exact hσ.ge

/-- **The properness face**: a dip under the top mark says exactly that
some point is permitted at finite penalty. -/
theorem dip_top_iff {σ : K → ℝ≥0∞} :
    Dip σ (⊤ : K → ℝ≥0∞) ↔ (permitted σ).Nonempty := by
  constructor
  · rintro ⟨μ, hμ⟩
    rw [Pi.top_apply] at hμ
    exact ⟨μ, lt_top_iff_ne_top.mp hμ⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [Pi.top_apply]
    exact lt_top_iff_ne_top.mpr hμ

/-- Safe and proper against a region: the class-semantics cell of a
crisp claim. -/
def safeProper (C : Set K) : Set (K → ℝ≥0∞) :=
  {σ | permitted σ ⊆ C ∧ (permitted σ).Nonempty}

theorem mem_safeProper_iff {C : Set K} {σ : K → ℝ≥0∞} :
    σ ∈ safeProper C ↔ permitted σ ⊆ C ∧ (permitted σ).Nonempty :=
  Iff.rfl

theorem safeProper_inter (C D : Set K) :
    safeProper C ∩ safeProper D = safeProper (C ∩ D) := by
  ext σ
  constructor
  · rintro ⟨⟨hC, hne⟩, hD, -⟩
    exact ⟨Set.subset_inter hC hD, hne⟩
  · rintro ⟨h, hne⟩
    exact ⟨⟨h.trans Set.inter_subset_left, hne⟩,
      h.trans Set.inter_subset_right, hne⟩

theorem safeProper_empty : safeProper (∅ : Set K) = ∅ := by
  ext σ
  simp only [mem_safeProper_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro h ⟨μ, hμ⟩
  exact h hμ

/-- The safety atom of a region: its wall as the floor, and the
properness demand alone as the liveness family. -/
noncomputable def safetyAtom (C : Set K) : SpecAtom K where
  floor := wallOn C
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := Set.mem_singleton _

@[simp] theorem safetyAtom_floor (C : Set K) :
    (safetyAtom C).floor = wallOn C := rfl

@[simp] theorem safetyAtom_marks (C : Set K) :
    (safetyAtom C).marks = {(⊤ : K → ℝ≥0∞)} := rfl

/-- **The presupposition cell**: satisfying a safety atom is being safe
AND proper — to satisfy anything, first exist.  (The vacuous instance
`C = Set.univ` is `coupledSat_zero_topSpec_iff`.) -/
theorem coupledSat_safetyAtom_iff {C : Set K} {σ : K → ℝ≥0∞} :
    CoupledSat σ (wallOn C) {⊤} ↔
      permitted σ ⊆ C ∧ (permitted σ).Nonempty := by
  unfold CoupledSat
  rw [wallOn_le_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    exact dip_top_iff.mp (h ⊤ (Set.mem_singleton _))
  · intro h v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact dip_top_iff.mpr h

theorem safetyAtom_modelClass (C : Set K) :
    (safetyAtom C).modelClass = safeProper C := by
  ext σ
  exact coupledSat_safetyAtom_iff

/-! ## The fibre lattice cells: merge and union -/

/-- Atom merge — the conjunction cell: floors join by pointwise max,
mark families union.  The properness mark rides by construction. -/
def SpecAtom.merge (a b : SpecAtom K) : SpecAtom K where
  floor := a.floor ⊔ b.floor
  marks := a.marks ∪ b.marks
  finite_marks := a.finite_marks.union b.finite_marks
  top_mem := Set.mem_union_left _ a.top_mem

@[simp] theorem SpecAtom.merge_floor (a b : SpecAtom K) :
    (a.merge b).floor = a.floor ⊔ b.floor := rfl

@[simp] theorem SpecAtom.merge_marks (a b : SpecAtom K) :
    (a.merge b).marks = a.marks ∪ b.marks := rfl

/-- **The conjunction cell is exact**: satisfying the merge is
satisfying both atoms.  Safety face: the conjunction-is-max universal
property (`sup_le_iff`; the judgment-stratum kin is `sat_sup_iff`).
Liveness face: demands accumulate across the union. -/
theorem SpecAtom.coupledSat_merge_iff {a b : SpecAtom K}
    {σ : K → ℝ≥0∞} :
    CoupledSat σ (a.merge b).floor (a.merge b).marks ↔
      CoupledSat σ a.floor a.marks ∧ CoupledSat σ b.floor b.marks := by
  unfold CoupledSat
  simp only [merge_floor, merge_marks, sup_le_iff, Set.mem_union]
  constructor
  · rintro ⟨⟨ha, hb⟩, hlive⟩
    exact ⟨⟨ha, fun v hv => hlive v (Or.inl hv)⟩,
      hb, fun v hv => hlive v (Or.inr hv)⟩
  · rintro ⟨⟨ha, hla⟩, hb, hlb⟩
    exact ⟨⟨ha, hb⟩, fun v hv => hv.elim (hla v) (hlb v)⟩

theorem SpecAtom.modelClass_merge (a b : SpecAtom K) :
    (a.merge b).modelClass = a.modelClass ∩ b.modelClass := by
  ext σ
  exact coupledSat_merge_iff

/-- The singleton presentation. -/
def SpecDnf.single (a : SpecAtom K) : SpecDnf K where
  atoms := {a}
  finite_atoms := Set.finite_singleton _

@[simp] theorem SpecDnf.single_atoms (a : SpecAtom K) :
    (SpecDnf.single a).atoms = {a} := rfl

theorem SpecDnf.modelClass_single (a : SpecAtom K) :
    (SpecDnf.single a).modelClass = a.modelClass := by
  simp [SpecDnf.modelClass, single_atoms]

/-- Conjunction of presentations: the atom merge, disjunct-pairwise. -/
def SpecDnf.conj (D E : SpecDnf K) : SpecDnf K where
  atoms := Set.image2 SpecAtom.merge D.atoms E.atoms
  finite_atoms := D.finite_atoms.image2 _ E.finite_atoms

@[simp] theorem SpecDnf.conj_atoms (D E : SpecDnf K) :
    (D.conj E).atoms = Set.image2 SpecAtom.merge D.atoms E.atoms := rfl

/-- Disjunction of presentations: the disjunct union outright. -/
def SpecDnf.disj (D E : SpecDnf K) : SpecDnf K where
  atoms := D.atoms ∪ E.atoms
  finite_atoms := D.finite_atoms.union E.finite_atoms

@[simp] theorem SpecDnf.disj_atoms (D E : SpecDnf K) :
    (D.disj E).atoms = D.atoms ∪ E.atoms := rfl

/-- The true presentation: one atom, free floor, properness alone — the
bare feasibility spec. -/
noncomputable def SpecDnf.top : SpecDnf K :=
  SpecDnf.single (safetyAtom Set.univ)

/-- The false presentation: no disjuncts. -/
def SpecDnf.bot : SpecDnf K where
  atoms := ∅
  finite_atoms := Set.finite_empty

@[simp] theorem SpecDnf.bot_atoms : (SpecDnf.bot : SpecDnf K).atoms = ∅ :=
  rfl

/-- **The conjunction cell, presentation level**: the pairwise merge's
class is the intersection — exactness distributes across the disjunct
unions. -/
theorem SpecDnf.modelClass_conj (D E : SpecDnf K) :
    (D.conj E).modelClass = D.modelClass ∩ E.modelClass := by
  ext σ
  simp only [mem_modelClass_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨c, hc, hsat⟩
    rw [conj_atoms] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_image2.mp hc
    obtain ⟨hA, hB⟩ := SpecAtom.coupledSat_merge_iff.mp hsat
    exact ⟨⟨a, ha, hA⟩, b, hb, hB⟩
  · rintro ⟨⟨a, ha, hA⟩, b, hb, hB⟩
    exact ⟨a.merge b, Set.mem_image2_of_mem ha hb,
      SpecAtom.coupledSat_merge_iff.mpr ⟨hA, hB⟩⟩

/-- **The disjunction cell, presentation level**: the disjunct union's
class is the plain union. -/
theorem SpecDnf.modelClass_disj (D E : SpecDnf K) :
    (D.disj E).modelClass = D.modelClass ∪ E.modelClass := by
  ext σ
  simp only [mem_modelClass_iff, disj_atoms, Set.mem_union]
  constructor
  · rintro ⟨a, ha | ha, hsat⟩
    · exact Or.inl ⟨a, ha, hsat⟩
    · exact Or.inr ⟨a, ha, hsat⟩
  · rintro (⟨a, ha, hsat⟩ | ⟨a, ha, hsat⟩)
    · exact ⟨a, Or.inl ha, hsat⟩
    · exact ⟨a, Or.inr ha, hsat⟩

/-- The true presentation's class: exactly the proper systems.  Not
vacuous — the minimal claim, distinguishing an inconsistent system from
a working one. -/
theorem SpecDnf.modelClass_top :
    (SpecDnf.top : SpecDnf K).modelClass = safeProper Set.univ := by
  simp [SpecDnf.top, modelClass_single, safetyAtom_modelClass]

/-- The false presentation's class is empty. -/
theorem SpecDnf.modelClass_bot :
    (SpecDnf.bot : SpecDnf K).modelClass = ∅ := by
  simp [SpecDnf.modelClass, bot_atoms]

/-! ## The surface grammar and its normal form -/

/-- State formulas over an atom alphabet `α`: the surface grammar's
state fragment.  Atoms enter abstractly — an atom's compiled denotation
is a region of the carrier, supplied at the compile; the concrete
positional-polynomial reading lives at the encoding stratum. -/
inductive StateFormula (α : Type v) : Type v
  | tru : StateFormula α
  | fls : StateFormula α
  | atom (a : α) : StateFormula α
  | conj (φ ψ : StateFormula α) : StateFormula α
  | disj (φ ψ : StateFormula α) : StateFormula α
  | neg (φ : StateFormula α) : StateFormula α

namespace StateFormula

/-- The region semantics: complement at negation. -/
def den (A : α → Set K) : StateFormula α → Set K
  | tru => Set.univ
  | fls => ∅
  | atom a => A a
  | conj φ ψ => φ.den A ∩ ψ.den A
  | disj φ ψ => φ.den A ∪ ψ.den A
  | neg φ => (φ.den A)ᶜ

/-- The base stratum: constants, atoms, and their and/or closure —
nothing else.  No rule concludes membership of a negation. -/
def Theta0 : StateFormula α → Prop
  | tru => True
  | fls => True
  | atom _ => True
  | conj φ ψ => Theta0 φ ∧ Theta0 ψ
  | disj φ ψ => Theta0 φ ∧ Theta0 ψ
  | neg _ => False

/-- The base stratum, decidably. -/
def theta0 : StateFormula α → Bool
  | tru => true
  | fls => true
  | atom _ => true
  | conj φ ψ => φ.theta0 && ψ.theta0
  | disj φ ψ => φ.theta0 && ψ.theta0
  | neg _ => false

theorem theta0_iff (φ : StateFormula α) :
    φ.theta0 = true ↔ φ.Theta0 := by
  induction φ <;> simp [theta0, Theta0, *]

/-- The atoms a formula reads, in syntactic order. -/
def atoms : StateFormula α → List α
  | tru => []
  | fls => []
  | atom a => [a]
  | conj φ ψ => φ.atoms ++ ψ.atoms
  | disj φ ψ => φ.atoms ++ ψ.atoms
  | neg φ => φ.atoms

end StateFormula

/-- Negation normal forms: literals, constants, and the two lattice
connectives.  There is **no negation constructor** — a residue that
cannot be consumed cannot be written, so the compile below needs no
defensive clause for it. -/
inductive NnfForm (α : Type v) : Type v
  | tru : NnfForm α
  | fls : NnfForm α
  | lit (pos : Bool) (a : α) : NnfForm α
  | conj (ψ χ : NnfForm α) : NnfForm α
  | disj (ψ χ : NnfForm α) : NnfForm α

namespace NnfForm

/-- The region semantics of a normal form: a negative literal denotes
the complement — at the concrete atom stratum this is the closed/strict
swap (`den_compl_le`). -/
def den (A : α → Set K) : NnfForm α → Set K
  | tru => Set.univ
  | fls => ∅
  | lit true a => A a
  | lit false a => (A a)ᶜ
  | conj ψ χ => ψ.den A ∩ χ.den A
  | disj ψ χ => ψ.den A ∪ χ.den A

end NnfForm

namespace StateFormula

/-- Negation normal form by polarity recursion: `pos = false` reads the
formula under an odd number of negations. -/
def nnfAux : StateFormula α → Bool → NnfForm α
  | tru, true => .tru
  | tru, false => .fls
  | fls, true => .fls
  | fls, false => .tru
  | atom a, pos => .lit pos a
  | conj φ ψ, true => .conj (φ.nnfAux true) (ψ.nnfAux true)
  | conj φ ψ, false => .disj (φ.nnfAux false) (ψ.nnfAux false)
  | disj φ ψ, true => .disj (φ.nnfAux true) (ψ.nnfAux true)
  | disj φ ψ, false => .conj (φ.nnfAux false) (ψ.nnfAux false)
  | neg φ, pos => φ.nnfAux (!pos)

/-- Negation normal form. -/
def nnf (φ : StateFormula α) : NnfForm α := φ.nnfAux true

theorem den_nnfAux (A : α → Set K) (φ : StateFormula α) :
    (φ.nnfAux true).den A = φ.den A ∧
      (φ.nnfAux false).den A = (φ.den A)ᶜ := by
  induction φ with
  | tru => simp [nnfAux, NnfForm.den, den]
  | fls => simp [nnfAux, NnfForm.den, den]
  | atom a => simp [nnfAux, NnfForm.den, den]
  | conj φ ψ ihφ ihψ =>
    constructor
    · simp [nnfAux, NnfForm.den, den, ihφ.1, ihψ.1]
    · simp [nnfAux, NnfForm.den, den, ihφ.2, ihψ.2, Set.compl_inter]
  | disj φ ψ ihφ ihψ =>
    constructor
    · simp [nnfAux, NnfForm.den, den, ihφ.1, ihψ.1]
    · simp [nnfAux, NnfForm.den, den, ihφ.2, ihψ.2, Set.compl_union]
  | neg φ ih =>
    constructor
    · show (φ.nnfAux false).den A = (φ.den A)ᶜ
      exact ih.2
    · show (φ.nnfAux true).den A = ((φ.den A)ᶜ)ᶜ
      rw [compl_compl]
      exact ih.1

/-- **Normal-form resolution is exact**: the region semantics is
preserved on the nose (De Morgan and double negation; the closed/strict
swap enters at literals). -/
theorem den_nnf (A : α → Set K) (φ : StateFormula α) :
    (φ.nnf).den A = φ.den A :=
  (den_nnfAux A φ).1

end StateFormula

/-! ## The compile and its adequacy fold -/

namespace NnfForm

/-- The compile: one clause per formation rule.  Literals become safety
atoms of their regions; conjunction is the merge; disjunction is the
union.  There is no negation clause because there is no negation
node. -/
noncomputable def elabNnf (A : α → Set K) : NnfForm α → SpecDnf K
  | tru => SpecDnf.top
  | fls => SpecDnf.bot
  | lit true a => SpecDnf.single (safetyAtom (A a))
  | lit false a => SpecDnf.single (safetyAtom (A a)ᶜ)
  | conj ψ χ => (elabNnf A ψ).conj (elabNnf A χ)
  | disj ψ χ => (elabNnf A ψ).disj (elabNnf A χ)

/-- The class semantics: the rule-indexed cell family the adequacy
statement folds. -/
def classSem (A : α → Set K) : NnfForm α → Set (K → ℝ≥0∞)
  | tru => safeProper Set.univ
  | fls => ∅
  | lit true a => safeProper (A a)
  | lit false a => safeProper (A a)ᶜ
  | conj ψ χ => classSem A ψ ∩ classSem A χ
  | disj ψ χ => classSem A ψ ∪ classSem A χ

/-- **The record-level adequacy fold**: the compiled presentation's
model class equals the class semantics — per-rule cells pasted by
induction over the formation derivation. -/
theorem elabNnf_modelClass (A : α → Set K) (ψ : NnfForm α) :
    (elabNnf A ψ).modelClass = classSem A ψ := by
  induction ψ with
  | tru =>
    simp only [elabNnf, classSem]
    exact SpecDnf.modelClass_top
  | fls =>
    simp only [elabNnf, classSem]
    exact SpecDnf.modelClass_bot
  | lit pos a =>
    cases pos <;>
      simp only [elabNnf, classSem, SpecDnf.modelClass_single,
        safetyAtom_modelClass]
  | conj ψ χ ihψ ihχ =>
    simp only [elabNnf, classSem, SpecDnf.modelClass_conj, ihψ, ihχ]
  | disj ψ χ ihψ ihχ =>
    simp only [elabNnf, classSem, SpecDnf.modelClass_disj, ihψ, ihχ]

/-- **Every compiled atom carries the properness mark** — the
default-liveness reading as a theorem of the compile.  One line: the
fence is structural (`SpecAtom.top_mem` is a field), so an atom without
the mark is unrepresentable, not refuted. -/
theorem elabNnf_top_mem (A : α → Set K) (ψ : NnfForm α) :
    ∀ a ∈ (elabNnf A ψ).atoms, (⊤ : K → ℝ≥0∞) ∈ a.marks :=
  fun a _ => a.top_mem

/-- The disjunction-free fragment. -/
def DisjFree : NnfForm α → Prop
  | tru => True
  | fls => True
  | lit _ _ => True
  | conj ψ χ => DisjFree ψ ∧ DisjFree χ
  | disj _ _ => False

/-- On the disjunction-free fragment the class semantics collapses to
safe-and-proper against the denoted region: the region reading is exact
exactly where no hedging is possible. -/
theorem classSem_disjFree (A : α → Set K) :
    ∀ ψ : NnfForm α, ψ.DisjFree → classSem A ψ = safeProper (ψ.den A)
  | tru, _ => by simp [classSem, den]
  | fls, _ => by simp [classSem, den, safeProper_empty]
  | lit true a, _ => rfl
  | lit false a, _ => rfl
  | conj ψ χ, h => by
    obtain ⟨h₁, h₂⟩ := h
    simp only [classSem, den, classSem_disjFree A ψ h₁,
      classSem_disjFree A χ h₂, safeProper_inter]
  | disj ψ χ, h => absurd h (by simp [DisjFree])

theorem elabNnf_modelClass_disjFree (A : α → Set K) (ψ : NnfForm α)
    (h : ψ.DisjFree) :
    (elabNnf A ψ).modelClass = safeProper (ψ.den A) := by
  rw [elabNnf_modelClass, classSem_disjFree A ψ h]

/-- **Models of a disjunction may hedge — the presentation semantics
excludes them, and the gap is inhabited**: a proper system whose
permitted region sits inside the union of two literal regions while
belonging to neither disjunct's class.  This is why the adequacy fold
reads the class semantics, not safe-and-proper of the region, across a
disjunction.  (Judgment-stratum kin: `exists_sat_inf_not_sat`.) -/
theorem exists_hedging_gap :
    ∃ (A : Bool → Set Bool) (ψ χ : NnfForm Bool) (σ : Bool → ℝ≥0∞),
      σ ∈ safeProper ((NnfForm.disj ψ χ).den A) ∧
        σ ∉ classSem A (NnfForm.disj ψ χ) := by
  refine ⟨fun b => {b}, .lit true true, .lit true false, 0, ⟨?_, ?_⟩, ?_⟩
  · intro μ _
    show μ ∈ ({true} : Set Bool) ∪ {false}
    cases μ
    · exact Or.inr rfl
    · exact Or.inl rfl
  · refine ⟨true, ?_⟩
    simp [mem_permitted_iff]
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · have hf : false ∈ permitted (0 : Bool → ℝ≥0∞) := by
        simp [mem_permitted_iff]
      simpa using h hf
    · have ht : true ∈ permitted (0 : Bool → ℝ≥0∞) := by
        simp [mem_permitted_iff]
      simpa using h ht

end NnfForm

/-! ## Concrete literals: the closed/strict swap -/

/-- A threshold atom over the carrier: a compiled observable, an exact
rational threshold, and a direction.  The observable is the compiled
positional-polynomial reading — the encoding stratum owns the
serialization; here it enters as the function it denotes. -/
structure ThresholdAtom (K : Type u) : Type u where
  /-- The compiled observable. -/
  obs : K → ℝ
  /-- The exact rational threshold. -/
  threshold : ℚ
  /-- `true` for a `≤`-atom, `false` for a `≥`-atom. -/
  isLE : Bool

/-- The denoted closed region. -/
def ThresholdAtom.den (t : ThresholdAtom K) : Set K :=
  if t.isLE then {μ | t.obs μ ≤ (t.threshold : ℝ)}
  else {μ | (t.threshold : ℝ) ≤ t.obs μ}

/-- The closed/strict swap, `≤`-orientation: the complement of a closed
lower atom is the strict upper set — a normal-form-internal literal, no
margin spent. -/
theorem den_compl_le (f : K → ℝ) (c : ℚ) :
    {μ | f μ ≤ (c : ℝ)}ᶜ = {μ | (c : ℝ) < f μ} := by
  ext μ
  simp [not_le]

/-- The closed/strict swap, `≥`-orientation. -/
theorem den_compl_ge (f : K → ℝ) (c : ℚ) :
    {μ | (c : ℝ) ≤ f μ}ᶜ = {μ | f μ < (c : ℝ)} := by
  ext μ
  simp [not_le]

/-! ## Records, interfaces, and conformance -/

/-- The interface data of an open record.  The assumption slot lives
*inside* the interface: an assumption-carrying record carries an
interface by type — the fence is the absence of any other constructor,
not a check. -/
structure OpenIface (α : Type v) : Type v where
  /-- Input-wire arity: the positional width assumptions read. -/
  inArity : ℕ
  /-- Output-wire arity: the positional width guarantees read. -/
  outArity : ℕ
  /-- The assumption, if any — policed to the base stratum by
  conformance; carried as data by the compile (its conditional
  semantics is deferred, fail-closed). -/
  assumption? : Option (StateFormula α)

/-- A specification record: the root guarantee, and optionally an
interface (with its optional assumption). -/
structure SpecRecord (α : Type v) : Type v where
  /-- The root guarantee. -/
  root : StateFormula α
  /-- The interface, when the record is open. -/
  iface? : Option (OpenIface α)

/-- Conformance refusals, with the failure's geometry: the offending
atom, its found width, the expected arity, and which slot it sits in
(`inAssumption`). -/
inductive ConformanceError (α : Type v) : Type v
  | widthMismatch (a : α) (found expected : ℕ) (inAssumption : Bool)
  | assumptionNotBase

/-- Ok-ness of an `Except`, as a proposition. -/
def IsOk {ε β : Type*} : Except ε β → Prop
  | .ok _ => True
  | .error _ => False

@[simp] theorem isOk_ok {ε β : Type*} (b : β) :
    IsOk (.ok b : Except ε β) := trivial

@[simp] theorem not_isOk_error {ε β : Type*} (e : ε) :
    ¬ IsOk (.error e : Except ε β) := fun h => h

/-- Check every listed atom against an expected width; refuse at the
first offender, naming it. -/
def checkWidths (width : α → ℕ) (expected : ℕ) (inAssumption : Bool) :
    List α → Except (ConformanceError α) Unit
  | [] => .ok ()
  | a :: rest =>
    if width a = expected then
      checkWidths width expected inAssumption rest
    else
      .error (.widthMismatch a (width a) expected inAssumption)

theorem checkWidths_isOk_iff {width : α → ℕ} {expected : ℕ}
    {inAssumption : Bool} {l : List α} :
    IsOk (checkWidths width expected inAssumption l) ↔
      ∀ a ∈ l, width a = expected := by
  induction l with
  | nil => simp [checkWidths]
  | cons a rest ih =>
    by_cases h : width a = expected <;>
      simp [checkWidths, h, ih]

theorem checkWidths_error_spec {width : α → ℕ} {expected : ℕ}
    {inA : Bool} :
    ∀ {l : List α} {a : α} {f e : ℕ} {b : Bool},
      checkWidths width expected inA l
          = .error (.widthMismatch a f e b) →
        a ∈ l ∧ width a = f ∧ f ≠ e ∧ e = expected ∧ b = inA := by
  intro l
  induction l with
  | nil =>
    intro a f e b h
    exact absurd h (by simp [checkWidths])
  | cons x rest ih =>
    intro a f e b h
    simp only [checkWidths] at h
    by_cases hx : width x = expected
    · rw [if_pos hx] at h
      obtain ⟨hmem, hrest⟩ := ih h
      exact ⟨List.mem_cons_of_mem x hmem, hrest⟩
    · rw [if_neg hx] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConformanceError.widthMismatch.inj (Except.error.inj h)
      exact ⟨by simp, rfl, hx, rfl, rfl⟩

/-- Record-level conformance, as the formation rules' premises: root
atoms at the guarantee arity (the interface's output arity, or the
closed record's common width), assumption atoms at the input arity, and
assumptions in the base stratum.  Stated as a plain conjunction of
implications (match-free), so consumers case on the record shape rather
than on a motive. -/
def SpecRecord.Conformant (width : α → ℕ) (r : SpecRecord α) : Prop :=
  (∀ I, r.iface? = some I →
    (∀ a ∈ r.root.atoms, width a = I.outArity) ∧
      ∀ φ, I.assumption? = some φ →
        φ.Theta0 ∧ ∀ a ∈ φ.atoms, width a = I.inArity) ∧
  (r.iface? = none →
    ∀ a ∈ r.root.atoms, ∀ b ∈ r.root.atoms, width a = width b)

/-- **Interface resolution**: the record's positional arity, or a
refusal carrying the failure's geometry — before any recursion.  Open
records resolve to the interface's output arity; closed records resolve
to their atoms' common width (`0` when there are no atoms: width
agreement is vacuous and the minimal wire object serves). -/
def SpecRecord.resolveArity (width : α → ℕ) (r : SpecRecord α) :
    Except (ConformanceError α) ℕ :=
  match r.iface? with
  | some I =>
    match checkWidths width I.outArity false r.root.atoms with
    | .error e => .error e
    | .ok () =>
      match I.assumption? with
      | none => .ok I.outArity
      | some φ =>
        if φ.theta0 then
          match checkWidths width I.inArity true φ.atoms with
          | .error e => .error e
          | .ok () => .ok I.outArity
        else .error .assumptionNotBase
  | none =>
    match r.root.atoms with
    | [] => .ok 0
    | a :: rest =>
      match checkWidths width (width a) false rest with
      | .error e => .error e
      | .ok () => .ok (width a)

/-- **Resolution is total on conformant records and refuses
otherwise.** -/
theorem SpecRecord.resolveArity_isOk_iff {width : α → ℕ}
    {r : SpecRecord α} :
    IsOk (r.resolveArity width) ↔ r.Conformant width := by
  obtain ⟨root, ifc⟩ := r
  unfold resolveArity Conformant
  cases ifc with
  | some I =>
    obtain ⟨inA, outA, asm⟩ := I
    dsimp only
    cases hroot : checkWidths width outA false root.atoms with
    | error e =>
      have hno : ¬ ∀ a ∈ root.atoms, width a = outA := by
        rw [← checkWidths_isOk_iff (inAssumption := false), hroot]
        exact not_isOk_error e
      simp only [not_isOk_error, false_iff]
      rintro ⟨h1, -⟩
      exact hno (h1 ⟨inA, outA, asm⟩ rfl).1
    | ok u =>
      cases u
      have hroot' : ∀ a ∈ root.atoms, width a = outA :=
        checkWidths_isOk_iff.mp (by rw [hroot]; trivial)
      dsimp only
      cases asm with
      | none =>
        simp only [isOk_ok, true_iff]
        refine ⟨fun I' hI' => ?_, fun hcontra => absurd hcontra (by simp)⟩
        obtain rfl := Option.some.inj hI'
        exact ⟨hroot', fun φ hφ => absurd hφ (by simp)⟩
      | some φ0 =>
        dsimp only
        by_cases hθ : φ0.theta0
        · rw [if_pos hθ]
          cases hass : checkWidths width inA true φ0.atoms with
          | error e =>
            have hno : ¬ ∀ a ∈ φ0.atoms, width a = inA := by
              rw [← checkWidths_isOk_iff (inAssumption := true), hass]
              exact not_isOk_error e
            simp only [not_isOk_error, false_iff]
            rintro ⟨h1, -⟩
            obtain ⟨-, h2⟩ := (h1 ⟨inA, outA, some φ0⟩ rfl).2 φ0 rfl
            exact hno h2
          | ok u =>
            cases u
            have hass' : ∀ a ∈ φ0.atoms, width a = inA :=
              checkWidths_isOk_iff.mp (by rw [hass]; trivial)
            simp only [isOk_ok, true_iff]
            refine ⟨fun I' hI' => ?_,
              fun hcontra => absurd hcontra (by simp)⟩
            obtain rfl := Option.some.inj hI'
            refine ⟨hroot', fun φ' hφ' => ?_⟩
            obtain rfl := Option.some.inj hφ'
            exact ⟨φ0.theta0_iff.mp hθ, hass'⟩
        · rw [if_neg hθ]
          simp only [not_isOk_error, false_iff]
          rintro ⟨h1, -⟩
          obtain ⟨h2, -⟩ := (h1 ⟨inA, outA, some φ0⟩ rfl).2 φ0 rfl
          exact hθ (φ0.theta0_iff.mpr h2)
  | none =>
    dsimp only
    cases hatoms : root.atoms with
    | nil =>
      simp only [isOk_ok, true_iff]
      exact ⟨fun I' hI' => absurd hI' (by simp),
        fun _ x hx => absurd hx (by simp)⟩
    | cons x rest =>
      dsimp only
      cases hrest : checkWidths width (width x) false rest with
      | error e =>
        have hno : ¬ ∀ b ∈ rest, width b = width x := by
          rw [← checkWidths_isOk_iff (inAssumption := false), hrest]
          exact not_isOk_error e
        simp only [not_isOk_error, false_iff]
        rintro ⟨-, h2⟩
        refine hno fun b hb => ?_
        exact h2 (by trivial) b (List.mem_cons_of_mem x hb) x (by simp)
      | ok u =>
        cases u
        have hrest' : ∀ b ∈ rest, width b = width x :=
          checkWidths_isOk_iff.mp (by rw [hrest]; trivial)
        simp only [isOk_ok, true_iff]
        refine ⟨fun I' hI' => absurd hI' (by simp),
          fun _ p hp q hq => ?_⟩
        -- pairwise agreement through the head atom
        rcases List.mem_cons.mp hp with rfl | hp' <;>
          rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · exact (hrest' q hq').symm
        · exact hrest' p hp'
        · rw [hrest' p hp', hrest' q hq']

/-- **A width refusal names an actual offender**: the named atom really
is in the named slot, its width really is the reported one, and it
really disagrees with the expectation. -/
theorem SpecRecord.resolveArity_error_names_offender {width : α → ℕ}
    {r : SpecRecord α} {a : α} {f e : ℕ} {b : Bool}
    (h : r.resolveArity width = .error (.widthMismatch a f e b)) :
    width a = f ∧ f ≠ e ∧
      ((b = false ∧ a ∈ r.root.atoms) ∨
        (b = true ∧ ∃ I, r.iface? = some I ∧
          ∃ φ, I.assumption? = some φ ∧ a ∈ φ.atoms)) := by
  obtain ⟨root, ifc⟩ := r
  unfold resolveArity at h
  cases ifc with
  | some I =>
    obtain ⟨inA, outA, asm⟩ := I
    dsimp only at h ⊢
    cases hroot : checkWidths width outA false root.atoms with
    | error e' =>
      rw [hroot] at h
      obtain rfl := Except.error.inj h
      obtain ⟨hmem, hw, hne, -, rfl⟩ := checkWidths_error_spec hroot
      exact ⟨hw, hne, Or.inl ⟨rfl, hmem⟩⟩
    | ok u =>
      cases u
      rw [hroot] at h
      dsimp only at h
      cases asm with
      | none => exact absurd h (by simp)
      | some φ0 =>
        dsimp only at h
        by_cases hθ : φ0.theta0
        · rw [if_pos hθ] at h
          cases hass : checkWidths width inA true φ0.atoms with
          | error e' =>
            rw [hass] at h
            obtain rfl := Except.error.inj h
            obtain ⟨hmem, hw, hne, -, rfl⟩ := checkWidths_error_spec hass
            exact ⟨hw, hne,
              Or.inr ⟨rfl, ⟨inA, outA, some φ0⟩, rfl, φ0, rfl, hmem⟩⟩
          | ok u =>
            cases u
            rw [hass] at h
            exact absurd h (by simp)
        · rw [if_neg hθ] at h
          exact absurd (Except.error.inj h) (by simp)
  | none =>
    dsimp only at h ⊢
    cases hatoms : root.atoms with
    | nil =>
      rw [hatoms] at h
      exact absurd h (by simp)
    | cons x rest =>
      rw [hatoms] at h
      dsimp only at h
      cases hrest : checkWidths width (width x) false rest with
      | error e' =>
        rw [hrest] at h
        obtain rfl := Except.error.inj h
        obtain ⟨hmem, hw, hne, -, rfl⟩ := checkWidths_error_spec hrest
        exact ⟨hw, hne, Or.inl ⟨rfl, List.mem_cons_of_mem x hmem⟩⟩
      | ok u =>
        cases u
        rw [hrest] at h
        exact absurd h (by simp)

/-- **The compile**: interface resolution, then structural recursion
over the formation structure — the root guarantee through normal-form
resolution into the exact cells.  The assumption is carried as record
data; the compile never reads it (fail-closed: no silent unconditional
strengthening). -/
noncomputable def SpecRecord.elabSpec (width : α → ℕ) (A : α → Set K)
    (r : SpecRecord α) : Except (ConformanceError α) (SpecDnf K) :=
  match r.resolveArity width with
  | .error e => .error e
  | .ok _ => .ok (NnfForm.elabNnf A r.root.nnf)

/-- The compile succeeds exactly on conformant records. -/
theorem SpecRecord.elabSpec_isOk_iff {width : α → ℕ} {A : α → Set K}
    {r : SpecRecord α} :
    IsOk (r.elabSpec width A) ↔ r.Conformant width := by
  rw [← resolveArity_isOk_iff (width := width) (r := r)]
  unfold elabSpec
  cases r.resolveArity width <;> simp

/-- On success, the compiled class is the adequacy fold of the root's
normal form: the record-level theorem composes through resolution. -/
theorem SpecRecord.elabSpec_ok_modelClass {width : α → ℕ}
    {A : α → Set K} {r : SpecRecord α} {D : SpecDnf K}
    (h : r.elabSpec width A = .ok D) :
    D.modelClass = NnfForm.classSem A r.root.nnf := by
  unfold elabSpec at h
  cases hr : r.resolveArity width with
  | error e =>
    rw [hr] at h
    exact absurd h (by simp)
  | ok n =>
    rw [hr] at h
    obtain rfl := Except.ok.inj h
    exact NnfForm.elabNnf_modelClass A r.root.nnf

/-- On success, every compiled atom carries the properness mark: the
record-level default-liveness receipt.  (True of every presentation, by
the structural fence.) -/
theorem SpecRecord.elabSpec_top_mem {width : α → ℕ} {A : α → Set K}
    {r : SpecRecord α} {D : SpecDnf K}
    (_h : r.elabSpec width A = .ok D) :
    ∀ a ∈ D.atoms, (⊤ : K → ℝ≥0∞) ∈ a.marks :=
  fun a _ => a.top_mem

end SuFunctor.Universe

/-! ## Axiom receipts

Expected closure for every statement below: ⊆ `[propext,
Classical.choice, Quot.sound]`, zero `sorryAx`. -/

#print axioms SuFunctor.Universe.wallOn_le_iff
#print axioms SuFunctor.Universe.dip_top_iff
#print axioms SuFunctor.Universe.coupledSat_safetyAtom_iff
#print axioms SuFunctor.Universe.safetyAtom_modelClass
#print axioms SuFunctor.Universe.SpecAtom.coupledSat_merge_iff
#print axioms SuFunctor.Universe.SpecAtom.modelClass_merge
#print axioms SuFunctor.Universe.SpecDnf.modelClass_single
#print axioms SuFunctor.Universe.SpecDnf.modelClass_conj
#print axioms SuFunctor.Universe.SpecDnf.modelClass_disj
#print axioms SuFunctor.Universe.SpecDnf.modelClass_top
#print axioms SuFunctor.Universe.SpecDnf.modelClass_bot
#print axioms SuFunctor.Universe.StateFormula.theta0_iff
#print axioms SuFunctor.Universe.StateFormula.den_nnf
#print axioms SuFunctor.Universe.NnfForm.elabNnf_modelClass
#print axioms SuFunctor.Universe.NnfForm.elabNnf_top_mem
#print axioms SuFunctor.Universe.NnfForm.classSem_disjFree
#print axioms SuFunctor.Universe.NnfForm.elabNnf_modelClass_disjFree
#print axioms SuFunctor.Universe.NnfForm.exists_hedging_gap
#print axioms SuFunctor.Universe.den_compl_le
#print axioms SuFunctor.Universe.den_compl_ge
#print axioms SuFunctor.Universe.checkWidths_isOk_iff
#print axioms SuFunctor.Universe.checkWidths_error_spec
#print axioms SuFunctor.Universe.SpecRecord.resolveArity_isOk_iff
#print axioms SuFunctor.Universe.SpecRecord.resolveArity_error_names_offender
#print axioms SuFunctor.Universe.SpecRecord.elabSpec_isOk_iff
#print axioms SuFunctor.Universe.SpecRecord.elabSpec_ok_modelClass
#print axioms SuFunctor.Universe.SpecRecord.elabSpec_top_mem
