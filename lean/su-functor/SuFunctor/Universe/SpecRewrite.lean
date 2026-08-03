import SuFunctor.Adequacy.SpecPathLens

/-! # The rewrite layer, as equalities and inclusions of compiled classes

The specification language ships a *rewrite layer*: negation normal
form (double negation, De Morgan, the closed/strict atom swaps), the
derived spellings (avoid, the two Streett degenerations), the closure
moves that resolve strict literals, and the bounded-horizon alias that
discharges a negated reach by an unbounded invariance.  Each of those
is warranted, at the proof-theory grade, by **one region-denotation
equality** — the rewritten formula denotes the same region, so every
region-satisfaction judgment transports across it unchanged.

This module asks the semantic-universe question about that layer:
*when is a rewrite sound at the level of compiled model classes?*  Two
predicates are compared, each in an interpretation-relative form (at a
fixed carrier and atom reading) and a uniform form (at all of them):

* `DenEq` / `DenEquiv` — the proof-theory warrant: the two formulas
  denote the same region.
* `ClassEq` / `ClassEquiv` — the universe warrant: the two formulas
  *compile* to presentations with the same model class.

The headline is that **the two are not the same predicate, and the
proof-theory one is strictly weaker** (`exists_denEq_not_classEq`):
a disjunction and a single atom of the same denotation compile to
different classes, because a system may hedge — keep its permitted
region inside the union while committing to neither disjunct — and the
presentation semantics excludes exactly those.  The gap is the compiled
image of `exists_hedging_gap`, transported through normal-form
resolution.

So the layer's soundness at the universe is carried by *term structure*,
not by denotation: `classSem` is a homomorphism of the distributive
lattice of normal forms (`classSem_conj_comm` and its family), so every
rewrite that moves an NNF term by lattice laws is sound at the
universe, and the normal-form dualities are sound for the sharper
reason that they do not move the term at all
(`classEquiv_of_nnf_eq`).  The lattice family includes **absorption as
a class equality** (`classSem_absorb_conj`, `classSem_absorb_disj`; at
the surface, `classEquiv_absorb_conj`) — a prereg surprise: the leg
predicted the one disjunction-deleting law would fail, but the hedging
gap is a fact about the region↔class seam, and absorption never
crosses that seam — both sides are classes, and `classSem` lands in a
genuine distributive lattice of sets, where the law holds with nothing
to pay.  Where the fragment cannot hedge, the two warrants coincide
(`classSem_eq_iff_den_eq_disjFree`) — with one fence: the empty
region's class is empty, so the denotation direction of the
equivalence consumes nonemptiness.

The path-and-record half of the layer is restated at the record site,
and the restatement's value is that it makes the rewrites' **types**
disagree, exactly as their tiering does:

* the derived spelling of avoidance is an equality — of record classes
  (`recordClass_avoid`) and of stage predicates (`recordPred_avoid_iff`);
* the "infinitely often" Streett degeneration is an equivalence
  *conditioned on occupation* (`streettOn_singleton_univ_iff`, with
  `streettOn_singleton_univ_empty` exhibiting the empty record as the
  one stage set on which the two readings part);
* the bounded-horizon alias is an inclusion
  (`recordClass_always_subset_alwaysT`), never an equality
  (`exists_recordClass_alwaysT_not_always`);
* and the missing mirror of that alias is a refusal the compiler
  states (`pathNnf_notPath_always_refuses`), not a prose fence.

Everything here is carrier-generic and consumes only the landed exact
core (`SpecElab`) and record site (`SpecPathLens`).
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

universe u v

/-! ## The two soundness predicates

Interpretation-relative first (this is the grade at which a rewrite is
*used*: a checker holds one carrier and one atom reading), then the
uniform closure. -/

section Predicates

variable {α : Type v} {K : Type u}

/-- **The proof-theory warrant, at one interpretation**: the two state
formulas denote the same region.  This is the unpacking target the
rewrite rules are filed against — a region-denotation equality and
nothing else. -/
def DenEq (A : α → Set K) (φ ψ : StateFormula α) : Prop :=
  φ.den A = ψ.den A

/-- **The universe warrant, at one interpretation**: the two state
formulas compile — through normal-form resolution and the presentation
compile — to coupled DNFs with the same model class. -/
def ClassEq (A : α → Set K) (φ ψ : StateFormula α) : Prop :=
  (NnfForm.elabNnf A φ.nnf).modelClass = (NnfForm.elabNnf A ψ.nnf).modelClass

/-- The proof-theory warrant, uniformly: at every carrier and every
reading of the atoms.  A rewrite rule of the layer claims this. -/
def DenEquiv (φ ψ : StateFormula α) : Prop :=
  ∀ {K : Type u} (A : α → Set K), DenEq A φ ψ

/-- The universe warrant, uniformly.  This is what "a rewrite is sound
iff the compiled classes are equal" asks for. -/
def ClassEquiv (φ ψ : StateFormula α) : Prop :=
  ∀ {K : Type u} (A : α → Set K), ClassEq A φ ψ

theorem ClassEquiv.refl (φ : StateFormula α) : ClassEquiv.{u} φ φ :=
  fun _ => rfl

theorem ClassEquiv.symm {φ ψ : StateFormula α} (h : ClassEquiv.{u} φ ψ) :
    ClassEquiv.{u} ψ φ :=
  fun A => (h A).symm

theorem ClassEquiv.trans {φ ψ χ : StateFormula α}
    (h₁ : ClassEquiv.{u} φ ψ) (h₂ : ClassEquiv.{u} ψ χ) :
    ClassEquiv.{u} φ χ :=
  fun A => (h₁ A).trans (h₂ A)

theorem DenEquiv.refl (φ : StateFormula α) : DenEquiv.{u} φ φ :=
  fun _ => rfl

theorem DenEquiv.symm {φ ψ : StateFormula α} (h : DenEquiv.{u} φ ψ) :
    DenEquiv.{u} ψ φ :=
  fun A => (h A).symm

/-- **Syntactic normal-form agreement suffices.**  The dualities the
rewrite layer is mostly made of — double negation, De Morgan through
the two lattice connectives — do not move the normal form at all, so
their class equality is definitional.  This is the cheapest sound
route, and the one the normal-form batch actually travels. -/
theorem classEq_of_nnf_eq {A : α → Set K} {φ ψ : StateFormula α}
    (h : φ.nnf = ψ.nnf) : ClassEq A φ ψ := by
  unfold ClassEq; rw [h]

theorem classEquiv_of_nnf_eq {φ ψ : StateFormula α} (h : φ.nnf = ψ.nnf) :
    ClassEquiv.{u} φ ψ :=
  fun _ => classEq_of_nnf_eq h

end Predicates

/-! ## The universe warrant implies the proof-theory warrant

One direction is easy and holds at every interpretation: walls are the
probe.  A region is recovered from a class by asking which walls it
contains. -/

section ClassImpliesDen

variable {α : Type v} {K : Type u}

/-- The wall of a region permits exactly that region. -/
@[simp] theorem permitted_wallOn (C : Set K) : permitted (wallOn C) = C := by
  ext μ
  by_cases h : μ ∈ C
  · simp [mem_permitted_iff, wallOn_apply_of_mem h, h]
  · simp [mem_permitted_iff, wallOn_apply_of_not_mem h, h]

/-- A nonempty region's wall is safe and proper against it — the probe
system for reading regions off classes. -/
theorem wallOn_mem_safeProper {C : Set K} (h : C.Nonempty) :
    wallOn C ∈ safeProper C := by
  constructor
  · rw [permitted_wallOn]
  · rw [permitted_wallOn]; exact h

/-- Membership of a wall in a class of the disjunction-free fragment
reads the denotation directly. -/
theorem wallOn_mem_safeProper_iff {C D : Set K} (h : C.Nonempty) :
    wallOn C ∈ safeProper D ↔ C ⊆ D := by
  constructor
  · rintro ⟨hsub, -⟩
    rwa [permitted_wallOn] at hsub
  · intro hsub
    exact ⟨by rw [permitted_wallOn]; exact hsub, by rw [permitted_wallOn]; exact h⟩

end ClassImpliesDen

/-! ## The fork: the proof-theory warrant is strictly weaker

The witness lives at one interpretation, which is the grade a checker
uses; the uniform statement follows because a uniform equivalence
restricts to every interpretation. -/

section Fork

/-- **The fork, decided: region-denotation equality does not transport
to class equality.**  A disjunction of two atoms and a single atom of
the same denotation compile to *different* model classes — the
disjunction's class excludes the hedging systems, whose permitted
region sits inside the union while committing to neither disjunct.

The proof-theory layer's warrant is therefore *strictly weaker* than
the universe's: soundness of the rewrite layer at the semantic universe
is not a corollary of the denotation equalities the rules are filed
against, and must be carried by the term structure instead (the
lattice-homomorphism family below).

This is the presentation-boundary sibling of the measure-boundary fault
line the negation calculus is fenced at: the fence there is that no
duality crosses the measure boundary; the fence here is that no rewrite
of the layer deletes a disjunction. -/
theorem exists_denEq_not_classEq :
    ∃ (A : Fin 3 → Set Bool) (φ ψ : StateFormula (Fin 3)),
      DenEq A φ ψ ∧ ¬ ClassEq A φ ψ := by
  classical
  refine ⟨![{true}, {false}, Set.univ],
    .disj (.atom 0) (.atom 1), .atom 2, ?_, ?_⟩
  · -- the denotations agree: `{true} ∪ {false} = univ` on `Bool`
    show ({true} : Set Bool) ∪ {false} = Set.univ
    ext μ; cases μ <;> simp
  · -- the classes differ: the zero system hedges
    intro hcls
    have hmem : (0 : Bool → ℝ≥0∞)
        ∈ (NnfForm.elabNnf ![{true}, {false}, Set.univ]
            (StateFormula.atom (2 : Fin 3)).nnf).modelClass := by
      have : (NnfForm.elabNnf (![{true}, {false}, Set.univ] : Fin 3 → Set Bool)
          (StateFormula.atom (2 : Fin 3)).nnf).modelClass
            = safeProper (Set.univ : Set Bool) := by
        rw [NnfForm.elabNnf_modelClass]
        rfl
      rw [this]
      exact ⟨fun _ _ => trivial, ⟨true, by simp [mem_permitted_iff]⟩⟩
    rw [← hcls] at hmem
    -- but the zero system belongs to neither disjunct's class
    rw [NnfForm.elabNnf_modelClass] at hmem
    have hexp : NnfForm.classSem (![{true}, {false}, Set.univ] : Fin 3 → Set Bool)
        (StateFormula.disj (.atom 0) (.atom 1)).nnf
        = safeProper ({true} : Set Bool) ∪ safeProper ({false} : Set Bool) := rfl
    rw [hexp] at hmem
    rcases hmem with ⟨h, -⟩ | ⟨h, -⟩
    · have hf : false ∈ permitted (0 : Bool → ℝ≥0∞) := by
        simp [mem_permitted_iff]
      simpa using h hf
    · have ht : true ∈ permitted (0 : Bool → ℝ≥0∞) := by
        simp [mem_permitted_iff]
      simpa using h ht

/-- **The transport schema fails.**  There is no implication from the
proof-theory warrant to the universe warrant, taken as a rule about
interpretations: some interpretation satisfies the first and refutes
the second.  (This is the form in which the failure bites a checker,
which holds one interpretation at a time.) -/
theorem not_denEq_imp_classEq :
    ¬ ∀ (A : Fin 3 → Set Bool) (φ ψ : StateFormula (Fin 3)),
        DenEq A φ ψ → ClassEq A φ ψ := by
  obtain ⟨A, φ, ψ, hden, hcls⟩ := exists_denEq_not_classEq
  exact fun h => hcls (h A φ ψ hden)

end Fork

/-! ## The positive replacement: the compile is a lattice homomorphism

The fork says denotation cannot carry the layer.  What carries it is
*term structure*: `classSem` sends the two normal-form connectives to
intersection and union of model classes, so the whole distributive
lattice of set operations is available on the class side, law by law.
Every rewrite that moves an NNF term by a lattice law is therefore
sound at the universe — and, unlike the denotation route, this is
proved once and reused, at every carrier and every interpretation. -/

section Lattice

variable {α : Type v} {K : Type u} (A : α → Set K)

@[simp] theorem classSem_conj (ψ χ : NnfForm α) :
    NnfForm.classSem A (.conj ψ χ)
      = NnfForm.classSem A ψ ∩ NnfForm.classSem A χ := rfl

@[simp] theorem classSem_disj (ψ χ : NnfForm α) :
    NnfForm.classSem A (.disj ψ χ)
      = NnfForm.classSem A ψ ∪ NnfForm.classSem A χ := rfl

theorem classSem_conj_comm (ψ χ : NnfForm α) :
    NnfForm.classSem A (.conj ψ χ) = NnfForm.classSem A (.conj χ ψ) := by
  simp [Set.inter_comm]

theorem classSem_disj_comm (ψ χ : NnfForm α) :
    NnfForm.classSem A (.disj ψ χ) = NnfForm.classSem A (.disj χ ψ) := by
  simp [Set.union_comm]

theorem classSem_conj_assoc (ψ χ ω : NnfForm α) :
    NnfForm.classSem A (.conj (.conj ψ χ) ω)
      = NnfForm.classSem A (.conj ψ (.conj χ ω)) := by
  simp [Set.inter_assoc]

theorem classSem_disj_assoc (ψ χ ω : NnfForm α) :
    NnfForm.classSem A (.disj (.disj ψ χ) ω)
      = NnfForm.classSem A (.disj ψ (.disj χ ω)) := by
  simp [Set.union_assoc]

theorem classSem_conj_idem (ψ : NnfForm α) :
    NnfForm.classSem A (.conj ψ ψ) = NnfForm.classSem A ψ := by
  simp

theorem classSem_disj_idem (ψ : NnfForm α) :
    NnfForm.classSem A (.disj ψ ψ) = NnfForm.classSem A ψ := by
  simp

/-- Distribution of the meet over the join, at the class level. -/
theorem classSem_conj_disj_left (ψ χ ω : NnfForm α) :
    NnfForm.classSem A (.conj ψ (.disj χ ω))
      = NnfForm.classSem A (.disj (.conj ψ χ) (.conj ψ ω)) := by
  simp [Set.inter_union_distrib_left]

/-- Distribution of the join over the meet, at the class level. -/
theorem classSem_disj_conj_left (ψ χ ω : NnfForm α) :
    NnfForm.classSem A (.disj ψ (.conj χ ω))
      = NnfForm.classSem A (.conj (.disj ψ χ) (.disj ψ ω)) := by
  simp [Set.union_inter_distrib_left]

/-- The top constant is the meet unit — with the fence that `tru`'s
class is `safeProper univ`, the *proper* systems, not all of them: the
properness demand is never dischargeable, so `tru` is a unit only
against classes already inside it, which every `classSem` cell is. -/
theorem classSem_le_tru (ψ : NnfForm α) :
    NnfForm.classSem A ψ ⊆ NnfForm.classSem A (.tru : NnfForm α) := by
  induction ψ with
  | tru => exact subset_rfl
  | fls => exact Set.empty_subset _
  | lit pos a =>
    cases pos <;>
      exact fun σ hσ => ⟨fun _ _ => trivial, hσ.2⟩
  | conj ψ χ ihψ _ => exact fun σ hσ => ihψ hσ.1
  | disj ψ χ ihψ ihχ =>
    rintro σ (hσ | hσ)
    · exact ihψ hσ
    · exact ihχ hσ

theorem classSem_tru_conj (ψ : NnfForm α) :
    NnfForm.classSem A (.conj .tru ψ) = NnfForm.classSem A ψ := by
  simp only [classSem_conj]
  exact Set.inter_eq_self_of_subset_right (classSem_le_tru A ψ)

theorem classSem_fls_disj (ψ : NnfForm α) :
    NnfForm.classSem A (.disj .fls ψ) = NnfForm.classSem A ψ := by
  simp [NnfForm.classSem]

theorem classSem_fls_conj (ψ : NnfForm α) :
    NnfForm.classSem A (.conj .fls ψ) = NnfForm.classSem A (.fls : NnfForm α) := by
  simp [NnfForm.classSem]

/-- **Absorption holds at the class level — a prereg surprise.**  The
leg predicted this would fail, on the reasoning that absorption is
where a disjunction is *deleted* and the hedging gap makes a
disjunction's class smaller than its denotation suggests.  The
prediction confused two strata.  The hedging gap is about the relation
between a class and a *region*; absorption is a relation between
classes and classes, and `classSem` lands in a genuine distributive
lattice of sets, where `S ∩ (S ∪ T) = S` holds with nothing to pay.

The honest reading: the fork's obstruction is exactly and only the
region↔class seam.  Once both sides of a rewrite are read as classes,
the whole lattice is available. -/
theorem classSem_absorb_conj (ψ χ : NnfForm α) :
    NnfForm.classSem A (.conj ψ (.disj ψ χ)) = NnfForm.classSem A ψ := by
  simp

theorem classSem_absorb_disj (ψ χ : NnfForm α) :
    NnfForm.classSem A (.disj ψ (.conj ψ χ)) = NnfForm.classSem A ψ := by
  simp

end Lattice

/-! ### Lattice laws as class equalities of surface formulas

The lemmas above live on normal forms.  Their surface consequences are
what a rewrite engine consumes: each is an equality of *compiled model
classes* of `StateFormula`s, at every carrier and interpretation. -/

section LatticeSurface

variable {α : Type v} {K : Type u}

/-- The bridge: a class equality at one interpretation is exactly an
equality of the two class-semantics cells, through the landed compile
adequacy fold. -/
theorem classEq_iff_classSem {A : α → Set K} {φ ψ : StateFormula α} :
    ClassEq A φ ψ
      ↔ NnfForm.classSem A φ.nnf = NnfForm.classSem A ψ.nnf := by
  unfold ClassEq
  rw [NnfForm.elabNnf_modelClass, NnfForm.elabNnf_modelClass]

theorem classEquiv_conj_comm (φ ψ : StateFormula α) :
    ClassEquiv.{u} (.conj φ ψ) (.conj ψ φ) :=
  fun A => classEq_iff_classSem.mpr (classSem_conj_comm A _ _)

theorem classEquiv_disj_comm (φ ψ : StateFormula α) :
    ClassEquiv.{u} (.disj φ ψ) (.disj ψ φ) :=
  fun A => classEq_iff_classSem.mpr (classSem_disj_comm A _ _)

theorem classEquiv_conj_assoc (φ ψ χ : StateFormula α) :
    ClassEquiv.{u} (.conj (.conj φ ψ) χ) (.conj φ (.conj ψ χ)) :=
  fun A => classEq_iff_classSem.mpr (classSem_conj_assoc A _ _ _)

theorem classEquiv_disj_assoc (φ ψ χ : StateFormula α) :
    ClassEquiv.{u} (.disj (.disj φ ψ) χ) (.disj φ (.disj ψ χ)) :=
  fun A => classEq_iff_classSem.mpr (classSem_disj_assoc A _ _ _)

theorem classEquiv_absorb_conj (φ ψ : StateFormula α) :
    ClassEquiv.{u} (.conj φ (.disj φ ψ)) φ :=
  fun A => classEq_iff_classSem.mpr (classSem_absorb_conj A _ _)

theorem classEquiv_distrib (φ ψ χ : StateFormula α) :
    ClassEquiv.{u} (.conj φ (.disj ψ χ)) (.disj (.conj φ ψ) (.conj φ χ)) :=
  fun A => classEq_iff_classSem.mpr (classSem_conj_disj_left A _ _ _)

end LatticeSurface

/-! ## The normal-form dualities: sound because they do not move the term

Double negation and the two De Morgan directions are `ClassEquiv` for
the sharpest possible reason — normal-form resolution sends both sides
to the *same* term, so no semantic argument is needed at all.  This is
the whole normal-form batch of the rewrite layer, discharged by
`classEquiv_of_nnf_eq`. -/

section Dualities

variable {α : Type v}

theorem classEquiv_neg_neg (φ : StateFormula α) :
    ClassEquiv.{u} (.neg (.neg φ)) φ :=
  classEquiv_of_nnf_eq rfl

theorem classEquiv_neg_conj (φ ψ : StateFormula α) :
    ClassEquiv.{u} (.neg (.conj φ ψ)) (.disj (.neg φ) (.neg ψ)) :=
  classEquiv_of_nnf_eq rfl

theorem classEquiv_neg_disj (φ ψ : StateFormula α) :
    ClassEquiv.{u} (.neg (.disj φ ψ)) (.conj (.neg φ) (.neg ψ)) :=
  classEquiv_of_nnf_eq rfl

theorem classEquiv_neg_tru :
    ClassEquiv.{u} (.neg .tru : StateFormula α) .fls :=
  classEquiv_of_nnf_eq rfl

theorem classEquiv_neg_fls :
    ClassEquiv.{u} (.neg .fls : StateFormula α) .tru :=
  classEquiv_of_nnf_eq rfl

end Dualities

/-! ## Where the two warrants coincide

The fork's obstruction is disjunction.  Off it, the class is
`safeProper` of the denotation and the two warrants are the same
statement — which is the sentence the specification chapter can carry
about when a denotation argument suffices. -/

section DisjFree

variable {α : Type v} {K : Type u}

/-- **The coincidence, on the disjunction-free fragment.**  When both
normal forms avoid disjunction, class equality and denotation equality
are interderivable — with one fence: the empty region's class is empty
(`safeProper_empty`), so two distinct empty-denoting formulas have equal
classes without equal denotations.  The clean statement therefore runs
from denotation to class, and back under nonemptiness. -/
theorem classSem_eq_of_den_eq_disjFree {A : α → Set K} {ψ χ : NnfForm α}
    (hψ : ψ.DisjFree) (hχ : χ.DisjFree) (h : ψ.den A = χ.den A) :
    NnfForm.classSem A ψ = NnfForm.classSem A χ := by
  rw [NnfForm.classSem_disjFree A ψ hψ, NnfForm.classSem_disjFree A χ hχ, h]

/-- The converse, under nonemptiness: a nonempty region is read back off
its class by the wall probe. -/
theorem den_eq_of_classSem_eq_disjFree {A : α → Set K} {ψ χ : NnfForm α}
    (hψ : ψ.DisjFree) (hχ : χ.DisjFree)
    (hne : (ψ.den A).Nonempty) (hne' : (χ.den A).Nonempty)
    (h : NnfForm.classSem A ψ = NnfForm.classSem A χ) :
    ψ.den A = χ.den A := by
  rw [NnfForm.classSem_disjFree A ψ hψ, NnfForm.classSem_disjFree A χ hχ] at h
  apply Set.Subset.antisymm
  · have hmem : wallOn (ψ.den A) ∈ safeProper (χ.den A) := by
      rw [← h]; exact wallOn_mem_safeProper hne
    exact (wallOn_mem_safeProper_iff hne).mp hmem
  · have hmem : wallOn (χ.den A) ∈ safeProper (ψ.den A) := by
      rw [h]; exact wallOn_mem_safeProper hne'
    exact (wallOn_mem_safeProper_iff hne').mp hmem

/-- The chapter's sentence: on the disjunction-free fragment with
nonempty denotations, the proof-theory warrant and the universe warrant
are the same warrant. -/
theorem classSem_eq_iff_den_eq_disjFree {A : α → Set K} {ψ χ : NnfForm α}
    (hψ : ψ.DisjFree) (hχ : χ.DisjFree)
    (hne : (ψ.den A).Nonempty) (hne' : (χ.den A).Nonempty) :
    NnfForm.classSem A ψ = NnfForm.classSem A χ ↔ ψ.den A = χ.den A :=
  ⟨den_eq_of_classSem_eq_disjFree hψ hχ hne hne',
    classSem_eq_of_den_eq_disjFree hψ hχ⟩

end DisjFree

/-! ## The layer at the record site: what is an equality, and what is not

The state-formula half of the rewrite layer is all equalities.  The
path half is not, and the semantic-universe restatement is where that
becomes visible **in the types**: the derived spelling of avoidance is
an equality, the bounded-horizon alias is a one-way inclusion, and the
missing mirror of that alias is a refusal the normal-form resolver
states rather than a fence the prose keeps. -/

section RecordLayer

variable {X : Type u} [Fintype X] [TopologicalSpace X] {α : Type v}
variable [DiscreteTopology X]

/-- **The derived spelling of avoidance is an equality.**  "Avoid `β`"
is a surface abbreviation whose expansion is unbounded invariance of
`¬β`.  Its warrant is that the expansion's record class is exactly the
class of records avoiding the region — stated against the *avoidance
predicate itself*, so the theorem has content rather than being a
restatement of the abbreviation. -/
def avoidsRegion (sp : RecordSpecies) (B : Set X) :
    Set (NonemptyCompacts X × ProbState X) :=
  {p | ∀ x ∈ stages sp p, x ∉ B}

theorem recordClass_avoid (sp : RecordSpecies) (τ : X → ℕ) (A : α → Set X)
    (β : StateFormula α) :
    recordClass sp τ A (.always β.neg) = avoidsRegion sp (β.den A) := by
  ext p
  rw [mem_recordClass_iff]
  exact Iff.rfl

/-- Avoidance, unfolded to the stage predicate the compile actually
reads: no occupied stage lies in the avoided region. -/
theorem recordPred_avoid_iff {τ : X → ℕ} {A : α → Set X}
    {β : StateFormula α} {S : Set X} :
    recordPred τ A (.always β.neg) S ↔ ∀ x ∈ S, x ∉ β.den A :=
  Iff.rfl

/-- **The bounded-horizon alias is an inclusion, not an equality.**
Unbounded invariance implies invariance up to any deadline, so the
alias over-approximates in exactly one direction — the direction the
catalogue's soundness obligation names. -/
theorem recordClass_always_subset_alwaysT (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (n : ℕ) (φ : StateFormula α) :
    recordClass sp τ A (.always φ) ⊆ recordClass sp τ A (.alwaysT n φ) := by
  intro p hp
  rw [mem_recordClass_iff] at hp ⊢
  exact fun x hx _ => hp hx

/-- **And the reverse fails.**  A bounded-invariance record need not be
an unbounded-invariance record: a stage outside the window may leave
the good region.  So the alias is genuinely one-way, and stating it as
a class equality would be unsound. -/
theorem exists_recordClass_alwaysT_not_always :
    ∃ (τ : Bool → ℕ) (A : Fin 1 → Set Bool) (n : ℕ) (φ : StateFormula (Fin 1))
      (S : Set Bool),
      recordPred τ A (.alwaysT n φ) S ∧ ¬ recordPred τ A (.always φ) S := by
  classical
  refine ⟨fun b => if b then 1 else 0, ![{false}], 0, .atom 0, Set.univ,
    ?_, ?_⟩
  · intro x _ hτ
    -- inside the window `τ x ≤ 0`, only `false` survives, and it is good
    cases x with
    | false => exact Set.mem_singleton _
    | true => exact absurd hτ (by decide)
  · intro h
    have := h (Set.mem_univ true)
    simp [StateFormula.den] at this

/-- **The missing mirror is a refusal, not a fence.**  The dual of the
bounded alias would discharge a negated *unbounded* invariance, and no
unbounded-reach former spells it — so normal-form resolution refuses
with a named address instead of producing a term.  The absence is
machine-visible. -/
theorem pathNnf_notPath_always_refuses (φ : StateFormula α) :
    pathNnf (.notPath (.always φ)) = .error .negatedAlways :=
  rfl

/-- The two other refusals of the same discipline, for completeness of
the receipt: no release former, no Rabin acceptance. -/
theorem pathNnf_notPath_untilF_refuses (n : ℕ) (sf tg : StateFormula α) :
    pathNnf (.notPath (.untilF n sf tg)) = .error .negatedUntil :=
  rfl

theorem pathNnf_notPath_streett_refuses (prs : List (StreettPair α)) :
    pathNnf (.notPath (.streett prs)) = .error .negatedStreett :=
  rfl

/-! ### The two Streett degenerations at the record site

The audit of the surface sugars flagged the "infinitely often"
degeneration as *chart-relative*: read over paths, its identification
with reachability consumes a side condition about the empty stage set.
At the record site the question changes shape, because the acceptance
combinator quantifies over *occupied stages*, never over paths — and
the side condition becomes an explicit nonemptiness hypothesis that
the statement can simply carry. -/

/-- The single-pair Streett condition with a trivial request degenerates
to reachability of the response region — **conditioned on occupation**,
which is the record-stratum form of the chart-relativity the audit
named at the path stratum. -/
theorem streettOn_singleton_univ_iff {Y : Type*} {G S : Set Y} :
    streettOn [(Set.univ, G)] S ↔ (S.Nonempty → (S ∩ G).Nonempty) := by
  constructor
  · rintro h ⟨x, hx⟩
    obtain ⟨y, hy, hyG⟩ := h (Set.univ, G) (by simp) ⟨x, hx, trivial⟩
    exact ⟨y, hy, hyG⟩
  · rintro h pr hpr ⟨x, hx, -⟩
    simp only [List.mem_singleton] at hpr
    subst hpr
    obtain ⟨y, hy, hyG⟩ := h ⟨x, hx⟩
    exact ⟨y, hy, hyG⟩

/-- **The record stratum dissolves the chart-relativity** — with the
side condition made explicit rather than hidden.  On an occupied record
the degeneration is an unconditional identity with bounded reach at any
window that admits every occupied stage. -/
theorem streettOn_singleton_univ_of_nonempty {Y : Type*} {G S : Set Y}
    (hS : S.Nonempty) :
    streettOn [(Set.univ, G)] S ↔ (S ∩ G).Nonempty := by
  rw [streettOn_singleton_univ_iff]
  exact ⟨fun h => h hS, fun h _ => h⟩

/-- The empty record is the escape clause, exhibited: the degeneration
holds vacuously there while reachability fails.  This is the audit's
finding, mechanized as the one stage set on which the two readings
part. -/
theorem streettOn_singleton_univ_empty {Y : Type*} {G : Set Y} :
    streettOn [(Set.univ, G)] (∅ : Set Y) ∧ ¬ ((∅ : Set Y) ∩ G).Nonempty := by
  refine ⟨?_, ?_⟩
  · rintro pr - ⟨x, hx, -⟩
    exact absurd hx (Set.notMem_empty x)
  · rintro ⟨x, hx, -⟩
    exact absurd hx (Set.notMem_empty x)

end RecordLayer

end SuFunctor.Universe
