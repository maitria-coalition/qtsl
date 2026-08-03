/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the semantic double functor `semFunctor` into `Crd` and its
composed soundness statement (`semFunctor_sound`).  The successor shape
is a decoration-functor route from the virtual derivation calculus into
the class-valued fibres of `SuFunctor.Site.SiteFunctor`.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Source
import SuFunctor.Target
import DoubleCat.Functor.Pseudo
import Qtsl.Soundness

/-! # The semantic functor

Judgment semantics over a hypernet's admissible valuations, the
per-rule square interface, and the double functor from the proof
calculus to the per-element stratum of the semantic universe's
denotation tier.

## What is proved here

Everything: the assembly is unconditional, and pseudo.

* **Satisfaction** (`Sat`) reads a judgment's kind as a constraint on
  the verdict pair; **conjunctive satisfaction** (`SatConj`) reads a
  loose arrow — a formal conjunction of judgments — as the conjunction
  of its elements' constraints.
* **The coherence bundle** (`SatCoherence`, proved by `satCoherence`):
  the associator squares and the congruence of composition under
  entailment.  For the retired kind-table composition these three were
  refuted, uniformly in the hypernet — the table taxed one semantic
  tautology and erased the other, and no sound, unital, syntactic
  single-judgment table could repair it (`SuFunctorLegacy.Refute` keeps the
  pins).  Under formal conjunction all three are list bookkeeping.
* **The anchor square** (`sat_ofProof`): every proof object of the
  certificate calculus yields a cell from the empty conjunction whose
  image asserts its sequent's judgment against every subprobability
  model — the soundness theorem of the calculus, landed in the
  semantic universe's vocabulary; and the converse direction
  (`satAll_ofSequent_iff`), through point-mass models, so the
  degenerate face embeds exactly.
* **The functor** (`semFunctor`), now inhabited outright — and
  **pseudo, not merely lax** (`semFunctor_isPseudo`): the compositor
  `SatConj l₁ ∧ SatConj l₂ → SatConj (l₁ ++ l₂)` is invertible
  (`satConj_append` is an iff), as is the unit comparison.  The
  retired table's compositor was to be genuinely non-invertible — its
  laxity read as semantic content — but that information loss was an
  artifact of funnelling a pair of judgments into a single one, and it
  left with the funnel: composition now retains its factors, so the
  comparison in each direction is pure bookkeeping.  The Fréchet and
  Boole inequalities are not laxity and never were; they are ordinary
  *cells* — entailments out of formal pairs — packaged as rule
  families (`unionBoundFamily` below for Boole; its siblings in
  `SuFunctorLegacy.Squares`), their content intact.
* **The composed statement** (`semFunctor_sound`): a proof object,
  read through the semantic layer, asserts its sequent's judgment
  against every subprobability model of the admissible scene, and that
  assertion is equivalent to the calculus's own semantic validity.
-/

namespace SuFunctor

open PPLC CategoryTheory PseudoDoubleCategoryStruct

/-- Admissible valuations of a hypernet: the carrier of its semantic
scene.  Admissibility is carried by the object rather than repeated in
every judgment. -/
def AdmVal (H : Hypernet) : Type := {σ : H.Valuation // σ.Admissible}

/-- The event a formula carves out of the admissible scene. -/
def evt (H : Hypernet) (φ : Formula) : Set (AdmVal H) :=
  {σ | φ.holds σ.1}

/-- The violation event of a sequent: premise holds, conclusion fails. -/
def violation (H : Hypernet) (seq : Sequent) : Set (AdmVal H) :=
  {σ | seq.pre.holds σ.1 ∧ ¬ seq.post.holds σ.1}

@[simp] theorem evt_and (H : Hypernet) (φ ψ : Formula) :
    evt H (.and φ ψ) = evt H φ ∩ evt H ψ :=
  Set.ext fun _ => Iff.rfl

@[simp] theorem evt_or (H : Hypernet) (φ ψ : Formula) :
    evt H (.or φ ψ) = evt H φ ∪ evt H ψ :=
  Set.ext fun _ => Iff.rfl

/-- Per-element semantics of a judgment: which subprobability models
satisfy it.  The kind selects the constrained component of the verdict
pair — the sequent kind bounds the violation event's (upper) weight at
zero, the `probGE` kind bounds an event's (lower) weight from below,
the `probLE` kind from above.  The envelope (credal-set) reading
quantifies this predicate over a credal set, lower kinds over the
radially maximal slice and upper kinds over the whole set; that lifting
is a successor, stated in the design record, and every square below is
formulated per-element exactly so the lifting is a one-quantifier
step. -/
def Sat (H : Hypernet) : Judgment → (SubPMF (AdmVal H) → Prop)
  | .seqValid s => fun μ => μ.prob (violation H s) ≤ 0
  | .probGE t φ => fun μ => t ≤ μ.prob (evt H φ)
  | .probLE t φ => fun μ => μ.prob (evt H φ) ≤ t

/-- Satisfaction of a formal conjunction: every judgment in the list
holds.  This is the semantic functor's action on loose arrows, and it
sends loose composition (concatenation) to conjunction on the nose
(`satConj_append`). -/
def SatConj (H : Hypernet) (l : List Judgment) (μ : SubPMF (AdmVal H)) :
    Prop :=
  ∀ j ∈ l, Sat H j μ

@[simp] theorem satConj_nil (H : Hypernet) (μ : SubPMF (AdmVal H)) :
    SatConj H [] μ :=
  fun _ hj => absurd hj List.not_mem_nil

@[simp] theorem satConj_cons {H : Hypernet} {j : Judgment}
    {l : List Judgment} {μ : SubPMF (AdmVal H)} :
    SatConj H (j :: l) μ ↔ Sat H j μ ∧ SatConj H l μ :=
  List.forall_mem_cons

/-- The compositor identity: satisfaction of a concatenation is the
conjunction of the satisfactions.  Both directions hold — this iff is
why the semantic functor is pseudo rather than lax. -/
@[simp] theorem satConj_append {H : Hypernet} {l₁ l₂ : List Judgment}
    {μ : SubPMF (AdmVal H)} :
    SatConj H (l₁ ++ l₂) μ ↔ SatConj H l₁ μ ∧ SatConj H l₂ μ :=
  List.forall_mem_append

@[simp] theorem satConj_singleton {H : Hypernet} {j : Judgment}
    {μ : SubPMF (AdmVal H)} :
    SatConj H [j] μ ↔ Sat H j μ :=
  List.forall_mem_singleton

/-- Satisfaction of an atomic composite is the conjunction of the two
atoms' satisfactions: the two-element case of `satConj_append`. -/
theorem satConj_pair {H : Hypernet} {m n : Judgment}
    {μ : SubPMF (AdmVal H)} :
    SatConj H (m.comp n) μ ↔ Sat H m μ ∧ Sat H n μ := by
  simp [Judgment.comp_def]

/-- The tautological sequent judgment holds in every model: its
violation event is empty. -/
theorem sat_unit (H : Hypernet) (μ : SubPMF (AdmVal H)) :
    Sat H Judgment.unit μ := by
  show μ.prob (violation H ⟨.tt, .tt⟩) ≤ 0
  have h : violation H ⟨.tt, .tt⟩ = (∅ : Set (AdmVal H)) := by
    ext σ
    simp only [violation, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨-, hpost⟩
    exact hpost trivial
  rw [h, SubPMF.prob_empty]

/-- The vacuous probability judgment holds in every model. -/
theorem sat_vacuous (H : Hypernet) (μ : SubPMF (AdmVal H)) :
    Sat H Judgment.vacuous μ :=
  μ.prob_nonneg _

/-- **The anchor square.**  A proof object of the certificate calculus
yields, semantically, a cell from the empty conjunction: its sequent's
judgment holds in every subprobability model over the admissible scene.
This is the calculus's soundness theorem (`ProofObject.sound`) restated
in the denotation tier's vocabulary — the violation event is empty, so
even its upper weight is zero. -/
theorem sat_ofProof {H : Hypernet} {seq : Sequent}
    (po : ProofObject H seq) (μ : SubPMF (AdmVal H)) :
    Sat H (Judgment.ofSequent seq) μ := by
  show μ.prob (violation H seq) ≤ 0
  have hval := po.sound
  have h : violation H seq = (∅ : Set (AdmVal H)) := by
    ext σ
    simp only [violation, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hpre, hnpost⟩
    exact hnpost (hval σ.1 σ.2 hpre)
  rw [h, SubPMF.prob_empty]

/-- **The degenerate face, exactly.**  A sequent's judgment holds in
every subprobability model over the admissible scene if and only if the
sequent is semantically valid in the calculus's own sense.  Forward:
point masses at admissible valuations are models.  Backward: validity
empties the violation event.  This is the checker's semantic anchor —
the allowed-or-forbidden verdict as one face of the credal stack — as a
statement rather than a remark. -/
theorem satAll_ofSequent_iff (H : Hypernet) (seq : Sequent) :
    (∀ μ : SubPMF (AdmVal H), Sat H (Judgment.ofSequent seq) μ) ↔
      seq.semanticallyValid H := by
  constructor
  · intro h σ hadm hpre
    by_contra hnpost
    have hmem : (⟨σ, hadm⟩ : AdmVal H) ∈ violation H seq := ⟨hpre, hnpost⟩
    have h1 : (SubPMF.dirac (⟨σ, hadm⟩ : AdmVal H)).prob (violation H seq)
        = 1 := SubPMF.dirac_prob_of_mem hmem
    have h0 : (SubPMF.dirac (⟨σ, hadm⟩ : AdmVal H)).prob (violation H seq)
        ≤ 0 := h (SubPMF.dirac (⟨σ, hadm⟩ : AdmVal H))
    rw [h1] at h0
    linarith
  · intro hval μ
    show μ.prob (violation H seq) ≤ 0
    have h : violation H seq = (∅ : Set (AdmVal H)) := by
      ext σ
      simp only [violation, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨hpre, hnpost⟩
      exact hnpost (hval σ.1 σ.2 hpre)
    rw [h, SubPMF.prob_empty]

/-! ## The structure squares

Under formal conjunction these are list identities.  The left unitors
are definitional (`[] ++ l` reduces to `l`); the right unitors and the
associators are transports along `List.append_nil` and
`List.append_assoc`. -/

/-- Unitor square, left, forward direction (definitional). -/
theorem sat_unitL (H : Hypernet) (l : List Judgment)
    (μ : SubPMF (AdmVal H)) (h : SatConj H ([] ++ l) μ) : SatConj H l μ :=
  h

/-- Unitor square, left, inverse direction (definitional). -/
theorem sat_unitLInv (H : Hypernet) (l : List Judgment)
    (μ : SubPMF (AdmVal H)) (h : SatConj H l μ) : SatConj H ([] ++ l) μ :=
  h

/-- Unitor square, right, forward direction. -/
theorem sat_unitR (H : Hypernet) (l : List Judgment)
    (μ : SubPMF (AdmVal H)) (h : SatConj H (l ++ []) μ) : SatConj H l μ :=
  by simpa using h

/-- Unitor square, right, inverse direction. -/
theorem sat_unitRInv (H : Hypernet) (l : List Judgment)
    (μ : SubPMF (AdmVal H)) (h : SatConj H l μ) : SatConj H (l ++ []) μ :=
  by simpa using h

/-- The structural obligations the loose composition owes the
semantics: both associator squares and loose congruence (monotonicity
of composition under semantic entailment of the arguments).

For the retired kind-table composition this bundle was **refuted, for
every hypernet**: the vacuous judgment was not a unit for its own row —
the Fréchet row taxed it — while the tautological sequent was
transparent through the projection rows, and both the associators and
congruence failed on that asymmetry, at thresholds inside `[0, 1]` and
with `tt`-only formulas (`SuFunctorLegacy.Refute` keeps the episode as
regression pins).  Under formal conjunction the bundle is proved once,
by list bookkeeping: `satCoherence`. -/
structure SatCoherence (H : Hypernet) : Prop where
  /-- Associator square, forward direction. -/
  assoc : ∀ (m n p : List Judgment) (μ : SubPMF (AdmVal H)),
    SatConj H ((m ++ n) ++ p) μ → SatConj H (m ++ (n ++ p)) μ
  /-- Associator square, inverse direction. -/
  assocInv : ∀ (m n p : List Judgment) (μ : SubPMF (AdmVal H)),
    SatConj H (m ++ (n ++ p)) μ → SatConj H ((m ++ n) ++ p) μ
  /-- Loose congruence: composition is monotone under semantic
  entailment of its arguments. -/
  hcompMono : ∀ {m₁ n₁ m₂ n₂ : List Judgment},
    (∀ μ, SatConj H m₁ μ → SatConj H n₁ μ) →
    (∀ μ, SatConj H m₂ μ → SatConj H n₂ μ) →
    ∀ μ : SubPMF (AdmVal H),
      SatConj H (m₁ ++ m₂) μ → SatConj H (n₁ ++ n₂) μ

/-- The coherence bundle holds for formal conjunction: associativity
and unitality are identities of the free monoid, and congruence is
pointwise.  This theorem is the pivot of the repair — the same bundle
was uninhabitable for the kind-table composition — and everything
downstream consumes it. -/
theorem satCoherence (H : Hypernet) : SatCoherence H where
  assoc m n p μ h := by rw [List.append_assoc] at h; exact h
  assocInv m n p μ h := by rw [← List.append_assoc] at h; exact h
  hcompMono {m₁ n₁ m₂ n₂} h₁ h₂ μ h := by
    rw [satConj_append] at h ⊢
    exact ⟨h₁ μ h.1, h₂ μ h.2⟩

/-! ## The functor -/

/-- A rule family together with its semantic squares: the tier-one
interface.  Core rules supply squares; admissible and alias rules ride
the core layer by recipe expansion before reaching the family; the
gate is the (parametric) tier membership. -/
structure SemRuleFamily (H : Hypernet) : Type 1 where
  /-- The syntactic family. -/
  rules : RuleFamily H
  /-- One semantic square per enabled instance. -/
  square : ∀ t, rules.gate t →
    ∀ μ : SubPMF (AdmVal H),
      SatConj H (rules.top t) μ → SatConj H (rules.bot t) μ

/-- Semantic reading of a derivation: structural recursion sending each
generator to its square and each closure constructor to the
corresponding semantic composition.  The structure-cell and congruence
cases consume the proven coherence bundle (`satCoherence`); nothing is
conditional. -/
theorem JDeriv.sem {H : Hypernet} {F : RuleFamily H}
    (sq : ∀ t, F.gate t →
      ∀ μ, SatConj H (F.top t) μ → SatConj H (F.bot t) μ)
    {l l' : List Judgment} (d : JDeriv H F l l') :
    ∀ μ : SubPMF (AdmVal H), SatConj H l μ → SatConj H l' μ := by
  induction d with
  | ofRule t ht => exact sq t ht
  | ofProof po =>
      exact fun μ _ => satConj_singleton.mpr (sat_ofProof po μ)
  | refl l => exact fun _ h => h
  | trans _ _ ih₁ ih₂ => exact fun μ h => ih₂ μ (ih₁ μ h)
  | hcomp _ _ ih₁ ih₂ => exact (satCoherence H).hcompMono ih₁ ih₂
  | assoc m n p => exact (satCoherence H).assoc m n p
  | assocInv m n p => exact (satCoherence H).assocInv m n p
  | unitL m => exact sat_unitL H m
  | unitLInv m => exact sat_unitLInv H m
  | unitR m => exact sat_unitR H m
  | unitRInv m => exact sat_unitRInv H m

/-- **The semantic double functor** from the proof calculus over a
hypernet to the per-element stratum of the denotation tier.

* objects and tight arrows: trivial at this stratum (one scene per
  hypernet; the wiring-base indexing with hypernet morphisms as tight
  arrows is the named successor);
* loose arrows: a formal conjunction of judgments maps to the
  conjunction of their satisfaction constraints;
* cells: a derivation maps to its semantic entailment (`JDeriv.sem`);
* compositor and unit comparison: the identities of conjunction
  (`satConj_append`, `satConj_nil`) — invertible, so the functor is
  pseudo (`semFunctor_isPseudo`), packaged through the lax interface
  the library uses as its carrier for pseudo-ness.

The five coherence laws hold by proof irrelevance: both double
categories are thin in the cell dimension. -/
noncomputable def semFunctor (H : Hypernet) (F : SemRuleFamily H) :
    LaxDoubleFunctor (BLD H F.rules) (Crd (AdmVal H)) where
  toFunctor :=
    { obj := fun _ => Crd.mk'
      map := fun _ => ⟨⟩ }
  mapLoose := SatConj H
  mapCell α := ⟨JDeriv.sem F.square α.down⟩
  mapCell_vId _ := Subsingleton.elim _ _
  mapCell_vComp _ _ := Subsingleton.elim _ _
  laxComp _ _ := ⟨fun _ h => satConj_append.mpr h⟩
  laxId _ := ⟨fun μ _ => satConj_nil H μ⟩
  laxComp_natural _ _ := Subsingleton.elim _ _
  laxId_natural _ := Subsingleton.elim _ _
  laxComp_assoc _ _ _ := Subsingleton.elim _ _
  laxComp_leftUnitor _ := Subsingleton.elim _ _
  laxComp_rightUnitor _ := Subsingleton.elim _ _

/-- **The functor is pseudo, not merely lax**: the compositor and the
unit comparison are invertible cells.  Composition in the source is a
formal object retaining its factors, so each comparison direction is
pure bookkeeping (`satConj_append` is an iff).  The retired kind
table's compositor genuinely lost information — composing two graded
judgments through one slot forgot their marginals — but that loss was
an artifact of the funnel, and it left with the funnel.  The Fréchet
and Boole content is not laxity: it lives in ordinary cells, packaged
as rule families with their inequalities intact. -/
theorem semFunctor_isPseudo (H : Hypernet) (F : SemRuleFamily H) :
    (semFunctor H F).IsPseudo where
  laxComp_isInvertible _ _ :=
    ⟨⟨fun _ h => satConj_append.mp h⟩,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  laxId_isInvertible _ :=
    ⟨⟨fun _ _ => trivial⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-! ## The worked rule family: the union bound

The battery-glue rule concluding a risk bound from two risk bounds is
Boole's inequality followed by monotone weakening along the event
decomposition `fail ⊆ E₁ ∪ E₂`.  Under the retired table this content
doubled as the upper-kind compositor row; demoted, it is an ordinary
family cell out of a formal pair — the premise judgments enter
verbatim, and the inequality is the square. -/

/-- Instances of the union-bound rule: two premise thresholds and
events, a target event, and (as the gate) the event decomposition side
condition. -/
def unionBoundFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula × Formula
      gate := fun i => evt H i.2.2.2.2 ⊆ evt H i.2.2.1 ∪ evt H i.2.2.2.1
      top := fun i =>
        (Judgment.probLE i.1 i.2.2.1).comp (Judgment.probLE i.2.1 i.2.2.2.1)
      bot := fun i => [Judgment.probLE (i.1 + i.2.1) i.2.2.2.2] }
  square := by
    rintro ⟨a, b, e₁, e₂, fail⟩ hgate μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    show μ.prob (evt H fail) ≤ a + b
    have h₁ : μ.prob (evt H e₁) ≤ a := h.1
    have h₂ : μ.prob (evt H e₂) ≤ b := h.2
    have hb := μ.prob_union_le (evt H e₁) (evt H e₂)
    exact le_trans (μ.prob_mono hgate) (by linarith)

/-- The composed statement at this stratum: a proof object of the
certificate calculus, read through the semantic functor, asserts its
sequent's judgment against every subprobability model of the
admissible scene — and that assertion is equivalent to the calculus's
own semantic validity. -/
theorem semFunctor_sound (H : Hypernet) {seq : Sequent}
    (po : ProofObject H seq) : seq.semanticallyValid H :=
  (satAll_ofSequent_iff H seq).mp fun μ => sat_ofProof po μ

end SuFunctor
