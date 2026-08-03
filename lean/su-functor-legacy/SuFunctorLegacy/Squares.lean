/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the per-rule semantic square families at the per-element
`SubPMF` stratum.  The successor content is per-rule soundness over the
locally closed class fibres.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Functor

/-! # Semantic squares at the per-element stratum

The rule families whose semantic squares are statable and provable at
this stratum — per-element constraints on subprobability mass functions
over a single hypernet's admissible scene.  `unionBoundFamily` (in
`SuFunctorLegacy.Functor`) is the worked two-premise instance; this module
adds the structural family, the remaining rows of the retired
composition table as derivable cells, the transport families that every
later refinement factors through, worked instances, and the
multi-premise rules that pair retention admits verbatim.

## The one remaining obstruction

* **The zero-model obstruction.**  The zero mass function satisfies
  every sequent judgment and every upper bound, but no lower bound with
  positive threshold.  Hence no rule concluding `probGE p _` with
  `0 < p` admits a per-element square whose premises are sequent-kind
  (or empty): the square's statement is refuted by the zero model
  before any rule content enters.  Lower-bound conclusions need either
  a lower-bound premise (the transport shape below, the mass premise of
  the safety battery, the verdict premise of monitor elimination) or
  the envelope stratum, where the lower component reads the radially
  maximal slice and the zero model leaves the quantifier's range.  This
  is the quantifier discipline of the semantic-universe chapter
  (per-element first, envelope last) showing up as a hard boundary
  rather than a preference.

## The retired obstruction

An earlier revision recorded a second, *interface* obstruction here: a
rule entered a family through the loose **composite** of its premises,
and the kind-table composition collapsed every mixed lower/upper pair
to the vacuous judgment — so a rule pairing a risk bound with a mass
premise (every safety/deadline battery) presented a tautology as its
top, and its square obligation was false even though the two-premise
implication was semantically sound.  The sound implication and the
collapse were exhibited side by side as `safetyShell` and a
`rfl`-lemma showing its premise pair funnelling to `vacuous`.  Formal
conjunction retains premise lists verbatim, so the obstruction is gone:
`safetyShell` now *is* the square of `safetyBatteryFamily`, the funnel
lemma is a type error kept as a regression pin in `SuFunctorLegacy.Refute`,
and the same door admits cut's judgment-level face (`cutFamily`) and
monitor elimination (`monElimFamily`) — the three rule shapes whose
premise pairs the one-slot table could not carry.
-/

namespace SuFunctor

open PPLC

/-! ## The structural family

Formal conjunction is syntactically ordered and repetition-sensitive
(lists, so that loose composition is strictly monoidal), while its
semantics is a conjunction — commutative and idempotent.  The slack
between the two is exactly the structural entailments: projection,
reordering, duplication.  They enter as one family whose gate is
membership containment. -/

/-- Structural cells of formal conjunction: a list entails any list
whose judgments it contains — weakening, exchange, and contraction for
the conjunctive context, in one gate.  The projection rows of the
retired composition table survive here: dropping a sequent beside a
probability judgment is the two-element instance. -/
def projFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := List Judgment × List Judgment
      gate := fun i => ∀ j ∈ i.2, j ∈ i.1
      top := fun i => i.1
      bot := fun i => i.2 }
  square := fun _ hgate _ h j hj => h j (hgate j hj)

/-! ## The retired table's informative rows, as derivable cells

The Fréchet row and the conjunct-sequent row of the retired kind table,
each restated as an entailment out of a formal pair (the Boole row is
`unionBoundFamily`, beside the functor).  Their inequality content is
unchanged; only their role moved — from defining composition (where
they broke associativity and congruence) to ordinary cells (where they
are sound and composable). -/

/-- The Fréchet row as a derivable cell: two lower bounds jointly
entail the Fréchet-discounted lower bound on any event containing their
conjunction.  Sound for subprobability mass — only `μ(⊤) ≤ 1` is
consumed. -/
def frechetFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula × Formula
      gate := fun i => evt H i.2.2.1 ∩ evt H i.2.2.2.1 ⊆ evt H i.2.2.2.2
      top := fun i =>
        (Judgment.probGE i.1 i.2.2.1).comp (Judgment.probGE i.2.1 i.2.2.2.1)
      bot := fun i => [Judgment.probGE (i.1 + i.2.1 - 1) i.2.2.2.2] }
  square := by
    rintro ⟨t₁, t₂, φ₁, φ₂, tgt⟩ hgate μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    show t₁ + t₂ - 1 ≤ μ.prob (evt H tgt)
    have h₁ : t₁ ≤ μ.prob (evt H φ₁) := h.1
    have h₂ : t₂ ≤ μ.prob (evt H φ₂) := h.2
    have hf := μ.frechet_inter (evt H φ₁) (evt H φ₂)
    have hm := μ.prob_mono hgate
    linarith

/-- The conjunct-sequent row as a derivable cell: two sequents jointly
entail their conjunct sequent (violation of the conjunct is contained
in the union of the violations). -/
def seqConjFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := Sequent × Sequent
      gate := fun _ => True
      top := fun i => (Judgment.seqValid i.1).comp (Judgment.seqValid i.2)
      bot := fun i =>
        [Judgment.seqValid ⟨.and i.1.pre i.2.pre, .and i.1.post i.2.post⟩] }
  square := by
    rintro ⟨s₁, s₂⟩ - μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    show μ.prob (violation H ⟨.and s₁.pre s₂.pre, .and s₁.post s₂.post⟩) ≤ 0
    have hsub : violation H ⟨.and s₁.pre s₂.pre, .and s₁.post s₂.post⟩ ⊆
        violation H s₁ ∪ violation H s₂ := by
      rintro σ ⟨⟨hp₁, hp₂⟩, hnp⟩
      by_cases h₁ : s₁.post.holds σ.1
      · exact Or.inr ⟨hp₂, fun h₂ => hnp ⟨h₁, h₂⟩⟩
      · exact Or.inl ⟨hp₁, h₁⟩
    have h₁ : μ.prob (violation H s₁) ≤ 0 := h.1
    have h₂ : μ.prob (violation H s₂) ≤ 0 := h.2
    have hu := le_trans (μ.prob_mono hsub) (μ.prob_union_le _ _)
    have h₀ :=
      μ.prob_nonneg (violation H ⟨.and s₁.pre s₂.pre, .and s₁.post s₂.post⟩)
    linarith

/-- Cut, as a two-premise family cell: from `φ ⊢ χ` and `φ ∧ χ ⊢ ψ`,
conclude `φ ⊢ ψ`.  Under the retired one-slot composition this was the
founding counterexample — the conjunct-sequent composite of cut's
premises is strictly weaker than the pair, so cut could not factor
through loose composition and lived only inside the proof-object
calculus.  Formal conjunction retains the pair, and cut's
judgment-level face becomes an ordinary cell.  (The proof-object
calculus keeps its own internal cut; nothing moved out of it.) -/
def cutFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := Formula × Formula × Formula
      gate := fun _ => True
      top := fun i =>
        (Judgment.seqValid ⟨i.1, i.2.1⟩).comp
          (Judgment.seqValid ⟨.and i.1 i.2.1, i.2.2⟩)
      bot := fun i => [Judgment.seqValid ⟨i.1, i.2.2⟩] }
  square := by
    rintro ⟨φ, χ, ψ⟩ - μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    show μ.prob (violation H ⟨φ, ψ⟩) ≤ 0
    have hsub : violation H ⟨φ, ψ⟩ ⊆
        violation H ⟨φ, χ⟩ ∪ violation H ⟨.and φ χ, ψ⟩ := by
      rintro σ ⟨hpre, hnpost⟩
      by_cases hχ : χ.holds σ.1
      · exact Or.inr ⟨⟨hpre, hχ⟩, hnpost⟩
      · exact Or.inl ⟨hpre, hχ⟩
    have h₁ : μ.prob (violation H ⟨φ, χ⟩) ≤ 0 := h.1
    have h₂ : μ.prob (violation H ⟨.and φ χ, ψ⟩) ≤ 0 := h.2
    have hu := le_trans (μ.prob_mono hsub) (μ.prob_union_le _ _)
    have h₀ := μ.prob_nonneg (violation H ⟨φ, ψ⟩)
    linarith

/-! ## Transport families

Three kind-preserving transport families: the per-element shells
through which the quantitative rule page's tier-one rows factor at this
stratum — an event-inclusion side condition in the gate, threshold
arithmetic in the square. -/

/-- Sequent weakening along violation-event inclusion: any sequent
whose violation event shrinks (as a subset of the admissible scene)
stays valid.  Subsumes premise-strengthening and
conclusion-weakening in one gate. -/
def weakenFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := Sequent × Sequent
      gate := fun i => violation H i.2 ⊆ violation H i.1
      top := fun i => [.seqValid i.1]
      bot := fun i => [.seqValid i.2] }
  square := by
    rintro ⟨s₁, s₂⟩ hgate μ h
    rw [satConj_singleton] at h ⊢
    show μ.prob (violation H s₂) ≤ 0
    exact le_trans (μ.prob_mono hgate) h

/-- Risk-bound transport (upper kind): an upper bound transports along
event inclusion and threshold relaxation. -/
def monoLEFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula
      gate := fun i => evt H i.2.2.2 ⊆ evt H i.2.2.1 ∧ i.1 ≤ i.2.1
      top := fun i => [.probLE i.1 i.2.2.1]
      bot := fun i => [.probLE i.2.1 i.2.2.2] }
  square := by
    rintro ⟨t, t', φ, ψ⟩ ⟨hsub, hle⟩ μ h
    rw [satConj_singleton] at h ⊢
    show μ.prob (evt H ψ) ≤ t'
    exact le_trans (le_trans (μ.prob_mono hsub) h) hle

/-- Guarantee transport (lower kind): a lower bound transports along
event inclusion and threshold tightening.  The premise is lower-kind,
so the zero-model obstruction does not apply: the square is conditional
on a judgment the zero model already fails. -/
def monoGEFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula
      gate := fun i => evt H i.2.2.1 ⊆ evt H i.2.2.2 ∧ i.2.1 ≤ i.1
      top := fun i => [.probGE i.1 i.2.2.1]
      bot := fun i => [.probGE i.2.1 i.2.2.2] }
  square := by
    rintro ⟨t, t', φ, ψ⟩ ⟨hsub, hle⟩ μ h
    rw [satConj_singleton] at h ⊢
    show t' ≤ μ.prob (evt H ψ)
    exact le_trans hle (le_trans h (μ.prob_mono hsub))

/-! ## Worked single-hop instances -/

/-- The basin rule's per-element shell: certainty of an invariant
region transports to certainty of any region containing it (the
avoided set's complement, abstracted as a formula).  The invariant-scope
premise enters as a lower-kind certainty judgment, which is what lets
the shell dodge the zero-model obstruction; the deterministic-flow
content of the full rule lives at the trajectory stratum. -/
theorem basin_shell (H : Hypernet) (inv safe : Formula)
    (hsub : evt H inv ⊆ evt H safe) (μ : SubPMF (AdmVal H))
    (h : Sat H (.probGE 1 inv) μ) : Sat H (.probGE 1 safe) μ :=
  satConj_singleton.mp
    ((monoGEFamily H).square (1, 1, inv, safe) ⟨hsub, le_refl 1⟩ μ
      (satConj_singleton.mpr h))

/-- The aggregation-reduction shell: a scope-universal constraint is a
sequent judgment, and reduction along a violation-inclusion is
`weakenFamily` on the nose. -/
theorem aggReduce_shell (H : Hypernet) (s₁ s₂ : Sequent)
    (hsub : violation H s₂ ⊆ violation H s₁) (μ : SubPMF (AdmVal H))
    (h : Sat H (.seqValid s₁) μ) : Sat H (.seqValid s₂) μ :=
  satConj_singleton.mp
    ((weakenFamily H).square (s₁, s₂) hsub μ (satConj_singleton.mpr h))

/-! ## The safety battery: the premise pair, admitted verbatim -/

/-- The safety-battery shell as a two-premise implication: a risk bound
on the avoid event plus mass totality yields the guarantee, whenever
the two events cover the scene.  (Boole plus the covering hypothesis;
the supermartingale content of the full rule is what discharges the
risk-bound premise at the trajectory stratum.) -/
theorem safetyShell (H : Hypernet) (p : ℚ) (φG U : Formula)
    (hcover : ∀ σ : AdmVal H, σ ∈ evt H φG ∪ evt H U)
    (μ : SubPMF (AdmVal H))
    (hU : Sat H (.probLE (1 - p) U) μ) (hmass : Sat H (.probGE 1 .tt) μ) :
    Sat H (.probGE p φG) μ := by
  show p ≤ μ.prob (evt H φG)
  have hmass' : (1 : ℚ) ≤ μ.prob (evt H .tt) := hmass
  have hU' : μ.prob (evt H U) ≤ 1 - p := hU
  have hcov : evt H .tt ⊆ evt H φG ∪ evt H U := fun σ _ => hcover σ
  have h₁ : μ.prob (evt H .tt) ≤ μ.prob (evt H φG ∪ evt H U) :=
    μ.prob_mono hcov
  have h₂ : μ.prob (evt H φG ∪ evt H U) ≤
      μ.prob (evt H φG) + μ.prob (evt H U) :=
    μ.prob_union_le _ _
  linarith

/-- The safety battery as a rule family: the mixed-kind premise pair —
a risk bound beside a mass premise — stated verbatim as the top list.
Under the retired composition table this entry was impossible: the
mixed row collapsed the pair to the vacuous judgment, presenting `⊤` as
the rule's top even though the two-premise implication was sound (the
funnel is now a type error, pinned in `SuFunctorLegacy.Refute`).  Formal
conjunction retains the pair, and `safetyShell` is the square,
verbatim.  The mass premise is also what dodges the zero-model
obstruction: the zero model fails the top, so the square constrains it
vacuously. -/
def safetyBatteryFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × Formula × Formula
      gate := fun i => ∀ σ : AdmVal H, σ ∈ evt H i.2.1 ∪ evt H i.2.2
      top := fun i =>
        (Judgment.probLE (1 - i.1) i.2.2).comp (Judgment.probGE 1 .tt)
      bot := fun i => [Judgment.probGE i.1 i.2.1] }
  square := by
    rintro ⟨p, φG, U⟩ hcover μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    exact safetyShell H p φG U hcover μ h.1 h.2

/-! ## Monitor elimination: the smoke test for pair retention

The monitor-elimination rule derives a probability judgment about a
system from an expectation judgment about the system composed with a
deterministic monitor, under a correspondence side condition
identifying the monitor's verdict with the specification's
satisfaction.  Its full form lives at the wiring stratum — premise and
conclusion sit over different base objects, related by a projection
tight arrow — which is the named successor's territory.  What belongs
to this stratum is the *premise shape*: a mixed-kind list, a verdict
bound beside an escape-risk bound, which the retired composition table
would have collapsed to the vacuous judgment and which formal
conjunction states verbatim.

`monElimFamily` is the single-scene shadow: the monitor's verdict event
and the specification's event live over one scene, the correspondence
enters as the gate (off the escape event, a monitor verdict implies
satisfaction), and the square is exact escape-corrected transport:
verdict probability at least `p` and escape probability at most `β`
yield satisfaction probability at least `p − β`.  At `β = 0` — a sound
monitor — this degenerates to guarantee transport (`monElim_alias`),
which is the alias rung: the monitor is the identity and the
correspondence is definitional. -/

/-- Escape-corrected transport: the monitor-elimination shell at the
per-element stratum.  A verdict bound, an escape bound, and the
correspondence `verdict \ escape ⊆ spec` yield the guarantee, exactly
discounted by the escape mass. -/
theorem monElimShell (H : Hypernet) (p β : ℚ) (out esc φ : Formula)
    (hcorr : evt H out \ evt H esc ⊆ evt H φ) (μ : SubPMF (AdmVal H))
    (hout : Sat H (.probGE p out) μ) (hesc : Sat H (.probLE β esc) μ) :
    Sat H (.probGE (p - β) φ) μ := by
  show p - β ≤ μ.prob (evt H φ)
  have hout' : p ≤ μ.prob (evt H out) := hout
  have hesc' : μ.prob (evt H esc) ≤ β := hesc
  have hsplit : evt H out ⊆ (evt H out \ evt H esc) ∪ evt H esc := by
    intro σ hσ
    by_cases he : σ ∈ evt H esc
    · exact Or.inr he
    · exact Or.inl ⟨hσ, he⟩
  have h₁ : μ.prob (evt H out) ≤
      μ.prob (evt H out \ evt H esc) + μ.prob (evt H esc) :=
    le_trans (μ.prob_mono hsplit) (μ.prob_union_le _ _)
  have h₂ : μ.prob (evt H out \ evt H esc) ≤ μ.prob (evt H φ) :=
    μ.prob_mono hcorr
  linarith

/-- Monitor elimination as a rule family: the mixed-kind premise pair
`[verdict ≥ p, escape ≤ β]` stated verbatim, the correspondence as the
gate, escape-corrected transport as the square. -/
def monElimFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula × Formula
      gate := fun i => evt H i.2.2.1 \ evt H i.2.2.2.1 ⊆ evt H i.2.2.2.2
      top := fun i =>
        (Judgment.probGE i.1 i.2.2.1).comp (Judgment.probLE i.2.1 i.2.2.2.1)
      bot := fun i => [Judgment.probGE (i.1 - i.2.1) i.2.2.2.2] }
  square := by
    rintro ⟨p, β, out, esc, φ⟩ hcorr μ h
    rw [satConj_pair] at h
    rw [satConj_singleton]
    exact monElimShell H p β out esc φ hcorr μ h.1 h.2

/-- The alias rung of monitor elimination: a sound monitor (no escape
event at all) transports its verdict probability to the specification
exactly — guarantee transport recovered as the `β = 0` face.  In family
form this is `monoGEFamily` at equal thresholds. -/
theorem monElim_alias (H : Hypernet) (p : ℚ) (out φ : Formula)
    (hcorr : evt H out ⊆ evt H φ) (μ : SubPMF (AdmVal H))
    (hout : Sat H (.probGE p out) μ) : Sat H (.probGE p φ) μ := by
  show p ≤ μ.prob (evt H φ)
  exact le_trans hout (μ.prob_mono hcorr)

end SuFunctor
