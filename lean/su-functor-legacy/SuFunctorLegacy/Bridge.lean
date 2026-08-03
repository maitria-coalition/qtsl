/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the graded reading over `SubPMF` spec penalties, the
quantifier collapse, and the batch soundness lifts (`gradedAnchor`,
`gradedSound_ofProof`).  The successor carrier's judgment is natively
graded (`SuFunctor.Universe.Judgment`).

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Functor
import QtslAux.Imprecise.MarginalCompat

/-! # The bridge: violation transport, spec penalties, and the quantifier collapse

Three presentations of one soundness content, and the equivalences
between them:

1. **The valuation level**: violation transport — the conclusion's
   violation event is contained in the union of the premises' violation
   events (`ViolationTransport`).
2. **The model level**: the per-element cell — every subprobability
   model satisfying the premise judgments satisfies the conclusion (the
   shape of `SemRuleFamily.square`).
3. **The penalty level**: the graded obligation — every penalty
   functional dominating the premises' spec penalties dominates the
   conclusion's (`specPenalty`, heights in `ENNRat`).

`gradedCellConj_iff_cell` collapses 3 onto 2 for arbitrary judgment
lists: the join of the premise spec penalties is itself a penalty
functional, so the universally quantified obligation is decided at that
join.  (The join is the indicator of an intersection of satisfaction
sets, each cut out by weak inequalities in linear functionals of the
mass, so it is convex and lower semicontinuous; the collapse therefore
also holds verbatim with the quantifier restricted to any class of
functionals containing these indicators, such as the convex lower
semicontinuous ones.)  `seqCell_iff_violationTransport` identifies 2
with 1 for sequent-kind judgments: downward, monotonicity and finite
subadditivity of subprobability mass; upward, point masses.  For
threshold kinds (`probGE`/`probLE`) the second equivalence is
deliberately not asserted: the zero model and its submass kin
participate in 2 but escape any point-mass analysis (see the zero-model
obstruction in `SuFunctorLegacy.Squares`).

The batch consequences close the file: every square-carrying rule
family lifts to the penalty level (`SemRuleFamily.gradedSquare`), every
derivation lifts (`JDeriv.gradedSem`), the certificate calculus enters
as a single zero-premise family whose gate is derivability
(`calculusFamily`), and a derivable sequent's judgment holds for every
system refining the admissible scene at every height (`gradedAnchor`,
`gradedSound_ofProof`) — the soundness theorem of the calculus read in
the graded order, where it is the transitivity
`specPenalty ≤ scenePenalty ≤ σ`.
-/

namespace SuFunctor

open PPLC Qtsl.Imprecise

/-! ## Subprobability mass: two more instruments

Point masses off an event, and finite subadditivity over a list of
events — the two facts the valuation-level bridge consumes beside the
stock of `SuFunctor.Target`. -/

universe u

variable {V : Type u}

theorem SubPMF.dirac_prob_of_not_mem {v : V} {S : Set V} (h : v ∉ S) :
    (SubPMF.dirac v).prob S = 0 := by
  classical
  unfold SubPMF.prob SubPMF.dirac
  rw [Finsupp.support_single_ne_zero v one_ne_zero]
  simp [h]

/-- Finite subadditivity of subprobability mass over a list of events. -/
theorem SubPMF.prob_listUnion_le {α : Type*} (μ : SubPMF V) (l : List α)
    (f : α → Set V) :
    μ.prob (⋃ a ∈ l, f a) ≤ (l.map fun a => μ.prob (f a)).sum := by
  induction l with
  | nil =>
      have h : (⋃ a ∈ ([] : List α), f a) = (∅ : Set V) := by
        ext x; simp
      rw [h]
      simp
  | cons b l ih =>
      have hcons : (⋃ a ∈ b :: l, f a) = f b ∪ ⋃ a ∈ l, f a := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, List.mem_cons]
        constructor
        · rintro ⟨a, rfl | ha, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨a, ha, hx⟩
        · rintro (hx | ⟨a, ha, hx⟩)
          · exact ⟨b, Or.inl rfl, hx⟩
          · exact ⟨a, Or.inr ha, hx⟩
      rw [hcons, List.map_cons, List.sum_cons]
      exact le_trans (μ.prob_union_le _ _) (add_le_add le_rfl ih)

/-! ## Sequent kinds: the valuation-level bridge -/

/-- Violation transport for a rule with premise sequents `ps` and
conclusion sequent `c`: over the admissible scene, every valuation
violating the conclusion violates some premise.  This is the property a
soundness proof establishes when it introduces a single valuation and
applies every premise hypothesis to it. -/
def ViolationTransport (H : Hypernet) (ps : List Sequent) (c : Sequent) :
    Prop :=
  violation H c ⊆ ⋃ p ∈ ps, violation H p

/-- **The valuation-level bridge.**  For sequent-kind judgments the
per-element cell is equivalent to violation transport.  Downward:
monotonicity and finite subadditivity — a model giving zero weight to
every premise violation gives zero weight to the conclusion violation.
Upward: a valuation violating the conclusion but no premise carries a
point mass refuting the cell. -/
theorem seqCell_iff_violationTransport (H : Hypernet) (ps : List Sequent)
    (c : Sequent) :
    (∀ μ : SubPMF (AdmVal H),
        SatConj H (ps.map Judgment.seqValid) μ →
          Sat H (Judgment.seqValid c) μ) ↔
      ViolationTransport H ps c := by
  constructor
  · intro h v hv
    by_contra hnot
    have hall : ∀ p ∈ ps, v ∉ violation H p := by
      intro p hp hvp
      exact hnot (Set.mem_iUnion₂.mpr ⟨p, hp, hvp⟩)
    have hpre : SatConj H (ps.map Judgment.seqValid) (SubPMF.dirac v) := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      show (SubPMF.dirac v).prob (violation H p) ≤ 0
      rw [SubPMF.dirac_prob_of_not_mem (hall p hp)]
    have hc : (SubPMF.dirac v).prob (violation H c) ≤ 0 := h _ hpre
    rw [SubPMF.dirac_prob_of_mem hv] at hc
    linarith
  · intro h μ hpre
    show μ.prob (violation H c) ≤ 0
    have h₁ : μ.prob (violation H c) ≤ μ.prob (⋃ p ∈ ps, violation H p) :=
      μ.prob_mono h
    have h₂ := μ.prob_listUnion_le ps (violation H)
    have h₃ : (ps.map fun p => μ.prob (violation H p)).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hs : Sat H (Judgment.seqValid p) μ :=
        hpre _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
      exact le_antisymm hs (μ.prob_nonneg _)
    rw [h₃] at h₂
    exact le_trans h₁ h₂

/-! ## The penalty level and the quantifier collapse -/

/-- A penalty functional on subprobability models of the admissible
scene: the carrier of the graded satisfaction order at this stratum.
Heights are extended nonnegative rationals; specs and systems are both
points of the pointwise function order, and a system `σ` satisfies a
spec `φ` when `φ ≤ σ`. -/
abbrev Penalty (H : Hypernet) : Type :=
  SubPMF (AdmVal H) → ENNRat

open Classical in
/-- The spec penalty of a judgment: the `{0, ⊤}`-valued indicator of
its satisfaction set.  A penalty functional `σ` with
`specPenalty H j ≤ σ` is a system satisfying `j` in the graded order;
the wall-valued (allowed-or-forbidden) judgment is the restriction of
that order to these indicators. -/
noncomputable def specPenalty (H : Hypernet) (j : Judgment) : Penalty H :=
  fun μ => if Sat H j μ then 0 else ⊤

open Classical in
/-- The spec penalty of a formal conjunction: the indicator of the
joint satisfaction set — the join of the members' spec penalties
(`specPenaltyConj_le_iff`). -/
noncomputable def specPenaltyConj (H : Hypernet) (l : List Judgment) :
    Penalty H :=
  fun μ => if SatConj H l μ then 0 else ⊤

theorem specPenalty_of_sat {H : Hypernet} {j : Judgment}
    {μ : SubPMF (AdmVal H)} (h : Sat H j μ) : specPenalty H j μ = 0 := by
  simp [specPenalty, h]

theorem specPenalty_of_not_sat {H : Hypernet} {j : Judgment}
    {μ : SubPMF (AdmVal H)} (h : ¬ Sat H j μ) : specPenalty H j μ = ⊤ := by
  simp [specPenalty, h]

theorem specPenaltyConj_of_sat {H : Hypernet} {l : List Judgment}
    {μ : SubPMF (AdmVal H)} (h : SatConj H l μ) :
    specPenaltyConj H l μ = 0 := by
  simp [specPenaltyConj, h]

theorem specPenaltyConj_of_not_sat {H : Hypernet} {l : List Judgment}
    {μ : SubPMF (AdmVal H)} (h : ¬ SatConj H l μ) :
    specPenaltyConj H l μ = ⊤ := by
  simp [specPenaltyConj, h]

@[simp] theorem specPenaltyConj_singleton (H : Hypernet) (j : Judgment) :
    specPenaltyConj H [j] = specPenalty H j := by
  funext μ
  by_cases h : Sat H j μ
  · rw [specPenaltyConj_of_sat (satConj_singleton.mpr h),
      specPenalty_of_sat h]
  · rw [specPenaltyConj_of_not_sat (fun hc => h (satConj_singleton.mp hc)),
      specPenalty_of_not_sat h]

/-- The conjunction's spec penalty dominates each member's. -/
theorem specPenalty_le_specPenaltyConj {H : Hypernet} {l : List Judgment}
    {j : Judgment} (hj : j ∈ l) :
    specPenalty H j ≤ specPenaltyConj H l := by
  intro μ
  by_cases hc : SatConj H l μ
  · rw [specPenalty_of_sat (hc j hj)]
    exact zero_le
  · rw [specPenaltyConj_of_not_sat hc]
    exact le_top

/-- `specPenaltyConj` is the join: a penalty functional dominates the
conjunction's spec penalty iff it dominates every member's. -/
theorem specPenaltyConj_le_iff {H : Hypernet} {l : List Judgment}
    {σ : Penalty H} :
    specPenaltyConj H l ≤ σ ↔ ∀ j ∈ l, specPenalty H j ≤ σ := by
  constructor
  · intro h j hj
    exact le_trans (specPenalty_le_specPenaltyConj hj) h
  · intro h μ
    by_cases hc : SatConj H l μ
    · rw [specPenaltyConj_of_sat hc]
      exact zero_le
    · obtain ⟨j, hj, hns⟩ : ∃ j ∈ l, ¬ Sat H j μ := by
        by_contra hall
        exact hc fun j hj =>
          Classical.byContradiction fun hns => hall ⟨j, hj, hns⟩
      have hσ := h j hj μ
      rw [specPenalty_of_not_sat hns] at hσ
      rw [specPenaltyConj_of_not_sat hc]
      exact hσ

/-- **The quantifier collapse.**  The graded obligation between two
formal conjunctions — every penalty functional dominating the first
dominates the second — is equivalent to the per-element cell between
them: the universally quantified obligation is decided at the join of
the premise spec penalties, which is itself a penalty functional. -/
theorem gradedCellConj_iff_cell (H : Hypernet) (l₁ l₂ : List Judgment) :
    (∀ σ : Penalty H,
        specPenaltyConj H l₁ ≤ σ → specPenaltyConj H l₂ ≤ σ) ↔
      ∀ μ : SubPMF (AdmVal H), SatConj H l₁ μ → SatConj H l₂ μ := by
  constructor
  · intro h μ h₁
    by_contra hns
    have h₂ := h (specPenaltyConj H l₁) le_rfl μ
    rw [specPenaltyConj_of_sat h₁, specPenaltyConj_of_not_sat hns] at h₂
    exact absurd h₂ (by simp)
  · intro h σ hσ μ
    by_cases hs : SatConj H l₂ μ
    · rw [specPenaltyConj_of_sat hs]
      exact zero_le
    · rw [specPenaltyConj_of_not_sat hs]
      have h₁ : ¬ SatConj H l₁ μ := fun hc => hs (h μ hc)
      have hσμ := hσ μ
      rw [specPenaltyConj_of_not_sat h₁] at hσμ
      exact hσμ

/-- The graded obligation of a rule — premises `ps`, conclusion `c`,
heights everywhere — collapsed to the per-element cell. -/
theorem gradedObligation_iff_cell (H : Hypernet) (ps : List Judgment)
    (c : Judgment) :
    (∀ σ : Penalty H,
        (∀ j ∈ ps, specPenalty H j ≤ σ) → specPenalty H c ≤ σ) ↔
      ∀ μ : SubPMF (AdmVal H), SatConj H ps μ → Sat H c μ := by
  constructor
  · intro h μ hμ
    have hcell := (gradedCellConj_iff_cell H ps [c]).mp
      (fun σ hσ => by
        rw [specPenaltyConj_singleton]
        exact h σ (specPenaltyConj_le_iff.mp hσ)) μ hμ
    exact satConj_singleton.mp hcell
  · intro h σ hσ
    have hcell := (gradedCellConj_iff_cell H ps [c]).mpr
      (fun μ hμ => satConj_singleton.mpr (h μ hμ)) σ
      (specPenaltyConj_le_iff.mpr hσ)
    rw [specPenaltyConj_singleton] at hcell
    exact hcell

/-- **The full bridge for sequent-kind rules**: the graded obligation
at every height is equivalent to violation transport at the valuation
level. -/
theorem gradedObligation_iff_violationTransport (H : Hypernet)
    (ps : List Sequent) (c : Sequent) :
    (∀ σ : Penalty H,
        (∀ j ∈ ps.map Judgment.seqValid, specPenalty H j ≤ σ) →
          specPenalty H (Judgment.seqValid c) ≤ σ) ↔
      ViolationTransport H ps c :=
  (gradedObligation_iff_cell H (ps.map Judgment.seqValid)
      (Judgment.seqValid c)).trans
    (seqCell_iff_violationTransport H ps c)

/-! ## Batch consequences -/

/-- Every square-carrying rule family lifts to the penalty level: each
of its cells holds at every height. -/
theorem SemRuleFamily.gradedSquare {H : Hypernet} (F : SemRuleFamily H)
    (t : F.rules.Tag) (ht : F.rules.gate t) :
    ∀ σ : Penalty H,
      specPenaltyConj H (F.rules.top t) ≤ σ →
        specPenaltyConj H (F.rules.bot t) ≤ σ :=
  (gradedCellConj_iff_cell H _ _).mpr (F.square t ht)

/-- Every derivation lifts to the penalty level. -/
theorem JDeriv.gradedSem {H : Hypernet} {F : RuleFamily H}
    (sq : ∀ t, F.gate t →
      ∀ μ, SatConj H (F.top t) μ → SatConj H (F.bot t) μ)
    {l l' : List Judgment} (d : JDeriv H F l l') :
    ∀ σ : Penalty H, specPenaltyConj H l ≤ σ → specPenaltyConj H l' ≤ σ :=
  (gradedCellConj_iff_cell H l l').mpr (d.sem sq)

/-- The certificate calculus as a single semantic rule family: every
derivable sequent enters the graded layer as a zero-premise cell, the
gate being derivability itself.  The per-rule content lives in the
structural recursion of `ProofObject.sound` (one soundness lemma per
rule of the calculus); no rule owes a separate graded square, because a
derivable conclusion's satisfaction set is the whole scene. -/
noncomputable def calculusFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := Sequent
      gate := fun s => Nonempty (ProofObject H s)
      top := fun _ => []
      bot := fun s => [Judgment.seqValid s] }
  square := fun _ hs μ _ => satConj_singleton.mpr (sat_ofProof hs.some μ)

/-- The scene penalty at this stratum.  The carrier is the admissible
scene itself — models are subprobability mass on admissible
valuations — so the scene's indicator penalty is zero. -/
def scenePenalty (H : Hypernet) : Penalty H := 0

/-- Every penalty functional refines the scene at this stratum. -/
theorem scenePenalty_le {H : Hypernet} (σ : Penalty H) :
    scenePenalty H ≤ σ :=
  fun _ => zero_le

/-- A derivable sequent's judgment is scene-implied: its spec penalty
is dominated by the scene penalty. -/
theorem specPenalty_ofProof_le_scenePenalty {H : Hypernet} {seq : Sequent}
    (po : ProofObject H seq) :
    specPenalty H (Judgment.ofSequent seq) ≤ scenePenalty H := by
  intro μ
  rw [specPenalty_of_sat (sat_ofProof po μ)]
  exact zero_le

/-- **The anchor, graded.**  A derivable sequent's judgment holds for
every system refining the admissible scene, at every height: the
transitivity `specPenalty ≤ scenePenalty ≤ σ`. -/
theorem gradedAnchor {H : Hypernet} {seq : Sequent}
    (po : ProofObject H seq) (σ : Penalty H)
    (hσ : scenePenalty H ≤ σ) :
    specPenalty H (Judgment.ofSequent seq) ≤ σ :=
  le_trans (specPenalty_ofProof_le_scenePenalty po) hσ

/-- Batch graded soundness of the certificate calculus: a derivable
sequent's spec penalty is dominated by *every* penalty functional —
the judgment holds at every height, for every system. -/
theorem gradedSound_ofProof {H : Hypernet} {seq : Sequent}
    (po : ProofObject H seq) (σ : Penalty H) :
    specPenalty H (Judgment.ofSequent seq) ≤ σ :=
  gradedAnchor po σ (scenePenalty_le σ)

end SuFunctor
