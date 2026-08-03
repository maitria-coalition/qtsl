import SuFunctor.Universe.Closure

/-! # The graded judgment: satisfaction is the pointwise order

The satisfaction judgment of the semantic universe:

> a system `σ` satisfies a specification `φ` iff `σ` dominates `φ`
> pointwise — the system is at least as incompatible with every
> distribution as the specification demands.

`Sat σ φ` is *defined* as `φ ≤ σ`; entailment between specifications,
satisfaction, and the universe's order are one relation.  The shipped
crisp judgment is the restriction of this order to wall-valued
specifications, where it is containment (`sat_wall_wall_iff`) — the
compatibility theorem, stated as a restriction and not an equivalence:
off the walls the graded order distinguishes landscapes that every
crisp verdict conflates.

The lattice facts here are the judgment-level faces of the closure
table:

* conjunction is the categorical **product** in the entailment order,
  computed as pointwise max — `sat_sup_iff` is its universal property
  (the real-stratum face of the exact-rational
  `SuFunctor.specPenaltyConj_le_iff`);
* disjunction is the categorical **coproduct**, computed as pointwise
  min *exactly* — `entails_inf_iff` is its universal property, and
  context-free disjunction elimination is that property verbatim;
* the disjunction property fails, witnessed: a hedging system can
  satisfy a disjunction while satisfying neither disjunct
  (`exists_sat_inf_not_sat`) — models of a disjunction may hedge, and
  case analysis is exactly the inference that pretends they cannot;
* contextual disjunction elimination is the distributive law, which
  holds **with pointwise equality** in the universe
  (`conj_disj_distrib`) because heights form a chain; in the convex
  certification chart the same law fails (three interval walls realize
  the diamond configuration) — the refutation is chart-relative, the
  universe validates the rule;
* the graded judgment is equivalently the family of tolerance-indexed
  slice containments (`sat_iff_sublevel_subset`) — the bridge between
  the order and its certificate-level presentation, where each slice
  claim is a crisp containment about a sublevel set.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-- The graded satisfaction judgment: `σ` satisfies `φ` iff `σ`
dominates `φ` pointwise.  The judgment, spec-to-spec entailment, and
the universe's order coincide by definition. -/
def Sat (σ φ : Penalty V) : Prop := φ ≤ σ

theorem sat_def {σ φ : Penalty V} : Sat σ φ ↔ φ ≤ σ := Iff.rfl

@[simp] theorem sat_self (σ : Penalty V) : Sat σ σ := le_rfl

/-- Weakening on the specification side: a satisfied spec's every
consequence is satisfied. -/
theorem Sat.of_spec_le {σ φ ψ : Penalty V} (h : Sat σ φ) (hψ : ψ ≤ φ) :
    Sat σ ψ := hψ.trans h

/-- Monotonicity on the system side: a more incompatible system
satisfies everything a less incompatible one does. -/
theorem Sat.of_le_sys {σ σ' φ : Penalty V} (h : Sat σ φ) (hσ : σ ≤ σ') :
    Sat σ' φ := h.trans hσ

/-- The vacuous specification (`0`, the wall of the whole carrier) is
satisfied by every system. -/
@[simp] theorem sat_zero (σ : Penalty V) : Sat σ 0 := fun _ => zero_le

/-- The inconsistent specification (`⊤`, the empty wall) is satisfied
only by the inconsistent system. -/
theorem sat_top_iff {σ : Penalty V} : Sat σ ⊤ ↔ σ = ⊤ :=
  top_le_iff

/-! ## The crisp restriction -/

/-- **The compatibility theorem.**  On walls, the graded judgment is
containment of the permitted sets: the shipped crisp judgment is the
restriction of the order to wall-valued data.  (Restriction, not
equivalence: off the walls the order compares heights that no crisp
verdict sees.) -/
theorem sat_wall_wall_iff {S C : Set (BelState V)} :
    Sat (wall S) (wall C) ↔ S ⊆ C :=
  wall_le_wall_iff

/-- Against a wall spec, satisfaction says exactly that the system's
finite-penalty region is permitted. -/
theorem sat_wall_iff {σ : Penalty V} {C : Set (BelState V)} :
    Sat σ (wall C) ↔ ∀ μ, σ μ ≠ ⊤ → μ ∈ C := by
  rw [Sat, wall_le_iff]
  exact ⟨fun h μ hμ => by_contra fun hC => hμ (h μ hC),
    fun h μ hμ => by_contra fun hne => hμ (h μ hne)⟩

/-! ## Conjunction: the product -/

/-- **Conjunction is pointwise max, and max is the product.**  The
universal property of the categorical product in the entailment order:
a system satisfies the conjunction iff it satisfies both conjuncts.
(The exact-rational stratum ships the same fact for finite families of
judgment walls as `SuFunctor.specPenaltyConj_le_iff`.) -/
theorem sat_sup_iff {σ φ ψ : Penalty V} :
    Sat σ (φ ⊔ ψ) ↔ Sat σ φ ∧ Sat σ ψ :=
  sup_le_iff

/-- Arbitrary conjunctions: a system satisfies the supremum of a family
iff it satisfies every member. -/
theorem sat_iSup_iff {ι : Sort*} {σ : Penalty V} {f : ι → Penalty V} :
    Sat σ (⨆ i, f i) ↔ ∀ i, Sat σ (f i) :=
  iSup_le_iff

/-! ## Disjunction: the coproduct, exact -/

/-- Disjunction introduction, left: `φ` entails `φ ∨ ψ`.  (The coproduct
injection.) -/
theorem sat_inf_of_left {σ φ ψ : Penalty V} (h : Sat σ φ) : Sat σ (φ ⊓ ψ) :=
  h.of_spec_le inf_le_left

/-- Disjunction introduction, right. -/
theorem sat_inf_of_right {σ φ ψ : Penalty V} (h : Sat σ ψ) : Sat σ (φ ⊓ ψ) :=
  h.of_spec_le inf_le_right

/-- **Disjunction is pointwise min, and min is the coproduct.**  The
universal property, which is context-free disjunction elimination
verbatim, sound and complete: the disjunction entails `ρ` iff both
disjuncts do.  No envelope, no hull: the pointwise minimum of two
citizens is a citizen (`lsc_inf`), so the coproduct in the universe is
computed exactly. -/
theorem entails_inf_iff {φ ψ ρ : Penalty V} :
    ρ ≤ φ ⊓ ψ ↔ ρ ≤ φ ∧ ρ ≤ ψ :=
  le_inf_iff

/-- **The disjunction property fails, witnessed by a hedging system.**
There are a system and two specifications with the system satisfying
the disjunction and neither disjunct: over `V = Bool`, take the two
point-mass walls and the system committed exactly to their union — it
hedges across the disjuncts.  Models of a disjunction may hedge; the
coproduct itself is such a model whenever the disjuncts are
incomparable. -/
theorem exists_sat_inf_not_sat :
    ∃ σ φ ψ : Penalty Bool, Sat σ (φ ⊓ ψ) ∧ ¬ Sat σ φ ∧ ¬ Sat σ ψ := by
  classical
  refine ⟨wall {BelState.dirac true} ⊓ wall {BelState.dirac false},
    wall {BelState.dirac true}, wall {BelState.dirac false},
    sat_self _, ?_, ?_⟩
  · -- the hedger does not satisfy the left disjunct: at `dirac false`
    -- the left wall is `⊤` but the min is `0`.
    intro h
    have hne : (BelState.dirac false : BelState Bool) ∉
        ({BelState.dirac true} : Set (BelState Bool)) := by
      intro hmem
      have h1 := congrArg (fun μ : BelState Bool => (μ : Bool → ℝ) true)
        (Set.mem_singleton_iff.mp hmem)
      rw [BelState.dirac_apply_of_ne (by decide : true ≠ false),
        BelState.dirac_apply_same] at h1
      norm_num at h1
    have hle := h (BelState.dirac false)
    rw [Pi.inf_apply, wall_apply_of_not_mem hne,
      wall_apply_of_mem (Set.mem_singleton _)] at hle
    simp at hle
  · intro h
    have hne : (BelState.dirac true : BelState Bool) ∉
        ({BelState.dirac false} : Set (BelState Bool)) := by
      intro hmem
      have h1 := congrArg (fun μ : BelState Bool => (μ : Bool → ℝ) true)
        (Set.mem_singleton_iff.mp hmem)
      rw [BelState.dirac_apply_same,
        BelState.dirac_apply_of_ne (by decide : true ≠ false)] at h1
      norm_num at h1
    have hle := h (BelState.dirac true)
    rw [Pi.inf_apply, wall_apply_of_not_mem hne,
      wall_apply_of_mem (Set.mem_singleton _)] at hle
    simp at hle

/-! ## The slice bridge -/

/-- **The bridge theorem.**  The graded judgment is equivalently the
∀-family of tolerance-indexed slice containments: `σ` dominates `φ` iff
at every tolerance `s`, the system's `s`-slice is contained in the
spec's `s`-slice.  Each slice claim is a crisp containment about
sublevel sets — the certificate-level presentation of the graded
judgment, with the tolerance as one added field. -/
theorem sat_iff_sublevel_subset {σ φ : Penalty V} :
    Sat σ φ ↔ ∀ s : ℝ≥0∞,
      {μ : BelState V | σ μ ≤ s} ⊆ {μ : BelState V | φ μ ≤ s} := by
  constructor
  · intro h s μ hμ
    exact le_trans (h μ) hμ
  · intro h μ
    exact h (σ μ) (le_refl (σ μ) : μ ∈ {ν : BelState V | σ ν ≤ σ μ})

/-! ## Chart-invariance of wall obligations -/

/-- **The quantifier collapse, chart-parametrically.**  For any class
`P` of penalties containing the joined premise `ψ`, the universally
quantified graded obligation "every `P`-system dominating `ψ` dominates
`χ`" collapses to the single order fact `χ ≤ ψ` — the obligation is
decided at the join.  (The exact-rational stratum's
`SuFunctor.gradedCellConj_iff_cell` is this argument at the indicator
join; here it is stated for an arbitrary chart class.) -/
theorem gradedObligation_iff_le {P : Penalty V → Prop} {ψ χ : Penalty V}
    (hψ : P ψ) :
    (∀ σ, P σ → Sat σ ψ → Sat σ χ) ↔ χ ≤ ψ := by
  constructor
  · intro h
    exact h ψ hψ (sat_self ψ)
  · intro h σ _ hσ
    exact hσ.of_spec_le h

/-- **Tent-invariance of wall-denoting obligations.**  For rules whose
premises and conclusion denote walls, the graded obligation over *any*
chart class containing the premise wall — the convex chart, the whole
universe, anything between — is the same set-containment fact.
Consequently a change of universe (convex to lsc) changes no such
rule's obligation: pointwise soundness proofs transfer verbatim, and
chart-sensitivity can enter a rule only through connectives whose
denotation is chart-indexed. -/
theorem gradedObligation_wall_iff {P : Penalty V → Prop}
    {C D : Set (BelState V)} (hC : P (wall C)) :
    (∀ σ, P σ → Sat σ (wall C) → Sat σ (wall D)) ↔ C ⊆ D := by
  rw [gradedObligation_iff_le hC]
  exact wall_le_wall_iff

/-! ## Distributivity: contextual disjunction elimination -/

/-- **The distributive law, with pointwise equality.**  Conjunction
distributes over disjunction in the universe because heights form a
chain: `γ ∧ (φ ∨ ψ) = (γ ∧ φ) ∨ (γ ∧ ψ)` exactly.  This is the
semantic validity of *contextual* disjunction elimination: from
`γ ∧ φ ⊢ ρ` and `γ ∧ ψ ⊢ ρ` infer `γ ∧ (φ ∨ ψ) ⊢ ρ`.

The same law fails in the convex certification chart — hulls of unions
forget the case boundary, and three interval walls realize the diamond
(`M₃`) configuration — so a judge that renders disjunctions by their
convex shadows loses contextual case analysis while the universe keeps
it.  The rule's underivability from the crisp core is a fact about the
chart; its validity is a fact about the universe. -/
theorem conj_disj_distrib (γ φ ψ : Penalty V) :
    γ ⊔ (φ ⊓ ψ) = (γ ⊔ φ) ⊓ (γ ⊔ ψ) :=
  sup_inf_left γ φ ψ

end SuFunctor.Universe
