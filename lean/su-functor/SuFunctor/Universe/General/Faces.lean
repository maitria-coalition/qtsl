import SuFunctor.Universe.General.CheckerAnchor

/-! # The connective order faces at the general carrier

The judgment-level faces of the connectives — the finite storey's
`SuFunctor.Universe.Judgment`, restated over the general subprobability
carrier and its penalty vocabulary `StatePenalty X`
(`SuFunctor.Universe.General.CheckerAnchor`).  Everything here is an
order fact about `[0,∞]`-valued functionals plus one topological fact
about walls; nothing consumes finiteness, compactness, or a metric —
the standing hypotheses of the general carrier are the only ones.

* conjunction is the categorical **product** in the entailment order,
  computed as pointwise max — `sat_sup_iff` is its universal property
  (`sat_iSup_iff` the arbitrary-family form);
* disjunction is the categorical **coproduct**, computed as pointwise
  min *exactly* — `entails_inf_iff` is its universal property, and
  context-free disjunction elimination is that property verbatim;
* the disjunction property fails, witnessed: `exists_sat_inf_not_sat`
  exhibits a hedging system over **every nonempty carrier** — an
  upgrade over the finite storey, whose witness lived on `V = Bool`.
  The two states the witness separates are the bottom state and the
  unit-mass Dirac at any point; mass tells them apart, so no
  distinguished measurable structure and no decidability enter;
* contextual disjunction elimination is the distributive law, which
  holds with pointwise equality because heights form a chain
  (`conj_disj_distrib`);
* on walls, conjunction is intersection and disjunction is union,
  verbatim (`wall_sup_wall`, `wall_inf_wall`), the wall order is
  containment (`wall_le_wall_iff`), and walls are citizens exactly on
  closed sets (`lowerSemicontinuous_wall_iff`) — closed, *not*
  convex-closed, at full carrier generality;
* wall obligations are chart-invariant (`gradedObligation_iff_le`,
  `gradedObligation_wall_iff`).
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-! ## Order faces of the judgment -/

/-- Weakening on the specification side: a satisfied spec's every
consequence is satisfied. -/
theorem Sat.of_spec_le {σ φ ψ : StatePenalty X} (h : Sat σ φ) (hψ : ψ ≤ φ) :
    Sat σ ψ := hψ.trans h

/-- Monotonicity on the system side: a more incompatible system
satisfies everything a less incompatible one does. -/
theorem Sat.of_le_sys {σ σ' φ : StatePenalty X} (h : Sat σ φ) (hσ : σ ≤ σ') :
    Sat σ' φ := h.trans hσ

/-- The vacuous specification (`0`, the wall of the whole carrier) is
satisfied by every system. -/
@[simp] theorem sat_zero (σ : StatePenalty X) : Sat σ 0 := fun _ => zero_le

/-- The inconsistent specification (`⊤`, the empty wall) is satisfied
only by the inconsistent system. -/
theorem sat_top_iff {σ : StatePenalty X} : Sat σ ⊤ ↔ σ = ⊤ :=
  top_le_iff

/-! ## Conjunction: the product -/

/-- **Conjunction is pointwise max, and max is the product.**  The
universal property of the categorical product in the entailment order,
over the general carrier: a system satisfies the conjunction iff it
satisfies both conjuncts. -/
theorem sat_sup_iff {σ φ ψ : StatePenalty X} :
    Sat σ (φ ⊔ ψ) ↔ Sat σ φ ∧ Sat σ ψ :=
  sup_le_iff

/-- Arbitrary conjunctions: a system satisfies the supremum of a family
iff it satisfies every member. -/
theorem sat_iSup_iff {ι : Sort*} {σ : StatePenalty X} {f : ι → StatePenalty X} :
    Sat σ (⨆ i, f i) ↔ ∀ i, Sat σ (f i) :=
  iSup_le_iff

/-! ## Disjunction: the coproduct, exact -/

/-- Disjunction introduction, left: `φ` entails `φ ∨ ψ`.  (The coproduct
injection.) -/
theorem sat_inf_of_left {σ φ ψ : StatePenalty X} (h : Sat σ φ) :
    Sat σ (φ ⊓ ψ) :=
  h.of_spec_le inf_le_left

/-- Disjunction introduction, right. -/
theorem sat_inf_of_right {σ φ ψ : StatePenalty X} (h : Sat σ ψ) :
    Sat σ (φ ⊓ ψ) :=
  h.of_spec_le inf_le_right

/-- **Disjunction is pointwise min, and min is the coproduct.**  The
universal property, which is context-free disjunction elimination
verbatim, sound and complete over the general carrier: the disjunction
entails `ρ` iff both disjuncts do.  (That the pointwise minimum of two
citizens is a citizen is `lsc_inf` in
`SuFunctor.Universe.General.ClosureGeneral`.) -/
theorem entails_inf_iff {φ ψ ρ : StatePenalty X} :
    ρ ≤ φ ⊓ ψ ↔ ρ ≤ φ ∧ ρ ≤ ψ :=
  le_inf_iff

/-- **The disjunction property fails, witnessed by a hedging system —
over every nonempty carrier.**  Take the walls of the unit-mass Dirac
at any point and of the bottom state, and the system committed exactly
to their union: it satisfies the disjunction and neither disjunct.
(The finite storey's witness lived on `V = Bool`; here the general
carrier's own two canonical states — a Dirac direction at full mass
and the zero measure — are separated by mass alone.) -/
theorem exists_sat_inf_not_sat [Nonempty X] :
    ∃ σ φ ψ : StatePenalty X, Sat σ (φ ⊓ ψ) ∧ ¬ Sat σ φ ∧ ¬ Sat σ ψ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  set δ : SubProbabilityMeasure X :=
    SubProbabilityMeasure.scalePoint 1 le_rfl
      ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩ with hδdef
  have hδmass : (δ : FiniteMeasure X).mass = 1 := by
    rw [hδdef, SubProbabilityMeasure.coe_scalePoint,
      SubProbabilityMeasure.mass_smul, ProbabilityMeasure.mass_toFiniteMeasure,
      mul_one]
  have hδ0 : δ ≠ (0 : SubProbabilityMeasure X) := by
    intro h
    have hm := (SubProbabilityMeasure.mass_eq_zero_iff δ).mpr h
    rw [hδmass] at hm
    exact one_ne_zero hm
  refine ⟨wall {δ} ⊓ wall {(0 : SubProbabilityMeasure X)},
    wall {δ}, wall {(0 : SubProbabilityMeasure X)}, sat_self _, ?_, ?_⟩
  · -- the hedger does not satisfy the left disjunct: at the bottom
    -- state the left wall is `⊤` but the min is `0`.
    intro h
    have h0δ : (0 : SubProbabilityMeasure X)
        ∉ ({δ} : Set (SubProbabilityMeasure X)) :=
      fun hmem => hδ0 (Set.mem_singleton_iff.mp hmem).symm
    have hle := h (0 : SubProbabilityMeasure X)
    rw [Pi.inf_apply, wall_apply_of_not_mem h0δ,
      wall_apply_of_mem (Set.mem_singleton _)] at hle
    simp at hle
  · -- nor the right disjunct: at the Dirac state the right wall is `⊤`
    -- but the min is `0`.
    intro h
    have hδn0 : δ ∉ ({(0 : SubProbabilityMeasure X)}
        : Set (SubProbabilityMeasure X)) :=
      fun hmem => hδ0 (Set.mem_singleton_iff.mp hmem)
    have hle := h δ
    rw [Pi.inf_apply, wall_apply_of_mem (Set.mem_singleton _),
      wall_apply_of_not_mem hδn0] at hle
    simp at hle

/-! ## Wall algebra

On walls, conjunction is intersection and disjunction is union —
verbatim, with no hull: the crisp fragment of the universe is closed
under both lattice operations at the general carrier. -/

theorem wall_sup_wall (C D : Set (SubProbabilityMeasure X)) :
    wall C ⊔ wall D = wall (C ∩ D) := by
  funext ν
  by_cases hC : ν ∈ C <;> by_cases hD : ν ∈ D <;>
    simp [Pi.sup_apply, wall, hC, hD]

theorem wall_inf_wall (C D : Set (SubProbabilityMeasure X)) :
    wall C ⊓ wall D = wall (C ∪ D) := by
  funext ν
  by_cases hC : ν ∈ C <;> by_cases hD : ν ∈ D <;>
    simp [Pi.inf_apply, wall, hC, hD]

theorem le_wall_iff {C : Set (SubProbabilityMeasure X)} {σ : StatePenalty X} :
    σ ≤ wall C ↔ ∀ ν ∈ C, σ ν = 0 := by
  constructor
  · intro h ν hν
    have hle := h ν
    rw [wall_apply_of_mem hν] at hle
    exact le_antisymm hle zero_le
  · intro h ν
    by_cases hν : ν ∈ C
    · rw [wall_apply_of_mem hν, h ν hν]
    · rw [wall_apply_of_not_mem hν]
      exact le_top

/-- The wall order is containment, contravariantly: a larger permitted
set is a weaker requirement. -/
theorem wall_le_wall_iff {C D : Set (SubProbabilityMeasure X)} :
    wall D ≤ wall C ↔ C ⊆ D := by
  rw [wall_le_iff]
  constructor
  · intro h ν hν
    by_contra hD
    have := h ν hD
    rw [wall_apply_of_mem hν] at this
    exact ENNReal.zero_ne_top this
  · intro hCD ν hν
    exact wall_apply_of_not_mem fun hC => hν (hCD hC)

theorem wall_anti {C D : Set (SubProbabilityMeasure X)} (h : C ⊆ D) :
    wall D ≤ wall C :=
  wall_le_wall_iff.mpr h

@[simp] theorem wall_univ :
    wall (Set.univ : Set (SubProbabilityMeasure X)) = 0 := by
  funext ν; simp [wall]

@[simp] theorem wall_empty :
    wall (∅ : Set (SubProbabilityMeasure X)) = ⊤ := by
  funext ν; simp [wall]

/-- A `{0, ⊤}`-valued penalty is a wall — the wall of its zero set.  The
crisp fragment of the universe is exactly the walls. -/
theorem eq_wall_of_two_valued {σ : StatePenalty X}
    (h : ∀ ν, σ ν = 0 ∨ σ ν = ⊤) : σ = wall {ν | σ ν = 0} := by
  funext ν
  rcases h ν with h0 | htop
  · rw [wall_apply_of_mem h0, h0]
  · rw [htop, wall_apply_of_not_mem]
    rw [Set.mem_setOf_eq, htop]
    exact ENNReal.top_ne_zero

/-- **Walls are citizens exactly on closed sets** — closedness, *not*
convexity, is the membership condition, over the general carrier.
Nothing in the finite storey's proof consumed finiteness or a metric;
this is that proof at the general stratum. -/
theorem lowerSemicontinuous_wall_iff {C : Set (SubProbabilityMeasure X)} :
    LowerSemicontinuous (wall C) ↔ IsClosed C := by
  constructor
  · intro h
    have hcl := lowerSemicontinuous_iff_isClosed_preimage.mp h 0
    have hrepr : wall C ⁻¹' Set.Iic 0 = C := by
      ext ν
      simp only [Set.mem_preimage, Set.mem_Iic, le_zero_iff]
      constructor
      · intro hν
        by_contra hC
        rw [wall_apply_of_not_mem hC] at hν
        exact ENNReal.top_ne_zero hν
      · intro hν
        rw [wall_apply_of_mem hν]
    rw [← hrepr]
    exact hcl
  · intro hC ν y hy
    by_cases hν : ν ∈ C
    · rw [wall_apply_of_mem hν] at hy
      exact absurd hy (by simp)
    · have htop : y < ⊤ := by
        rw [wall_apply_of_not_mem hν] at hy
        exact hy
      have hmem : ∀ᶠ ρ in nhds ν, ρ ∈ Cᶜ :=
        hC.isOpen_compl.mem_nhds hν
      filter_upwards [hmem] with ρ hρ
      rw [wall_apply_of_not_mem hρ]
      exact htop

/-! ## Chart-invariance of wall obligations -/

/-- **The quantifier collapse, chart-parametrically.**  For any class
`P` of penalties containing the joined premise `ψ`, the universally
quantified graded obligation "every `P`-system dominating `ψ` dominates
`χ`" collapses to the single order fact `χ ≤ ψ` — the obligation is
decided at the join, over the general carrier. -/
theorem gradedObligation_iff_le {P : StatePenalty X → Prop}
    {ψ χ : StatePenalty X} (hψ : P ψ) :
    (∀ σ, P σ → Sat σ ψ → Sat σ χ) ↔ χ ≤ ψ := by
  constructor
  · intro h
    exact h ψ hψ (sat_self ψ)
  · intro h σ _ hσ
    exact hσ.of_spec_le h

/-- **Tent-invariance of wall-denoting obligations.**  For rules whose
premises and conclusion denote walls, the graded obligation over *any*
chart class containing the premise wall is the same set-containment
fact; chart-sensitivity can enter a rule only through connectives whose
denotation is chart-indexed. -/
theorem gradedObligation_wall_iff {P : StatePenalty X → Prop}
    {C D : Set (SubProbabilityMeasure X)} (hC : P (wall C)) :
    (∀ σ, P σ → Sat σ (wall C) → Sat σ (wall D)) ↔ C ⊆ D := by
  rw [gradedObligation_iff_le hC]
  exact wall_le_wall_iff

/-! ## Distributivity: contextual disjunction elimination -/

/-- **The distributive law, with pointwise equality.**  Conjunction
distributes over disjunction in the universe because heights form a
chain — over the general carrier exactly as at the finite stratum:
the semantic validity of *contextual* disjunction elimination. -/
theorem conj_disj_distrib (γ φ ψ : StatePenalty X) :
    γ ⊔ (φ ⊓ ψ) = (γ ⊔ φ) ⊓ (γ ⊔ ψ) :=
  sup_inf_left γ φ ψ

end SuFunctor.Universe.General
