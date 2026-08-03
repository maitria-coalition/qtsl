import SuFunctor.Universe.General.Carrier

/-! # The checker anchor at the general carrier

The shipped checker's two anchor theorems — the wall restriction and
the tolerance-slice bridge — stated over the general subprobability
carrier.  Both are order facts about `[0,∞]`-valued functionals, and
the proofs below are the finite-stratum proofs verbatim modulo the
carrier: nothing in them ever used finiteness, and stating them here
retires the last "kernel-checked at the finite stratum" scoping of the
checker-anchor remark.

* `Sat σ φ` — the graded judgment: the system dominates the spec
  pointwise; one relation serving as satisfaction, spec-to-spec
  entailment, and the universe's order.
* `sat_wall_iff` — against a wall spec, satisfaction says exactly that
  the system's finite-penalty region is permitted: the shipped
  checker's verdict, as the restriction of the graded order to walls.
* `sat_wall_wall_iff` — wall against wall is containment: the
  compatibility theorem.
* `sat_iff_sublevel_subset` — the bridge theorem: the graded judgment
  is equivalently the ∀-family of tolerance-indexed slice
  containments, each slice a crisp containment of sublevel sets — the
  certification chart of the graded order, with the tolerance as one
  added field.
-/

namespace SuFunctor.Universe.General

open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- System-level penalty functionals: `[0,∞]`-valued heights on the
general subprobability carrier. -/
abbrev StatePenalty (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : Type _ :=
  SubProbabilityMeasure X → ℝ≥0∞

/-- The graded satisfaction judgment: `σ` satisfies `φ` iff `σ`
dominates `φ` pointwise.  The judgment, spec-to-spec entailment, and
the universe's order coincide by definition. -/
def Sat (σ φ : StatePenalty X) : Prop := φ ≤ σ

theorem sat_def {σ φ : StatePenalty X} : Sat σ φ ↔ φ ≤ σ := Iff.rfl

@[simp] theorem sat_self (σ : StatePenalty X) : Sat σ σ := le_rfl

open Classical in
/-- The wall of a permitted region: zero inside, hard violation
outside. -/
noncomputable def wall (C : Set (SubProbabilityMeasure X)) :
    StatePenalty X :=
  fun ν => if ν ∈ C then 0 else ⊤

theorem wall_apply_of_mem {C : Set (SubProbabilityMeasure X)}
    {ν : SubProbabilityMeasure X} (h : ν ∈ C) : wall C ν = 0 := by
  simp [wall, h]

theorem wall_apply_of_not_mem {C : Set (SubProbabilityMeasure X)}
    {ν : SubProbabilityMeasure X} (h : ν ∉ C) : wall C ν = ⊤ := by
  simp [wall, h]

theorem wall_le_iff {C : Set (SubProbabilityMeasure X)}
    {σ : StatePenalty X} :
    wall C ≤ σ ↔ ∀ ν, ν ∉ C → σ ν = ⊤ := by
  constructor
  · intro h ν hν
    have hle := h ν
    rw [wall_apply_of_not_mem hν] at hle
    exact top_le_iff.mp hle
  · intro h ν
    by_cases hν : ν ∈ C
    · rw [wall_apply_of_mem hν]
      exact zero_le
    · rw [wall_apply_of_not_mem hν, h ν hν]

/-- **The wall restriction**: against a wall spec, satisfaction says
exactly that the system's finite-penalty region is permitted — the
shipped checker's verdict, over the general carrier. -/
theorem sat_wall_iff {σ : StatePenalty X}
    {C : Set (SubProbabilityMeasure X)} :
    Sat σ (wall C) ↔ ∀ ν, σ ν ≠ ⊤ → ν ∈ C := by
  rw [Sat, wall_le_iff]
  exact ⟨fun h ν hν => by_contra fun hC => hν (h ν hC),
    fun h ν hν => by_contra fun hne => hν (h ν hne)⟩

/-- **The compatibility theorem**: on walls, the graded judgment is
containment of the permitted sets — the shipped crisp judgment is the
restriction of the order to wall-valued data. -/
theorem sat_wall_wall_iff {S C : Set (SubProbabilityMeasure X)} :
    Sat (wall S) (wall C) ↔ S ⊆ C := by
  rw [Sat, wall_le_iff]
  constructor
  · intro h ν hν
    by_contra hC
    have := h ν hC
    rw [wall_apply_of_mem hν] at this
    exact (ENNReal.zero_ne_top) this
  · intro h ν hν
    rw [wall_apply_of_not_mem fun hS => hν (h hS)]

/-- **The bridge theorem — tolerance slices.**  The graded judgment is
equivalently the ∀-family of tolerance-indexed slice containments: `σ`
dominates `φ` iff at every tolerance `s`, the system's `s`-slice is
contained in the spec's `s`-slice.  Each slice claim is a crisp
containment of sublevel sets — the certificate-level presentation of
the graded judgment, with the tolerance as one added field, over the
general carrier. -/
theorem sat_iff_sublevel_subset {σ φ : StatePenalty X} :
    Sat σ φ ↔ ∀ s : ℝ≥0∞,
      {ν : SubProbabilityMeasure X | σ ν ≤ s}
        ⊆ {ν : SubProbabilityMeasure X | φ ν ≤ s} := by
  constructor
  · intro h s ν hν
    exact le_trans (h ν) hν
  · intro h ν
    exact h (σ ν)
      (le_refl (σ ν) : ν ∈ {ρ : SubProbabilityMeasure X | σ ρ ≤ σ ν})

end SuFunctor.Universe.General
