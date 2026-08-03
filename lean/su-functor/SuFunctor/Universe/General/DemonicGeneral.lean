import SuFunctor.Universe.General.CrescentStratum
import SuFunctor.Universe.DemonicClock

/-! # The seam conjunct at the general carrier

The demonic-clock module's two halves were audited for stratum before
this upgrade, and the audit corrected the census: the relational /
Egli–Milner half (`SuFunctor.Universe.DemonicClock`, sections
`RelKernel`, `EgliMilner`) was always carrier-free, and — the census
surprise — so was the **criterion half**: `selSup_sup_left`,
`coupledSat_sup_wall_iff`, `cross_site_union_refinement_iff`,
`lowerSemicontinuous_selSup`, and `cross_site_union_refinement_iff_lsc`
are all stated over an arbitrary (topological) carrier `K` and are
consumed here, not re-proven.  What was genuinely Fintype-bound was the
**wall species** and the **class-level exactness** (`DemonicClock`,
section `WallSpecies`), and those are what this module upgrades:

* `probWall` — the indicator wall over a set of general probability
  directions, with `lowerSemicontinuous_probWall_iff`: walls are
  citizens exactly on closed admissible sets — over the narrow topology
  of an arbitrary carrier.  (Body-side wall species live elsewhere:
  `General.CheckerAnchor.wall` is the wall of a set of subprobability
  *states*; `General.WallTaxonomy` classifies wall zero-sets.  This is
  the penalty-domain wall the seam conjunct joins into a premise
  floor.)
* `crescentClass_inter_wall` — at the class level the wall conjunct is
  exact over the general crescents.
* `cross_site_union_refinement_iff_probWall` — **the criterion's floor
  at the general carrier**: seam-crossing entailment from a
  wall-conjoined premise is decided by the same finite blocking table,
  with the general wall species discharging the adversary-class
  hypothesis through the (consumed) sup-of-lsc supply.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-! ## The wall species over general probability directions -/

open Classical in
/-- The wall of a set of general probability directions: `0` inside,
`⊤` outside — the compiled form of a transport relation's realization
constraint, on the penalty domain of the general carrier. -/
noncomputable def probWall (B : Set (ProbabilityMeasure X)) : Penalty X :=
  fun μ => if μ ∈ B then 0 else ⊤

theorem probWall_apply_of_mem {B : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∈ B) : probWall B μ = 0 := by
  simp [probWall, h]

theorem probWall_apply_of_notMem {B : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∉ B) : probWall B μ = ⊤ := by
  simp [probWall, h]

/-- Dominating a wall says exactly that the forbidden region is hard
violation. -/
theorem probWall_le_iff {B : Set (ProbabilityMeasure X)} {σ : Penalty X} :
    probWall B ≤ σ ↔ ∀ μ, μ ∉ B → σ μ = ⊤ := by
  constructor
  · intro h μ hμ
    have hμ' := h μ
    rw [probWall_apply_of_notMem hμ] at hμ'
    exact top_le_iff.mp hμ'
  · intro h μ
    by_cases hμ : μ ∈ B
    · rw [probWall_apply_of_mem hμ]
      exact zero_le
    · rw [probWall_apply_of_notMem hμ, h μ hμ]

/-- **Walls are citizens exactly on closed admissible sets**, over the
narrow topology of an arbitrary carrier. -/
theorem lowerSemicontinuous_probWall_iff {B : Set (ProbabilityMeasure X)} :
    LowerSemicontinuous (probWall B) ↔ IsClosed B := by
  constructor
  · intro h
    have hB : B = probWall B ⁻¹' Set.Iic 0 := by
      ext μ
      simp only [Set.mem_preimage, Set.mem_Iic]
      constructor
      · intro hμ
        rw [probWall_apply_of_mem hμ]
      · intro hμ
        by_contra hBμ
        rw [probWall_apply_of_notMem hBμ] at hμ
        exact absurd (top_le_iff.mp hμ) ENNReal.zero_ne_top
    rw [hB]
    exact h.isClosed_preimage 0
  · intro hB μ y hy
    by_cases hμ : μ ∈ B
    · rw [probWall_apply_of_mem hμ] at hy
      exact absurd hy (not_lt.mpr zero_le)
    · have htop : y < ⊤ := by
        rw [probWall_apply_of_notMem hμ] at hy
        exact hy
      filter_upwards [hB.isOpen_compl.mem_nhds hμ] with ν hν
      rw [probWall_apply_of_notMem hν]
      exact htop

/-! ## The class level, and the criterion's floor -/

/-- At the class level the wall conjunct is exact over the general
crescents: intersecting an atom's crescent with a pure-safety wall
crescent is the crescent of the wall-conjoined atom. -/
theorem crescentClass_inter_wall (u w : Penalty X) (𝒱 : Set (Penalty X)) :
    crescentClass u 𝒱 ∩ crescentClass w ∅ = crescentClass (u ⊔ w) 𝒱 := by
  rw [crescentClass_inter_crescentClass, Set.union_empty]

/-- **The seam-crossing criterion's floor at the general carrier**: an
indicator wall over a closed admissible set of general probability
directions is a citizen, and entailment across the seam from the
wall-conjoined premise is decided by the same finite blocking table —
`cross_site_union_refinement_iff_lsc` (already carrier-general,
consumed) instantiated at the general carrier with the general wall
species. -/
theorem cross_site_union_refinement_iff_probWall {m : ℕ}
    {B : Set (ProbabilityMeasure X)} (hB : IsClosed B)
    {u : Penalty X} {𝒱 : Set (Penalty X)}
    {u' : Fin m → Penalty X} {𝒱' : Fin m → Set (Penalty X)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ probWall B) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ probWall B) 𝒱 u' c :=
  cross_site_union_refinement_iff_lsc hu
    (lowerSemicontinuous_probWall_iff.mpr hB) h𝒱'

end SuFunctor.Universe.General
