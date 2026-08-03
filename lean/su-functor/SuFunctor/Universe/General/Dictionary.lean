import SuFunctor.Universe.General.Carrier

/-! # The radial compile at the general carrier: order and algebra

The chapter's penalty↔body dictionary
(`Definition su-penalty-functional`), stated over the general
subprobability carrier: penalty functionals on the probability
measures of an arbitrary topological measurable space compile to
radial bodies inside `SubProbabilityMeasure X`.  This module carries
the order/algebra half — everything that holds with **no topological
hypothesis at all**:

* `compile` — the radial compile
  `S(f) = {γ·μ | γ ≤ e^{−f(μ)}}`; every body owns the bottom state
  (`zero_mem_compile` — the bottom body is `{0}`, never empty), and
  every body is radial (`isRadial_compile`).
* **antitonicity** (`compile_subset_compile_iff`): body inclusion is
  the reversed pointwise order on penalties — the order dictionary,
  with no excluded cases.
* the ray algebra: the trace of a body on the ray at a direction is
  the exact interval `[0, e^{−f(μ)}]` (`raySet_compile`), so the ray
  gauge of a body *computes the grade* (`rayGauge_compile`) and the
  gauge penalty of a body is the compiled penalty on the nose
  (`rayPenalty_compile`) — **unconditionally**: at the general
  stratum the inverse law on the penalty side needs no citizenship
  hypothesis, an improvement over the finite-stratum route through
  injectivity on citizens.  Injectivity (`compile_injective`) is then
  a corollary.

The topological half — closedness of the compile ⟺ lower
semicontinuity of the penalty, attainment of the gauge, and the image
characterization — is `SuFunctor.Universe.General.Closedness`.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- Penalty functionals on the general probability carrier: the
spec-side vocabulary of the dictionary.  Citizenship — where the
topological stratum needs it — is lower semicontinuity with respect to
the narrow topology, and nothing else. -/
abbrev Penalty (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : Type _ :=
  ProbabilityMeasure X → ℝ≥0∞

/-- The **radial compile** of a penalty functional: its epistemic body
inside the general subprobability carrier — each probability direction
`μ`, scaled by any mass up to the grade `e^{−f(μ)}`. -/
def compile (f : Penalty X) : Set (SubProbabilityMeasure X) :=
  {ν | ∃ (μ : ProbabilityMeasure X) (γ : ℝ≥0), γ ≤ gradeN (f μ)
    ∧ (ν : FiniteMeasure X) = γ • μ.toFiniteMeasure}

/-- Every body owns the bottom state: the bottom body is `{0}`, never
the empty set — nothing in this universe denotes the empty set. -/
theorem zero_mem_compile [Nonempty X] (f : Penalty X) :
    (0 : SubProbabilityMeasure X) ∈ compile f := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  refine ⟨⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩, 0,
    zero_le, ?_⟩
  rw [SubProbabilityMeasure.coe_zero, zero_smul]

/-- A scaled point below the grade budget is in the body. -/
theorem scalePoint_mem_compile {f : Penalty X} {μ : ProbabilityMeasure X}
    {γ : ℝ≥0} (hγ : γ ≤ gradeN (f μ)) :
    SubProbabilityMeasure.scalePoint γ (hγ.trans (gradeN_le_one _)) μ
      ∈ compile f :=
  ⟨μ, γ, hγ, SubProbabilityMeasure.coe_scalePoint _ _ _⟩

/-- Ray-down-closure: the defining shape property of epistemic bodies
on the general carrier. -/
def IsRadial (R : Set (SubProbabilityMeasure X)) : Prop :=
  ∀ ν ∈ R, ∀ (t : ℝ≥0) (ht : t ≤ 1),
    SubProbabilityMeasure.scale t ht ν ∈ R

/-- A nonempty radial set owns the bottom state. -/
theorem zero_mem_of_isRadial {R : Set (SubProbabilityMeasure X)}
    (hne : R.Nonempty) (hrad : IsRadial R) :
    (0 : SubProbabilityMeasure X) ∈ R := by
  obtain ⟨ν, hν⟩ := hne
  have h := hrad ν hν 0 zero_le_one
  have he : SubProbabilityMeasure.scale 0 zero_le_one ν
      = (0 : SubProbabilityMeasure X) :=
    SubProbabilityMeasure.ext (by
      rw [SubProbabilityMeasure.coe_scale, zero_smul,
        SubProbabilityMeasure.coe_zero])
  rwa [he] at h

/-- Every body is radial: the ray-down motion of the carrier preserves
membership. -/
theorem isRadial_compile (f : Penalty X) : IsRadial (compile f) := by
  rintro ν ⟨μ, γ, hle, he⟩ t ht
  refine ⟨μ, t * γ, le_trans ?_ hle, ?_⟩
  · calc t * γ ≤ 1 * γ := mul_le_mul_of_nonneg_right ht zero_le
      _ = γ := one_mul γ
  · rw [SubProbabilityMeasure.coe_scale, he, smul_smul]

/-- Membership bounds the scale by the grade, along any positive polar
decomposition: the radial coordinate cannot exceed the body's ray
budget. -/
theorem compile_scale_le {f : Penalty X} {ν : SubProbabilityMeasure X}
    (hν : ν ∈ compile f) {γ : ℝ≥0} {μ : ProbabilityMeasure X}
    (hγ : γ ≠ 0) (hd : (ν : FiniteMeasure X) = γ • μ.toFiniteMeasure) :
    γ ≤ gradeN (f μ) := by
  obtain ⟨μ₁, γ₁, hle, he⟩ := hν
  have heq : γ • μ.toFiniteMeasure = γ₁ • μ₁.toFiniteMeasure := by
    rw [← hd, ← he]
  have hγγ : γ = γ₁ := SubProbabilityMeasure.polar_scale_eq heq
  rw [← hγγ] at hle heq
  have hμ : μ = μ₁ := SubProbabilityMeasure.polar_direction_eq hγ heq
  rw [hμ]
  exact hle

/-- **Antitonicity — the order dictionary.**  Body inclusion is the
reversed pointwise order on penalties: `σ ≤ τ` exactly when the body of
`τ` sits inside the body of `σ`.  Refinement as shrinkage, with no
excluded cases and no topological hypothesis. -/
theorem compile_subset_compile_iff {f h : Penalty X} :
    compile f ⊆ compile h ↔ h ≤ f := by
  constructor
  · intro hsub μ
    by_cases hfμ : f μ = ⊤
    · rw [hfμ]
      exact le_top
    · have htip := scalePoint_mem_compile (f := f) (μ := μ)
        (le_refl (gradeN (f μ)))
      have hb := compile_scale_le (hsub htip)
        (gradeN_pos hfμ).ne' (SubProbabilityMeasure.coe_scalePoint _ _ _)
      exact gradeN_le_gradeN_iff.mp hb
  · rintro hle ν ⟨μ, γ, hγ, he⟩
    exact ⟨μ, γ, hγ.trans (gradeN_anti (hle μ)), he⟩

/-! ## The ray algebra -/

/-- The trace of a set on the ray at a probability direction: the
scales at which the ray meets the set. -/
def raySet (R : Set (SubProbabilityMeasure X)) (μ : ProbabilityMeasure X) :
    Set ℝ≥0 :=
  {γ | γ ∈ Set.Icc (0 : ℝ≥0) 1
    ∧ γ • μ.toFiniteMeasure
        ∈ SubProbabilityMeasure.toFiniteMeasure '' R}

theorem mem_raySet_iff {R : Set (SubProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} {γ : ℝ≥0} :
    γ ∈ raySet R μ ↔ (γ ≤ 1
      ∧ γ • μ.toFiniteMeasure
          ∈ SubProbabilityMeasure.toFiniteMeasure '' R) := by
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨zero_le, h1⟩, h2⟩

theorem scalePoint_mem_of_mem_raySet {R : Set (SubProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} {γ : ℝ≥0} (hγ : γ ∈ raySet R μ) :
    SubProbabilityMeasure.scalePoint γ hγ.1.2 μ ∈ R := by
  obtain ⟨ν, hνR, hν⟩ := hγ.2
  have he : SubProbabilityMeasure.scalePoint γ hγ.1.2 μ = ν :=
    SubProbabilityMeasure.ext (by
      rw [SubProbabilityMeasure.coe_scalePoint, hν])
  rw [he]
  exact hνR

theorem zero_mem_raySet {R : Set (SubProbabilityMeasure X)}
    (hz : (0 : SubProbabilityMeasure X) ∈ R) (μ : ProbabilityMeasure X) :
    (0 : ℝ≥0) ∈ raySet R μ := by
  refine ⟨⟨le_rfl, zero_le_one⟩, 0, hz, ?_⟩
  rw [SubProbabilityMeasure.coe_zero, zero_smul]

theorem bddAbove_raySet (R : Set (SubProbabilityMeasure X))
    (μ : ProbabilityMeasure X) : BddAbove (raySet R μ) :=
  ⟨1, fun _ hγ => hγ.1.2⟩

/-- The ray gauge: the length of the set's ray at each direction. -/
noncomputable def rayGauge (R : Set (SubProbabilityMeasure X))
    (μ : ProbabilityMeasure X) : ℝ≥0 :=
  sSup (raySet R μ)

theorem le_rayGauge_of_mem_raySet {R : Set (SubProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} {γ : ℝ≥0} (hγ : γ ∈ raySet R μ) :
    γ ≤ rayGauge R μ :=
  le_csSup (bddAbove_raySet R μ) hγ

theorem rayGauge_le_one {R : Set (SubProbabilityMeasure X)}
    (hz : (0 : SubProbabilityMeasure X) ∈ R) (μ : ProbabilityMeasure X) :
    rayGauge R μ ≤ 1 :=
  csSup_le ⟨0, zero_mem_raySet hz μ⟩ fun _ hγ => hγ.1.2

/-- The gauge penalty of a set: `−log` of its ray gauge, through the
grade inverse of the topological stratum. -/
noncomputable def rayPenalty (R : Set (SubProbabilityMeasure X)) :
    Penalty X :=
  fun μ => gradeInv (rayGauge R μ : ℝ)

/-! ## The gauge of a body computes the grade -/

/-- The ray trace of a body is the exact grade interval: pure polar
algebra, no closedness anywhere. -/
theorem raySet_compile [Nonempty X] (f : Penalty X)
    (μ : ProbabilityMeasure X) :
    raySet (compile f) μ = Set.Icc 0 (gradeN (f μ)) := by
  ext γ
  constructor
  · rintro ⟨⟨-, h1⟩, ν, hν, he⟩
    refine ⟨zero_le, ?_⟩
    rcases eq_or_ne γ 0 with rfl | hγ0
    · exact zero_le
    · exact compile_scale_le hν hγ0 he
  · rintro ⟨-, hγ⟩
    refine ⟨⟨zero_le, hγ.trans (gradeN_le_one _)⟩,
      SubProbabilityMeasure.scalePoint γ (hγ.trans (gradeN_le_one _)) μ,
      scalePoint_mem_compile hγ,
      SubProbabilityMeasure.coe_scalePoint _ _ _⟩

/-- The ray gauge of a body computes the grade of its penalty. -/
theorem rayGauge_compile [Nonempty X] (f : Penalty X)
    (μ : ProbabilityMeasure X) :
    rayGauge (compile f) μ = gradeN (f μ) := by
  rw [rayGauge, raySet_compile]
  exact csSup_Icc zero_le

/-- **The inverse law on the penalty side, unconditionally**: the gauge
penalty of a body is the compiled penalty on the nose — with no
citizenship hypothesis.  (The finite stratum stated this law on
citizens, through injectivity; at the general stratum it is the ray
algebra composed with the unconditional grade round trip.) -/
theorem rayPenalty_compile [Nonempty X] (f : Penalty X) :
    rayPenalty (compile f) = f := by
  funext μ
  rw [rayPenalty, rayGauge_compile, coe_gradeN, gradeInv_grade]

/-- **Injectivity**: distinct penalties have distinct bodies — the
compile forgets nothing. -/
theorem compile_injective [Nonempty X] :
    Function.Injective (compile (X := X)) := by
  intro f h hfh
  rw [← rayPenalty_compile f, ← rayPenalty_compile h, hfh]

end SuFunctor.Universe.General
