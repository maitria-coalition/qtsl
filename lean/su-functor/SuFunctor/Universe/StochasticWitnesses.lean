import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Nat

/-! # Stochastic witnesses: what narrow convergence does and does not see

Point-native exhibits for the probability stratum of the semantic
universe, pinning the polarity discipline of event evaluation and the
honesty of the compactness bookkeeping.  All witnesses run on concrete
carriers (`ℕ`, `ℝ`) with Dirac point masses, so every claim is an exact
computation.

* **Mass cannot leak in the narrow limit** (`tendsto_mass`,
  `mass_of_tendsto`): the total mass of a finite measure is a narrowly
  *continuous* coordinate — the one Borel-blind functional that
  converges unconditionally.  A narrow limit of measures of mass `p`
  again has mass `p`; escape of mass cannot happen *along* a convergent
  family.  Sequences that try to push mass to infinity instead fail to
  converge at all:

* **The escape witness** (`not_exists_tendsto_diracProb`): on `ℕ` the
  point masses `δ_n` have **no** narrow limit.  Any candidate limit
  would assign measure zero to every singleton — by the portmanteau
  lower-semicontinuity of open-event evaluation — hence, by countable
  additivity over the singleton cover, measure zero to the whole
  space, contradicting unit mass.  This is the σ-additivity refusal in
  kernel form: the finitely-additive "limit" (mass at infinity) is not
  a citizen of the carrier, and the carrier over a noncompact space is
  honestly noncompact (`not_compactSpace_probabilityMeasure_nat`).

* **Event evaluation is not narrowly continuous**
  (`not_tendsto_diracProb_apply_singleton`): on `ℝ`, `δ_{1/(n+1)} → δ_0`
  narrowly (`tendsto_diracProb_one_div_add_one`), yet evaluation at the
  Borel event `{0}` sends the sequence to `0` and the limit to `1`.
  Only the portmanteau *inequalities* survive at a general event: open
  events evaluate lower-semicontinuously, closed events upper, and a
  set whose frontier carries limit mass — here `frontier {0} = {0}`
  itself — converges in neither direction.  Consequently the wall
  `{μ | μ {0} ≤ 0}` is **not** narrowly closed
  (`not_isClosed_setOf_apply_singleton_le`): upper bounds on the
  measure of a general Borel event are not closed conditions of the
  carrier; closedness of a wall must come from the polarity discipline,
  never from Borel bookkeeping alone.
-/

namespace SuFunctor.Universe

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ## Dirac point masses as probability measures -/

/-- The Dirac point mass at `x`, as a probability measure. -/
noncomputable def diracProb {X : Type*} [MeasurableSpace X] (x : X) :
    ProbabilityMeasure X :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

@[simp]
theorem diracProb_toMeasure {X : Type*} [MeasurableSpace X] (x : X) :
    (diracProb x : Measure X) = Measure.dirac x := rfl

theorem diracProb_apply_of_mem {X : Type*} [MeasurableSpace X] {x : X}
    {s : Set X} (h : x ∈ s) : diracProb x s = 1 := by
  simp [ProbabilityMeasure.coeFn_def, Measure.dirac_apply_of_mem h]

theorem diracProb_apply_of_notMem {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {x : X} {s : Set X} (h : x ∉ s) :
    diracProb x s = 0 := by
  simp [ProbabilityMeasure.coeFn_def, Measure.dirac_apply,
    Set.indicator_of_notMem h]

/-! ## Mass cannot leak in the narrow limit -/

section Mass

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] {ι : Type*} {l : Filter ι}

/-- Total mass is a narrowly continuous coordinate: narrow convergence of
finite measures transports to convergence of the total masses.  (The
positive face of the no-leak principle; a restatement of
`MeasureTheory.FiniteMeasure.continuous_mass`.) -/
theorem tendsto_mass {f : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hf : Tendsto f l (𝓝 μ)) :
    Tendsto (fun i => (f i).mass) l (𝓝 μ.mass) :=
  hf.mass

/-- Mass cannot leak in a narrow limit: if the members of a narrowly
convergent family eventually all have total mass `p`, so does the limit. -/
theorem mass_of_tendsto [l.NeBot] {f : ι → FiniteMeasure X}
    {μ : FiniteMeasure X} {p : ℝ≥0} (hf : Tendsto f l (𝓝 μ))
    (hmass : ∀ᶠ i in l, (f i).mass = p) : μ.mass = p :=
  tendsto_nhds_unique hf.mass
    (Tendsto.congr' (hmass.mono fun _ hi => hi.symm) tendsto_const_nhds)

end Mass

/-! ## The escape witness: point masses marching to infinity have no limit -/

/-- Along any index sequence escaping to infinity, the Dirac point masses on
`ℕ` narrowly converge to **no** probability measure: a candidate limit `μ`
would satisfy `μ {k} ≤ liminf δ_{ns n} {k} = 0` for every `k` (open events
evaluate lower-semicontinuously — the portmanteau inequality), hence by
countable additivity over the singleton cover `μ` would annihilate the whole
space, contradicting unit mass. -/
theorem not_tendsto_diracProb_atTop {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) (μ : ProbabilityMeasure ℕ) :
    ¬ Tendsto (fun n => diracProb (ns n)) atTop (𝓝 μ) := by
  intro h
  -- every singleton is null for the candidate limit
  have hsing : ∀ k : ℕ, (μ : Measure ℕ) {k} = 0 := by
    intro k
    have hle : (μ : Measure ℕ) {k}
        ≤ atTop.liminf fun n => (diracProb (ns n) : Measure ℕ) {k} :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto h
        (isOpen_discrete _)
    -- the evaluations vanish once the escaping index has cleared `k`
    have hev : ∀ᶠ n in atTop,
        (diracProb (ns n) : Measure ℕ) {k} = 0 := by
      filter_upwards [hns.eventually_gt_atTop k] with n hn
      have hnot : ns n ∉ ({k} : Set ℕ) := by simpa using hn.ne'
      simp [Set.indicator_of_notMem hnot]
    have hlim :
        (atTop.liminf fun n => (diracProb (ns n) : Measure ℕ) {k}) ≤ 0 :=
      liminf_le_of_frequently_le' (hev.frequently.mono fun _ hn => hn.le)
    exact le_zero_iff.mp (hle.trans hlim)
  -- σ-additivity over the singleton cover of `univ`
  have huniv : (μ : Measure ℕ) univ = 0 := by
    rw [← Set.iUnion_of_singleton ℕ]
    exact measure_iUnion_null hsing
  exact one_ne_zero ((measure_univ (μ := (μ : Measure ℕ))).symm.trans huniv)

/-- **The escape witness.**  The sequence of point masses `δ_0, δ_1, δ_2, …`
on `ℕ` has no narrow limit at all: mass escapes to infinity, and the
finitely-additive phantom that would catch it is not a probability measure.
This is the σ-additivity refusal in kernel form, and the reason the
subprobability carrier's topology must let mass *vanish* (into the
partiality coordinate) rather than pretend a vague limit is a citizen. -/
theorem not_exists_tendsto_diracProb :
    ¬ ∃ μ : ProbabilityMeasure ℕ,
        Tendsto (fun n => diracProb n) atTop (𝓝 μ) :=
  fun ⟨μ, h⟩ => not_tendsto_diracProb_atTop tendsto_id μ h

/-! ## Event evaluation is not narrowly continuous -/

/-- The evaluations of the moving point masses at the event `{0}`: each is
zero, since `1/(n+1)` never hits `0`. -/
theorem diracProb_one_div_apply_singleton (n : ℕ) :
    diracProb (1 / ((n : ℝ) + 1)) ({0} : Set ℝ) = 0 := by
  have hne : (1 : ℝ) / ((n : ℝ) + 1) ∉ ({0} : Set ℝ) := by
    simp only [mem_singleton_iff]
    positivity
  exact diracProb_apply_of_notMem hne

/-- The limit measure evaluates the event `{0}` to one. -/
theorem diracProb_zero_apply_singleton :
    diracProb (0 : ℝ) ({0} : Set ℝ) = 1 :=
  diracProb_apply_of_mem (mem_singleton_iff.mpr rfl)

/-- The moving point masses `δ_{1/(n+1)}` narrowly converge to `δ_0` on `ℝ`:
integration of a bounded continuous test function against a point mass is
evaluation at the point, and evaluation moves continuously with the point. -/
theorem tendsto_diracProb_one_div_add_one :
    Tendsto (fun n : ℕ => diracProb (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (diracProb (0 : ℝ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  simp only [diracProb_toMeasure, lintegral_dirac]
  exact ENNReal.tendsto_coe.mpr
    ((f.continuous.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat)

/-- **Event evaluation is not narrowly continuous.**  Along the narrowly
convergent sequence `δ_{1/(n+1)} → δ_0`, evaluation at the Borel event `{0}`
sends every member to `0` and the limit to `1`.  The frontier of the event
carries the limit's whole mass — exactly the configuration the portmanteau
theorem excludes from its convergence conclusion, witnessed here as sharp. -/
theorem not_tendsto_diracProb_apply_singleton :
    ¬ Tendsto (fun n : ℕ => diracProb (1 / ((n : ℝ) + 1)) ({0} : Set ℝ))
        atTop (𝓝 (diracProb (0 : ℝ) ({0} : Set ℝ))) := by
  intro h
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ≥0)) atTop
      (𝓝 (diracProb (0 : ℝ) ({0} : Set ℝ))) := by
    simpa only [diracProb_one_div_apply_singleton] using h
  have h1 : diracProb (0 : ℝ) ({0} : Set ℝ) = 0 :=
    tendsto_nhds_unique h0 tendsto_const_nhds
  rw [diracProb_zero_apply_singleton] at h1
  exact one_ne_zero h1

/-- The wall `{μ | μ {0} ≤ 0}` — "the event `{0}` is null" — is **not**
narrowly closed: the moving point masses all sit inside it while their
narrow limit `δ_0` does not.  Upper bounds on the measure of a general
Borel event are not closed conditions of the carrier; only *closed* events
evaluate upper-semicontinuously (the portmanteau polarity), and `{0}` seen
as the target of the moving masses acts through its open complement. -/
theorem not_isClosed_setOf_apply_singleton_le :
    ¬ IsClosed {μ : ProbabilityMeasure ℝ | μ {0} ≤ 0} := by
  intro hcl
  have hmem : ∀ n : ℕ, diracProb (1 / ((n : ℝ) + 1))
      ∈ {μ : ProbabilityMeasure ℝ | μ {0} ≤ 0} := fun n =>
    (diracProb_one_div_apply_singleton n).le
  have hlim : diracProb (0 : ℝ) ∈ {μ : ProbabilityMeasure ℝ | μ {0} ≤ 0} :=
    hcl.mem_of_tendsto tendsto_diracProb_one_div_add_one
      (Eventually.of_forall hmem)
  rw [mem_setOf_eq, diracProb_zero_apply_singleton] at hlim
  exact one_ne_zero (le_antisymm hlim zero_le)

/-! ## The carrier over a noncompact space is noncompact -/

/-- The space of probability measures on `ℕ` is not compact.  Compactness
would extract a narrowly convergent subsequence from the escaping point
masses — the narrow topology on a separable (pseudo)metrizable Borel space
is metrizable, so sequential extraction is available — and a subsequence of
an escaping sequence still escapes, contradicting the escape witness.
Prokhorov's compactness dividend `CompactSpace E → CompactSpace
(ProbabilityMeasure E)` is therefore honest: it has no free upgrade to
noncompact `E`. -/
theorem not_compactSpace_probabilityMeasure_nat :
    ¬ CompactSpace (ProbabilityMeasure ℕ) := by
  intro hc
  haveI := hc
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ProbabilityMeasure ℕ)).tendsto_subseq
      (x := fun n => diracProb n) fun n => mem_univ _
  exact not_tendsto_diracProb_atTop hφ.tendsto_atTop μ hlim

end SuFunctor.Universe
