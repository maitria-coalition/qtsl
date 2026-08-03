import Pointfree.Valuation.Topology
import Pointfree.Valuation.Bridge
import Pointfree.Measure.SubProbability
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Bridge continuity: weak convergence lands in narrow convergence

The bridge (`Measure.toValuation`, restriction to opens) is not merely
a map of carriers: it is continuous from the classical weak topology
into the point-free narrow topology.  Classical weak convergence of
subprobability measures maps to narrow convergence of their valuation
restrictions.

The load-bearing new lemma is the **open half of the portmanteau
theorem for finite measures**
(`FiniteMeasure.le_liminf_measure_open_of_tendsto`): mathlib's open
half exists only for probability measures, and its complement-passing
helper (`le_measure_liminf_of_limsup_measure_compl_le`) assumes
`IsProbabilityMeasure` on both sides.  The generalization costs *no*
extra hypothesis: on `FiniteMeasure` the weak topology already makes
total mass continuous, so the moving-mass complement argument goes
through — the probability lock was an omission, not a mathematical
fence.  Chain: `liminf massᵢ = mass` (mass continuity), the modular
split `mass = μᵢ Gᶜ + μᵢ G`, superadditivity
(`liminf_add_le_limsup_add_liminf` — mathlib's own superadditivity
lives under `[AddCommGroup]`, which `ℝ≥0∞` is not), the closed half on
`Gᶜ`, and cancellation of the finite `μ Gᶜ`.

With the open half in hand, evaluation at each open is lower
semicontinuous on `FiniteMeasure`, and continuity of the bridge into
the narrow topology is exactly generator-checking: evaluation
half-spaces pull back to lsc superlevel sets, mass half-spaces to
sublevel sets of the (continuous) mass coordinate.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology

variable {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

section OpenHalf

variable [OpensMeasurableSpace Ω]

/-- Weak convergence of finite measures converges the total masses
(in `ℝ≥0∞`): the mass functional is continuous for the weak topology. -/
theorem _root_.MeasureTheory.FiniteMeasure.tendsto_measure_univ_of_tendsto
    {L : Filter ι} {μ : FiniteMeasure Ω} {μs : ι → FiniteMeasure Ω}
    (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => (μs i : Measure Ω) Set.univ) L (𝓝 ((μ : Measure Ω) Set.univ)) := by
  have hmass : Tendsto (fun i => (μs i).mass) L (𝓝 μ.mass) :=
    (FiniteMeasure.continuous_mass.tendsto μ).comp h
  have hcoe : Tendsto (fun i => ((μs i).mass : ℝ≥0∞)) L (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.tendsto_coe.mpr hmass
  simpa [FiniteMeasure.ennreal_mass] using hcoe

/-- Superadditivity bookkeeping for `ℝ≥0∞`:
`liminf (u + v) ≤ limsup u + liminf v`.  Mathlib's `liminf_add_le`
lives under `[AddCommGroup α]` — which `ℝ≥0∞` is not — so the
tropical half-space carries its own proof: approach the bound from
above, split the slack in half, and combine an eventual bound on `u`
with a frequent bound on `v`. -/
theorem liminf_add_le_limsup_add_liminf {L : Filter ι} (u v : ι → ℝ≥0∞) :
    L.liminf (u + v) ≤ L.limsup u + L.liminf v := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hS : L.limsup u ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt le_self_add hc)
  have hI : L.liminf v ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt le_add_self hc)
  obtain ⟨ε, hε, hlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hc
  have hε2 : ((ε : ℝ≥0∞) / 2) ≠ 0 :=
    (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hε.ne')).ne'
  have hu_ev : ∀ᶠ i in L, u i < L.limsup u + (ε : ℝ≥0∞) / 2 :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hS hε2)
  have hv_freq : ∃ᶠ i in L, v i < L.liminf v + (ε : ℝ≥0∞) / 2 :=
    frequently_lt_of_liminf_lt (h := ENNReal.lt_add_right hI hε2)
  have hfreq : ∃ᶠ i in L, (u + v) i
      ≤ (L.limsup u + (ε : ℝ≥0∞) / 2) + (L.liminf v + (ε : ℝ≥0∞) / 2) := by
    refine (hv_freq.and_eventually hu_ev).mono fun i hi => ?_
    rw [Pi.add_apply]
    exact (ENNReal.add_lt_add hi.2 hi.1).le
  refine (liminf_le_of_frequently_le' hfreq).trans ?_
  calc (L.limsup u + (ε : ℝ≥0∞) / 2) + (L.liminf v + (ε : ℝ≥0∞) / 2)
      = (L.limsup u + L.liminf v) + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) :=
        add_add_add_comm _ _ _ _
    _ = (L.limsup u + L.liminf v) + ε := by rw [ENNReal.add_halves]
    _ ≤ c := hlt.le

set_option maxHeartbeats 800000 in
/-- **The open half of the portmanteau theorem for finite measures.**
Weak convergence of finite measures implies that the liminf of the
measures of any open set is at least the measure of the open set under
the limit measure.

Mathlib (at this pin) has this only for probability measures: its
complement-passing helper assumes `IsProbabilityMeasure` on both
sides.  No hypothesis replaces that assumption here — on
`FiniteMeasure` the weak topology already converges total masses, so
the complement argument runs with moving mass: the probability
assumption in the pin's helper was an omission, not a fence. -/
theorem _root_.MeasureTheory.FiniteMeasure.le_liminf_measure_open_of_tendsto
    [HasOuterApproxClosed Ω]
    {L : Filter ι} {μ : FiniteMeasure Ω} {μs : ι → FiniteMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  -- masses converge, so their liminf is the limit mass
  have liminf_univ :
      (L.liminf fun i => (μs i : Measure Ω) Set.univ) = (μ : Measure Ω) Set.univ :=
    (FiniteMeasure.tendsto_measure_univ_of_tendsto μs_lim).liminf_eq
  -- split each mass along the open set and its closed complement
  have decomp : (fun i => (μs i : Measure Ω) Set.univ)
      = (fun i => (μs i : Measure Ω) Gᶜ) + fun i => (μs i : Measure Ω) G := by
    funext i
    rw [Pi.add_apply, add_comm,
      measure_add_measure_compl (μ := (μs i : Measure Ω)) G_open.measurableSet]
  -- superadditivity: liminf (u + v) ≤ limsup u + liminf v
  have key : (μ : Measure Ω) Set.univ
      ≤ (L.limsup fun i => (μs i : Measure Ω) Gᶜ)
        + L.liminf fun i => (μs i : Measure Ω) G := by
    rw [← liminf_univ, decomp]
    exact liminf_add_le_limsup_add_liminf _ _
  -- the closed half bounds the limsup on the complement
  have closed_half : (L.limsup fun i => (μs i : Measure Ω) Gᶜ) ≤ (μ : Measure Ω) Gᶜ :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto μs_lim
      (isClosed_compl_iff.mpr G_open)
  -- combine and cancel the finite complement mass
  have h2 : (μ : Measure Ω) G + (μ : Measure Ω) Gᶜ
      ≤ (L.liminf fun i => (μs i : Measure Ω) G) + (μ : Measure Ω) Gᶜ := by
    calc (μ : Measure Ω) G + (μ : Measure Ω) Gᶜ
        = (μ : Measure Ω) Set.univ :=
          measure_add_measure_compl G_open.measurableSet
      _ ≤ (L.limsup fun i => (μs i : Measure Ω) Gᶜ)
            + L.liminf fun i => (μs i : Measure Ω) G := key
      _ ≤ (μ : Measure Ω) Gᶜ + L.liminf fun i => (μs i : Measure Ω) G :=
          add_le_add closed_half le_rfl
      _ = (L.liminf fun i => (μs i : Measure Ω) G) + (μ : Measure Ω) Gᶜ :=
          add_comm _ _
  exact (ENNReal.add_le_add_iff_right (measure_lt_top (μ : Measure Ω) Gᶜ).ne).mp h2

/-- Evaluation at an open set is lower semicontinuous for the weak
topology on finite measures — the classical face of the point-free
"evaluation is lsc by construction". -/
theorem _root_.MeasureTheory.FiniteMeasure.lowerSemicontinuous_measure_open
    [HasOuterApproxClosed Ω] {G : Set Ω} (G_open : IsOpen G) :
    LowerSemicontinuous fun ν : FiniteMeasure Ω => (ν : Measure Ω) G := by
  intro ν y hy
  have hlim : (ν : Measure Ω) G
      ≤ (𝓝 ν).liminf fun ξ : FiniteMeasure Ω => (ξ : Measure Ω) G :=
    FiniteMeasure.le_liminf_measure_open_of_tendsto tendsto_id G_open
  exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hy hlim)

/-- Evaluation at an open set is lower semicontinuous on probability
measures (the pin's open half, in semicontinuity form). -/
theorem _root_.MeasureTheory.ProbabilityMeasure.lowerSemicontinuous_measure_open
    [HasOuterApproxClosed Ω] {G : Set Ω} (G_open : IsOpen G) :
    LowerSemicontinuous fun ν : ProbabilityMeasure Ω => (ν : Measure Ω) G := by
  intro ν y hy
  have hlim : (ν : Measure Ω) G
      ≤ (𝓝 ν).liminf fun ξ : ProbabilityMeasure Ω => (ξ : Measure Ω) G :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id G_open
  exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hy hlim)

end OpenHalf

/-! ## Continuity of the bridge -/

section Bridge

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [HasOuterApproxClosed X] [OpensMeasurableSpace X]

/-- **The bridge is continuous into the narrow topology**: restriction
to opens maps the classical subprobability carrier (weak topology)
continuously to the point-free one (narrow topology).  Evaluation
half-spaces pull back to superlevel sets of the (lsc) open-evaluations;
mass half-spaces pull back to sublevel sets of the (continuous) mass
coordinate. -/
theorem SubProbabilityMeasure.continuous_toSubProb :
    Continuous (SubProbabilityMeasure.toSubProb (X := X)) := by
  rw [show (SubProb.instTopologicalSpace (Opens X) : TopologicalSpace (SubProb (Opens X)))
        = generateFrom (SubProb.narrowGenerators (Opens X)) from rfl,
    continuous_generateFrom_iff]
  rintro S (⟨U, r, rfl⟩ | ⟨r, rfl⟩)
  · -- evaluation half-space: superlevel set of an lsc map
    have hlsc : LowerSemicontinuous fun μ : SubProbabilityMeasure X =>
        (μ.1 : Measure X) (U : Set X) :=
      (FiniteMeasure.lowerSemicontinuous_measure_open U.isOpen).comp
        SubProbabilityMeasure.continuous_toFiniteMeasure
    exact lowerSemicontinuous_iff_isOpen_preimage.mp hlsc r
  · -- mass half-space: sublevel set of the continuous mass coordinate
    have hcont : Continuous fun μ : SubProbabilityMeasure X =>
        (μ.1 : Measure X) Set.univ := by
      have hc : Continuous fun μ : SubProbabilityMeasure X =>
          ((μ.1.mass : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.continuous_coe.comp
          (FiniteMeasure.continuous_mass.comp continuous_subtype_val)
      simpa [FiniteMeasure.ennreal_mass] using hc
    exact isOpen_Iio.preimage hcont

/-- Classical weak convergence of subprobability measures maps to
point-free narrow convergence of their valuation restrictions. -/
theorem SubProbabilityMeasure.tendsto_toSubProb_of_tendsto
    {L : Filter ι} {μs : ι → SubProbabilityMeasure X} {μ : SubProbabilityMeasure X}
    (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => (μs i).toSubProb) L (𝓝 μ.toSubProb) :=
  (SubProbabilityMeasure.continuous_toSubProb.tendsto μ).comp h

/-- The probability face: restriction to opens is continuous from the
weak topology on probability measures to the lower topology on
probability valuations. -/
theorem continuous_toProb :
    Continuous fun μ : ProbabilityMeasure X => (μ : Measure X).toProb := by
  rw [show (Prob.instTopologicalSpace (Opens X) : TopologicalSpace (Prob (Opens X)))
        = generateFrom (Prob.lowerGenerators (Opens X)) from rfl,
    continuous_generateFrom_iff]
  rintro S ⟨U, r, rfl⟩
  have hlsc : LowerSemicontinuous fun μ : ProbabilityMeasure X =>
      (μ : Measure X) (U : Set X) :=
    ProbabilityMeasure.lowerSemicontinuous_measure_open U.isOpen
  exact lowerSemicontinuous_iff_isOpen_preimage.mp hlsc r

end Bridge

end Pointfree
