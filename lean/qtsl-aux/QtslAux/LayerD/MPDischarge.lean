import QtslAux.LayerD.ItoSampling
import QtslAux.LayerD.Until
import QtslAux.LayerD.Streett

/-! # Discharging the segment Dynkin inequality from a martingale problem

This module discharges the per-model hypothesis `SegmentDynkin M θ V` — the
sole analytic input of the segment-skeleton soundness theorems — from a
*martingale-problem presentation* of the inter-jump dynamics, so that the
battery theorems of `QtslAux.LayerD.Skeleton`, `…Deadline`, and `…Until`
apply to general stochastic hybrid systems whose inter-jump motion is a
jump-diffusion (or any process presented by its generator), not only to
piecewise-deterministic flows.

Presenting a process by its generator through the martingale property —
`fun t ω => V (X t ω) - ∫ s in 0..t, (𝒜V) (X s ω)` is a martingale — is the
standard characterisation of jump-diffusions (Stroock–Varadhan,
*Multidimensional Diffusion Processes*, Ch. 6; Dynkin, *Markov Processes*,
Ch. V, via the characteristic operator; Davis, *Markov Models and
Optimization*, Ch. 2, for the piecewise-deterministic case). Here the
generator enters as *data*: a function `AV` recording `𝒜V` along each path,
tied to the process only by the martingale hypothesis. No operator-domain
theory is required — for the intended certificate class (piecewise-polynomial
`V` and coefficients) `AV` is again piecewise polynomial and the membership
of `V` in the generator's domain is immediate. A companion development
derives such presentations from *computed* generator rows for concrete
model classes — there the drift record is produced by the model's own
presentation rather than supplied as data, and the interfaces of this
module are its target; the two faces are designed complements.

Three presentations, in decreasing order of rawness:

* `ItoSupermartingaleData M θ V x` — the *supermartingale floor*: exactly
  `ItoInterface.ofSupermartingale`'s inputs as a bundle, so per-entry-state
  families can be quantified. The two analytic fields are `hZ` (the
  discounted certificate process along the flow data is a supermartingale)
  and `hτ` (the exit time's stopping-time measurability family, in the sense
  of Dellacherie–Meyer, *Probabilités et potentiel*, Ch. IV).
* `MPFlow M θ V x` — the *martingale-problem presentation*: `hZ` is replaced
  by generator data `AV`, the martingale hypothesis `hmp` for the discounted
  compensated certificate process, and the pointwise drift row `hrow`
  (`AV + jr + θ·V∘γ ≤ r·V∘γ`, i.e. `𝒜V + λ(J V − V) + θV ≤ 0` with `jr`
  playing `λ·JV`). The supermartingale property is *derived*
  (`certProcess_supermartingale`), via
  `OptionalSamplingRC.supermartingale_of_compensator_nonpos`.
* `ItoSupermartingaleData.ofMPNoAlarm` — for segments with no spontaneous
  (rate) jumps, the presentation rawer still: the *undiscounted* martingale
  problem for `𝒜` tested at `V` itself, plus the row `AV + θ·V∘γ ≤ 0`;
  the discounting is performed by
  `OptionalSamplingRC.supermartingale_exp_discount`.

Main consequences:

* `segmentDynkin_of_mp` : per-state `MPFlow` families give
  `SegmentDynkin M θ V`; `segmentDynkin_of_supermartingale` and
  `segmentDynkin_of_mixed` are the analogues for the supermartingale floor
  and for per-state mixtures with deterministic (Dini) flow data.
* `sound_GSHS_safety_battery_mp`, `sound_GSHS_deadline_battery_mp`,
  `sound_GSHS_until_battery_mp` (with the reach-bound forms
  `sound_GSHS_safety_mp`, `sound_GSHS_deadline_mp`,
  `sound_GSHS_avoid_timed_mp`, `sound_GSHS_until_mp`): the segment-skeleton
  battery theorems at the martingale-problem profile — the hypothesis
  `SegmentDynkin M θ V` replaced by a per-entry-state martingale-problem
  presentation, all other hypotheses unchanged.
* `rankingSegmentDynkin_of_mp`: the `ε = 0` ranking rows of the
  Streett/recurrence bundle follow as well. The strict-decrement rows
  (`ε > 0`) quantify progress per segment, which the supermartingale
  property alone cannot see; they are discharged from one additional
  presentation field — the pathwise progress row of `MPFlowStrict` — by
  `rankingSegmentDynkin_of_mp_strict` (mechanism: split the stopped
  certificate as martingale part + drift accumulation; upper-bound
  optional sampling on the martingale part, dominated convergence on the
  `ε`-truncated drift accumulations). `sound_GSHS_streett_bundle_mp_strict`
  is the resulting fully martingale-problem Streett bundle, with no
  analytic per-model hypothesis remaining.
-/

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

/-! ## The supermartingale floor, bundled -/

/-- The inputs of `ItoInterface.ofSupermartingale` as a structure, so that
per-entry-state families can be quantified. The two analytic fields are
`hZ` (the discounted certificate process is a supermartingale) and `hτ`
(the exit time's stopping-time measurability family); every other field is
the pathwise bookkeeping the sampling interface already carried. -/
structure ItoSupermartingaleData (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) (x : State) where
  /-- the driving path-data space -/
  Ω : Type*
  /-- its σ-algebra -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the driving data issued from `x` -/
  P : Measure Ω
  /-- the law is a probability measure -/
  hprob : IsProbabilityMeasure P
  /-- the filtration the certificate process rides -/
  ℱ : Filtration ℝ≥0 mΩ
  /-- exit time of each path (unread on never-exiting paths) -/
  T : Ω → ℝ
  hT : ∀ ω, 0 ≤ T ω
  /-- terminator species of each path -/
  k : Ω → ExitKind
  hk : ∀ ω, k ω = ExitKind.guard ∨ k ω = ExitKind.halt
    ∨ k ω = ExitKind.live
  /-- the trajectory of each path (extended off the segment) -/
  γ : Ω → ℝ → State
  hγ : ∀ ω, Measurable (γ ω)
  hvc : ∀ ω, Continuous fun u => V (γ ω u)
  hVγ : ∀ ω u, 0 ≤ V (γ ω u)
  /-- paths start at the entry state -/
  hγ0 : ∀ ω, γ ω 0 = x
  /-- spontaneous-jump intensity along each path -/
  r : Ω → ℝ → ℝ
  hr : ∀ ω, Continuous (r ω)
  hr0 : ∀ ω u, 0 ≤ r ω u
  /-- intensity-weighted post-jump read along each path -/
  jr : Ω → ℝ → ℝ
  hjr : ∀ ω, Continuous (jr ω)
  hjr0 : ∀ ω u, 0 ≤ jr ω u
  hjr_couple : ∀ ω, ∀ u ∈ segDom (T ω) (k ω),
    ENNReal.ofReal (jr ω u)
      = ENNReal.ofReal (r ω u)
        * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ ω u, ExitKind.alarm))
  /-- the read-level disintegration of the segment law along paths -/
  hread : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
    ≤ ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
        ∂(segMeasureIto (γ ω) (r ω) (T ω) (k ω)) ∂P
  /-- analytic field 1: the certificate process is a supermartingale -/
  hZ : Supermartingale (certProcess θ V γ r jr) ℱ P
  /-- analytic field 2: the exit time's measurability family -/
  hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
    {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)}

attribute [instance] ItoSupermartingaleData.mΩ

namespace ItoSupermartingaleData

variable {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} {x : State}

/-- The bundle assembles into a full sampling interface:
`ItoInterface.ofSupermartingale`, applied. -/
noncomputable def toItoInterface (D : ItoSupermartingaleData M θ V x) :
    ItoInterface M θ V x :=
  haveI := D.hprob
  ItoInterface.ofSupermartingale M D.hT D.hk D.hγ D.hvc D.hVγ D.hr D.hr0
    D.hjr D.hjr0 D.hjr_couple D.hread D.hγ0 D.hZ D.hτ

end ItoSupermartingaleData

/-- The segment Dynkin inequality from the supermartingale floor: a model
all of whose entry states carry supermartingale bundles satisfies
`SegmentDynkin`. -/
theorem segmentDynkin_of_supermartingale (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (ItoSupermartingaleData M θ V x)) :
    SegmentDynkin M θ V :=
  segmentDynkin_of_ito M θ V hV fun x => (h x).elim fun D => ⟨D.toItoInterface⟩

/-- The pointwise stochastic/deterministic mixture: each entry state carries
either a supermartingale bundle (stochastic inter-jump motion) or
terminating Dini flow data (deterministic segments), mixed freely;
`SegmentDynkin` follows. -/
theorem segmentDynkin_of_mixed (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (ItoSupermartingaleData M θ V x)
      ∨ Nonempty (PDMPFlowFinDini M θ V x)) :
    SegmentDynkin M θ V := by
  intro x
  cases h x with
  | inl hD =>
      obtain ⟨D⟩ := hD
      exact D.toItoInterface.segD_at hV
  | inr hD =>
      obtain ⟨D⟩ := hD
      exact D.segD_at hV

/-! ## The martingale-problem presentation -/

/-- The formal drift of the discounted certificate process along a path:
with `F s = survWeight (r ω) θ s` (so `F' = (θ - r)·F`, by
`survWeight_hasDerivAt`), the process
`F s · V (γ ω s) + ∫ u in 0..s, F u · jr ω u` has formal time-derivative
`mpDrift θ V γ r jr AV s ω` whenever `AV` records the generator drift of
`s ↦ V (γ ω s)`. -/
noncomputable def mpDrift {Ω : Type*} (θ : ℝ) (V : State → ℝ)
    (γ : Ω → ℝ → State) (r jr AV : Ω → ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  survWeight (r ω) θ s * ((θ - r ω s) * V (γ ω s) + AV ω s + jr ω s)

/-- **The martingale-problem presentation of a segment.** The bookkeeping
fields are those of `ItoSupermartingaleData`; the supermartingale field is
replaced by the rawer pair of a generator-drift record `AV` (the value of
`𝒜V` along each path — *data*, tied to the process only by `hmp`) with

* `hmp` — the martingale problem for the time-extended generator, tested at
  the discounted certificate: the compensated process
  `certProcess - ∫ mpDrift` is a martingale. For an inter-jump law solving
  the martingale problem for `𝒜` this is the Dynkin-formula compensation of
  `e^{θs - ∫₀ˢ r}·V(X_s) + ∫₀ˢ e^{θu - ∫₀ᵘ r}·jr(u)du`
  (Stroock–Varadhan, Ch. 6; Liptser–Shiryaev, *Statistics of Random
  Processes*, Ch. 4);
* `hrow` — the drift row `AV + jr + θ·V∘γ ≤ r·V∘γ` pointwise at nonnegative
  times, i.e. `𝒜V + λ(JV - V) + θV ≤ 0` in generator form;

plus the adaptedness and integrability side conditions consumed by
`OptionalSamplingRC.supermartingale_of_compensator_nonpos`. -/
structure MPFlow (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) (x : State) where
  /-- the driving path-data space -/
  Ω : Type*
  /-- its σ-algebra -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the driving data issued from `x` -/
  P : Measure Ω
  /-- the law is a probability measure -/
  hprob : IsProbabilityMeasure P
  /-- the filtration the certificate process rides -/
  ℱ : Filtration ℝ≥0 mΩ
  /-- exit time of each path (unread on never-exiting paths) -/
  T : Ω → ℝ
  hT : ∀ ω, 0 ≤ T ω
  /-- terminator species of each path -/
  k : Ω → ExitKind
  hk : ∀ ω, k ω = ExitKind.guard ∨ k ω = ExitKind.halt
    ∨ k ω = ExitKind.live
  /-- the trajectory of each path (extended off the segment) -/
  γ : Ω → ℝ → State
  hγ : ∀ ω, Measurable (γ ω)
  hvc : ∀ ω, Continuous fun u => V (γ ω u)
  hVγ : ∀ ω u, 0 ≤ V (γ ω u)
  /-- paths start at the entry state -/
  hγ0 : ∀ ω, γ ω 0 = x
  /-- spontaneous-jump intensity along each path -/
  r : Ω → ℝ → ℝ
  hr : ∀ ω, Continuous (r ω)
  hr0 : ∀ ω u, 0 ≤ r ω u
  /-- intensity-weighted post-jump read along each path -/
  jr : Ω → ℝ → ℝ
  hjr : ∀ ω, Continuous (jr ω)
  hjr0 : ∀ ω u, 0 ≤ jr ω u
  hjr_couple : ∀ ω, ∀ u ∈ segDom (T ω) (k ω),
    ENNReal.ofReal (jr ω u)
      = ENNReal.ofReal (r ω u)
        * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ ω u, ExitKind.alarm))
  /-- the read-level disintegration of the segment law along paths -/
  hread : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
    ≤ ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
        ∂(segMeasureIto (γ ω) (r ω) (T ω) (k ω)) ∂P
  /-- the exit time's measurability family -/
  hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
    {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)}
  /-- the generator drift of the certificate along each path — data -/
  AV : Ω → ℝ → ℝ
  hAVc : ∀ ω, Continuous (AV ω)
  /-- the martingale problem, tested at the discounted certificate -/
  hmp : Martingale
    (fun (t : ℝ≥0) (ω : Ω) => certProcess θ V γ r jr t ω
      - ∫ s in (0:ℝ)..(t:ℝ), mpDrift θ V γ r jr AV s ω) ℱ P
  /-- the drift row: `𝒜V + λ(JV - V) + θV ≤ 0` in the `jr` reading -/
  hrow : ∀ ω, ∀ u : ℝ, 0 ≤ u →
    AV ω u + jr ω u + θ * V (γ ω u) ≤ r ω u * V (γ ω u)
  /-- the compensator is adapted -/
  hGadp : Adapted ℱ
    (fun (t : ℝ≥0) (ω : Ω) =>
      ∫ s in (0:ℝ)..(t:ℝ), mpDrift θ V γ r jr AV s ω)
  /-- the certificate process is integrable at each time -/
  hCint : ∀ t : ℝ≥0, Integrable (certProcess θ V γ r jr t) P

attribute [instance] MPFlow.mΩ

namespace MPFlow

variable {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} {x : State}

/-- The drift row makes the formal drift nonpositive at nonnegative times. -/
lemma mpDrift_nonpos (D : MPFlow M θ V x) (ω : D.Ω) {s : ℝ} (hs : 0 ≤ s) :
    mpDrift θ V D.γ D.r D.jr D.AV s ω ≤ 0 := by
  have hrow := D.hrow ω s hs
  simp only [mpDrift]
  exact mul_nonpos_of_nonneg_of_nonpos (survWeight_pos θ s).le (by linarith)

/-- The discounted certificate process along a martingale-problem
presentation is a supermartingale: the compensated process is a martingale
by `hmp`, and the compensation density is nonpositive by the drift row. -/
theorem certProcess_supermartingale (D : MPFlow M θ V x) :
    Supermartingale (certProcess θ V D.γ D.r D.jr) D.ℱ D.P := by
  haveI := D.hprob
  refine OptionalSamplingRC.supermartingale_of_compensator_nonpos
    (certProcess θ V D.γ D.r D.jr)
    (fun s ω => mpDrift θ V D.γ D.r D.jr D.AV s ω)
    D.hmp D.hGadp D.hCint (fun ω t => ?_) (fun ω s hs => D.mpDrift_nonpos ω hs)
  have hc : Continuous fun s => mpDrift θ V D.γ D.r D.jr D.AV s ω := by
    simp only [mpDrift]
    exact (survWeight_continuous (D.hr ω) θ).mul
      ((((continuous_const.sub (D.hr ω)).mul (D.hvc ω)).add
        (D.hAVc ω)).add (D.hjr ω))
  exact hc.intervalIntegrable 0 t

/-- A martingale-problem presentation yields a supermartingale bundle. -/
noncomputable def toItoSupermartingaleData (D : MPFlow M θ V x) :
    ItoSupermartingaleData M θ V x where
  Ω := D.Ω
  mΩ := D.mΩ
  P := D.P
  hprob := D.hprob
  ℱ := D.ℱ
  T := D.T
  hT := D.hT
  k := D.k
  hk := D.hk
  γ := D.γ
  hγ := D.hγ
  hvc := D.hvc
  hVγ := D.hVγ
  hγ0 := D.hγ0
  r := D.r
  hr := D.hr
  hr0 := D.hr0
  jr := D.jr
  hjr := D.hjr
  hjr0 := D.hjr0
  hjr_couple := D.hjr_couple
  hread := D.hread
  hZ := D.certProcess_supermartingale
  hτ := D.hτ

end MPFlow

/-- **The segment Dynkin inequality at the martingale-problem profile**: a
model all of whose entry states carry martingale-problem presentations
satisfies `SegmentDynkin M θ V`. This is the general continuous-time
(jump-diffusion) discharge: the three classically missing ingredients enter
as the presentation's `AV`/`hmp` (generator domains — the generator is data,
tested at `V` by the martingale property), `hvc` (path regularity), and the
optional-sampling floor of `OptionalSamplingRC` (stopping at the segment's
exit time). -/
theorem segmentDynkin_of_mp (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (MPFlow M θ V x)) :
    SegmentDynkin M θ V :=
  segmentDynkin_of_supermartingale M θ V hV fun x =>
    (h x).elim fun D => ⟨D.toItoSupermartingaleData⟩

/-- Per-state mixture of all three presentations: martingale-problem,
supermartingale bundle, or deterministic (Dini) flow data. -/
theorem segmentDynkin_of_mp_mixed (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (MPFlow M θ V x)
      ∨ Nonempty (ItoSupermartingaleData M θ V x)
      ∨ Nonempty (PDMPFlowFinDini M θ V x)) :
    SegmentDynkin M θ V := by
  intro x
  rcases h x with hD | hD | hD
  · obtain ⟨D⟩ := hD
    exact D.toItoSupermartingaleData.toItoInterface.segD_at hV
  · obtain ⟨D⟩ := hD
    exact D.toItoInterface.segD_at hV
  · obtain ⟨D⟩ := hD
    exact D.segD_at hV

/-- The `ε = 0` ranking rows of the Streett/recurrence bundle at the
martingale-problem profile. The strict-decrement rows (`ε > 0`) quantify
progress per segment, which the supermartingale property alone cannot see;
they are discharged from strict presentations by
`rankingSegmentDynkin_of_mp_strict` below. -/
theorem rankingSegmentDynkin_of_mp (M : SegmentModel State)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (MPFlow M 0 V x)) (Sc : Set State) :
    RankingSegmentDynkin M Sc V 0 :=
  rankingSegmentDynkin_of_segmentDynkin (segmentDynkin_of_mp M 0 V hV h) Sc

/-! ## The no-alarm case from the undiscounted martingale problem

For segments with no spontaneous jumps (`r = jr = 0` — diffusion or other
Markov motion between forced jumps), the presentation can be rawer still:
the martingale problem for `𝒜` tested at `V` itself, with no reference to
the discounted certificate. The exponential discounting is then *performed*
by `OptionalSamplingRC.supermartingale_exp_discount`. -/

@[simp] lemma cumInt_zero_fun (t : ℝ) : cumInt (fun _ => (0:ℝ)) t = 0 := by
  simp [cumInt]

@[simp] lemma survWeight_zero_fun (θ t : ℝ) :
    survWeight (fun _ => (0:ℝ)) θ t = Real.exp (θ * t) := by
  simp [survWeight]

@[simp] lemma jint_zero_fun (r : ℝ → ℝ) (θ t : ℝ) :
    jint r (fun _ => (0:ℝ)) θ t = 0 := by
  simp [jint]

omit [MeasurableSpace State] in
/-- On a no-alarm segment the discounted certificate process is the
clock-weighted certificate along the path. -/
lemma certProcess_zero_rate {Ω : Type*} (θ : ℝ) (V : State → ℝ)
    (γ : Ω → ℝ → State) :
    certProcess θ V γ (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
      = fun (t : ℝ≥0) (ω : Ω) => Real.exp (θ * (t:ℝ)) * V (γ ω (t:ℝ)) := by
  funext t ω
  simp [certProcess]

/-- **The no-alarm martingale-problem constructor.** A segment with no
spontaneous jumps, whose inter-jump motion is presented by the undiscounted
martingale problem — `fun t ω => V (γ ω t) - ∫ s in 0..t, AV ω s` is a
martingale — with the drift row `AV + θ·V∘γ ≤ 0`, uniform bounds, and the
adaptedness/measurability side conditions, yields a supermartingale bundle:
the discounting is performed by
`OptionalSamplingRC.supermartingale_exp_discount` at rate `-θ`. -/
noncomputable def ItoSupermartingaleData.ofMPNoAlarm
    {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} {x : State}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (hprob : IsProbabilityMeasure P) (ℱ : Filtration ℝ≥0 mΩ)
    (T : Ω → ℝ) (hT : ∀ ω, 0 ≤ T ω) (k : Ω → ExitKind)
    (hk : ∀ ω, k ω = ExitKind.guard ∨ k ω = ExitKind.halt
      ∨ k ω = ExitKind.live)
    (γ : Ω → ℝ → State) (hγ : ∀ ω, Measurable (γ ω))
    (hvc : ∀ ω, Continuous fun u => V (γ ω u))
    (hVγ : ∀ ω u, 0 ≤ V (γ ω u)) (hγ0 : ∀ ω, γ ω 0 = x)
    (hread : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
      ≤ ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
          ∂(segMeasureIto (γ ω) (fun _ => (0:ℝ)) (T ω) (k ω)) ∂P)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
      {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)})
    (AV : Ω → ℝ → ℝ) (C : ℝ)
    (hVadp : Adapted ℱ (fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ))))
    (hVb : ∀ (t : ℝ≥0) (ω : Ω), |V (γ ω (t:ℝ))| ≤ C)
    (hAVmeas : Measurable
      (Function.uncurry fun (s : ℝ≥0) (ω : Ω) => AV ω (s:ℝ)))
    (hAVb : ∀ (t : ℝ≥0) (ω : Ω), |AV ω (t:ℝ)| ≤ C)
    (hmpV : Martingale
      (fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ))
        - ∫ s in (0:ℝ)..(t:ℝ), AV ω s) ℱ P)
    (hrow0 : ∀ ω, ∀ u : ℝ, 0 ≤ u → AV ω u + θ * V (γ ω u) ≤ 0) :
    ItoSupermartingaleData M θ V x where
  Ω := Ω
  mΩ := mΩ
  P := P
  hprob := hprob
  ℱ := ℱ
  T := T
  hT := hT
  k := k
  hk := hk
  γ := γ
  hγ := hγ
  hvc := hvc
  hVγ := hVγ
  hγ0 := hγ0
  r := fun _ _ => 0
  hr := fun _ => continuous_const
  hr0 := fun _ _ => le_rfl
  jr := fun _ _ => 0
  hjr := fun _ => continuous_const
  hjr0 := fun _ _ => le_rfl
  hjr_couple := fun ω u _ => by simp
  hread := hread
  hZ := by
    haveI := hprob
    have hmart : Martingale
        (fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ))
          - ∫ s in (0:ℝ)..(t:ℝ),
              (fun (u : ℝ≥0) (ω' : Ω) => AV ω' (u:ℝ)) s.toNNReal ω) ℱ P := by
      have heq : (fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ))
            - ∫ s in (0:ℝ)..(t:ℝ),
                (fun (u : ℝ≥0) (ω' : Ω) => AV ω' (u:ℝ)) s.toNNReal ω)
          = fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ))
            - ∫ s in (0:ℝ)..(t:ℝ), AV ω s := by
        funext t ω
        congr 1
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
        show AV ω ((s.toNNReal : ℝ≥0) : ℝ) = AV ω s
        rw [Real.coe_toNNReal s hs.1]
      rw [heq]
      exact hmpV
    have hsm := OptionalSamplingRC.supermartingale_exp_discount
      (fun (t : ℝ≥0) (ω : Ω) => V (γ ω (t:ℝ)))
      (fun (u : ℝ≥0) (ω : Ω) => AV ω (u:ℝ)) (-θ) C
      hVadp (fun ω => (hvc ω).comp NNReal.continuous_coe) hVb
      hAVmeas hAVb hmart
      (fun t ω => by
        have h := hrow0 ω (t:ℝ) (NNReal.coe_nonneg t)
        have : (-θ) * V (γ ω (t:ℝ)) = -(θ * V (γ ω (t:ℝ))) := by ring
        rw [this]
        linarith)
    have hpe : (fun (t : ℝ≥0) (ω : Ω) =>
          Real.exp (-(-θ) * (t:ℝ)) * V (γ ω (t:ℝ)))
        = certProcess θ V γ (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) := by
      rw [certProcess_zero_rate]
      funext t ω
      congr 2
      ring
    rw [← hpe]
    exact hsm
  hτ := hτ

/-! ## The battery theorems at the martingale-problem profile

Each of the following is the corresponding segment-skeleton battery theorem
with the `SegmentDynkin` hypothesis discharged from a per-entry-state
martingale-problem presentation; every other hypothesis is unchanged. -/

variable {M : SegmentModel State}

/-- Safety (avoidance) at the martingale-problem profile: the probability
that the segment skeleton ever enters the bad set is at most `V x`. -/
theorem sound_GSHS_safety_mp [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {U : Set State} (hV : Measurable V) (hU : MeasurableSet U)
    (hmp : ∀ x : State, Nonempty (MPFlow M 0 V x))
    (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, V y ≤ C)
    (hFloor : ∀ y ∈ U, 1 ≤ V y) (x : State) :
    Battery.pathMeasure (skel M) (SkelState.alive x)
        {ω | ∃ n, ω n ∈ skelBad U}
      ≤ ENNReal.ofReal (V x) :=
  sound_GSHS_safety hV hU (segmentDynkin_of_mp M 0 V hV hmp) hForce hNonneg
    hC0 hVC hFloor x

/-- The safety battery at the martingale-problem profile. -/
theorem sound_GSHS_safety_battery_mp
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {U : Set State} {p thr : ℝ}
    (hV : Measurable V) (hU : MeasurableSet U)
    (hmp : ∀ x : State, Nonempty (MPFlow M 0 V x))
    (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, V y ≤ C)
    (hFloor : ∀ y ∈ U, 1 ≤ V y)
    (hΘ : p + thr ≤ 1) (x : State) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ n, ω n ∉ skelBad U} :=
  sound_GSHS_safety_battery hV hU (segmentDynkin_of_mp M 0 V hV hmp) hForce
    hNonneg hC0 hVC hFloor hΘ x hthr

/-- The deadline reach bound at the martingale-problem profile. -/
theorem sound_GSHS_deadline_mp [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0}
    (hV : Measurable V) (hθ : 0 ≤ θ)
    (hmp : ∀ x : State, Nonempty (MPFlow M θ V x))
    (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (hε : 0 < ε) (hFloor : ∀ y, ε ≤ V y) (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, T < tclock (ω n)}
      ≤ ENNReal.ofReal (Real.exp (-(θ * T)) * V x / ε) :=
  sound_GSHS_deadline hV hθ (segmentDynkin_of_mp M θ V hV hmp) hForce
    hNonneg hε hFloor x

/-- The deadline battery at the martingale-problem profile. -/
theorem sound_GSHS_deadline_battery_mp
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε p thr : ℝ} {T : ℝ≥0}
    (hV : Measurable V) (hθ : 0 ≤ θ)
    (hmp : ∀ x : State, Nonempty (MPFlow M θ V x))
    (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (hε : 0 < ε) (hFloor : ∀ y, ε ≤ V y)
    (hΘ : p + Real.exp (-(θ * T)) * thr / ε ≤ 1) (x : State)
    (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
      {ω | ∀ n, tclock (ω n) ≤ T} :=
  sound_GSHS_deadline_battery hV hθ (segmentDynkin_of_mp M θ V hV hmp)
    hForce hNonneg hε hFloor hΘ x hthr

/-- Timed avoidance at the martingale-problem profile. -/
theorem sound_GSHS_avoid_timed_mp
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va : State → ℝ} {Us : Set State}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hmpa : ∀ x : State, Nonempty (MPFlow M 0 Va x))
    (hForce : ForcedNonexpansion M Va)
    (hNonneg : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloor : ∀ y ∈ Us, 1 ≤ Va y) (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, ω n ∈ tbadIn Us}
      ≤ ENNReal.ofReal (Va x) :=
  sound_GSHS_avoid_timed hVa hUs (segmentDynkin_of_mp M 0 Va hVa hmpa)
    hForce hNonneg hC0 hVC hFloor x

/-- The timed until reach bound at the martingale-problem profile: both the
avoidance certificate (rate `0`) and the deadline certificate (rate `θ`)
are presented by martingale problems. -/
theorem sound_GSHS_until_mp [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va Vd : State → ℝ} {Us : Set State} {θ ε : ℝ} {T : ℝ≥0}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hmpa : ∀ x : State, Nonempty (MPFlow M 0 Va x))
    (hForcea : ForcedNonexpansion M Va)
    (hNonnega : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloora : ∀ y ∈ Us, 1 ≤ Va y)
    (hVd : Measurable Vd) (hθ : 0 ≤ θ)
    (hmpd : ∀ x : State, Nonempty (MPFlow M θ Vd x))
    (hForced : ForcedNonexpansion M Vd)
    (hNonnegd : NonnegV Vd) (hε : 0 < ε) (hFloord : ∀ y, ε ≤ Vd y)
    (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)}
      ≤ ENNReal.ofReal (Va x)
        + ENNReal.ofReal (Real.exp (-(θ * T)) * Vd x / ε) :=
  sound_GSHS_until hVa hUs (segmentDynkin_of_mp M 0 Va hVa hmpa) hForcea
    hNonnega hC0 hVC hFloora hVd hθ (segmentDynkin_of_mp M θ Vd hVd hmpd)
    hForced hNonnegd hε hFloord x

/-- The Streett/recurrence bundle at the martingale-problem profile,
mixed ranking scope: the confinement certificate `V₀` and every pair's
ranking certificate `W i` are presented by martingale problems, which
discharges all the `ε = 0` ranking rows. The strict-decrement rows
`hSegDWR` (`ε i > 0`) stay hypotheses *of this theorem*, for models that
discharge them by other means; `sound_GSHS_streett_bundle_mp_strict` below
discharges them too, from strict presentations (`MPFlowStrict`) on the
requested-but-ungranted region. -/
theorem sound_GSHS_streett_bundle_mp
    {ι : Type*} [Countable ι]
    {D Dbar U : Set State} {V₀ : State → ℝ} {Rq G : ι → Set State}
    {W : ι → State → ℝ} {p thr C₀ : ℝ} {ε C : ι → ℝ} {x : State}
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hmp₀ : ∀ x : State, Nonempty (MPFlow M 0 V₀ x))
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hmpW : ∀ i, ∀ x : State, Nonempty (MPFlow M 0 (W i) x))
    (hSegDWR : ∀ i, RankingSegmentDynkin M (((D \ U) ∩ Rq i) \ G i) (W i) (ε i))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} :=
  sound_GSHS_streett_bundle hD hDbar hU hV₀ hRq hG hW hΘ hDsub
    hLive hHalt hReset (rankingSegmentDynkin_of_mp M V₀ hV₀ hmp₀ _)
    hForce₀ hNonneg₀ hC₀0 hV₀C hFloor₀ hε
    (fun i => rankingSegmentDynkin_of_mp M (W i) (hW i) (hmpW i) _)
    hSegDWR hForceW hNonnegW hC0 hWC hx hthr

/-- The until battery at the martingale-problem profile. -/
theorem sound_GSHS_until_battery_mp
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va Vd : State → ℝ} {Us : Set State} {θ ε p thra thrd : ℝ} {T : ℝ≥0}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hmpa : ∀ x : State, Nonempty (MPFlow M 0 Va x))
    (hForcea : ForcedNonexpansion M Va)
    (hNonnega : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloora : ∀ y ∈ Us, 1 ≤ Va y)
    (hVd : Measurable Vd) (hθ : 0 ≤ θ)
    (hmpd : ∀ x : State, Nonempty (MPFlow M θ Vd x))
    (hForced : ForcedNonexpansion M Vd)
    (hNonnegd : NonnegV Vd) (hε : 0 < ε) (hFloord : ∀ y, ε ≤ Vd y)
    (hΘ : p + (thra + Real.exp (-(θ * T)) * thrd / ε) ≤ 1)
    (x : State) (hthra : Va x ≤ thra) (hthrd : Vd x ≤ thrd) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
      {ω | ∀ n, ω n ∉ tbadIn Us ∧ tclock (ω n) ≤ T} :=
  sound_GSHS_until_battery hVa hUs (segmentDynkin_of_mp M 0 Va hVa hmpa)
    hForcea hNonnega hC0 hVC hFloora hVd hθ
    (segmentDynkin_of_mp M θ Vd hVd hmpd) hForced hNonnegd hε hFloord
    hΘ x hthra hthrd

/-! ## The strict (ranking) rows from a pathwise progress row

The `ε > 0` ranking rows of the Streett/recurrence bundle quantify progress
per segment. At the martingale-problem profile they are discharged from one
additional presentation field — a **pathwise progress row**: along every
path, the accumulated generator drift of the discounted certificate reaches
`≤ -ε` by some finite sample time (for exit paths the natural witness is
the exit time itself, making the row `∫₀^{T ω} mpDrift ≤ -ε`; the intended
certificate-side derivation is a strict drift `≤ -δ` together with a
minimum dwell time `t_min`, giving `ε = δ · t_min`).

Mechanism: split the stopped certificate as martingale part plus drift
accumulation, `cP (ρₙ) = Mart (ρₙ) + Dₙ`. The martingale part is a
*nonnegative* right-continuous supermartingale, so the landed upper-bound
optional sampling gives `E[Mart (ρₙ)] ≤ V x`; the drift accumulations `Dₙ`
are nonincreasing and eventually `≤ -ε` pathwise, so dominated convergence
on the truncations `max (Dₙ, -ε) ∈ [-ε, 0]` gives
`liminf E[cP (ρₙ)] ≤ V x - ε`, which the Fatou/liminf chain of
`ItoInterface.segD_at` carries to the outcome read. (The lower-bound
optional-sampling lemma `OptionalSamplingRC.integral_stoppedValue_min_ge`,
built alongside this transport, turns out not to bind in it: only the
upper bound on the martingale part is consumed.) -/

/-- The primitive of a continuous function that is nonpositive on
`[0, ∞)` is antitone over nonnegative upper limits. -/
lemma integral_primitive_anti {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, 0 ≤ u → f u ≤ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in (0:ℝ)..b, f s ≤ ∫ s in (0:ℝ)..a, f s := by
  have hint : ∀ c d : ℝ, IntervalIntegrable f volume c d :=
    fun c d => hf.intervalIntegrable c d
  have hsplit : (∫ s in (0:ℝ)..a, f s) + ∫ s in a..b, f s
      = ∫ s in (0:ℝ)..b, f s :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
  have htail : (∫ s in a..b, f s) ≤ 0 := by
    have h : (0:ℝ) ≤ ∫ s in a..b, -f s :=
      intervalIntegral.integral_nonneg hab
        (fun u hu => neg_nonneg.mpr (hf0 u (le_trans ha hu.1)))
    rw [intervalIntegral.integral_neg] at h
    linarith
  linarith

/-- **The strict liminf bound at the martingale-problem profile.** For a
presentation `D : MPFlow M θ V x` whose drift certificate satisfies the
pathwise progress row at level `ε ≥ 0`, the sampled reads of the segment
satisfy `liminf ∫⁻ sampledRead ≤ ofReal (V x - ε)` — and `ε ≤ V x` comes
for free (the certificate cannot promise more progress than it has). -/
theorem MPFlow.liminf_lintegral_sampledRead_le
    {θ : ℝ} {V : State → ℝ} {x : State}
    (D : MPFlow M θ V x) {ε : ℝ} (hε : 0 ≤ ε)
    (hprog : ∀ ω, ∃ t : ℝ, 0 ≤ t ∧
      ∫ s in (0:ℝ)..(stopClip (D.T ω) (D.k ω) t),
        mpDrift θ V D.γ D.r D.jr D.AV s ω ≤ -ε) :
    ε ≤ V x ∧
      Filter.liminf (fun n : ℕ =>
          ∫⁻ ω, sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
            ∂D.P) Filter.atTop
        ≤ ENNReal.ofReal (V x - ε) := by
  haveI := D.hprob
  -- nonemptiness of the path space, and `0 ≤ V x`
  have hΩ : Nonempty D.Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact zero_ne_one (α := ℝ≥0∞) (by
      calc (0 : ℝ≥0∞) = D.P Set.univ := by
            rw [Set.univ_eq_empty_iff.mpr hne]; simp
        _ = 1 := measure_univ)
  have hVx0 : 0 ≤ V x := by
    obtain ⟨ω⟩ := hΩ
    have h := D.hVγ ω 0
    rwa [D.hγ0 ω] at h
  -- the drift along paths: continuity and sign of its primitive
  have hdc : ∀ ω, Continuous fun s : ℝ =>
      mpDrift θ V D.γ D.r D.jr D.AV s ω := by
    intro ω
    simp only [mpDrift]
    exact (survWeight_continuous (D.hr ω) θ).mul
      ((((continuous_const.sub (D.hr ω)).mul (D.hvc ω)).add
        (D.hAVc ω)).add (D.hjr ω))
  have hDnonpos : ∀ ω, ∀ b : ℝ, 0 ≤ b →
      (∫ s in (0:ℝ)..b, mpDrift θ V D.γ D.r D.jr D.AV s ω) ≤ 0 := by
    intro ω b hb
    have h : (0:ℝ) ≤ ∫ s in (0:ℝ)..b, -mpDrift θ V D.γ D.r D.jr D.AV s ω :=
      intervalIntegral.integral_nonneg hb
        (fun u hu => neg_nonneg.mpr (D.mpDrift_nonpos ω hu.1))
    rw [intervalIntegral.integral_neg] at h
    linarith
  -- the certificate process: nonneg, supermartingale, right-continuous
  have hcPnn : ∀ (s : ℝ≥0) ω, 0 ≤ certProcess θ V D.γ D.r D.jr s ω :=
    fun s ω =>
      add_nonneg (mul_nonneg (survWeight_pos θ _).le (D.hVγ ω _))
        (intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun u _ =>
          mul_nonneg (survWeight_pos θ u).le (D.hjr0 ω u))
  have hcPsm := D.certProcess_supermartingale
  have hcPrc : ∀ ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => certProcess θ V D.γ D.r D.jr u ω)
        (Set.Ici s) s := by
    intro ω s
    have hF : Continuous fun u : ℝ =>
        survWeight (D.r ω) θ u * V (D.γ ω u) + jint (D.r ω) (D.jr ω) θ u :=
      ((survWeight_continuous (D.hr ω) θ).mul (D.hvc ω)).add
        (continuous_iff_continuousAt.2 fun u =>
          (jint_hasDerivAt (D.hr ω) (D.hjr ω) θ u).continuousAt)
    exact (hF.comp NNReal.continuous_coe).continuousWithinAt
  -- the compensated martingale: nonneg, supermartingale, right-continuous
  set Mp : ℝ≥0 → D.Ω → ℝ := fun t ω => certProcess θ V D.γ D.r D.jr t ω
    - ∫ s in (0:ℝ)..(t:ℝ), mpDrift θ V D.γ D.r D.jr D.AV s ω with hMp
  have hMmart : Martingale Mp D.ℱ D.P := D.hmp
  have hMsm : Supermartingale Mp D.ℱ D.P := hMmart.supermartingale
  have hMnn : ∀ (s : ℝ≥0) ω, 0 ≤ Mp s ω := by
    intro s ω
    have h1 := hcPnn s ω
    have h2 := hDnonpos ω (s:ℝ) (NNReal.coe_nonneg s)
    simp only [hMp]
    linarith
  have hMrc : ∀ ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => Mp u ω) (Set.Ici s) s := by
    intro ω s
    have hprim : Continuous fun b : ℝ =>
        ∫ v in (0:ℝ)..b, mpDrift θ V D.γ D.r D.jr D.AV v ω :=
      continuous_iff_continuousAt.2 fun b =>
        (intervalIntegral.integral_hasDerivAt_right
          ((hdc ω).intervalIntegrable _ _)
          ((hdc ω).stronglyMeasurableAtFilter _ _)
          (hdc ω).continuousAt).continuousAt
    exact (hcPrc ω s).sub
      ((hprim.comp NNReal.continuous_coe).continuousWithinAt)
  have hM0 : ∀ ω, Mp 0 ω = V x := by
    intro ω
    have h1 : certProcess θ V D.γ D.r D.jr 0 ω = V x := by
      simp [certProcess, jint, D.hγ0 ω]
    simp only [hMp]
    rw [h1]
    simp
  -- the stopped time at sample horizon `n`, and the stopped drift
  set ρ : ℕ → D.Ω → ℝ≥0 := fun n ω =>
    min (OptionalSamplingRC.ennrealTrunc (exitDebut D.T D.k)
      (Real.toNNReal (n:ℝ)) ω) (Real.toNNReal (n:ℝ)) with hρ
  set Dn : ℕ → D.Ω → ℝ := fun n ω =>
    ∫ s in (0:ℝ)..((ρ n ω : ℝ≥0) : ℝ), mpDrift θ V D.γ D.r D.jr D.AV s ω
    with hDn
  set En : ℕ → D.Ω → ℝ := fun n ω => max (Dn n ω) (-ε) with hEn
  have hρcoe : ∀ (n : ℕ) ω, ((ρ n ω : ℝ≥0) : ℝ)
      = stopClip (D.T ω) (D.k ω) (n : ℝ) := by
    intro n ω
    simp only [hρ]
    exact coe_min_exitTrunc_eq_stopClip D.hT (Nat.cast_nonneg n) ω
  have hτfam : ∀ n : ℕ, ∀ s : ℝ≥0, MeasurableSet[D.ℱ s]
      {ω | OptionalSamplingRC.ennrealTrunc (exitDebut D.T D.k)
        (Real.toNNReal (n:ℝ)) ω ≤ s} :=
    fun n => exitTrunc_family (ℱ := D.ℱ) D.hτ (Real.toNNReal (n:ℝ))
  -- measurability of the stopped processes
  have hCmeas : ∀ n : ℕ, AEMeasurable
      (fun ω => certProcess θ V D.γ D.r D.jr (ρ n ω) ω) D.P := fun n =>
    OptionalSamplingRC.aemeasurable_stoppedValue_min
      (certProcess θ V D.γ D.r D.jr) hcPsm hcPrc _ (hτfam n) _
  have hMmeas : ∀ n : ℕ, AEMeasurable (fun ω => Mp (ρ n ω) ω) D.P := fun n =>
    OptionalSamplingRC.aemeasurable_stoppedValue_min Mp hMsm hMrc _
      (hτfam n) _
  -- optional sampling (upper bound) on the martingale part
  have hMlint : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Mp (ρ n ω) ω) ∂D.P ≤ ENNReal.ofReal (V x) := by
    intro n
    have hOS := OptionalSamplingRC.lintegral_stoppedValue_min_le
      Mp hMsm hMnn hMrc
      (fun ω => OptionalSamplingRC.ennrealTrunc (exitDebut D.T D.k)
        (Real.toNNReal (n:ℝ)) ω)
      (hτfam n) (Real.toNNReal (n:ℝ))
    calc ∫⁻ ω, ENNReal.ofReal (Mp (ρ n ω) ω) ∂D.P
        ≤ ∫⁻ ω, ENNReal.ofReal (Mp 0 ω) ∂D.P := hOS
      _ = ENNReal.ofReal (V x) := by
          simp only [hM0]
          simp [lintegral_const]
  -- integrability of the stopped processes
  have hMint : ∀ n : ℕ, Integrable (fun ω => Mp (ρ n ω) ω) D.P := by
    intro n
    refine ⟨(hMmeas n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => hMnn _ _)]
    exact lt_of_le_of_lt (hMlint n) ENNReal.ofReal_lt_top
  have hMreal : ∀ n : ℕ, ∫ ω, Mp (ρ n ω) ω ∂D.P ≤ V x := by
    intro n
    have h1 : ENNReal.ofReal (∫ ω, Mp (ρ n ω) ω ∂D.P)
        = ∫⁻ ω, ENNReal.ofReal (Mp (ρ n ω) ω) ∂D.P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hMint n)
        (Filter.Eventually.of_forall fun ω => hMnn _ _)
    have h2 := hMlint n
    rw [← h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hVx0).mp h2
  have hsplit : ∀ (n : ℕ) ω, certProcess θ V D.γ D.r D.jr (ρ n ω) ω
      = Mp (ρ n ω) ω + Dn n ω := by
    intro n ω
    simp only [hMp, hDn]
    ring
  have hcPle : ∀ (n : ℕ) ω,
      certProcess θ V D.γ D.r D.jr (ρ n ω) ω ≤ Mp (ρ n ω) ω := by
    intro n ω
    have h1 := hDnonpos ω ((ρ n ω : ℝ≥0):ℝ) (NNReal.coe_nonneg _)
    have h2 := hsplit n ω
    simp only [hDn] at h2
    linarith
  have hCint : ∀ n : ℕ, Integrable
      (fun ω => certProcess θ V D.γ D.r D.jr (ρ n ω) ω) D.P := by
    intro n
    refine (hMint n).mono' (hCmeas n).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hcPnn _ _)]
    exact hcPle n ω
  have hDint : ∀ n : ℕ, Integrable (Dn n) D.P := by
    intro n
    have h : Dn n = fun ω =>
        certProcess θ V D.γ D.r D.jr (ρ n ω) ω - Mp (ρ n ω) ω := by
      funext ω
      have := hsplit n ω
      linarith
    rw [h]
    exact (hCint n).sub (hMint n)
  -- the ε-truncated drift accumulations: bounded, integrable, → -ε
  have hDn_nonpos : ∀ (n : ℕ) ω, Dn n ω ≤ 0 := by
    intro n ω
    simp only [hDn]
    exact hDnonpos ω _ (NNReal.coe_nonneg _)
  have hEn_bound : ∀ (n : ℕ) ω, ‖En n ω‖ ≤ ε := by
    intro n ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · simp only [hEn]
      exact le_max_right _ _
    · simp only [hEn]
      exact max_le ((hDn_nonpos n ω).trans hε) (neg_le_self hε)
  have hEmeas : ∀ n : ℕ, AEStronglyMeasurable (En n) D.P := by
    intro n
    have hd : AEMeasurable (Dn n) D.P :=
      (hDint n).aestronglyMeasurable.aemeasurable
    exact (hd.max aemeasurable_const).aestronglyMeasurable
  have hEint : ∀ n : ℕ, Integrable (En n) D.P := fun n =>
    (integrable_const ε).mono' (hEmeas n)
      (Filter.Eventually.of_forall (hEn_bound n))
  have hEn_tendsto : ∀ ω, Filter.Tendsto (fun n : ℕ => En n ω)
      Filter.atTop (nhds (-ε)) := by
    intro ω
    obtain ⟨t₀, ht₀0, ht₀⟩ := hprog ω
    have hev : (fun n : ℕ => En n ω) =ᶠ[Filter.atTop] fun _ => -ε := by
      refine Filter.eventually_atTop.2 ⟨⌈t₀⌉₊, fun n hn => ?_⟩
      have htn : t₀ ≤ (n : ℝ) := (Nat.le_ceil t₀).trans (Nat.cast_le.2 hn)
      have hDle : Dn n ω ≤ -ε := by
        simp only [hDn]
        rw [hρcoe n ω]
        calc ∫ s in (0:ℝ)..(stopClip (D.T ω) (D.k ω) (n:ℝ)),
              mpDrift θ V D.γ D.r D.jr D.AV s ω
            ≤ ∫ s in (0:ℝ)..(stopClip (D.T ω) (D.k ω) t₀),
              mpDrift θ V D.γ D.r D.jr D.AV s ω :=
              integral_primitive_anti (hdc ω)
                (fun u hu => D.mpDrift_nonpos ω hu)
                (stopClip_nonneg (D.hT ω) _ ht₀0)
                (stopClip_mono _ _ htn)
          _ ≤ -ε := ht₀
      simp only [hEn]
      exact max_eq_right hDle
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫ ω, En n ω ∂D.P)
      Filter.atTop (nhds (-ε)) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => ε) hEmeas (integrable_const ε)
      (fun n => Filter.Eventually.of_forall (hEn_bound n))
      (Filter.Eventually.of_forall hEn_tendsto)
    simpa using h
  -- the per-sample chain and the two conclusions
  have hEDle : ∀ n : ℕ, ∫ ω, Dn n ω ∂D.P ≤ ∫ ω, En n ω ∂D.P := fun n =>
    integral_mono (hDint n) (hEint n) (fun ω => by
      simp only [hEn]
      exact le_max_left _ _)
  have hc_split : ∀ n : ℕ,
      ∫ ω, certProcess θ V D.γ D.r D.jr (ρ n ω) ω ∂D.P
        = (∫ ω, Mp (ρ n ω) ω ∂D.P) + ∫ ω, Dn n ω ∂D.P := by
    intro n
    rw [← MeasureTheory.integral_add (hMint n) (hDint n)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hsplit n ω)
  have hcn_le : ∀ n : ℕ,
      ∫ ω, certProcess θ V D.γ D.r D.jr (ρ n ω) ω ∂D.P
        ≤ V x + ∫ ω, En n ω ∂D.P := by
    intro n
    rw [hc_split n]
    exact add_le_add (hMreal n) (hEDle n)
  have hcn_nonneg : ∀ n : ℕ,
      0 ≤ ∫ ω, certProcess θ V D.γ D.r D.jr (ρ n ω) ω ∂D.P :=
    fun n => integral_nonneg fun ω => hcPnn _ _
  have hbtend : Filter.Tendsto (fun n : ℕ => V x + ∫ ω, En n ω ∂D.P)
      Filter.atTop (nhds (V x - ε)) := by
    have h := hEtend.const_add (V x)
    simpa [sub_eq_add_neg] using h
  have hεVx : ε ≤ V x := by
    have h0 : (0:ℝ) ≤ V x - ε :=
      ge_of_tendsto hbtend (Filter.Eventually.of_forall fun n =>
        le_trans (hcn_nonneg n) (hcn_le n))
    linarith
  refine ⟨hεVx, ?_⟩
  have ha_eq : ∀ n : ℕ,
      (∫⁻ ω, sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
        ∂D.P)
        = ENNReal.ofReal
            (∫ ω, certProcess θ V D.γ D.r D.jr (ρ n ω) ω ∂D.P) := by
    intro n
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hCint n)
      (Filter.Eventually.of_forall fun ω => hcPnn _ _)]
    refine lintegral_congr fun ω => ?_
    exact sampledRead_eq_ofReal_certProcess D.hT D.hVγ D.hjr0
      (Nat.cast_nonneg n) ω
  have hb : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (V x + ∫ ω, En n ω ∂D.P))
      Filter.atTop (nhds (ENNReal.ofReal (V x - ε))) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hbtend
  have hle_ev : ∀ n : ℕ,
      (∫⁻ ω, sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
        ∂D.P)
        ≤ ENNReal.ofReal (V x + ∫ ω, En n ω ∂D.P) := by
    intro n
    rw [ha_eq n]
    exact ENNReal.ofReal_le_ofReal (hcn_le n)
  calc Filter.liminf (fun n : ℕ =>
        ∫⁻ ω, sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
          ∂D.P) Filter.atTop
      ≤ Filter.liminf
          (fun n : ℕ => ENNReal.ofReal (V x + ∫ ω, En n ω ∂D.P))
          Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle_ev)
    _ = ENNReal.ofReal (V x - ε) := hb.liminf_eq

/-- **The strict (ranking) segment bound at the martingale-problem
profile.** A presentation with the pathwise progress row at level `ε`
strengthens the segment Dynkin inequality at its entry state by the
additive drop `ε` — the per-state content of `RankingSegmentDynkin`. -/
theorem MPFlow.segD_ranking_at [IsSFiniteKernel M.jump]
    {θ : ℝ} {V : State → ℝ} {x : State}
    (D : MPFlow M θ V x) (hV : Measurable V) {ε : ℝ} (hε : 0 ≤ ε)
    (hprog : ∀ ω, ∃ t : ℝ, 0 ≤ t ∧
      ∫ s in (0:ℝ)..(stopClip (D.T ω) (D.k ω) t),
        mpDrift θ V D.γ D.r D.jr D.AV s ω ≤ -ε) :
    ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) + ENNReal.ofReal ε
      ≤ ENNReal.ofReal (V x) := by
  haveI := D.hprob
  obtain ⟨hεVx, hliminf⟩ := D.liminf_lintegral_sampledRead_le hε hprog
  have hmain : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
      ≤ ENNReal.ofReal (V x - ε) := by
    refine le_trans D.hread ?_
    have hpt : ∀ ω, ∫⁻ o, outcomeRead M θ V o
        ∂(segMeasureIto (D.γ ω) (D.r ω) (D.T ω) (D.k ω))
          ≤ Filter.liminf (fun n : ℕ =>
              sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n)
            Filter.atTop := fun ω =>
      lintegral_outcomeRead_segMeasureIto_le_liminf hV (D.hT ω) (D.hk ω)
        (D.hγ ω) (D.hr ω) (D.hr0 ω) (D.hjr ω) (D.hjr0 ω)
        (D.hjr_couple ω) (D.hVγ ω)
    have hmeas : ∀ n : ℕ, AEMeasurable
        (fun ω => sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω)
          n) D.P :=
      fun n => aemeasurable_sampledRead_of_supermartingale D.hT D.hvc D.hVγ
        D.hr D.hjr D.hjr0 D.certProcess_supermartingale D.hτ n
        (Nat.cast_nonneg n)
    calc ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
          ∂(segMeasureIto (D.γ ω) (D.r ω) (D.T ω) (D.k ω)) ∂D.P
        ≤ ∫⁻ ω, Filter.liminf (fun n : ℕ =>
            sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n)
            Filter.atTop ∂D.P := lintegral_mono hpt
      _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω,
            sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
              ∂D.P) Filter.atTop :=
          MeasureTheory.lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal (V x - ε) := hliminf
  calc ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) + ENNReal.ofReal ε
      ≤ ENNReal.ofReal (V x - ε) + ENNReal.ofReal ε :=
        add_le_add hmain le_rfl
    _ = ENNReal.ofReal (V x) := by
        rw [← ENNReal.ofReal_add (by linarith) hε, sub_add_cancel]

/-- **The strict martingale-problem presentation of a segment.** An
`MPFlow` together with the pathwise progress row: along every path, the
accumulated generator drift of the discounted certificate reaches `≤ -ε`
by some finite sample time. For exit paths the natural witness is the exit
time itself (`stopClip` caps the accumulation there), so the row reads
`∫₀^{T ω} mpDrift ≤ -ε`; the intended certificate-side derivation is a
strict drift bound `≤ -δ` on the segment together with a minimum dwell
time `t_min`, giving `ε = δ · t_min`. -/
structure MPFlowStrict (M : SegmentModel State) (θ : ℝ) (V : State → ℝ)
    (x : State) (ε : ℝ) extends MPFlow M θ V x where
  /-- the pathwise progress row -/
  hprog : ∀ ω, ∃ t : ℝ, 0 ≤ t ∧
    ∫ s in (0:ℝ)..(stopClip (T ω) (k ω) t),
      mpDrift θ V γ r jr AV s ω ≤ -ε

/-- **The strict-decrement ranking rows at the martingale-problem
profile.** Entry states of the ranking region carrying strict
presentations at level `ε` satisfy `RankingSegmentDynkin M Sc V ε` — the
row family that `rankingSegmentDynkin_of_mp` could not produce. Note the
quantifier: only states in `Sc` need presentations (the `ε = 0` route
quantified over all states because it factored through `SegmentDynkin`). -/
theorem rankingSegmentDynkin_of_mp_strict (M : SegmentModel State)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    {Sc : Set State} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ Sc, Nonempty (MPFlowStrict M 0 V x ε)) :
    RankingSegmentDynkin M Sc V ε := fun x hx =>
  (h x hx).elim fun D => D.toMPFlow.segD_ranking_at hV hε D.hprog

/-- The Streett/recurrence bundle at the **fully martingale-problem
profile**: the confinement certificate `V₀` and every pair's ranking
certificate `W i` are presented by martingale problems, with the
requested-but-ungranted region additionally carrying *strict*
presentations (`MPFlowStrict` at level `ε i`). This discharges the
`hSegDWR` hypothesis of `sound_GSHS_streett_bundle_mp` — at this profile
no analytic per-model hypothesis remains. -/
theorem sound_GSHS_streett_bundle_mp_strict
    {ι : Type*} [Countable ι]
    {D Dbar U : Set State} {V₀ : State → ℝ} {Rq G : ι → Set State}
    {W : ι → State → ℝ} {p thr C₀ : ℝ} {ε C : ι → ℝ} {x : State}
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hmp₀ : ∀ x : State, Nonempty (MPFlow M 0 V₀ x))
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hmpW : ∀ i, ∀ x : State, Nonempty (MPFlow M 0 (W i) x))
    (hmpWR : ∀ i, ∀ x ∈ ((D \ U) ∩ Rq i) \ G i,
      Nonempty (MPFlowStrict M 0 (W i) x (ε i)))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} :=
  sound_GSHS_streett_bundle_mp hD hDbar hU hV₀ hRq hG hW hΘ hDsub
    hLive hHalt hReset hmp₀ hForce₀ hNonneg₀ hC₀0 hV₀C hFloor₀ hε hmpW
    (fun i => rankingSegmentDynkin_of_mp_strict M (W i) (hW i) (hε i).le
      (hmpWR i))
    hForceW hNonnegW hC0 hWC hx hthr

end Qtsl.LayerD
