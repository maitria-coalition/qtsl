import QtslAux.LayerD.DiniDischarge
import Mathlib.Topology.Order.MonotoneConvergence

/-! # A sampling interface for stochastic segment discharge

This module provides an interface for discharging the segment Dynkin inequality
when the inter-jump dynamics are themselves stochastic (for instance driven by
a diffusion), so that no single deterministic flow certificate applies. The
strategy: represent the segment law as a mixture over random flow data
`(γ ω, r ω, jr ω, T ω, k ω)`, verify a certificate bound only at deterministic
sample times, and recover the full — possibly infinite-horizon — readout by
monotone convergence and Fatou's lemma.

* `segDom T k` and `stopClip T k`: the time domain of a segment and the
  clipping of a sample time at the exit time, with the `live` (never-exiting)
  case unclipped.
* `sampledRead θ V γ r jr T k t`: the certificate readout at sample time `t` —
  survival-weighted certificate value plus accumulated jump integral, both
  evaluated at `stopClip T k t`.
* `segMeasureIto`: the segment outcome law, extending `segMeasureFin` by the
  never-exiting case (alarm density on all of `(0, ∞)`, no terminal atom),
  with the reading lemma `segMeasureIto_live_read`.
* `ItoInterface M θ V x`: the interface structure — a probability space of flow
  data, the mixture bound `hread`, and the sampled bounds `hsampled` /
  `hsampled_meas`. Its main theorem `ItoInterface.segD_at` derives
  `∫⁻ outcomeRead ∂(M.seg x) ≤ ENNReal.ofReal (V x)` by taking liminf over
  integer sample times (`liminf_sampledRead_of_exit`,
  `le_liminf_sampledRead_of_live`) and applying Fatou's lemma;
  `segmentDynkin_of_ito` assembles `SegmentDynkin M θ V`.
* `ItoInterface.ofPDMPFlowFin`: the deterministic finite-horizon flow
  certificate embeds as the Dirac special case of the interface.
-/

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

def segDom (T : ℝ) (k : ExitKind) : Set ℝ :=
  if k = ExitKind.live then Ioi 0 else Ioc 0 T

@[simp] lemma segDom_live (T : ℝ) : segDom T ExitKind.live = Ioi 0 := by
  simp [segDom]

lemma segDom_of_ne {T : ℝ} {k : ExitKind} (hk : k ≠ ExitKind.live) :
    segDom T k = Ioc 0 T := by
  simp [segDom, hk]

noncomputable def stopClip (T : ℝ) (k : ExitKind) (t : ℝ) : ℝ :=
  if k = ExitKind.live then t else min t T

@[simp] lemma stopClip_live (T t : ℝ) : stopClip T ExitKind.live t = t := by
  simp [stopClip]

lemma stopClip_of_ne {T : ℝ} {k : ExitKind} (hk : k ≠ ExitKind.live)
    (t : ℝ) : stopClip T k t = min t T := by
  simp [stopClip, hk]

lemma stopClip_nonneg {T : ℝ} (hT : 0 ≤ T) (k : ExitKind) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ stopClip T k t := by
  unfold stopClip
  split_ifs
  · exact ht
  · exact le_min ht hT

lemma stopClip_mono (T : ℝ) (k : ExitKind) : Monotone (stopClip T k) := by
  intro a b hab
  unfold stopClip
  split_ifs
  · exact hab
  · exact min_le_min hab le_rfl

noncomputable def sampledRead (θ : ℝ) (V : State → ℝ) (γ : ℝ → State)
    (r jr : ℝ → ℝ) (T : ℝ) (k : ExitKind) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (survWeight r θ (stopClip T k t) * V (γ (stopClip T k t)))
    + ENNReal.ofReal (jint r jr θ (stopClip T k t))

noncomputable def segMeasureIto (γ : ℝ → State) (r : ℝ → ℝ) (T : ℝ)
    (k : ExitKind) : Measure (ℝ≥0 × State × ExitKind) :=
  if k = ExitKind.live then
    Measure.map (fun u => (Real.toNNReal u, γ u, ExitKind.alarm))
      ((volume.restrict (Ioi 0)).withDensity
        fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u))))
  else segMeasureFin γ r T k

lemma segMeasureIto_live (γ : ℝ → State) (r : ℝ → ℝ) (T : ℝ) :
    segMeasureIto γ r T ExitKind.live
      = Measure.map (fun u => (Real.toNNReal u, γ u, ExitKind.alarm))
          ((volume.restrict (Ioi 0)).withDensity
            fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u)))) := by
  simp [segMeasureIto]

lemma segMeasureIto_of_ne {γ : ℝ → State} {r : ℝ → ℝ} {T : ℝ}
    {k : ExitKind} (hk : k ≠ ExitKind.live) :
    segMeasureIto γ r T k = segMeasureFin γ r T k := by
  simp [segMeasureIto, hk]

lemma jint_mono {r j : ℝ → ℝ} {θ : ℝ} (hr : Continuous r)
    (hj : Continuous j) (hj0 : ∀ u, 0 ≤ j u) {a b : ℝ}
    (hab : a ≤ b) : jint r j θ a ≤ jint r j θ b := by
  have hint : ∀ c d : ℝ,
      IntervalIntegrable (fun u => survWeight r θ u * j u) volume c d :=
    fun c d => ((survWeight_continuous hr θ).mul hj).intervalIntegrable c d
  have hsplit : jint r j θ a + ∫ u in a..b, survWeight r θ u * j u
      = jint r j θ b :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
  have htail : 0 ≤ ∫ u in a..b, survWeight r θ u * j u :=
    intervalIntegral.integral_nonneg hab fun u _ =>
      mul_nonneg (survWeight_pos θ u).le (hj0 u)
  linarith

lemma setLIntegral_survJr_Ioc {r jr : ℝ → ℝ} {θ T : ℝ} (hT : 0 ≤ T)
    (hr : Continuous r) (hjr : Continuous jr) (hjr0 : ∀ u, 0 ≤ jr u) :
    ∫⁻ u in Ioc 0 T, ENNReal.ofReal (survWeight r θ u * jr u) ∂volume
      = ENNReal.ofReal (jint r jr θ T) := by
  have hcont : Continuous fun u => survWeight r θ u * jr u :=
    (survWeight_continuous hr θ).mul hjr
  have hint : IntegrableOn (fun u => survWeight r θ u * jr u)
      (Ioc 0 T) volume :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun u =>
      mul_nonneg (survWeight_pos θ u).le (hjr0 u))]
  rw [jint, intervalIntegral.integral_of_le hT]

theorem segMeasureIto_live_read {M : SegmentModel State} {θ : ℝ}
    {V : State → ℝ} [IsSFiniteKernel M.jump] (hV : Measurable V)
    {γ : ℝ → State} {r jr : ℝ → ℝ} {T : ℝ}
    (hγ : Measurable γ) (hr : Continuous r) (hr0 : ∀ u, 0 ≤ r u)
    (hjr_couple : ∀ u ∈ Ioi (0:ℝ),
      ENNReal.ofReal (jr u)
        = ENNReal.ofReal (r u)
          * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm))) :
    ∫⁻ o, outcomeRead M θ V o ∂(segMeasureIto γ r T ExitKind.live)
      = ∫⁻ u in Ioi 0, ENNReal.ofReal (survWeight r θ u * jr u) ∂volume := by
  classical
  have hf := measurable_outcomeRead M θ hV (V := V)
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (hγ.prodMk measurable_const)
  have hcomp : Measurable fun u : ℝ =>
      outcomeRead M θ V (Real.toNNReal u, γ u, ExitKind.alarm) := hf.comp hmap
  have hdens : Measurable fun u : ℝ =>
      ENNReal.ofReal (r u * Real.exp (-(cumInt r u))) :=
    ENNReal.measurable_ofReal.comp
      (hr.mul (Real.continuous_exp.comp (cumInt_continuous hr).neg)).measurable
  rw [segMeasureIto_live, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _ hdens hcomp]
  simp only [Pi.mul_apply]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro u hu
  have hu0 : (0:ℝ) ≤ u := le_of_lt hu
  have hcoe : ((Real.toNNReal u : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0
  show ENNReal.ofReal (r u * Real.exp (-(cumInt r u))) *
      outcomeRead M θ V (Real.toNNReal u, γ u, ExitKind.alarm)
    = ENNReal.ofReal (survWeight r θ u * jr u)
  rw [show outcomeRead M θ V (Real.toNNReal u, γ u, ExitKind.alarm)
      = expWeight θ (Real.toNNReal u) *
        ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm)) from rfl]
  rw [expWeight, hcoe, ENNReal.ofReal_mul (hr0 u)]
  calc ENNReal.ofReal (r u) * ENNReal.ofReal (Real.exp (-(cumInt r u))) *
        (ENNReal.ofReal (Real.exp (θ * u)) *
          ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm)))
      = ENNReal.ofReal (Real.exp (-(cumInt r u))) *
          (ENNReal.ofReal (Real.exp (θ * u)) *
            (ENNReal.ofReal (r u) *
              ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm)))) := by
        ring
    _ = ENNReal.ofReal (Real.exp (-(cumInt r u))) *
          (ENNReal.ofReal (Real.exp (θ * u)) * ENNReal.ofReal (jr u)) := by
        rw [← hjr_couple u hu]
    _ = ENNReal.ofReal (survWeight r θ u * jr u) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [survWeight, sub_eq_add_neg, Real.exp_add]
        ring

omit [MeasurableSpace State] in

lemma liminf_sampledRead_of_exit {V : State → ℝ} {γ : ℝ → State}
    {r jr : ℝ → ℝ} {θ T : ℝ} {k : ExitKind} (hk : k ≠ ExitKind.live) :
    Filter.liminf (fun n : ℕ => sampledRead θ V γ r jr T k n) Filter.atTop
      = ENNReal.ofReal (survWeight r θ T * V (γ T))
        + ENNReal.ofReal (jint r jr θ T) := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      sampledRead θ V γ r jr T k n
        = ENNReal.ofReal (survWeight r θ T * V (γ T))
          + ENNReal.ofReal (jint r jr θ T) := by
    obtain ⟨N, hN⟩ := exists_nat_ge T
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hTn : T ≤ (n : ℝ) := hN.trans (Nat.cast_le.2 hn)
    unfold sampledRead
    rw [stopClip_of_ne hk, min_eq_right hTn]
  rw [Filter.liminf_congr hev]
  exact Filter.liminf_const _

omit [MeasurableSpace State] in

lemma le_liminf_sampledRead_of_live {V : State → ℝ} {γ : ℝ → State}
    {r jr : ℝ → ℝ} {θ T : ℝ}
    (hr : Continuous r) (hjr : Continuous jr) (hjr0 : ∀ u, 0 ≤ jr u) :
    ∫⁻ u in Ioi 0, ENNReal.ofReal (survWeight r θ u * jr u) ∂volume
      ≤ Filter.liminf
          (fun n : ℕ => sampledRead θ V γ r jr T ExitKind.live n)
          Filter.atTop := by
  have hset : Ioi (0:ℝ) = ⋃ n : ℕ, Ioc (0:ℝ) n := by
    ext u
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hu
      obtain ⟨n, hn⟩ := exists_nat_ge u
      exact ⟨n, hu, hn⟩
    · rintro ⟨n, hu, _⟩
      exact hu
  have hmono : Monotone fun n : ℕ => Ioc (0:ℝ) n := fun a b hab =>
    Ioc_subset_Ioc le_rfl (Nat.cast_le.2 hab)
  have hslice : ∀ n : ℕ,
      (volume.withDensity fun u => ENNReal.ofReal (survWeight r θ u * jr u))
          (Ioc (0:ℝ) n)
        = ENNReal.ofReal (jint r jr θ n) := fun n => by
    rw [withDensity_apply _ measurableSet_Ioc]
    exact setLIntegral_survJr_Ioc (Nat.cast_nonneg n) hr hjr hjr0
  have hjm : Monotone fun n : ℕ => ENNReal.ofReal (jint r jr θ (n : ℝ)) :=
    fun a b hab => ENNReal.ofReal_le_ofReal
      (jint_mono hr hjr hjr0 (Nat.cast_le.2 hab))
  calc ∫⁻ u in Ioi 0, ENNReal.ofReal (survWeight r θ u * jr u) ∂volume
      = (volume.withDensity
          fun u => ENNReal.ofReal (survWeight r θ u * jr u)) (Ioi 0) :=
        (withDensity_apply _ measurableSet_Ioi).symm
    _ = ⨆ n : ℕ, (volume.withDensity
          fun u => ENNReal.ofReal (survWeight r θ u * jr u))
            (Ioc (0:ℝ) n) := by
        rw [hset, hmono.measure_iUnion]
    _ = ⨆ n : ℕ, ENNReal.ofReal (jint r jr θ (n : ℝ)) := iSup_congr hslice
    _ = Filter.liminf
          (fun n : ℕ => ENNReal.ofReal (jint r jr θ (n : ℝ)))
          Filter.atTop := (tendsto_atTop_iSup hjm).liminf_eq.symm
    _ ≤ Filter.liminf
          (fun n : ℕ => sampledRead θ V γ r jr T ExitKind.live n)
          Filter.atTop := by
        refine Filter.liminf_le_liminf
          (Filter.Eventually.of_forall fun n => ?_)
        unfold sampledRead
        rw [stopClip_live]
        exact self_le_add_left _ _

/-- The per-path liminf bound of `ItoInterface.segD_at`, standalone: the
outcome read of a single path's segment law is at most the liminf of its
sampled reads along integer sample times. Extracted so that discharges
which do not construct a full `ItoInterface` (e.g. the strict ranking
transport) can reuse the block. -/
lemma lintegral_outcomeRead_segMeasureIto_le_liminf
    {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} [IsSFiniteKernel M.jump]
    (hV : Measurable V) {γ : ℝ → State} {r jr : ℝ → ℝ} {T : ℝ} {k : ExitKind}
    (hT : 0 ≤ T)
    (hk : k = ExitKind.guard ∨ k = ExitKind.halt ∨ k = ExitKind.live)
    (hγ : Measurable γ) (hr : Continuous r) (hr0 : ∀ u, 0 ≤ r u)
    (hjr : Continuous jr) (hjr0 : ∀ u, 0 ≤ jr u)
    (hjr_couple : ∀ u ∈ segDom T k,
      ENNReal.ofReal (jr u)
        = ENNReal.ofReal (r u)
          * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm)))
    (hVγ : ∀ u, 0 ≤ V (γ u)) :
    ∫⁻ o, outcomeRead M θ V o ∂(segMeasureIto γ r T k)
      ≤ Filter.liminf (fun n : ℕ => sampledRead θ V γ r jr T k n)
          Filter.atTop := by
  by_cases hlive : k = ExitKind.live
  · have hc := hjr_couple
    rw [hlive, segDom_live] at hc
    rw [hlive, segMeasureIto_live_read hV hγ hr hr0 hc]
    exact le_liminf_sampledRead_of_live hr hjr hjr0
  · have hk2 : k = ExitKind.guard ∨ k = ExitKind.halt := by
      rcases hk with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hlive
    have hc := hjr_couple
    rw [segDom_of_ne hlive] at hc
    rw [segMeasureIto_of_ne hlive,
      segMeasureFin_outcomeRead_eq hV hT hk2 hγ hr hr0 hjr hjr0 hc hVγ,
      liminf_sampledRead_of_exit hlive]
    have hj0 : 0 ≤ jint r jr θ T :=
      intervalIntegral.integral_nonneg hT fun u _ =>
        mul_nonneg (survWeight_pos θ u).le (hjr0 u)
    have hsv0 : 0 ≤ survWeight r θ T * V (γ T) :=
      mul_nonneg (survWeight_pos θ _).le (hVγ _)
    exact le_of_eq (by rw [ENNReal.ofReal_add hj0 hsv0, add_comm])

structure ItoInterface (M : SegmentModel State) (θ : ℝ) (V : State → ℝ)
    (x : State) where

  Ω : Type*

  [mΩ : MeasurableSpace Ω]

  P : Measure Ω

  T : Ω → ℝ
  hT : ∀ ω, 0 ≤ T ω

  k : Ω → ExitKind
  hk : ∀ ω, k ω = ExitKind.guard ∨ k ω = ExitKind.halt
    ∨ k ω = ExitKind.live

  γ : Ω → ℝ → State
  hγ : ∀ ω, Measurable (γ ω)

  r : Ω → ℝ → ℝ
  hr : ∀ ω, Continuous (r ω)
  hr0 : ∀ ω u, 0 ≤ r ω u

  jr : Ω → ℝ → ℝ
  hjr : ∀ ω, Continuous (jr ω)
  hjr0 : ∀ ω u, 0 ≤ jr ω u
  hjr_couple : ∀ ω, ∀ u ∈ segDom (T ω) (k ω),
    ENNReal.ofReal (jr ω u)
      = ENNReal.ofReal (r ω u)
        * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ ω u, ExitKind.alarm))

  hVγ : ∀ ω u, 0 ≤ V (γ ω u)

  hread : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
    ≤ ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
        ∂(segMeasureIto (γ ω) (r ω) (T ω) (k ω)) ∂P

  hsampled : ∀ t : ℝ, 0 ≤ t →
    ∫⁻ ω, sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t ∂P
      ≤ ENNReal.ofReal (V x)

  hsampled_meas : ∀ t : ℝ, 0 ≤ t →
    AEMeasurable
      (fun ω => sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t) P

attribute [instance] ItoInterface.mΩ

namespace ItoInterface

variable {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : ItoInterface M θ V x)
    (hV : Measurable V) :
    ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x) := by
  refine le_trans D.hread ?_

  have hpt : ∀ ω,
      ∫⁻ o, outcomeRead M θ V o
          ∂(segMeasureIto (D.γ ω) (D.r ω) (D.T ω) (D.k ω))
        ≤ Filter.liminf
            (fun n : ℕ =>
              sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n)
            Filter.atTop := fun ω =>
    lintegral_outcomeRead_segMeasureIto_le_liminf hV (D.hT ω) (D.hk ω)
      (D.hγ ω) (D.hr ω) (D.hr0 ω) (D.hjr ω) (D.hjr0 ω) (D.hjr_couple ω)
      (D.hVγ ω)

  calc ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
          ∂(segMeasureIto (D.γ ω) (D.r ω) (D.T ω) (D.k ω)) ∂D.P
      ≤ ∫⁻ ω, Filter.liminf
            (fun n : ℕ =>
              sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n)
            Filter.atTop ∂D.P := lintegral_mono hpt
    _ ≤ Filter.liminf
          (fun n : ℕ => ∫⁻ ω,
            sampledRead θ V (D.γ ω) (D.r ω) (D.jr ω) (D.T ω) (D.k ω) n
              ∂D.P)
          Filter.atTop :=
        MeasureTheory.lintegral_liminf_le'
          (fun n => D.hsampled_meas n (Nat.cast_nonneg n))
    _ ≤ ENNReal.ofReal (V x) :=
        Filter.liminf_le_of_frequently_le'
          (Filter.Eventually.frequently (Filter.Eventually.of_forall
            fun n => D.hsampled n (Nat.cast_nonneg n)))

end ItoInterface

theorem segmentDynkin_of_ito (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (ItoInterface M θ V x)) :
    SegmentDynkin M θ V := by
  intro x
  obtain ⟨D⟩ := h x
  exact D.segD_at hV

noncomputable def ItoInterface.ofPDMPFlowFin {M : SegmentModel State}
    {θ : ℝ} {V : State → ℝ} {x : State} [IsSFiniteKernel M.jump]
    (F : PDMPFlowFin M θ V x) : ItoInterface M θ V x where
  Ω := Unit
  mΩ := inferInstance
  P := Measure.dirac ()
  T _ := F.T
  hT _ := F.hT
  k _ := F.k
  hk _ := by
    rcases F.hk with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  γ _ := F.γ
  hγ _ := F.hγ
  r _ := F.r
  hr _ := F.hr
  hr0 _ := F.hr0
  jr _ := F.jr
  hjr _ := F.hjr
  hjr0 _ := F.hjr0
  hjr_couple _ := by
    have hnl : F.k ≠ ExitKind.live := by
      rcases F.hk with h | h <;> rw [h] <;>
        exact fun hcontra => ExitKind.noConfusion hcontra
    rw [segDom_of_ne hnl]
    exact F.hjr_couple
  hVγ _ := F.hVγ
  hread := by
    have hnl : F.k ≠ ExitKind.live := by
      rcases F.hk with h | h <;> rw [h] <;>
        exact fun hcontra => ExitKind.noConfusion hcontra
    have hmeas : Measurable fun _ : Unit =>
        ∫⁻ o, outcomeRead M θ V o ∂(segMeasureIto F.γ F.r F.T F.k) :=
      measurable_const
    have heq : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
        = ∫⁻ o, outcomeRead M θ V o ∂(segMeasureIto F.γ F.r F.T F.k) := by
      rw [F.hseg, segMeasureIto_of_ne hnl]
    rw [heq]
    exact (lintegral_dirac' () hmeas).ge
  hsampled t ht := by
    have hnl : F.k ≠ ExitKind.live := by
      rcases F.hk with h | h <;> rw [h] <;>
        exact fun hcontra => ExitKind.noConfusion hcontra
    have hmeas : Measurable fun _ : Unit =>
        sampledRead θ V F.γ F.r F.jr F.T F.k t := measurable_const
    have hbound : sampledRead θ V F.γ F.r F.jr F.T F.k t
        ≤ ENNReal.ofReal (V x) := by
      have hs0 : 0 ≤ min t F.T := le_min ht F.hT
      have hsT : min t F.T ≤ F.T := min_le_right _ _
      have hcore := pdmp_dynkin_core (v := fun u => V (F.γ u)) (dv := F.dv)
        (r := F.r) (j := F.jr) (T := min t F.T) hs0 F.hr F.hjr
        (F.hv_cont.mono (Icc_subset_Icc le_rfl hsT))
        (fun u hu => F.hv u (Ioo_subset_Ioo le_rfl hsT hu))
        (fun u hu => F.hrow u (Ioo_subset_Ioo le_rfl hsT hu))
      have hj0 : 0 ≤ jint F.r F.jr θ (min t F.T) :=
        intervalIntegral.integral_nonneg hs0 fun u _ =>
          mul_nonneg (survWeight_pos θ u).le (F.hjr0 u)
      have hsv0 : 0 ≤ survWeight F.r θ (min t F.T) * V (F.γ (min t F.T)) :=
        mul_nonneg (survWeight_pos θ _).le (F.hVγ _)
      unfold sampledRead
      rw [stopClip_of_ne hnl, ← ENNReal.ofReal_add hsv0 hj0]
      refine ENNReal.ofReal_le_ofReal ?_
      calc survWeight F.r θ (min t F.T) * V (F.γ (min t F.T))
            + jint F.r F.jr θ (min t F.T)
          = jint F.r F.jr θ (min t F.T)
            + survWeight F.r θ (min t F.T) * V (F.γ (min t F.T)) := by ring
        _ ≤ V (F.γ 0) := hcore
        _ = V x := by rw [F.hγ0]
    exact le_trans (le_of_eq (lintegral_dirac' () hmeas)) hbound
  hsampled_meas _ _ := measurable_const.aemeasurable

end Qtsl.LayerD
