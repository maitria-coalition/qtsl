import QtslAux.LayerD.ItoInterface
import OptionalSamplingRC.Basic

/-! # Discharging the sampling interface by continuous-time optional sampling

This module connects the interface of `QtslAux.LayerD.ItoInterface`
to a genuine continuous-time supermartingale hypothesis, using an optional
sampling theorem for right-continuous nonnegative supermartingales indexed by
`ℝ≥0` (from the `OptionalSamplingRC` package).

* `certProcess θ V γ r jr s ω
    = survWeight (r ω) θ s * V (γ ω s) + jint (r ω) (jr ω) θ s`:
  the certificate process evaluated along the random flow data.
* `exitDebut T k`: the exit time as an `ℝ≥0∞`-valued random time (`⊤` on
  never-exiting samples). `exitTrunc_family` shows its truncations are stopping
  times of the filtration, and `coe_min_exitTrunc_eq_stopClip` identifies
  stopping at the truncated exit time with the interface's `stopClip`.
* `sampledRead_eq_ofReal_certProcess`: the interface's `sampledRead` at a
  sample time is exactly the certificate process stopped at the truncated exit
  time.
* `sampled_le_of_supermartingale`: if `certProcess` is a supermartingale with
  the right-continuity required by the optional sampling theorem and starts at
  `V x`, then every sampled readout integrates to at most
  `ENNReal.ofReal (V x)`; `aemeasurable_sampledRead_of_supermartingale`
  supplies the measurability side condition.
* `ItoInterface.ofSupermartingale`: packages these facts into an
  `ItoInterface`, so a continuous-time supermartingale certificate for the
  stochastic flow discharges the segment Dynkin inequality.
-/

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m0}

noncomputable def certProcess (θ : ℝ) (V : State → ℝ) (γ : Ω → ℝ → State)
    (r jr : Ω → ℝ → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  survWeight (r ω) θ (s : ℝ) * V (γ ω (s : ℝ))
    + jint (r ω) (jr ω) θ (s : ℝ)

noncomputable def exitDebut (T : Ω → ℝ) (k : Ω → ExitKind) (ω : Ω) :
    ℝ≥0∞ :=
  if k ω = ExitKind.live then ⊤ else ENNReal.ofReal (T ω)

section Glue

variable {θ : ℝ} {V : State → ℝ} {x : State}
  {γ : Ω → ℝ → State} {r jr : Ω → ℝ → ℝ} {T : Ω → ℝ} {k : Ω → ExitKind}

lemma exitTrunc_family
    (hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s] {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)})
    (tN : ℝ≥0) :
    ∀ s : ℝ≥0, MeasurableSet[ℱ s]
      {ω | OptionalSamplingRC.ennrealTrunc (exitDebut T k) tN ω ≤ s} := by
  intro s
  by_cases hst : s < tN
  · rw [OptionalSamplingRC.ennrealTrunc_le_iff (exitDebut T k) tN s hst]
    exact hτ s
  · have huniv :
        {ω | OptionalSamplingRC.ennrealTrunc (exitDebut T k) tN ω ≤ s}
          = Set.univ := by
      refine eq_univ_of_forall fun ω => ?_
      simp only [mem_setOf_eq, OptionalSamplingRC.ennrealTrunc]
      split_ifs with h
      · have h1 : (exitDebut T k ω).toNNReal ≤ tN := by
          have h2 := ENNReal.toNNReal_mono ENNReal.coe_ne_top h
          simpa using h2
        exact h1.trans (not_lt.mp hst)
      · exact not_lt.mp hst
    rw [huniv]
    exact MeasurableSet.univ

lemma coe_min_exitTrunc_eq_stopClip (hT : ∀ ω, 0 ≤ T ω) {t : ℝ}
    (ht : 0 ≤ t) (ω : Ω) :
    ((min (OptionalSamplingRC.ennrealTrunc (exitDebut T k)
        (Real.toNNReal t) ω) (Real.toNNReal t) : ℝ≥0) : ℝ)
      = stopClip (T ω) (k ω) t := by
  by_cases hlive : k ω = ExitKind.live
  · have hτω : exitDebut T k ω = ⊤ := by simp [exitDebut, hlive]
    have htr : OptionalSamplingRC.ennrealTrunc (exitDebut T k)
        (Real.toNNReal t) ω = Real.toNNReal t := by
      unfold OptionalSamplingRC.ennrealTrunc
      rw [hτω, if_neg (by simp)]
    rw [hlive, stopClip_live, htr, min_self, Real.coe_toNNReal t ht]
  · have hτω : exitDebut T k ω = ENNReal.ofReal (T ω) := by
      simp [exitDebut, hlive]
    rw [stopClip_of_ne hlive]
    by_cases hTt : T ω ≤ t
    · have hle : exitDebut T k ω ≤ ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) := by
        rw [hτω]
        show ENNReal.ofReal (T ω) ≤ ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞)
        exact (ENNReal.ofReal_le_ofReal_iff ht).2 hTt
      have htr := OptionalSamplingRC.ennrealTrunc_eq_of_le
        (exitDebut T k) (Real.toNNReal t) ω hle
      have hmin : (T ω).toNNReal ≤ Real.toNNReal t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal (T ω) (hT ω),
          Real.coe_toNNReal t ht]
        exact hTt
      rw [htr, hτω,
        show (ENNReal.ofReal (T ω)).toNNReal = (T ω).toNNReal from rfl,
        min_eq_left hmin,
        Real.coe_toNNReal (T ω) (hT ω), min_eq_right hTt]
    · have hnle : ¬ exitDebut T k ω ≤ ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) := by
        rw [hτω]
        show ¬ ENNReal.ofReal (T ω) ≤ ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞)
        exact fun hcontra =>
          hTt ((ENNReal.ofReal_le_ofReal_iff ht).1 hcontra)
      have htr : OptionalSamplingRC.ennrealTrunc (exitDebut T k)
          (Real.toNNReal t) ω = Real.toNNReal t := by
        unfold OptionalSamplingRC.ennrealTrunc
        rw [if_neg hnle]
      rw [htr, min_self, Real.coe_toNNReal t ht,
        min_eq_left (not_le.mp hTt).le]

omit [MeasurableSpace State] in

lemma sampledRead_eq_ofReal_certProcess (hT : ∀ ω, 0 ≤ T ω)
    (hVγ : ∀ ω u, 0 ≤ V (γ ω u)) (hjr0 : ∀ ω u, 0 ≤ jr ω u)
    {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t
      = ENNReal.ofReal (certProcess θ V γ r jr
          (min (OptionalSamplingRC.ennrealTrunc (exitDebut T k)
            (Real.toNNReal t) ω) (Real.toNNReal t)) ω) := by
  have hclip := coe_min_exitTrunc_eq_stopClip (k := k) hT ht ω
  have hsc0 : 0 ≤ stopClip (T ω) (k ω) t := by
    rw [← hclip]
    exact NNReal.coe_nonneg _
  have hsv0 : 0 ≤ survWeight (r ω) θ (stopClip (T ω) (k ω) t)
      * V (γ ω (stopClip (T ω) (k ω) t)) :=
    mul_nonneg (survWeight_pos θ _).le (hVγ ω _)
  have hj0 : 0 ≤ jint (r ω) (jr ω) θ (stopClip (T ω) (k ω) t) :=
    intervalIntegral.integral_nonneg hsc0 fun u _ =>
      mul_nonneg (survWeight_pos θ u).le (hjr0 ω u)
  unfold sampledRead certProcess
  rw [hclip, ← ENNReal.ofReal_add hsv0 hj0]

omit [MeasurableSpace State] in

theorem sampled_le_of_supermartingale [IsProbabilityMeasure P]
    (hT : ∀ ω, 0 ≤ T ω)
    (hvc : ∀ ω, Continuous fun u => V (γ ω u))
    (hVγ : ∀ ω u, 0 ≤ V (γ ω u))
    (hr : ∀ ω, Continuous (r ω)) (hjr : ∀ ω, Continuous (jr ω))
    (hjr0 : ∀ ω u, 0 ≤ jr ω u)
    (hγ0 : ∀ ω, γ ω 0 = x)
    (hZ : Supermartingale (certProcess θ V γ r jr) ℱ P)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
      {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)}) :
    ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t ∂P
        ≤ ENNReal.ofReal (V x) := by
  have hZnn : ∀ s ω, 0 ≤ certProcess θ V γ r jr s ω := fun s ω =>
    add_nonneg (mul_nonneg (survWeight_pos θ _).le (hVγ ω _))
      (intervalIntegral.integral_nonneg (NNReal.coe_nonneg s) fun u _ =>
        mul_nonneg (survWeight_pos θ u).le (hjr0 ω u))
  have hZrc : ∀ ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => certProcess θ V γ r jr u ω)
        (Set.Ici s) s := by
    intro ω s
    have hF : Continuous fun u : ℝ =>
        survWeight (r ω) θ u * V (γ ω u) + jint (r ω) (jr ω) θ u :=
      ((survWeight_continuous (hr ω) θ).mul (hvc ω)).add
        (continuous_iff_continuousAt.2 fun u =>
          (jint_hasDerivAt (hr ω) (hjr ω) θ u).continuousAt)
    exact (hF.comp NNReal.continuous_coe).continuousWithinAt
  intro t ht
  have hτ' := exitTrunc_family (ℱ := ℱ) hτ (Real.toNNReal t)
  have hOS := OptionalSamplingRC.lintegral_stoppedValue_min_le
    (certProcess θ V γ r jr) hZ hZnn hZrc
    (OptionalSamplingRC.ennrealTrunc (exitDebut T k) (Real.toNNReal t))
    hτ' (Real.toNNReal t)
  have hz0 : ∀ ω, certProcess θ V γ r jr 0 ω = V x := by
    intro ω
    simp [certProcess, jint, hγ0 ω]
  calc ∫⁻ ω, sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t ∂P
      = ∫⁻ ω, ENNReal.ofReal (certProcess θ V γ r jr
          (min (OptionalSamplingRC.ennrealTrunc (exitDebut T k)
            (Real.toNNReal t) ω) (Real.toNNReal t)) ω) ∂P :=
        lintegral_congr fun ω =>
          sampledRead_eq_ofReal_certProcess hT hVγ hjr0 ht ω
    _ ≤ ∫⁻ ω, ENNReal.ofReal (certProcess θ V γ r jr 0 ω) ∂P := hOS
    _ = ENNReal.ofReal (V x) := by
        simp only [hz0]
        simp [lintegral_const]

omit [MeasurableSpace State] in

theorem aemeasurable_sampledRead_of_supermartingale
    (hT : ∀ ω, 0 ≤ T ω)
    (hvc : ∀ ω, Continuous fun u => V (γ ω u))
    (hVγ : ∀ ω u, 0 ≤ V (γ ω u))
    (hr : ∀ ω, Continuous (r ω)) (hjr : ∀ ω, Continuous (jr ω))
    (hjr0 : ∀ ω u, 0 ≤ jr ω u)
    (hZ : Supermartingale (certProcess θ V γ r jr) ℱ P)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
      {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)}) :
    ∀ t : ℝ, 0 ≤ t →
      AEMeasurable
        (fun ω => sampledRead θ V (γ ω) (r ω) (jr ω) (T ω) (k ω) t) P := by
  have hZrc : ∀ ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => certProcess θ V γ r jr u ω)
        (Set.Ici s) s := by
    intro ω s
    have hF : Continuous fun u : ℝ =>
        survWeight (r ω) θ u * V (γ ω u) + jint (r ω) (jr ω) θ u :=
      ((survWeight_continuous (hr ω) θ).mul (hvc ω)).add
        (continuous_iff_continuousAt.2 fun u =>
          (jint_hasDerivAt (hr ω) (hjr ω) θ u).continuousAt)
    exact (hF.comp NNReal.continuous_coe).continuousWithinAt
  intro t ht
  have hτ' := exitTrunc_family (ℱ := ℱ) hτ (Real.toNNReal t)
  have h1 := OptionalSamplingRC.aemeasurable_stoppedValue_min
    (certProcess θ V γ r jr) hZ hZrc
    (OptionalSamplingRC.ennrealTrunc (exitDebut T k) (Real.toNNReal t))
    hτ' (Real.toNNReal t)
  exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable h1).congr
    (Filter.Eventually.of_forall fun ω =>
      (sampledRead_eq_ofReal_certProcess hT hVγ hjr0 ht ω).symm)

noncomputable def ItoInterface.ofSupermartingale
    (M : SegmentModel State) [IsProbabilityMeasure P]
    (hT : ∀ ω, 0 ≤ T ω)
    (hk : ∀ ω, k ω = ExitKind.guard ∨ k ω = ExitKind.halt
      ∨ k ω = ExitKind.live)
    (hγ : ∀ ω, Measurable (γ ω))
    (hvc : ∀ ω, Continuous fun u => V (γ ω u))
    (hVγ : ∀ ω u, 0 ≤ V (γ ω u))
    (hr : ∀ ω, Continuous (r ω)) (hr0 : ∀ ω u, 0 ≤ r ω u)
    (hjr : ∀ ω, Continuous (jr ω)) (hjr0 : ∀ ω u, 0 ≤ jr ω u)
    (hjr_couple : ∀ ω, ∀ u ∈ segDom (T ω) (k ω),
      ENNReal.ofReal (jr ω u)
        = ENNReal.ofReal (r ω u)
          * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ ω u, ExitKind.alarm)))
    (hread : ∫⁻ o, outcomeRead M θ V o ∂(M.seg x)
      ≤ ∫⁻ ω, ∫⁻ o, outcomeRead M θ V o
          ∂(segMeasureIto (γ ω) (r ω) (T ω) (k ω)) ∂P)
    (hγ0 : ∀ ω, γ ω 0 = x)
    (hZ : Supermartingale (certProcess θ V γ r jr) ℱ P)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[ℱ s]
      {ω | exitDebut T k ω ≤ (s : ℝ≥0∞)}) :
    ItoInterface M θ V x where
  Ω := Ω
  mΩ := m0
  P := P
  T := T
  hT := hT
  k := k
  hk := hk
  γ := γ
  hγ := hγ
  r := r
  hr := hr
  hr0 := hr0
  jr := jr
  hjr := hjr
  hjr0 := hjr0
  hjr_couple := hjr_couple
  hVγ := hVγ
  hread := hread
  hsampled := sampled_le_of_supermartingale hT hvc hVγ hr hjr hjr0 hγ0 hZ hτ
  hsampled_meas :=
    aemeasurable_sampledRead_of_supermartingale hT hvc hVγ hr hjr hjr0 hZ hτ

end Glue

end Qtsl.LayerD
