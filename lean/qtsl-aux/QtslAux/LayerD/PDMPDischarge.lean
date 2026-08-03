import QtslAux.LayerD
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # PDMP discharge of the segment Dynkin inequality

This module discharges the segment-level Dynkin inequality `SegmentDynkin M θ V`
for segments that evolve as a piecewise-deterministic Markov process (PDMP):
between jumps the state follows a deterministic flow `γ`, spontaneous jumps
arrive at a continuous rate `r`, and the segment law is the resulting exit-time
distribution.

* `cumInt r t = ∫ s in 0..t, r s`, the cumulative rate;
  `survWeight r θ t = exp (θ * t - cumInt r t)`, the `θ`-weighted survival
  factor; and `jint r j θ t`, the accumulated survival-weighted jump readout.
* `pdmp_dynkin_core`: the analytic core — if along the flow the certificate
  `v` satisfies the differential row inequality
  `dv t + θ * v t - r t * v t + j t ≤ 0` on `(0, T)`, then
  `jint r j θ T + survWeight r θ T * v T ≤ v 0`. The proof shows
  `t ↦ survWeight r θ t * v t + jint r j θ t` is antitone on `[0, T]`.
* `segMeasureFin γ r T k`: the outcome law of a finite-horizon PDMP segment —
  an `alarm` exit with density `r * exp (-cumInt r)` on `(0, T]`, plus a
  terminal atom of mass `exp (-cumInt r T)` at time `T` with exit kind `k`.
* `PDMPFlowFin` / `PDMPFlowInf`: certificate structures packaging a
  finite-horizon (respectively infinite-horizon, never force-exiting) PDMP flow
  together with the row inequality and the coupling of the jump readout `jr` to
  the jump kernel; their `segD_at` theorems bound the `outcomeRead` integral
  against `M.seg x` by `V x`.
* `segmentDynkin_of_pdmp`: if every start state carries one of the two
  certificates, then `SegmentDynkin M θ V` holds.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

noncomputable def cumInt (r : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, r s

lemma cumInt_hasDerivAt {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (cumInt r) (r t) t :=
  intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable _ _)
    (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt

lemma cumInt_continuous {r : ℝ → ℝ} (hr : Continuous r) : Continuous (cumInt r) :=
  continuous_iff_continuousAt.2 fun t => (cumInt_hasDerivAt hr t).continuousAt

@[simp] lemma cumInt_zero (r : ℝ → ℝ) : cumInt r 0 = 0 :=
  intervalIntegral.integral_same

noncomputable def survWeight (r : ℝ → ℝ) (θ t : ℝ) : ℝ :=
  Real.exp (θ * t - cumInt r t)

lemma survWeight_pos {r : ℝ → ℝ} (θ t : ℝ) : 0 < survWeight r θ t := Real.exp_pos _

@[simp] lemma survWeight_zero (r : ℝ → ℝ) (θ : ℝ) : survWeight r θ 0 = 1 := by
  simp [survWeight]

lemma survWeight_hasDerivAt {r : ℝ → ℝ} (hr : Continuous r) (θ t : ℝ) :
    HasDerivAt (survWeight r θ) ((θ - r t) * survWeight r θ t) t := by

  have hlin := (hasDerivAt_mul_const (x := t) θ).sub (cumInt_hasDerivAt hr t)
  have h2 := (Real.hasDerivAt_exp (t * θ - cumInt r t)).comp t hlin
  have heq : Real.exp (t * θ - cumInt r t) * (θ - r t)
      = (θ - r t) * survWeight r θ t := by
    rw [survWeight, mul_comm t θ]; ring
  rw [heq] at h2
  exact h2.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply, Pi.sub_apply, survWeight]
      congr 1
      ring)

lemma survWeight_continuous {r : ℝ → ℝ} (hr : Continuous r) (θ : ℝ) :
    Continuous (survWeight r θ) :=
  Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub (cumInt_continuous hr))

noncomputable def jint (r j : ℝ → ℝ) (θ t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, survWeight r θ u * j u

lemma jint_hasDerivAt {r j : ℝ → ℝ} (hr : Continuous r) (hj : Continuous j) (θ t : ℝ) :
    HasDerivAt (jint r j θ) (survWeight r θ t * j t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (((survWeight_continuous hr θ).mul hj).intervalIntegrable _ _)
    (((survWeight_continuous hr θ).mul hj).stronglyMeasurableAtFilter _ _)
    ((survWeight_continuous hr θ).mul hj).continuousAt

theorem pdmp_dynkin_core {v dv r j : ℝ → ℝ} {θ T : ℝ} (hT : 0 ≤ T)
    (hr : Continuous r) (hj : Continuous j)
    (hv_cont : ContinuousOn v (Icc 0 T))
    (hv : ∀ t ∈ Ioo 0 T, HasDerivAt v (dv t) t)
    (hrow : ∀ t ∈ Ioo 0 T, dv t + θ * v t - r t * v t + j t ≤ 0) :
    jint r j θ T + survWeight r θ T * v T ≤ v 0 := by
  set h : ℝ → ℝ := fun t => survWeight r θ t * v t + jint r j θ t with hh
  have hderiv : ∀ t ∈ Ioo 0 T,
      HasDerivAt h (survWeight r θ t * (dv t + θ * v t - r t * v t + j t)) t := by
    intro t ht
    have h1 := ((survWeight_hasDerivAt hr θ t).mul (hv t ht)).add
      (jint_hasDerivAt hr hj θ t)
    have heq : (θ - r t) * survWeight r θ t * v t + survWeight r θ t * dv t
        + survWeight r θ t * j t
        = survWeight r θ t * (dv t + θ * v t - r t * v t + j t) := by ring
    rw [heq] at h1
    exact h1
  have hcont : ContinuousOn h (Icc 0 T) :=
    (((survWeight_continuous hr θ).continuousOn.mul hv_cont).add
      (continuous_iff_continuousAt.2 fun t =>
        (jint_hasDerivAt hr hj θ t).continuousAt).continuousOn)
  have hanti : AntitoneOn h (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      exact mul_nonpos_iff.2 (Or.inl ⟨(survWeight_pos (r := r) θ t).le, hrow t ht⟩)
  have h0 : h 0 = v 0 := by
    simp [hh, jint]
  have hT0 : h T ≤ h 0 := hanti (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
  rw [h0] at hT0
  calc jint r j θ T + survWeight r θ T * v T = h T := by rw [hh]; ring
    _ ≤ v 0 := hT0

variable {M : SegmentModel State} {θ : ℝ} {V : State → ℝ}

theorem measurable_outcomeRead (M : SegmentModel State) (θ : ℝ)
    [IsSFiniteKernel M.jump]
    (hV : Measurable V) : Measurable (outcomeRead M θ V) := by
  have hexp : Measurable fun t : ℝ≥0 => expWeight θ t :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_coe_nnreal_real))
  have hjl : Measurable fun p : State × ExitKind =>
      ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump p) :=
    Measurable.lintegral_kernel_prod_right
      (f := fun _ z => ENNReal.ofReal (V z))
      ((ENNReal.measurable_ofReal.comp hV).comp measurable_snd)
  have heq : outcomeRead M θ V = fun o : ℝ≥0 × State × ExitKind =>
      if o.2.2 = ExitKind.alarm then
        expWeight θ o.1 * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (o.2.1, ExitKind.alarm))
      else if o.2.2 = ExitKind.live then 0
      else expWeight θ o.1 * ENNReal.ofReal (V o.2.1) := by
    funext o
    rcases o with ⟨t, y, k⟩
    cases k <;> simp [outcomeRead]
  rw [heq]
  have hkind : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.2 :=
    measurable_snd.comp measurable_snd
  have hval : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.1 :=
    measurable_fst.comp measurable_snd
  refine Measurable.ite (hkind (measurableSet_singleton _)) ?_ ?_
  · exact (hexp.comp measurable_fst).mul
      (hjl.comp (hval.prodMk measurable_const))
  · refine Measurable.ite (hkind (measurableSet_singleton _)) measurable_const ?_
    exact (hexp.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (hV.comp hval))

noncomputable def segMeasureFin (γ : ℝ → State) (r : ℝ → ℝ) (T : ℝ) (k : ExitKind) :
    Measure (ℝ≥0 × State × ExitKind) :=
  Measure.map (fun u => (Real.toNNReal u, γ u, ExitKind.alarm))
      ((volume.restrict (Ioc 0 T)).withDensity
        fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u))))
    + (ENNReal.ofReal (Real.exp (-(cumInt r T)))) •
        Measure.dirac (Real.toNNReal T, γ T, k)

structure PDMPFlowFin (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) (x : State) where

  T : ℝ
  hT : 0 ≤ T

  k : ExitKind
  hk : k = ExitKind.guard ∨ k = ExitKind.halt

  γ : ℝ → State
  hγ : Measurable γ
  hγ0 : γ 0 = x

  r : ℝ → ℝ
  hr : Continuous r
  hr0 : ∀ u, 0 ≤ r u

  jr : ℝ → ℝ
  hjr : Continuous jr
  hjr0 : ∀ u, 0 ≤ jr u
  hjr_couple : ∀ u ∈ Ioc 0 T,
    ENNReal.ofReal (jr u)
      = ENNReal.ofReal (r u)
        * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm))

  dv : ℝ → ℝ
  hv_cont : ContinuousOn (fun u => V (γ u)) (Icc 0 T)
  hv : ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => V (γ u)) (dv t) t

  hVγ : ∀ u, 0 ≤ V (γ u)

  hrow : ∀ t ∈ Ioo 0 T, dv t + θ * V (γ t) - r t * V (γ t) + jr t ≤ 0

  hseg : M.seg x = segMeasureFin γ r T k

namespace PDMPFlowFin

variable {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : PDMPFlowFin M θ V x)
    (hV : Measurable V) :
    ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x) := by
  classical
  have hf := measurable_outcomeRead M θ hV (V := V)
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, D.γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (D.hγ.prodMk measurable_const)
  have hcomp : Measurable fun u : ℝ =>
      outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm) := hf.comp hmap
  have hdens : Measurable fun u : ℝ =>
      ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) :=
    ENNReal.measurable_ofReal.comp
      (D.hr.mul (Real.continuous_exp.comp (cumInt_continuous D.hr).neg)).measurable
  rw [D.hseg, segMeasureFin, lintegral_add_measure, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _ hdens hcomp,
    lintegral_smul_measure, lintegral_dirac' _ hf]
  simp only [Pi.mul_apply, smul_eq_mul]

  have halarm : ∫⁻ u in Ioc 0 D.T,
      ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) *
        outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm) ∂volume
      = ENNReal.ofReal (jint D.r D.jr θ D.T) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (survWeight D.r θ u * D.jr u)) ?_]
    ·
      have hcont : Continuous fun u => survWeight D.r θ u * D.jr u :=
        (survWeight_continuous D.hr θ).mul D.hjr
      have hint : IntegrableOn (fun u => survWeight D.r θ u * D.jr u) (Ioc 0 D.T) volume :=
        (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun u =>
          mul_nonneg (survWeight_pos θ u).le (D.hjr0 u))]
      rw [jint, intervalIntegral.integral_of_le D.hT]
    ·
      intro u hu
      have hu0 : (0:ℝ) ≤ u := hu.1.le
      have hcoe : ((Real.toNNReal u : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0
      show ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) *
          outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm)
        = ENNReal.ofReal (survWeight D.r θ u * D.jr u)
      rw [show outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm)
          = expWeight θ (Real.toNNReal u) *
            ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)) from rfl]
      rw [expWeight, hcoe,
        ENNReal.ofReal_mul (D.hr0 u)]
      calc ENNReal.ofReal (D.r u) * ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
            (ENNReal.ofReal (Real.exp (θ * u)) *
              ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)))
          = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
              (ENNReal.ofReal (Real.exp (θ * u)) *
                (ENNReal.ofReal (D.r u) *
                  ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)))) := by
            ring
        _ = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
              (ENNReal.ofReal (Real.exp (θ * u)) * ENNReal.ofReal (D.jr u)) := by
            rw [← D.hjr_couple u hu]
        _ = ENNReal.ofReal (survWeight D.r θ u * D.jr u) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            rw [survWeight, sub_eq_add_neg, Real.exp_add]
            ring

  have hatom : outcomeRead M θ V (Real.toNNReal D.T, D.γ D.T, D.k)
      = ENNReal.ofReal (Real.exp (θ * D.T)) * ENNReal.ofReal (V (D.γ D.T)) := by
    have hcoe : ((Real.toNNReal D.T : ℝ≥0) : ℝ) = D.T := Real.coe_toNNReal D.T D.hT
    rcases D.hk with hk | hk <;>
      simp [hk, outcomeRead, expWeight, hcoe]
  rw [halarm, hatom]

  have hfin : ENNReal.ofReal (Real.exp (-(cumInt D.r D.T))) *
      (ENNReal.ofReal (Real.exp (θ * D.T)) * ENNReal.ofReal (V (D.γ D.T)))
      = ENNReal.ofReal (survWeight D.r θ D.T * V (D.γ D.T)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [survWeight, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hfin]
  have hjint0 : 0 ≤ jint D.r D.jr θ D.T :=
    intervalIntegral.integral_nonneg D.hT fun u _ =>
      mul_nonneg (survWeight_pos θ u).le (D.hjr0 u)
  rw [← ENNReal.ofReal_add hjint0
    (mul_nonneg (survWeight_pos θ D.T).le (D.hVγ D.T))]
  refine ENNReal.ofReal_le_ofReal ?_
  have := pdmp_dynkin_core (v := fun u => V (D.γ u)) (dv := D.dv) (r := D.r) (j := D.jr)
    D.hT D.hr D.hjr D.hv_cont D.hv D.hrow
  simpa [D.hγ0] using this

end PDMPFlowFin

structure PDMPFlowInf (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) (x : State) where
  γ : ℝ → State
  hγ : Measurable γ
  hγ0 : γ 0 = x
  r : ℝ → ℝ
  hr : Continuous r
  hr0 : ∀ u, 0 ≤ r u
  jr : ℝ → ℝ
  hjr : Continuous jr
  hjr0 : ∀ u, 0 ≤ jr u
  hjr_couple : ∀ u ∈ Ioi (0:ℝ),
    ENNReal.ofReal (jr u)
      = ENNReal.ofReal (r u)
        * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm))
  dv : ℝ → ℝ
  hv_cont : ContinuousOn (fun u => V (γ u)) (Ici 0)
  hv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt (fun u => V (γ u)) (dv t) t
  hVγ : ∀ u, 0 ≤ V (γ u)
  hrow : ∀ t ∈ Ioi (0:ℝ), dv t + θ * V (γ t) - r t * V (γ t) + jr t ≤ 0

  tail : Measure (ℝ≥0 × State × ExitKind)
  htail : tail {o | o.2.2 ≠ ExitKind.live} = 0
  hseg : M.seg x =
    Measure.map (fun u => (Real.toNNReal u, γ u, ExitKind.alarm))
      ((volume.restrict (Ioi 0)).withDensity
        fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u))))
    + tail

namespace PDMPFlowInf

variable {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : PDMPFlowInf M θ V x)
    (hV : Measurable V) :
    ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x) := by
  classical
  have hf := measurable_outcomeRead M θ hV (V := V)
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, D.γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (D.hγ.prodMk measurable_const)
  have hcomp : Measurable fun u : ℝ =>
      outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm) := hf.comp hmap
  have hdens : Measurable fun u : ℝ =>
      ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) :=
    ENNReal.measurable_ofReal.comp
      (D.hr.mul (Real.continuous_exp.comp (cumInt_continuous D.hr).neg)).measurable

  have htail0 : ∫⁻ o, outcomeRead M θ V o ∂D.tail = 0 := by
    have hae : outcomeRead M θ V =ᵐ[D.tail] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun o ho => ?_) D.htail
      rcases o with ⟨t, y, k⟩
      cases k <;> simp_all [outcomeRead]
    rw [lintegral_congr_ae hae]
    simp
  rw [D.hseg, lintegral_add_measure, htail0, add_zero, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _ hdens hcomp]
  simp only [Pi.mul_apply]

  rw [setLIntegral_congr_fun measurableSet_Ioi
    (g := fun u => ENNReal.ofReal (survWeight D.r θ u * D.jr u)) ?_]
  swap
  · intro u hu
    have hu0 : (0:ℝ) ≤ u := (le_of_lt hu)
    have hcoe : ((Real.toNNReal u : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0
    show ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) *
        outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm)
      = ENNReal.ofReal (survWeight D.r θ u * D.jr u)
    rw [show outcomeRead M θ V (Real.toNNReal u, D.γ u, ExitKind.alarm)
        = expWeight θ (Real.toNNReal u) *
          ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)) from rfl]
    rw [expWeight, hcoe, ENNReal.ofReal_mul (D.hr0 u)]
    calc ENNReal.ofReal (D.r u) * ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
          (ENNReal.ofReal (Real.exp (θ * u)) *
            ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)))
        = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
            (ENNReal.ofReal (Real.exp (θ * u)) *
              (ENNReal.ofReal (D.r u) *
                ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (D.γ u, ExitKind.alarm)))) := by
          ring
      _ = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
            (ENNReal.ofReal (Real.exp (θ * u)) * ENNReal.ofReal (D.jr u)) := by
          rw [← D.hjr_couple u hu]
      _ = ENNReal.ofReal (survWeight D.r θ u * D.jr u) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [survWeight, sub_eq_add_neg, Real.exp_add]
          ring

  · have hset : Ioi (0:ℝ) = ⋃ n : ℕ, Ioc (0:ℝ) n := by
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
    rw [← withDensity_apply _ measurableSet_Ioi, hset, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    rw [withDensity_apply _ measurableSet_Ioc]
    have hcont : Continuous fun u => survWeight D.r θ u * D.jr u :=
      (survWeight_continuous D.hr θ).mul D.hjr
    have hint : IntegrableOn (fun u => survWeight D.r θ u * D.jr u)
        (Ioc 0 (n:ℝ)) volume :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u =>
        mul_nonneg (survWeight_pos θ u).le (D.hjr0 u))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcore := pdmp_dynkin_core (v := fun u => V (D.γ u)) (dv := D.dv)
      (r := D.r) (j := D.jr) (T := (n : ℝ)) (Nat.cast_nonneg n) D.hr D.hjr
      (D.hv_cont.mono Icc_subset_Ici_self)
      (fun t ht => D.hv t (mem_Ioi.2 ht.1))
      (fun t ht => D.hrow t (mem_Ioi.2 ht.1))
    have hjint : ∫ u in Ioc (0:ℝ) n, survWeight D.r θ u * D.jr u ∂volume
        = jint D.r D.jr θ n := by
      rw [jint, intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
    have hsurv : 0 ≤ survWeight D.r θ n * V (D.γ n) :=
      mul_nonneg (survWeight_pos θ _).le (D.hVγ _)
    rw [hjint]
    have hv0 : V (D.γ 0) = V x := by rw [D.hγ0]
    linarith [hcore, hsurv]

end PDMPFlowInf

theorem segmentDynkin_of_pdmp (M : SegmentModel State) (θ : ℝ) (V : State → ℝ)
    [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State,
      Nonempty (PDMPFlowFin M θ V x) ∨ Nonempty (PDMPFlowInf M θ V x)) :
    SegmentDynkin M θ V := by
  intro x
  rcases h x with ⟨⟨D⟩⟩ | ⟨⟨D⟩⟩
  · exact D.segD_at hV
  · exact D.segD_at hV

end Qtsl.LayerD
