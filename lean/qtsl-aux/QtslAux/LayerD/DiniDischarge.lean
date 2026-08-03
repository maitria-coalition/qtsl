import QtslAux.LayerD.PDMPDischarge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-! # PDMP discharge via Dini (forward-slope) derivatives

This module weakens the differentiability hypothesis of the deterministic-flow
PDMP discharge in `QtslAux.LayerD.PDMPDischarge`: instead of a
two-sided derivative of `t ↦ V (γ t)` along the flow, only a forward
(right-slope liminf) row condition is needed, so certificates that are merely
continuous with one-sided kinks remain admissible.

* `pdmp_dynkin_core_dini`: the analytic core. If `v` is continuous on `[0, T]`
  and at every `t ∈ [0, T)` every `ρ` above `(r t - θ) * v t - j t` is
  frequently exceeded from the right in the sense that
  `slope v t z < ρ` frequently as `z → t⁺`, then
  `jint r j θ T + survWeight r θ T * v T ≤ v 0`. The proof runs a
  boundary-crossing (fence) argument on
  `h t = survWeight r θ t * v t + jint r j θ t` via
  `image_le_of_liminf_slope_right_le_deriv_boundary`.
* `segMeasureFin_outcomeRead_eq`: closed form of the `outcomeRead` integral
  against the finite-horizon segment law `segMeasureFin`, namely
  `jint r jr θ T + survWeight r θ T * V (γ T)`.
* `PDMPFlowFinDini`: a finite-horizon PDMP flow certificate whose row condition
  is stated with Dini slopes (`hrow_dini`); `PDMPFlowFinDini.segD_at`
  discharges the segment Dynkin inequality at its start state, and
  `segmentDynkin_of_pdmp_dini` assembles `SegmentDynkin M θ V` from a family
  of such certificates.
* `dini_row_of_deriv_row`: the classical differentiable row condition implies
  the Dini row condition, recovering the hypothesis of
  `QtslAux.LayerD.PDMPDischarge` as a special case.
-/

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

theorem pdmp_dynkin_core_dini {v r j : ℝ → ℝ} {θ T : ℝ} (hT : 0 ≤ T)
    (hr : Continuous r) (hj : Continuous j)
    (hv_cont : ContinuousOn v (Icc 0 T))
    (hrow : ∀ t ∈ Ico 0 T, ∀ ρ : ℝ, (r t - θ) * v t - j t < ρ →
      ∃ᶠ z in 𝓝[>] t, slope v t z < ρ) :
    jint r j θ T + survWeight r θ T * v T ≤ v 0 := by

  set h : ℝ → ℝ := fun t => survWeight r θ t * v t + jint r j θ t with hh
  have hjc : Continuous (jint r j θ) := continuous_iff_continuousAt.2 fun t =>
    (jint_hasDerivAt hr hj θ t).continuousAt
  have hcont : ContinuousOn h (Icc 0 T) :=
    ((survWeight_continuous hr θ).continuousOn.mul hv_cont).add hjc.continuousOn

  have hbound : ∀ u ∈ Ico (0:ℝ) T, ∀ ρ : ℝ, (fun _ : ℝ => (0:ℝ)) u < ρ →
      ∃ᶠ z in 𝓝[>] u, slope h u z < ρ := by
    intro u hu ρ hρ0
    have hρ : (0:ℝ) < ρ := hρ0
    set φu : ℝ := survWeight r θ u with hφu
    have hφupos : 0 < φu := survWeight_pos θ u
    set K : ℝ := (r u - θ) * v u - j u with hK
    set δ : ℝ := ρ / (2 * φu) with hδ
    have hδpos : 0 < δ := div_pos hρ (by positivity)
    set S : ℝ := |K + δ| + |v u| + 1 with hS
    have hSpos : 0 < S := by positivity
    set ε : ℝ := ρ / (2 * S) with hε
    have hεpos : 0 < ε := div_pos hρ (by positivity)

    have hfreq : ∃ᶠ z in 𝓝[>] u, slope v u z < K + δ :=
      hrow u hu (K + δ) (lt_add_of_pos_right K hδpos)

    have hφslope : Filter.Tendsto (slope (survWeight r θ) u) (𝓝[>] u)
        (𝓝 ((θ - r u) * φu)) := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp (survWeight_hasDerivAt hr θ u)
      exact h1.mono_left (nhdsWithin_mono u fun z hz => ne_of_gt hz)
    have hev1 : ∀ᶠ z in 𝓝[>] u,
        |slope (survWeight r θ) u z - (θ - r u) * φu| < ε := by
      have h1 := Metric.tendsto_nhds.mp hφslope ε hεpos
      filter_upwards [h1] with z hz
      rw [Real.dist_eq] at hz; exact hz

    have hjslope : Filter.Tendsto (slope (jint r j θ) u) (𝓝[>] u)
        (𝓝 (φu * j u)) := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp (jint_hasDerivAt hr hj θ u)
      have h2 := h1.mono_left (nhdsWithin_mono u fun z hz => ne_of_gt hz)

      rw [hφu]
      exact h2
    have hev2 : ∀ᶠ z in 𝓝[>] u, |slope (jint r j θ) u z - φu * j u| < ε := by
      have h1 := Metric.tendsto_nhds.mp hjslope ε hεpos
      filter_upwards [h1] with z hz
      rw [Real.dist_eq] at hz; exact hz

    have hev3 : ∀ᶠ z in 𝓝[>] u, |survWeight r θ z - φu| < ε := by
      have hcφ : Filter.Tendsto (survWeight r θ) (𝓝[>] u) (𝓝 φu) :=
        ((survWeight_continuous hr θ).tendsto u).mono_left nhdsWithin_le_nhds
      have h1 := Metric.tendsto_nhds.mp hcφ ε hεpos
      filter_upwards [h1] with z hz
      rw [Real.dist_eq] at hz; exact hz

    have hev0 : ∀ᶠ z in 𝓝[>] u, z ∈ Ioi u := eventually_mem_nhdsWithin

    refine (hfreq.and_eventually (hev0.and (hev1.and (hev2.and hev3)))).mono ?_
    rintro z ⟨hsv, hzu, h1, h2, h3⟩
    have hne : z - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt hzu)
    have hφz : 0 < survWeight r θ z := survWeight_pos θ z

    have hdecomp : slope h u z
        = survWeight r θ z * slope v u z
          + v u * slope (survWeight r θ) u z
          + slope (jint r j θ) u z := by
      simp only [hh, slope_def_field]
      field_simp
      ring

    have e1' : survWeight r θ z * (K + δ) ≤ φu * (K + δ) + ε * |K + δ| := by
      have h4 : (survWeight r θ z - φu) * (K + δ) ≤ ε * |K + δ| := by
        calc (survWeight r θ z - φu) * (K + δ)
            ≤ |(survWeight r θ z - φu) * (K + δ)| := le_abs_self _
          _ = |survWeight r θ z - φu| * |K + δ| := abs_mul _ _
          _ ≤ ε * |K + δ| :=
              mul_le_mul_of_nonneg_right h3.le (abs_nonneg _)
      linarith
    have e2 : v u * slope (survWeight r θ) u z
        ≤ v u * ((θ - r u) * φu) + ε * |v u| := by
      have h4 : v u * (slope (survWeight r θ) u z - (θ - r u) * φu)
          ≤ ε * |v u| := by
        calc v u * (slope (survWeight r θ) u z - (θ - r u) * φu)
            ≤ |v u * (slope (survWeight r θ) u z - (θ - r u) * φu)| :=
              le_abs_self _
          _ = |v u| * |slope (survWeight r θ) u z - (θ - r u) * φu| :=
              abs_mul _ _
          _ ≤ |v u| * ε := mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
          _ = ε * |v u| := mul_comm _ _
      linarith
    have e3 : slope (jint r j θ) u z ≤ φu * j u + ε := by
      have h4 : slope (jint r j θ) u z - φu * j u
          ≤ |slope (jint r j θ) u z - φu * j u| := le_abs_self _
      linarith [h2]

    have hcenter : φu * (K + δ) + v u * ((θ - r u) * φu) + φu * j u
        = φu * δ := by
      simp only [hK]; ring
    have hδhalf : φu * δ = ρ / 2 := by
      rw [hδ]; field_simp
    have hεhalf : ε * S = ρ / 2 := by
      rw [hε]; field_simp
    have e1s : survWeight r θ z * slope v u z
        < survWeight r θ z * (K + δ) :=
      mul_lt_mul_of_pos_left hsv hφz
    calc slope h u z
        = survWeight r θ z * slope v u z
          + v u * slope (survWeight r θ) u z
          + slope (jint r j θ) u z := hdecomp
      _ < (φu * (K + δ) + ε * |K + δ|)
          + (v u * ((θ - r u) * φu) + ε * |v u|)
          + (φu * j u + ε) := by
            linarith [lt_of_lt_of_le e1s e1', e2, e3]
      _ = (φu * (K + δ) + v u * ((θ - r u) * φu) + φu * j u)
          + ε * (|K + δ| + |v u| + 1) := by ring
      _ = ρ / 2 + ε * S := by rw [hcenter, hδhalf, hS]
      _ = ρ / 2 + ρ / 2 := by rw [hεhalf]
      _ = ρ := by ring

  have hB : ContinuousOn (fun _ : ℝ => h 0) (Icc 0 T) := continuousOn_const
  have hB' : ∀ u ∈ Ico (0:ℝ) T,
      HasDerivWithinAt (fun _ : ℝ => h 0) ((fun _ : ℝ => (0:ℝ)) u) (Ici u) u :=
    fun u _ => hasDerivWithinAt_const u _ (h 0)
  have hfence := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := h) (a := 0) (b := T) (B := fun _ => h 0) (B' := fun _ : ℝ => (0:ℝ))
    hcont le_rfl hB hB' hbound
  have hend := hfence ⟨hT, le_refl T⟩
  have h0 : h 0 = v 0 := by simp [hh, jint]
  have hTv : h T = survWeight r θ T * v T + jint r j θ T := by rw [hh]
  rw [h0, hTv] at hend
  linarith [hend]

theorem segMeasureFin_outcomeRead_eq {M : SegmentModel State} {θ : ℝ}
    {V : State → ℝ} [IsSFiniteKernel M.jump] (hV : Measurable V)
    {γ : ℝ → State} {r jr : ℝ → ℝ} {T : ℝ} {k : ExitKind}
    (hT : 0 ≤ T) (hk : k = ExitKind.guard ∨ k = ExitKind.halt)
    (hγ : Measurable γ) (hr : Continuous r) (hr0 : ∀ u, 0 ≤ r u)
    (hjr : Continuous jr) (hjr0 : ∀ u, 0 ≤ jr u)
    (hjr_couple : ∀ u ∈ Ioc 0 T,
      ENNReal.ofReal (jr u)
        = ENNReal.ofReal (r u)
          * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (γ u, ExitKind.alarm)))
    (hVγ : ∀ u, 0 ≤ V (γ u)) :
    ∫⁻ o, outcomeRead M θ V o ∂(segMeasureFin γ r T k)
      = ENNReal.ofReal (jint r jr θ T + survWeight r θ T * V (γ T)) := by
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
  rw [segMeasureFin, lintegral_add_measure, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _ hdens hcomp,
    lintegral_smul_measure, lintegral_dirac' _ hf]
  simp only [Pi.mul_apply, smul_eq_mul]
  have halarm : ∫⁻ u in Ioc 0 T,
      ENNReal.ofReal (r u * Real.exp (-(cumInt r u))) *
        outcomeRead M θ V (Real.toNNReal u, γ u, ExitKind.alarm) ∂volume
      = ENNReal.ofReal (jint r jr θ T) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (survWeight r θ u * jr u)) ?_]
    · have hcont : Continuous fun u => survWeight r θ u * jr u :=
        (survWeight_continuous hr θ).mul hjr
      have hint : IntegrableOn (fun u => survWeight r θ u * jr u) (Ioc 0 T) volume :=
        (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun u =>
          mul_nonneg (survWeight_pos θ u).le (hjr0 u))]
      rw [jint, intervalIntegral.integral_of_le hT]
    · intro u hu
      have hu0 : (0:ℝ) ≤ u := hu.1.le
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
  have hatom : outcomeRead M θ V (Real.toNNReal T, γ T, k)
      = ENNReal.ofReal (Real.exp (θ * T)) * ENNReal.ofReal (V (γ T)) := by
    have hcoe : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
    rcases hk with hk' | hk' <;> simp [hk', outcomeRead, expWeight, hcoe]
  rw [halarm, hatom]
  have hfin : ENNReal.ofReal (Real.exp (-(cumInt r T))) *
      (ENNReal.ofReal (Real.exp (θ * T)) * ENNReal.ofReal (V (γ T)))
      = ENNReal.ofReal (survWeight r θ T * V (γ T)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [survWeight, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hfin]
  have hjint0 : 0 ≤ jint r jr θ T :=
    intervalIntegral.integral_nonneg hT fun u _ =>
      mul_nonneg (survWeight_pos θ u).le (hjr0 u)
  rw [← ENNReal.ofReal_add hjint0
    (mul_nonneg (survWeight_pos θ T).le (hVγ T))]

structure PDMPFlowFinDini (M : SegmentModel State) (θ : ℝ) (V : State → ℝ)
    (x : State) where

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
  hv_cont : ContinuousOn (fun u => V (γ u)) (Icc 0 T)
  hVγ : ∀ u, 0 ≤ V (γ u)

  hrow_dini : ∀ t ∈ Ico 0 T, ∀ ρ : ℝ,
    (r t - θ) * V (γ t) - jr t < ρ →
      ∃ᶠ z in 𝓝[>] t, slope (fun u => V (γ u)) t z < ρ

  hseg : M.seg x = segMeasureFin γ r T k

namespace PDMPFlowFinDini

variable {M : SegmentModel State} {θ : ℝ} {V : State → ℝ} {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : PDMPFlowFinDini M θ V x)
    (hV : Measurable V) :
    ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x) := by
  rw [D.hseg, segMeasureFin_outcomeRead_eq hV D.hT D.hk D.hγ D.hr D.hr0
    D.hjr D.hjr0 D.hjr_couple D.hVγ]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcore := pdmp_dynkin_core_dini (v := fun u => V (D.γ u)) (r := D.r)
    (j := D.jr) D.hT D.hr D.hjr D.hv_cont D.hrow_dini
  simpa [D.hγ0] using hcore

end PDMPFlowFinDini

theorem segmentDynkin_of_pdmp_dini (M : SegmentModel State) (θ : ℝ)
    (V : State → ℝ) [IsSFiniteKernel M.jump] (hV : Measurable V)
    (h : ∀ x : State, Nonempty (PDMPFlowFinDini M θ V x)) :
    SegmentDynkin M θ V := by
  intro x
  obtain ⟨D⟩ := h x
  exact D.segD_at hV

theorem dini_row_of_deriv_row {v dv r j : ℝ → ℝ} {θ T : ℝ}
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v (dv t) t)
    (hrow : ∀ t ∈ Ico 0 T, dv t + θ * v t - r t * v t + j t ≤ 0) :
    ∀ t ∈ Ico 0 T, ∀ ρ : ℝ, (r t - θ) * v t - j t < ρ →
      ∃ᶠ z in 𝓝[>] t, slope v t z < ρ := by
  intro t ht ρ hρ
  have hdv : dv t ≤ (r t - θ) * v t - j t := by
    have := hrow t ht
    linarith
  have htends : Filter.Tendsto (slope v t) (𝓝[>] t) (𝓝 (dv t)) := by
    have h1 := hasDerivAt_iff_tendsto_slope.mp (hv t ht)
    exact h1.mono_left (nhdsWithin_mono t fun z hz => ne_of_gt hz)
  exact (htends.eventually_lt_const (lt_of_le_of_lt hdv hρ)).frequently

end Qtsl.LayerD
