import QtslAux.LayerD.PDMPDischarge
import QtslAux.LayerD.Skeleton
import QtslAux.FloorRenewal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Max-form certificates for PDMPs

This module extends the PDMP discharge machinery to certificates of the form
`s ↦ max (A s) (B s)`, which are typically nondifferentiable along the flow
exactly where the two branches cross.

* `max_endpoint_le`: the analytic core — if each of `f`, `g` has nonpositive
  derivative whenever its branch is active (at least as large as the other),
  then `max (f T) (g T) ≤ max (f 0) (g 0)`. The proof runs a right-slope
  boundary-crossing argument
  (`image_le_of_liminf_slope_right_lt_deriv_boundary`) on `max (f u) (g u)`
  against an `ε`-sloped barrier, handling crossing points by a max-of-slopes
  computation.
* `pdmp_dynkin_core_max`: the resulting Dynkin core for a pair of certificate
  branches `va`, `vb` satisfying the differential row inequality only on their
  active sides.
* `PDMPFlowFinPair` / `PDMPFlowInfPair`, with their `segD_at` theorems and
  `segmentDynkin_of_pdmp_max`: finite- and infinite-horizon PDMP flow
  certificates discharging `SegmentDynkin M θ (fun s => max (A s) (B s))`;
  `forcedNonexpansion_max_of_pathwise` discharges guard nonexpansion of the max
  from pathwise nonexpansion of each branch, and
  `Qtsl.Gauge.max_jump_nonexpansive` records the corresponding
  jump-repayment step for gauge certificates.
* Scaling lemmas `SegmentDynkin.const_mul` and `ForcedNonexpansion.const_mul`,
  and `sound_GSHS_safety_barrier`: reachability of `U` is bounded by `W x / m`
  when `W ≥ m > 0` on `U`.
* `sound_NPDMPII_maxform` (with `_gauged` and `_battery` variants): the
  two-obstacle safety theorem — with the pair `A`, `B` certified in max form,
  `A ≥ 1` on `U₁` and `B ≥ lam / lam'` on `U₂`, the probability of ever
  entering `U₁ ∪ U₂` is at most
  `max (A x) (B x) / min 1 (lam / lam')`. The gauged variant takes branches of
  the form `ψ * V` with gauges `ψ ≥ 1`; the battery variant restates the bound
  as a lower bound on the probability of staying safe forever.
-/

open MeasureTheory ProbabilityTheory Set Real Filter Topology
open scoped ENNReal NNReal

namespace Qtsl.Gauge

theorem max_jump_nonexpansive {η δ τ c V V' B : ℝ}
    (hδ : 0 < δ) (hdwell : δ ≤ τ) (hclock : c ≤ 1 + η * δ)
    (hV : 0 ≤ V) (hjump : V' ≤ c * V) :
    max (ψ η δ 0 * V') B ≤ max (ψ η δ τ * V) B :=
  max_le_max (gauge_repayment hδ hdwell hclock hV hjump) le_rfl

end Qtsl.Gauge

namespace Qtsl.LayerD

theorem max_endpoint_le {f g f' g' : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hf : ∀ t ∈ Ioo 0 T, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ioo 0 T, HasDerivAt g (g' t) t)
    (hfrow : ∀ t ∈ Ioo 0 T, g t ≤ f t → f' t ≤ 0)
    (hgrow : ∀ t ∈ Ioo 0 T, f t ≤ g t → g' t ≤ 0) :
    max (f T) (g T) ≤ max (f 0) (g 0) := by
  rcases eq_or_lt_of_le hT with rfl | hT0
  · exact le_rfl
  have hφc : ContinuousOn (fun u => max (f u) (g u)) (Icc 0 T) :=
    continuous_max.comp_continuousOn (hfc.prodMk hgc)

  have key : ∀ c ∈ Ioo (0:ℝ) T, max (f T) (g T) ≤ max (f c) (g c) := by
    intro c hc

    have hεb : ∀ ε : ℝ, 0 < ε →
        max (f T) (g T) ≤ max (f c) (g c) + ε * (T - c) := by
      intro ε hε
      have hIccsub : Icc c T ⊆ Icc 0 T := Icc_subset_Icc hc.1.le le_rfl
      have hIcosub : Ico c T ⊆ Ioo 0 T := fun u hu => ⟨lt_of_lt_of_le hc.1 hu.1, hu.2⟩

      have hslope : ∀ x ∈ Ico c T, ∀ r : ℝ, (0:ℝ) < r →
          ∃ᶠ z in 𝓝[>] x, slope (fun u => max (f u) (g u)) x z < r := by
        intro x hx r hr
        have hxI : x ∈ Ioo (0:ℝ) T := hIcosub hx
        rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
        ·
          have hev : ∀ᶠ z in 𝓝 x, f z < g z :=
            ((hf x hxI).continuousAt).eventually_lt ((hg x hxI).continuousAt) hlt
          have hslopeEq : ∀ᶠ z in 𝓝[>] x,
              slope (fun u => max (f u) (g u)) x z = slope g x z := by
            filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
            simp only [slope_def_field]
            rw [max_eq_right hz.le, max_eq_right hlt.le]
          have hevlt : ∀ᶠ z in 𝓝[>] x, slope g x z < r :=
            ((hasDerivAt_iff_tendsto_slope_left_right.1 (hg x hxI)).2).eventually_lt
              tendsto_const_nhds (lt_of_le_of_lt (hgrow x hxI hlt.le) hr)
          exact ((hslopeEq.and hevlt).mono fun z hz => by
            rw [hz.1]; exact hz.2).frequently
        ·

          have htf : Tendsto (slope f x) (𝓝[>] x) (𝓝 (f' x)) :=
            (hasDerivAt_iff_tendsto_slope_left_right.1 (hf x hxI)).2
          have htg : Tendsto (slope g x) (𝓝[>] x) (𝓝 (g' x)) :=
            (hasDerivAt_iff_tendsto_slope_left_right.1 (hg x hxI)).2
          have hslopeEq : ∀ᶠ z in 𝓝[>] x,
              slope (fun u => max (f u) (g u)) x z
                = max (slope f x z) (slope g x z) := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            have hzx : (0:ℝ) < z - x := sub_pos.2 hz
            have hmono : Monotone fun p : ℝ => p - f x :=
              fun a b h => sub_le_sub_right h _
            simp only [slope_def_field]
            rw [max_eq_left heq.ge, show g x = f x from heq.symm,
              show max (f z) (g z) - f x = max (f z - f x) (g z - f x) from
                hmono.map_max]
            exact (max_div_div_right hzx.le _ _).symm
          have hmaxlt : max (f' x) (g' x) < r :=
            max_lt (lt_of_le_of_lt (hfrow x hxI heq.ge) hr)
              (lt_of_le_of_lt (hgrow x hxI heq.le) hr)
          have hevlt : ∀ᶠ z in 𝓝[>] x, max (slope f x z) (slope g x z) < r :=
            (htf.max htg).eventually_lt tendsto_const_nhds hmaxlt
          exact ((hslopeEq.and hevlt).mono fun z hz => by
            rw [hz.1]; exact hz.2).frequently
        ·
          have hev : ∀ᶠ z in 𝓝 x, g z < f z :=
            ((hg x hxI).continuousAt).eventually_lt ((hf x hxI).continuousAt) hgt
          have hslopeEq : ∀ᶠ z in 𝓝[>] x,
              slope (fun u => max (f u) (g u)) x z = slope f x z := by
            filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
            simp only [slope_def_field]
            rw [max_eq_left hz.le, max_eq_left hgt.le]
          have hevlt : ∀ᶠ z in 𝓝[>] x, slope f x z < r :=
            ((hasDerivAt_iff_tendsto_slope_left_right.1 (hf x hxI)).2).eventually_lt
              tendsto_const_nhds (lt_of_le_of_lt (hfrow x hxI hgt.le) hr)
          exact ((hslopeEq.and hevlt).mono fun z hz => by
            rw [hz.1]; exact hz.2).frequently
      have hBd : ∀ u : ℝ,
          HasDerivAt (fun w => max (f c) (g c) + ε * (w - c)) ((fun _ : ℝ => ε) u) u := by
        intro u
        simpa using (((hasDerivAt_id u).sub_const c).const_mul ε).const_add
          (max (f c) (g c))
      have hres := image_le_of_liminf_slope_right_lt_deriv_boundary
        (f' := fun _ : ℝ => (0:ℝ)) (hφc.mono hIccsub) hslope (by simp) hBd
        (fun u _ _ => hε)
      simpa using hres (right_mem_Icc.2 hc.2.le)

    by_contra hcon
    rw [not_le] at hcon
    have hd : (0:ℝ) < T - c := sub_pos.2 hc.2
    have hεpos : (0:ℝ) <
        (max (f T) (g T) - max (f c) (g c)) / (2 * (T - c)) :=
      div_pos (sub_pos.2 hcon) (by positivity)
    have hb := hεb _ hεpos
    have hmul : (max (f T) (g T) - max (f c) (g c)) / (2 * (T - c)) * (T - c)
        = (max (f T) (g T) - max (f c) (g c)) / 2 := by
      field_simp
    rw [hmul] at hb
    linarith

  haveI : (𝓝[Ioc (0:ℝ) T] 0).NeBot := left_nhdsWithin_Ioc_neBot hT0
  have htend : Tendsto (fun u => max (f u) (g u)) (𝓝[Ioc (0:ℝ) T] 0)
      (𝓝 (max (f 0) (g 0))) :=
    Filter.Tendsto.mono_left (hφc 0 (left_mem_Icc.2 hT))
      (nhdsWithin_mono _ Ioc_subset_Icc_self)
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rcases eq_or_lt_of_le hc.2 with hceq | hclt
  · subst hceq; exact le_rfl
  · exact key c ⟨hc.1, hclt⟩

theorem pdmp_dynkin_core_max {va vb dva dvb r j : ℝ → ℝ} {θ T : ℝ} (hT : 0 ≤ T)
    (hr : Continuous r) (hj : Continuous j)
    (hva_cont : ContinuousOn va (Icc 0 T)) (hvb_cont : ContinuousOn vb (Icc 0 T))
    (hva : ∀ t ∈ Ioo 0 T, HasDerivAt va (dva t) t)
    (hvb : ∀ t ∈ Ioo 0 T, HasDerivAt vb (dvb t) t)
    (hrowa : ∀ t ∈ Ioo 0 T, vb t ≤ va t → dva t + θ * va t - r t * va t + j t ≤ 0)
    (hrowb : ∀ t ∈ Ioo 0 T, va t ≤ vb t → dvb t + θ * vb t - r t * vb t + j t ≤ 0) :
    jint r j θ T + survWeight r θ T * max (va T) (vb T) ≤ max (va 0) (vb 0) := by
  set FA : ℝ → ℝ := fun t => survWeight r θ t * va t + jint r j θ t with hFA
  set FB : ℝ → ℝ := fun t => survWeight r θ t * vb t + jint r j θ t with hFB
  have hderivA : ∀ t ∈ Ioo (0:ℝ) T,
      HasDerivAt FA (survWeight r θ t * (dva t + θ * va t - r t * va t + j t)) t := by
    intro t ht
    have h1 := ((survWeight_hasDerivAt hr θ t).mul (hva t ht)).add
      (jint_hasDerivAt hr hj θ t)
    have heq : (θ - r t) * survWeight r θ t * va t + survWeight r θ t * dva t
        + survWeight r θ t * j t
        = survWeight r θ t * (dva t + θ * va t - r t * va t + j t) := by ring
    rw [heq] at h1
    exact h1
  have hderivB : ∀ t ∈ Ioo (0:ℝ) T,
      HasDerivAt FB (survWeight r θ t * (dvb t + θ * vb t - r t * vb t + j t)) t := by
    intro t ht
    have h1 := ((survWeight_hasDerivAt hr θ t).mul (hvb t ht)).add
      (jint_hasDerivAt hr hj θ t)
    have heq : (θ - r t) * survWeight r θ t * vb t + survWeight r θ t * dvb t
        + survWeight r θ t * j t
        = survWeight r θ t * (dvb t + θ * vb t - r t * vb t + j t) := by ring
    rw [heq] at h1
    exact h1
  have hjc : Continuous (jint r j θ) :=
    continuous_iff_continuousAt.2 fun t => (jint_hasDerivAt hr hj θ t).continuousAt
  have hcontA : ContinuousOn FA (Icc 0 T) :=
    ((survWeight_continuous hr θ).continuousOn.mul hva_cont).add hjc.continuousOn
  have hcontB : ContinuousOn FB (Icc 0 T) :=
    ((survWeight_continuous hr θ).continuousOn.mul hvb_cont).add hjc.continuousOn
  have hrowFA : ∀ t ∈ Ioo (0:ℝ) T, FB t ≤ FA t →
      survWeight r θ t * (dva t + θ * va t - r t * va t + j t) ≤ 0 := by
    intro t ht hle
    have hw : 0 < survWeight r θ t := survWeight_pos θ t
    have hba : vb t ≤ va t := by
      simp only [hFA, hFB] at hle
      have h2 : survWeight r θ t * vb t ≤ survWeight r θ t * va t := by linarith
      exact le_of_mul_le_mul_left h2 hw
    exact mul_nonpos_iff.2 (Or.inl ⟨hw.le, hrowa t ht hba⟩)
  have hrowFB : ∀ t ∈ Ioo (0:ℝ) T, FA t ≤ FB t →
      survWeight r θ t * (dvb t + θ * vb t - r t * vb t + j t) ≤ 0 := by
    intro t ht hle
    have hw : 0 < survWeight r θ t := survWeight_pos θ t
    have hab : va t ≤ vb t := by
      simp only [hFA, hFB] at hle
      have h2 : survWeight r θ t * va t ≤ survWeight r θ t * vb t := by linarith
      exact le_of_mul_le_mul_left h2 hw
    exact mul_nonpos_iff.2 (Or.inl ⟨hw.le, hrowb t ht hab⟩)
  have hends := max_endpoint_le hT hcontA hcontB hderivA hderivB hrowFA hrowFB
  have hzero : max (FA 0) (FB 0) = max (va 0) (vb 0) := by
    simp [hFA, hFB, jint]
  have hTeq : max (FA T) (FB T)
      = jint r j θ T + survWeight r θ T * max (va T) (vb T) := by
    have hmono : Monotone fun p : ℝ => p + jint r j θ T :=
      fun a b h => add_le_add h le_rfl
    have h1 : max (FA T) (FB T)
        = max (survWeight r θ T * va T) (survWeight r θ T * vb T)
          + jint r j θ T := by
      simp only [hFA, hFB]
      exact (hmono.map_max
        (a := survWeight r θ T * va T) (b := survWeight r θ T * vb T)).symm
    have h2 : max (survWeight r θ T * va T) (survWeight r θ T * vb T)
        = survWeight r θ T * max (va T) (vb T) :=
      (mul_max_of_nonneg _ _ (survWeight_pos (r := r) θ T).le).symm
    rw [h1, h2, add_comm]
  rw [hTeq, hzero] at hends
  exact hends

variable {State : Type*} [MeasurableSpace State]
variable {M : SegmentModel State} {θ : ℝ} {A B : State → ℝ}

structure PDMPFlowFinPair (M : SegmentModel State) (θ : ℝ) (A B : State → ℝ)
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
        * ∫⁻ z, ENNReal.ofReal (max (A z) (B z)) ∂(M.jump (γ u, ExitKind.alarm))

  da : ℝ → ℝ
  db : ℝ → ℝ
  ha_cont : ContinuousOn (fun u => A (γ u)) (Icc 0 T)
  hb_cont : ContinuousOn (fun u => B (γ u)) (Icc 0 T)
  ha : ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => A (γ u)) (da t) t
  hb : ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => B (γ u)) (db t) t

  hAγ : ∀ u, 0 ≤ A (γ u)
  hBγ : ∀ u, 0 ≤ B (γ u)

  hrowA : ∀ t ∈ Ioo 0 T, B (γ t) ≤ A (γ t) →
    da t + θ * A (γ t) - r t * A (γ t) + jr t ≤ 0
  hrowB : ∀ t ∈ Ioo 0 T, A (γ t) ≤ B (γ t) →
    db t + θ * B (γ t) - r t * B (γ t) + jr t ≤ 0

  hseg : M.seg x = segMeasureFin γ r T k

namespace PDMPFlowFinPair

variable {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : PDMPFlowFinPair M θ A B x)
    (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ o, outcomeRead M θ (fun s => max (A s) (B s)) o ∂(M.seg x)
      ≤ ENNReal.ofReal (max (A x) (B x)) := by
  classical
  have hf := measurable_outcomeRead M θ (V := fun s => max (A s) (B s)) (hA.max hB)
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, D.γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (D.hγ.prodMk measurable_const)
  have hcomp : Measurable fun u : ℝ =>
      outcomeRead M θ (fun s => max (A s) (B s))
        (Real.toNNReal u, D.γ u, ExitKind.alarm) := hf.comp hmap
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
        outcomeRead M θ (fun s => max (A s) (B s))
          (Real.toNNReal u, D.γ u, ExitKind.alarm) ∂volume
      = ENNReal.ofReal (jint D.r D.jr θ D.T) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (survWeight D.r θ u * D.jr u)) ?_]
    · have hcont : Continuous fun u => survWeight D.r θ u * D.jr u :=
        (survWeight_continuous D.hr θ).mul D.hjr
      have hint : IntegrableOn (fun u => survWeight D.r θ u * D.jr u)
          (Ioc 0 D.T) volume :=
        (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun u =>
          mul_nonneg (survWeight_pos θ u).le (D.hjr0 u))]
      rw [jint, intervalIntegral.integral_of_le D.hT]
    · intro u hu
      have hu0 : (0:ℝ) ≤ u := hu.1.le
      have hcoe : ((Real.toNNReal u : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0
      show ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) *
          outcomeRead M θ (fun s => max (A s) (B s))
            (Real.toNNReal u, D.γ u, ExitKind.alarm)
        = ENNReal.ofReal (survWeight D.r θ u * D.jr u)
      rw [show outcomeRead M θ (fun s => max (A s) (B s))
          (Real.toNNReal u, D.γ u, ExitKind.alarm)
          = expWeight θ (Real.toNNReal u) *
            ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
              ∂(M.jump (D.γ u, ExitKind.alarm)) from rfl]
      rw [expWeight, hcoe, ENNReal.ofReal_mul (D.hr0 u)]
      calc ENNReal.ofReal (D.r u) * ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
            (ENNReal.ofReal (Real.exp (θ * u)) *
              ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
                ∂(M.jump (D.γ u, ExitKind.alarm)))
          = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
              (ENNReal.ofReal (Real.exp (θ * u)) *
                (ENNReal.ofReal (D.r u) *
                  ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
                    ∂(M.jump (D.γ u, ExitKind.alarm)))) := by
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

  have hatom : outcomeRead M θ (fun s => max (A s) (B s))
      (Real.toNNReal D.T, D.γ D.T, D.k)
      = ENNReal.ofReal (Real.exp (θ * D.T))
        * ENNReal.ofReal (max (A (D.γ D.T)) (B (D.γ D.T))) := by
    have hcoe : ((Real.toNNReal D.T : ℝ≥0) : ℝ) = D.T := Real.coe_toNNReal D.T D.hT
    rcases D.hk with hk | hk <;>
      simp [hk, outcomeRead, expWeight, hcoe]
  rw [halarm, hatom]
  have hWT : 0 ≤ max (A (D.γ D.T)) (B (D.γ D.T)) :=
    le_trans (D.hAγ D.T) (le_max_left _ _)
  have hfin : ENNReal.ofReal (Real.exp (-(cumInt D.r D.T))) *
      (ENNReal.ofReal (Real.exp (θ * D.T))
        * ENNReal.ofReal (max (A (D.γ D.T)) (B (D.γ D.T))))
      = ENNReal.ofReal (survWeight D.r θ D.T * max (A (D.γ D.T)) (B (D.γ D.T))) := by
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
    (mul_nonneg (survWeight_pos θ D.T).le hWT)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcore := pdmp_dynkin_core_max (r := D.r) (j := D.jr)
    D.hT D.hr D.hjr D.ha_cont D.hb_cont D.ha D.hb D.hrowA D.hrowB
  simpa [D.hγ0] using hcore

end PDMPFlowFinPair

structure PDMPFlowInfPair (M : SegmentModel State) (θ : ℝ) (A B : State → ℝ)
    (x : State) where
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
        * ∫⁻ z, ENNReal.ofReal (max (A z) (B z)) ∂(M.jump (γ u, ExitKind.alarm))
  da : ℝ → ℝ
  db : ℝ → ℝ
  ha_cont : ContinuousOn (fun u => A (γ u)) (Ici 0)
  hb_cont : ContinuousOn (fun u => B (γ u)) (Ici 0)
  ha : ∀ t ∈ Ioi (0:ℝ), HasDerivAt (fun u => A (γ u)) (da t) t
  hb : ∀ t ∈ Ioi (0:ℝ), HasDerivAt (fun u => B (γ u)) (db t) t
  hAγ : ∀ u, 0 ≤ A (γ u)
  hBγ : ∀ u, 0 ≤ B (γ u)
  hrowA : ∀ t ∈ Ioi (0:ℝ), B (γ t) ≤ A (γ t) →
    da t + θ * A (γ t) - r t * A (γ t) + jr t ≤ 0
  hrowB : ∀ t ∈ Ioi (0:ℝ), A (γ t) ≤ B (γ t) →
    db t + θ * B (γ t) - r t * B (γ t) + jr t ≤ 0

  tail : Measure (ℝ≥0 × State × ExitKind)
  htail : tail {o | o.2.2 ≠ ExitKind.live} = 0
  hseg : M.seg x =
    Measure.map (fun u => (Real.toNNReal u, γ u, ExitKind.alarm))
      ((volume.restrict (Ioi 0)).withDensity
        fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u))))
    + tail

namespace PDMPFlowInfPair

variable {x : State}

theorem segD_at [IsSFiniteKernel M.jump] (D : PDMPFlowInfPair M θ A B x)
    (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ o, outcomeRead M θ (fun s => max (A s) (B s)) o ∂(M.seg x)
      ≤ ENNReal.ofReal (max (A x) (B x)) := by
  classical
  have hf := measurable_outcomeRead M θ (V := fun s => max (A s) (B s)) (hA.max hB)
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, D.γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (D.hγ.prodMk measurable_const)
  have hcomp : Measurable fun u : ℝ =>
      outcomeRead M θ (fun s => max (A s) (B s))
        (Real.toNNReal u, D.γ u, ExitKind.alarm) := hf.comp hmap
  have hdens : Measurable fun u : ℝ =>
      ENNReal.ofReal (D.r u * Real.exp (-(cumInt D.r u))) :=
    ENNReal.measurable_ofReal.comp
      (D.hr.mul (Real.continuous_exp.comp (cumInt_continuous D.hr).neg)).measurable
  have htail0 : ∫⁻ o, outcomeRead M θ (fun s => max (A s) (B s)) o ∂D.tail = 0 := by
    have hae : outcomeRead M θ (fun s => max (A s) (B s)) =ᵐ[D.tail] 0 := by
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
        outcomeRead M θ (fun s => max (A s) (B s))
          (Real.toNNReal u, D.γ u, ExitKind.alarm)
      = ENNReal.ofReal (survWeight D.r θ u * D.jr u)
    rw [show outcomeRead M θ (fun s => max (A s) (B s))
        (Real.toNNReal u, D.γ u, ExitKind.alarm)
        = expWeight θ (Real.toNNReal u) *
          ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
            ∂(M.jump (D.γ u, ExitKind.alarm)) from rfl]
    rw [expWeight, hcoe, ENNReal.ofReal_mul (D.hr0 u)]
    calc ENNReal.ofReal (D.r u) * ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
          (ENNReal.ofReal (Real.exp (θ * u)) *
            ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
              ∂(M.jump (D.γ u, ExitKind.alarm)))
        = ENNReal.ofReal (Real.exp (-(cumInt D.r u))) *
            (ENNReal.ofReal (Real.exp (θ * u)) *
              (ENNReal.ofReal (D.r u) *
                ∫⁻ z, ENNReal.ofReal (max (A z) (B z))
                  ∂(M.jump (D.γ u, ExitKind.alarm)))) := by
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
    have hcore := pdmp_dynkin_core_max (r := D.r) (j := D.jr) (T := (n : ℝ))
      (Nat.cast_nonneg n) D.hr D.hjr
      (D.ha_cont.mono Icc_subset_Ici_self) (D.hb_cont.mono Icc_subset_Ici_self)
      (fun t ht => D.ha t (mem_Ioi.2 ht.1)) (fun t ht => D.hb t (mem_Ioi.2 ht.1))
      (fun t ht => D.hrowA t (mem_Ioi.2 ht.1))
      (fun t ht => D.hrowB t (mem_Ioi.2 ht.1))
    have hcore' : jint D.r D.jr θ (n:ℝ)
        + survWeight D.r θ (n:ℝ) * max (A (D.γ (n:ℝ))) (B (D.γ (n:ℝ)))
        ≤ max (A x) (B x) := by
      simpa [D.hγ0] using hcore
    have hjint : ∫ u in Ioc (0:ℝ) n, survWeight D.r θ u * D.jr u ∂volume
        = jint D.r D.jr θ n := by
      rw [jint, intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
    have hsurv : 0 ≤ survWeight D.r θ (n:ℝ) * max (A (D.γ (n:ℝ))) (B (D.γ (n:ℝ))) :=
      mul_nonneg (survWeight_pos θ _).le
        (le_trans (D.hAγ _) (le_max_left _ _))
    rw [hjint]
    linarith [hcore', hsurv]

end PDMPFlowInfPair

theorem segmentDynkin_of_pdmp_max (M : SegmentModel State) (θ : ℝ)
    (A B : State → ℝ) [IsSFiniteKernel M.jump]
    (hA : Measurable A) (hB : Measurable B)
    (h : ∀ x : State,
      Nonempty (PDMPFlowFinPair M θ A B x) ∨ Nonempty (PDMPFlowInfPair M θ A B x)) :
    SegmentDynkin M θ (fun s => max (A s) (B s)) := by
  intro x
  rcases h x with ⟨⟨D⟩⟩ | ⟨⟨D⟩⟩
  · exact D.segD_at hA hB
  · exact D.segD_at hA hB

theorem forcedNonexpansion_max_of_pathwise [IsMarkovKernel M.jump]
    (h : ∀ y : State,
      ∀ᵐ z ∂(M.jump (y, ExitKind.guard)), A z ≤ A y ∧ B z ≤ B y) :
    ForcedNonexpansion M (fun s => max (A s) (B s)) := by
  intro y
  calc ∫⁻ z, ENNReal.ofReal (max (A z) (B z)) ∂(M.jump (y, ExitKind.guard))
      ≤ ∫⁻ _z, ENNReal.ofReal (max (A y) (B y)) ∂(M.jump (y, ExitKind.guard)) :=
        lintegral_mono_ae ((h y).mono fun z hz =>
          ENNReal.ofReal_le_ofReal (max_le_max hz.1 hz.2))
    _ = ENNReal.ofReal (max (A y) (B y)) := by
        rw [lintegral_const, measure_univ, mul_one]

lemma outcomeRead_const_mul (M : SegmentModel State) (θ : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (V : State → ℝ) (o : ℝ≥0 × State × ExitKind) :
    outcomeRead M θ (fun s => c * V s) o = ENNReal.ofReal c * outcomeRead M θ V o := by
  rcases o with ⟨t, y, k⟩
  cases k
  case alarm =>
    show expWeight θ t * ∫⁻ z, ENNReal.ofReal (c * V z) ∂(M.jump (y, ExitKind.alarm))
        = ENNReal.ofReal c *
          (expWeight θ t * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, ExitKind.alarm)))
    simp only [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  case guard =>
    show expWeight θ t * ENNReal.ofReal (c * V y)
        = ENNReal.ofReal c * (expWeight θ t * ENNReal.ofReal (V y))
    rw [ENNReal.ofReal_mul hc]
    ring
  case halt =>
    show expWeight θ t * ENNReal.ofReal (c * V y)
        = ENNReal.ofReal c * (expWeight θ t * ENNReal.ofReal (V y))
    rw [ENNReal.ofReal_mul hc]
    ring
  case live =>
    show (0:ℝ≥0∞) = ENNReal.ofReal c * 0
    rw [mul_zero]

lemma SegmentDynkin.const_mul {V : State → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : SegmentDynkin M θ V) : SegmentDynkin M θ (fun s => c * V s) := by
  intro x
  show ∫⁻ o, outcomeRead M θ (fun s => c * V s) o ∂(M.seg x)
      ≤ ENNReal.ofReal (c * V x)
  calc ∫⁻ o, outcomeRead M θ (fun s => c * V s) o ∂(M.seg x)
      = ∫⁻ o, ENNReal.ofReal c * outcomeRead M θ V o ∂(M.seg x) :=
        lintegral_congr fun o => outcomeRead_const_mul M θ hc V o
    _ = ENNReal.ofReal c * ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (V x) := mul_le_mul' le_rfl (h x)
    _ = ENNReal.ofReal (c * V x) := (ENNReal.ofReal_mul hc).symm

lemma ForcedNonexpansion.const_mul {V : State → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ForcedNonexpansion M V) : ForcedNonexpansion M (fun s => c * V s) := by
  intro y
  show ∫⁻ z, ENNReal.ofReal (c * V z) ∂(M.jump (y, ExitKind.guard))
      ≤ ENNReal.ofReal (c * V y)
  simp only [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (h y)

theorem sound_GSHS_safety_barrier [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {W : State → ℝ} {U : Set State} {m : ℝ} (hm : 0 < m)
    (hW : Measurable W) (hU : MeasurableSet U)
    (hSegD : SegmentDynkin M 0 W) (hForce : ForcedNonexpansion M W)
    (hNonneg : NonnegV W) {C : ℝ} (hC0 : 0 ≤ C) (hWC : ∀ y, W y ≤ C)
    (hFloor : ∀ y ∈ U, m ≤ W y) (x : State) :
    Battery.pathMeasure (skel M) (SkelState.alive x) {ω | ∃ n, ω n ∈ skelBad U}
      ≤ ENNReal.ofReal (W x / m) := by
  have hminv : (0:ℝ) ≤ m⁻¹ := (inv_pos.2 hm).le
  have h := sound_GSHS_safety (M := M) (V := fun s => m⁻¹ * W s) (U := U)
    (hW.const_mul m⁻¹) hU (hSegD.const_mul hminv) (hForce.const_mul hminv)
    (fun s => mul_nonneg hminv (hNonneg s))
    (C := m⁻¹ * C) (mul_nonneg hminv hC0)
    (fun y => mul_le_mul_of_nonneg_left (hWC y) hminv)
    (fun y hy => by
      rw [inv_mul_eq_div]
      exact (one_le_div hm).2 (hFloor y hy)) x
  rwa [inv_mul_eq_div] at h

theorem sound_NPDMPII_maxform [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {U₁ U₂ : Set State} {lam lam' : ℝ}
    (hA : Measurable A) (hB : Measurable B)
    (hU₁ : MeasurableSet U₁) (hU₂ : MeasurableSet U₂)
    (hlam : 0 < lam) (hlam' : 0 < lam')
    (hflow : ∀ y : State,
      Nonempty (PDMPFlowFinPair M 0 A B y) ∨ Nonempty (PDMPFlowInfPair M 0 A B y))
    (hjump : ∀ y : State,
      ∀ᵐ z ∂(M.jump (y, ExitKind.guard)), A z ≤ A y ∧ B z ≤ B y)
    (hA0 : ∀ y, 0 ≤ A y)
    {C : ℝ} (hC0 : 0 ≤ C) (hAC : ∀ y, A y ≤ C) (hBC : ∀ y, B y ≤ C)
    (hFloor₁ : ∀ y ∈ U₁, 1 ≤ A y) (hFloor₂ : ∀ y ∈ U₂, lam / lam' ≤ B y)
    (x : State) :
    Battery.pathMeasure (skel M) (SkelState.alive x)
        {ω | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)}
      ≤ ENNReal.ofReal (max (A x) (B x) / min 1 (lam / lam')) := by
  have hm : (0:ℝ) < min 1 (lam / lam') := lt_min one_pos (div_pos hlam hlam')
  refine sound_GSHS_safety_barrier hm (hA.max hB) (hU₁.union hU₂)
    (segmentDynkin_of_pdmp_max M 0 A B hA hB hflow)
    (forcedNonexpansion_max_of_pathwise hjump)
    (fun y => le_trans (hA0 y) (le_max_left _ _))
    hC0 (fun y => max_le (hAC y) (hBC y)) (fun y hy => ?_) x
  rcases hy with hy₁ | hy₂
  · exact le_trans (min_le_left _ _)
      (le_trans (hFloor₁ y hy₁) (le_max_left _ _))
  · exact le_trans (min_le_right _ _)
      (le_trans (hFloor₂ y hy₂) (le_max_right _ _))

theorem sound_NPDMPII_maxform_gauged [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {ψ₁ ψ₂ V₁ V₂ : State → ℝ} {U₁ U₂ : Set State} {lam lam' : ℝ}
    (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂)
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hU₁ : MeasurableSet U₁) (hU₂ : MeasurableSet U₂)
    (hlam : 0 < lam) (hlam' : 0 < lam')
    (hψ₁1 : ∀ y, 1 ≤ ψ₁ y) (hψ₂1 : ∀ y, 1 ≤ ψ₂ y)
    (hV₁0 : ∀ y, 0 ≤ V₁ y) (hV₂0 : ∀ y, 0 ≤ V₂ y)
    (hflow : ∀ y : State,
      Nonempty (PDMPFlowFinPair M 0 (fun s => ψ₁ s * V₁ s)
        (fun s => lam * (ψ₂ s * V₂ s)) y) ∨
      Nonempty (PDMPFlowInfPair M 0 (fun s => ψ₁ s * V₁ s)
        (fun s => lam * (ψ₂ s * V₂ s)) y))
    (hjump : ∀ y : State, ∀ᵐ z ∂(M.jump (y, ExitKind.guard)),
      ψ₁ z * V₁ z ≤ ψ₁ y * V₁ y ∧ lam * (ψ₂ z * V₂ z) ≤ lam * (ψ₂ y * V₂ y))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hAC : ∀ y, ψ₁ y * V₁ y ≤ C) (hBC : ∀ y, lam * (ψ₂ y * V₂ y) ≤ C)
    (hFloor₁ : ∀ y ∈ U₁, 1 ≤ V₁ y) (hFloor₂ : ∀ y ∈ U₂, 1 ≤ lam' * V₂ y)
    (x : State) :
    Battery.pathMeasure (skel M) (SkelState.alive x)
        {ω | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)}
      ≤ ENNReal.ofReal
          (max (ψ₁ x * V₁ x) (lam * (ψ₂ x * V₂ x)) / min 1 (lam / lam')) := by
  refine sound_NPDMPII_maxform (hψ₁.mul hV₁) ((hψ₂.mul hV₂).const_mul lam)
    hU₁ hU₂ hlam hlam' hflow hjump
    (fun y => mul_nonneg (le_trans zero_le_one (hψ₁1 y)) (hV₁0 y))
    hC0 hAC hBC (fun y hy => ?_) (fun y hy => ?_) x
  ·
    exact le_trans (hFloor₁ y hy) (le_mul_of_one_le_left (hV₁0 y) (hψ₁1 y))
  ·
    have h1 : 1 / lam' ≤ V₂ y := by
      rw [div_le_iff₀ hlam']
      linarith [hFloor₂ y hy]
    calc lam / lam' = lam * (1 / lam') := by rw [mul_one_div]
      _ ≤ lam * V₂ y := mul_le_mul_of_nonneg_left h1 hlam.le
      _ ≤ lam * (ψ₂ y * V₂ y) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (hV₂0 y) (hψ₂1 y)) hlam.le

theorem sound_NPDMPII_maxform_battery [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {U₁ U₂ : Set State} {lam lam' : ℝ} {p thr : ℝ}
    (hA : Measurable A) (hB : Measurable B)
    (hU₁ : MeasurableSet U₁) (hU₂ : MeasurableSet U₂)
    (hlam : 0 < lam) (hlam' : 0 < lam')
    (hflow : ∀ y : State,
      Nonempty (PDMPFlowFinPair M 0 A B y) ∨ Nonempty (PDMPFlowInfPair M 0 A B y))
    (hjump : ∀ y : State,
      ∀ᵐ z ∂(M.jump (y, ExitKind.guard)), A z ≤ A y ∧ B z ≤ B y)
    (hA0 : ∀ y, 0 ≤ A y)
    {C : ℝ} (hC0 : 0 ≤ C) (hAC : ∀ y, A y ≤ C) (hBC : ∀ y, B y ≤ C)
    (hFloor₁ : ∀ y ∈ U₁, 1 ≤ A y) (hFloor₂ : ∀ y ∈ U₂, lam / lam' ≤ B y)
    (hΘ : p + thr ≤ 1) (x : State)
    (hthr : max (A x) (B x) / min 1 (lam / lam') ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ n, ω n ∉ skelBad (U₁ ∪ U₂)} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]
    exact zero_le
  have hreach := sound_NPDMPII_maxform hA hB hU₁ hU₂ hlam hlam' hflow hjump
    hA0 hC0 hAC hBC hFloor₁ hFloor₂ x
  have h1 : Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)} ≤ ENNReal.ofReal thr :=
    hreach.trans (ENNReal.ofReal_le_ofReal hthr)
  have hnever : {ω : ℕ → SkelState State | ∀ n, ω n ∉ skelBad (U₁ ∪ U₂)}
      = {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists]
  have hreachMeas : MeasurableSet
      {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)} := by
    have h : {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad (U₁ ∪ U₂)}
        = ⋃ n, (fun ω : ℕ → SkelState State => ω n) ⁻¹' skelBad (U₁ ∪ U₂) := by
      ext ω; simp
    rw [h]
    exact MeasurableSet.iUnion fun n =>
      (measurable_pi_apply n) (measurableSet_skelBad (hU₁.union hU₂))
  have hm : (0:ℝ) < min 1 (lam / lam') := lt_min one_pos (div_pos hlam hlam')
  have hthr0 : 0 ≤ thr :=
    le_trans (div_nonneg (le_trans (hA0 x) (le_max_left _ _)) hm.le) hthr
  rw [hnever, prob_compl_eq_one_sub hreachMeas]
  refine le_trans ?_ (tsub_le_tsub_left h1 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add hthr0 hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Qtsl.LayerD

#print axioms Qtsl.Gauge.max_jump_nonexpansive
#print axioms Qtsl.LayerD.max_endpoint_le
#print axioms Qtsl.LayerD.pdmp_dynkin_core_max
#print axioms Qtsl.LayerD.PDMPFlowFinPair.segD_at
#print axioms Qtsl.LayerD.PDMPFlowInfPair.segD_at
#print axioms Qtsl.LayerD.segmentDynkin_of_pdmp_max
#print axioms Qtsl.LayerD.forcedNonexpansion_max_of_pathwise
#print axioms Qtsl.LayerD.sound_GSHS_safety_barrier
#print axioms Qtsl.LayerD.sound_NPDMPII_maxform
#print axioms Qtsl.LayerD.sound_NPDMPII_maxform_gauged
#print axioms Qtsl.LayerD.sound_NPDMPII_maxform_battery
