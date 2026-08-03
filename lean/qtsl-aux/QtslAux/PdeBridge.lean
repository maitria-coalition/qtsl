import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Analytic bridge lemmas for periodic energy arguments

This module collects the real- and Fourier-analytic ingredients used to certify
energy decay for periodic evolution equations.

Principal declarations:

* `integral_deriv_eq_zero_of_periodic`: the integral of a derivative over one
  period vanishes.
* `energy_decay_of_deriv_right_le` and `absorbing_ball_of_deriv_right_le`:
  Grönwall-type bounds. If an energy functional `En` satisfies
  `En' t ≤ -α * En t` (resp. `En' t ≤ -δ * En t + c`) on `[0, b]`, then
  `En t ≤ En 0 * exp (-α * t)` (resp. `En t ≤ En 0 * exp (-δ * t) + c / δ`).
* `hasDerivAt_intervalIntegral_of_continuous`: differentiation under the
  interval integral sign for jointly continuous integrands, by local
  domination on a compact rectangle.
* `fourierCoeffOn_zero_eq_mean`, `fourierCoeffOn_deriv_of_periodic`,
  `fourierCoeffOn_deriv_zero_of_periodic`, `parseval_tsum_sq_fourierCoeffOn`:
  the zeroth Fourier coefficient is the mean, the coefficients of the
  derivative of a periodic function are `2πin/(b-a)` times those of the
  function, and Parseval's identity on an interval.
* `wirtinger_interval`: the Wirtinger/Poincaré inequality. A continuously
  differentiable periodic function with zero mean on an interval of length at
  most `2π` satisfies `∫ ‖u‖² ≤ ∫ ‖u'‖²`, proved by comparing Fourier modes
  termwise.
-/

open MeasureTheory intervalIntegral Set

namespace Qtsl

namespace PdeBridge

theorem integral_deriv_eq_zero_of_periodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F F' : ℝ → E} {a T : ℝ}
    (hderiv : ∀ x ∈ uIcc a (a + T), HasDerivAt F (F' x) x)
    (hint : IntervalIntegrable F' volume a (a + T))
    (hper : F (a + T) = F a) :
    ∫ x in a..(a + T), F' x = 0 := by
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, hper, sub_self]

theorem intervalIntegral_sigma_nonneg {σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hσ : ∀ x ∈ Icc a b, 0 ≤ σ x) :
    0 ≤ ∫ x in a..b, σ x :=
  intervalIntegral.integral_nonneg hab hσ

theorem integral_sigma_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {σ : α → ℝ} (hσ : 0 ≤ σ) :
    0 ≤ ∫ x, σ x ∂μ :=
  MeasureTheory.integral_nonneg hσ

theorem energy_decay_of_deriv_right_le {En En' : ℝ → ℝ} {α b : ℝ}
    (hcont : ContinuousOn En (Icc 0 b))
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt En (En' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, En' t ≤ -α * En t) :
    ∀ t ∈ Icc 0 b, En t ≤ En 0 * Real.exp (-α * t) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (δ := En 0) (K := -α) (ε := 0)
    hcont (fun x hx r hr => (hderiv x hx).liminf_right_slope_le hr) le_rfl
    (fun x hx => by simpa using hbound x hx) t ht
  simpa [gronwallBound_ε0] using h

theorem absorbing_ball_of_deriv_right_le {En En' : ℝ → ℝ} {δ c b : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c)
    (hcont : ContinuousOn En (Icc 0 b))
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt En (En' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, En' t ≤ -δ * En t + c) :
    ∀ t ∈ Icc 0 b, En t ≤ En 0 * Real.exp (-δ * t) + c / δ := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (δ := En 0) (K := -δ) (ε := c)
    hcont (fun x hx r hr => (hderiv x hx).liminf_right_slope_le hr) le_rfl
    hbound t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hδ.ne'), sub_zero] at h
  refine h.trans ?_
  have hp : 0 ≤ c / δ := div_nonneg hc hδ.le
  have hx0 : (0 : ℝ) < Real.exp (-δ * t) := Real.exp_pos _
  have : c / -δ * (Real.exp (-δ * t) - 1) ≤ c / δ := by
    rw [div_neg, neg_mul]
    nlinarith [mul_nonneg hp hx0.le]
  linarith

theorem hasDerivAt_intervalIntegral_of_continuous {F F' : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ t x, HasDerivAt (fun s => F s x) (F' t x) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ x in a..b, F t x) (∫ x in a..b, F' t₀ x) t₀ := by

  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Metric.closedBall t₀ 1 ×ˢ uIcc a b,
      ‖Function.uncurry F' p‖ ≤ C :=
    ((isCompact_closedBall t₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
      hF'.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := t₀) (a := a) (b := b) (μ := volume)
    (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      (hF.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
    ((hF.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable a b)
    (hF'.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x hx t ht => hC (t, x) ⟨ht, uIoc_subset_uIcc hx⟩)
    (intervalIntegrable_const)
    (MeasureTheory.ae_of_all _ fun x _ t _ => hdiff t x)
  exact key.2

section Fourier

open Complex

theorem fourierCoeffOn_zero_eq_mean {a b : ℝ} (hab : a < b) (u : ℝ → ℂ) :
    fourierCoeffOn hab u 0 = (1 / (b - a) : ℝ) • ∫ x in a..b, u x := by
  rw [fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp

theorem fourierCoeffOn_zero_eq_zero_of_mean_zero {a b : ℝ} (hab : a < b) {u : ℝ → ℂ}
    (hmean : ∫ x in a..b, u x = 0) :
    fourierCoeffOn hab u 0 = 0 := by
  rw [fourierCoeffOn_zero_eq_mean hab u, hmean, smul_zero]

theorem parseval_tsum_sq_fourierCoeffOn {a b : ℝ} {u : ℝ → ℂ} (hab : a < b)
    (hu : MemLp u 2 (volume.restrict (Ioc a b))) :
    ∑' k : ℤ, ‖fourierCoeffOn hab u k‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖u x‖ ^ 2 :=
  tsum_sq_fourierCoeffOn hab hu

theorem fourierCoeffOn_deriv_of_periodic {a b : ℝ} (hab : a < b) {u u' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hper : u b = u a) :
    fourierCoeffOn hab u' n =
      (2 * Real.pi * Complex.I * n / ((b : ℂ) - a)) * fourierCoeffOn hab u n := by
  have key := fourierCoeffOn_of_hasDerivAt hab hn hu hu'
  rw [hper, sub_self, mul_zero, zero_sub] at key
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hba : ((b : ℂ) - a) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hab.ne')
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at key

  rw [div_mul_eq_mul_div, eq_div_iff hba]
  linear_combination -key

theorem fourierCoeffOn_deriv_zero_of_periodic {a b : ℝ} (hab : a < b) {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hper : u b = u a) :
    fourierCoeffOn hab u' 0 = 0 := by
  refine fourierCoeffOn_zero_eq_zero_of_mean_zero hab ?_
  rw [integral_eq_sub_of_hasDerivAt hu hu', hper, sub_self]

end Fourier

theorem tsum_mode_nonneg {g : ℤ → ℝ} (hg : ∀ k, 0 ≤ g k) : 0 ≤ ∑' k, g k :=
  tsum_nonneg hg

theorem le_of_hasSum_of_termwise_le {f g : ℤ → ℝ} {A B : ℝ}
    (h : ∀ k, f k ≤ g k) (hf : HasSum f A) (hg : HasSum g B) : A ≤ B :=
  hasSum_le h hf hg

section Wirtinger

open Complex

private theorem memLp_two_of_continuous {a b : ℝ} {u : ℝ → ℂ}
    (hu : Continuous u) : MemLp u 2 (volume.restrict (Ioc a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hu.continuousOn
  refine MemLp.of_bound hu.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Ioc_subset_Icc_self hx)

theorem wirtinger_interval {a b : ℝ} (hab : a < b) (hlen : b - a ≤ 2 * Real.pi)
    {u u' : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u')
    (hper : u b = u a)
    (hmean : ∫ x in a..b, u x = 0) :
    ∫ x in a..b, ‖u x‖ ^ 2 ≤ ∫ x in a..b, ‖u' x‖ ^ 2 := by
  have hucont : Continuous u := by
    rw [continuous_iff_continuousAt]; exact fun x => (hu x).continuousAt

  have hPu := hasSum_sq_fourierCoeffOn hab (memLp_two_of_continuous hucont)
  have hPu' := hasSum_sq_fourierCoeffOn hab (memLp_two_of_continuous hu')
  have hbapos : (0 : ℝ) < b - a := sub_pos.mpr hab

  have hterm : ∀ k : ℤ, ‖fourierCoeffOn hab u k‖ ^ 2 ≤ ‖fourierCoeffOn hab u' k‖ ^ 2 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [fourierCoeffOn_zero_eq_zero_of_mean_zero hab hmean]
      simp
    · rw [fourierCoeffOn_deriv_of_periodic hab hk (fun x _ => hu x)
        (hu'.intervalIntegrable a b) hper, norm_mul, mul_pow]
      have hk1 : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
        rw [Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs hk
      have hnorm : (1 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b : ℂ) - a)‖ := by
        have hden : ‖((b : ℂ) - a)‖ = b - a := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hbapos.le]
        rw [norm_div, hden, one_le_div hbapos]
        calc b - a ≤ 2 * Real.pi := hlen
          _ = 2 * Real.pi * 1 := (mul_one _).symm
          _ ≤ 2 * Real.pi * ‖(k : ℂ)‖ := by
              have : (0 : ℝ) ≤ 2 * Real.pi := by positivity
              exact mul_le_mul_of_nonneg_left hk1 this
          _ = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * k‖ := by
              simp [Complex.norm_I, Complex.norm_real, abs_of_pos Real.pi_pos]
      calc ‖fourierCoeffOn hab u k‖ ^ 2
          = 1 * ‖fourierCoeffOn hab u k‖ ^ 2 := (one_mul _).symm
        _ ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b : ℂ) - a)‖ ^ 2 *
              ‖fourierCoeffOn hab u k‖ ^ 2 := by
            have h1 : (1 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b : ℂ) - a)‖ ^ 2 := by
              nlinarith [hnorm]
            exact mul_le_mul_of_nonneg_right h1 (by positivity)

  have hfin := hasSum_le hterm hPu hPu'
  rw [smul_eq_mul, smul_eq_mul] at hfin
  exact le_of_mul_le_mul_left hfin (inv_pos.mpr hbapos)

end Wirtinger

end PdeBridge

end Qtsl

#print axioms Qtsl.PdeBridge.integral_deriv_eq_zero_of_periodic
#print axioms Qtsl.PdeBridge.intervalIntegral_sigma_nonneg
#print axioms Qtsl.PdeBridge.integral_sigma_nonneg
#print axioms Qtsl.PdeBridge.energy_decay_of_deriv_right_le
#print axioms Qtsl.PdeBridge.absorbing_ball_of_deriv_right_le
#print axioms Qtsl.PdeBridge.hasDerivAt_intervalIntegral_of_continuous
#print axioms Qtsl.PdeBridge.fourierCoeffOn_zero_eq_mean
#print axioms Qtsl.PdeBridge.fourierCoeffOn_zero_eq_zero_of_mean_zero
#print axioms Qtsl.PdeBridge.parseval_tsum_sq_fourierCoeffOn
#print axioms Qtsl.PdeBridge.fourierCoeffOn_deriv_of_periodic
#print axioms Qtsl.PdeBridge.fourierCoeffOn_deriv_zero_of_periodic
#print axioms Qtsl.PdeBridge.tsum_mode_nonneg
#print axioms Qtsl.PdeBridge.le_of_hasSum_of_termwise_le
#print axioms Qtsl.PdeBridge.wirtinger_interval
