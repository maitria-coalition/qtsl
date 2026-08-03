import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Dini-derivative comparison lemmas

This module proves Grönwall-type bounds from one-sided (upper Dini) derivative
estimates, together with supporting facts about periodic functions. These
serve certificates for energy functionals that are continuous but not known to
be differentiable.

Principal declarations:

* `DiniUpperLE V φ s`: the upper right Dini derivative of `V` is bounded by
  `φ` at every point of `s`, phrased via forward difference quotients
  eventually below any `r > φ t`.
* `absorbing_ball_of_dini_le`: if `V` is continuous on `[0, b]` and satisfies
  `DiniUpperLE V (fun t => -δ * V t + c)` on `[0, b)`, then
  `V t ≤ V 0 * exp (-δ * t) + c / δ` — the absorbing-ball estimate with only
  Dini-derivative data.
* `eventually_slope_lt_of_touching`: a comparison principle. If `F` touches
  `V` from above at `t` (`V t = F t`, `V ≤ F`) and `F` has right derivative
  `d < r` at `t`, then the forward difference quotients of `V` at `t` are
  eventually below `r`.
* `exists_forall_le_of_periodic`: a continuous periodic function on `ℝ`
  attains a global minimum.
* `hasDerivAt_eq_zero_of_forall_le`: the derivative vanishes at a global
  minimum.
* `integral_translate_eq`: translation invariance of the integral of a
  periodic function over one period.
-/

open Set Filter Topology

namespace Qtsl

namespace PdeDini

def DiniUpperLE (V φ : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ r, φ t < r → ∀ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (V z - V t) < r

theorem absorbing_ball_of_dini_le {V : ℝ → ℝ} {δ c b : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c)
    (hcont : ContinuousOn V (Icc 0 b))
    (hdini : DiniUpperLE V (fun t => -δ * V t + c) (Ico 0 b)) :
    ∀ t ∈ Icc 0 b, V t ≤ V 0 * Real.exp (-δ * t) + c / δ := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := V) (f' := fun t => -δ * V t + c) (δ := V 0) (K := -δ) (ε := c) (a := 0) (b := b)
    hcont (fun x hx r hr => (hdini x hx r hr).frequently) le_rfl
    (fun x _ => le_rfl) t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hδ.ne'), sub_zero] at h
  refine h.trans ?_
  have hp : 0 ≤ c / δ := div_nonneg hc hδ.le
  have hx0 : (0 : ℝ) < Real.exp (-δ * t) := Real.exp_pos _
  have : c / -δ * (Real.exp (-δ * t) - 1) ≤ c / δ := by
    rw [div_neg, neg_mul]
    nlinarith [mul_nonneg hp hx0.le]
  linarith

theorem eventually_slope_lt_of_touching {V F : ℝ → ℝ} {t d r : ℝ}
    (htouch : V t = F t) (hle : ∀ z, V z ≤ F z)
    (hF : HasDerivWithinAt F d (Ici t) t) (hr : d < r) :
    ∀ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (V z - V t) < r := by
  have hIci : Ici t \ {t} = Ioi t := by
    ext z
    simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le, h.ne'⟩
  have hslope : Tendsto (slope F t) (𝓝[>] t) (𝓝 d) := by
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp hF
    rwa [hIci] at h1
  have hev : ∀ᶠ z in 𝓝[>] t, slope F t z < r := hslope.eventually_lt_const hr
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hz'
  have hzt : t < z := hz'
  have hinv : (0 : ℝ) ≤ (z - t)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hzt.le)
  have hVF : V z - V t ≤ F z - F t := by
    have := hle z
    linarith [htouch]
  calc (z - t)⁻¹ * (V z - V t)
      ≤ (z - t)⁻¹ * (F z - F t) := mul_le_mul_of_nonneg_left hVF hinv
    _ = slope F t z := by rw [slope_def_field, div_eq_inv_mul]
    _ < r := hz

theorem exists_forall_le_of_periodic {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T) :
    ∃ θ, ∀ z, f θ ≤ f z := by
  obtain ⟨θ, hθmem, hθmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith : (0:ℝ) ≤ T))
      hf.continuousOn
  refine ⟨θ, fun z => ?_⟩
  have hz : toIcoMod hT 0 z ∈ Ico (0:ℝ) T := by
    simpa using toIcoMod_mem_Ico' hT z
  have hfz : f (toIcoMod hT 0 z) = f z := by
    simp only [toIcoMod]
    exact hper.sub_zsmul_eq _
  have hmin := isMinOn_iff.mp hθmin (toIcoMod hT 0 z) (Ico_subset_Icc_self hz)
  rw [hfz] at hmin
  exact hmin

theorem hasDerivAt_eq_zero_of_forall_le {f : ℝ → ℝ} {θ d : ℝ}
    (hmin : ∀ z, f θ ≤ f z) (hd : HasDerivAt f d θ) : d = 0 :=
  IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall fun z => hmin z) hd

theorem integral_translate_eq {f : ℝ → ℝ} {T a θ : ℝ}
    (hper : Function.Periodic f T) :
    ∫ x in a..(a + T), f (x + θ) = ∫ x in a..(a + T), f x := by
  rw [intervalIntegral.integral_comp_add_right]
  have h : a + T + θ = (a + θ) + T := by ring
  rw [h]
  exact hper.intervalIntegral_add_eq (a + θ) a

end PdeDini

end Qtsl

#print axioms Qtsl.PdeDini.absorbing_ball_of_dini_le
#print axioms Qtsl.PdeDini.eventually_slope_lt_of_touching
#print axioms Qtsl.PdeDini.exists_forall_le_of_periodic
#print axioms Qtsl.PdeDini.hasDerivAt_eq_zero_of_forall_le
#print axioms Qtsl.PdeDini.integral_translate_eq
