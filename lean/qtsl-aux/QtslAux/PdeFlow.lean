import QtslAux.PdeBridge
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Fourier-mode evolution for a linear fourth-order periodic flow

This module tracks individual Fourier modes of a time-dependent periodic
function `u : ℝ → ℝ → ℂ` governed by the linear equation
`∂ₜ u = -(∂ₓ⁴ u) - ∂ₓ² u` (the linearization of the Kuramoto–Sivashinsky
equation) on an interval of length `2π`.

Principal declarations:

* `hasDerivAt_intervalIntegral_of_continuous'`: vector-valued differentiation
  under the interval integral sign.
* `fourierCoeffOn_eq_mul_integral`: the Fourier coefficient written as an
  explicit weighted integral.
* `hasDerivAt_fourierCoeffOn`: each Fourier coefficient of `u t` is
  differentiable in time, with derivative the corresponding coefficient of
  `∂ₜ u`.
* `fourierCoeffOn_deriv_two_pi`: on an interval of length exactly `2π`, the
  spatial derivative acts on the `n`-th coefficient as multiplication by
  `I * n`.
* `linear_mode_evolution`: for a classical periodic solution of
  `∂ₜ u = -u₄ - u₂` (with spatial jet `u₁, …, u₄`), the `n`-th coefficient
  evolves exactly as `exp ((n² - n⁴) * t)` times its initial value, by solving
  the resulting scalar linear ODE.
* `spectral_support_invariance`: consequently a mode that vanishes at time `0`
  vanishes for all time.
-/

open MeasureTheory intervalIntegral Set

namespace Qtsl

namespace PdeFlow

theorem hasDerivAt_intervalIntegral_of_continuous' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F F' : ℝ → ℝ → E} {a b : ℝ}
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

theorem fourierCoeffOn_eq_mul_integral {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hab f n
      = ((1 / (b - a) : ℝ) : ℂ)
          * ∫ x in a..b, (fourier (-n) (x : AddCircle (b - a)) : ℂ) * f x := by
  rw [fourierCoeffOn_eq_integral f n hab, Complex.real_smul]
  have hint : (fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) • f x)
      = fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * f x := by
    funext x
    simp [smul_eq_mul]
  rw [hint]

theorem hasDerivAt_fourierCoeffOn {u w : ℝ → ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hu : Continuous (Function.uncurry u)) (hw : Continuous (Function.uncurry w))
    (hdiff : ∀ t x, HasDerivAt (fun s => u s x) (w t x) t) (n : ℤ) (t₀ : ℝ) :
    HasDerivAt (fun t => fourierCoeffOn hab (u t) n)
      (fourierCoeffOn hab (w t₀) n) t₀ := by
  have hcoe : Continuous fun x : ℝ => (x : AddCircle (b - a)) := by continuity
  have he : Continuous fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) :=
    (fourier (-n)).continuous.comp hcoe
  have key := hasDerivAt_intervalIntegral_of_continuous'
    (F := fun t (x : ℝ) => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * u t x)
    (F' := fun t (x : ℝ) => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * w t x)
    (a := a) (b := b)
    ((he.comp continuous_snd).mul hu)
    ((he.comp continuous_snd).mul hw)
    (fun t x => (hdiff t x).const_mul _) t₀
  have h1 : (fun t => fourierCoeffOn hab (u t) n)
      = fun t => ((1 / (b - a) : ℝ) : ℂ)
          * ∫ x in a..b, (fourier (-n) (x : AddCircle (b - a)) : ℂ) * u t x :=
    funext fun t => fourierCoeffOn_eq_mul_integral hab (u t) n
  rw [h1, fourierCoeffOn_eq_mul_integral hab (w t₀) n]
  exact key.const_mul _

theorem fourierCoeffOn_neg_sub {a b : ℝ} (hab : a < b) {f g : ℝ → ℂ} (n : ℤ)
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b)) :
    fourierCoeffOn hab (fun x => -f x - g x) n
      = -(fourierCoeffOn hab f n) - fourierCoeffOn hab g n := by
  have hcoe : Continuous fun x : ℝ => (x : AddCircle (b - a)) := by continuity
  have he : Continuous fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) :=
    (fourier (-n)).continuous.comp hcoe
  have hef : IntervalIntegrable
      (fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * f x) volume a b :=
    (he.continuousOn.mul hf).intervalIntegrable
  have heg : IntervalIntegrable
      (fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * g x) volume a b :=
    (he.continuousOn.mul hg).intervalIntegrable
  rw [fourierCoeffOn_eq_mul_integral hab _ n, fourierCoeffOn_eq_mul_integral hab f n,
    fourierCoeffOn_eq_mul_integral hab g n, ← mul_neg, ← mul_sub]
  congr 1
  have hcongr : (fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) * (-f x - g x))
      = fun x : ℝ => -((fourier (-n) (x : AddCircle (b - a)) : ℂ) * f x)
          - (fourier (-n) (x : AddCircle (b - a)) : ℂ) * g x := by
    funext x
    ring
  have hefneg : IntervalIntegrable
      (fun x : ℝ => -((fourier (-n) (x : AddCircle (b - a)) : ℂ) * f x)) volume a b :=
    hef.neg
  rw [hcongr, intervalIntegral.integral_sub hefneg heg,
    intervalIntegral.integral_neg]

theorem fourierCoeffOn_deriv_two_pi {a b : ℝ} (hab : a < b)
    (hlen : b - a = 2 * Real.pi) {f f' : ℝ → ℂ} (n : ℤ)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hper : f b = f a) :
    fourierCoeffOn hab f' n = (Complex.I * n) * fourierCoeffOn hab f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [PdeBridge.fourierCoeffOn_deriv_zero_of_periodic hab hf hf' hper]
    simp
  · rw [PdeBridge.fourierCoeffOn_deriv_of_periodic hab hn hf hf' hper]
    congr 1
    have hba : ((b : ℂ) - a) = 2 * (Real.pi : ℂ) := by
      rw [← Complex.ofReal_sub, hlen]
      push_cast
      ring
    rw [hba]
    have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

theorem linear_mode_evolution {a b : ℝ} (hab : a < b)
    (hlen : b - a = 2 * Real.pi)
    {u u₁ u₂ u₃ u₄ w : ℝ → ℝ → ℂ}
    (hu : Continuous (Function.uncurry u)) (hw : Continuous (Function.uncurry w))
    (hj1 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u t) (u₁ t x) x)
    (hj2 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₁ t) (u₂ t x) x)
    (hj3 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₂ t) (u₃ t x) x)
    (hj4 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₃ t) (u₄ t x) x)
    (hc1 : ∀ t, ContinuousOn (u₁ t) (uIcc a b))
    (hc2 : ∀ t, ContinuousOn (u₂ t) (uIcc a b))
    (hc3 : ∀ t, ContinuousOn (u₃ t) (uIcc a b))
    (hc4 : ∀ t, ContinuousOn (u₄ t) (uIcc a b))
    (hp0 : ∀ t, u t b = u t a) (hp1 : ∀ t, u₁ t b = u₁ t a)
    (hp2 : ∀ t, u₂ t b = u₂ t a) (hp3 : ∀ t, u₃ t b = u₃ t a)
    (hdiff : ∀ t x, HasDerivAt (fun s => u s x) (w t x) t)
    (hmech : ∀ t x, w t x = -(u₄ t x) - u₂ t x)
    (n : ℤ) (t : ℝ) :
    fourierCoeffOn hab (u t) n
      = Complex.exp (((n : ℂ) ^ 2 - (n : ℂ) ^ 4) * t) * fourierCoeffOn hab (u 0) n := by
  set y : ℝ → ℂ := fun s => fourierCoeffOn hab (u s) n with hy

  have hyd : ∀ s, HasDerivAt y (((n : ℂ) ^ 2 - (n : ℂ) ^ 4) * y s) s := by
    intro s
    have h0 := hasDerivAt_fourierCoeffOn hab hu hw hdiff n s
    have hws : w s = fun x => -(u₄ s x) - u₂ s x := funext fun x => hmech s x
    have e1 := fourierCoeffOn_deriv_two_pi hab hlen n (hj1 s)
      ((hc1 s).intervalIntegrable) (hp0 s)
    have e2 := fourierCoeffOn_deriv_two_pi hab hlen n (hj2 s)
      ((hc2 s).intervalIntegrable) (hp1 s)
    have e3 := fourierCoeffOn_deriv_two_pi hab hlen n (hj3 s)
      ((hc3 s).intervalIntegrable) (hp2 s)
    have e4 := fourierCoeffOn_deriv_two_pi hab hlen n (hj4 s)
      ((hc4 s).intervalIntegrable) (hp3 s)
    have hcoeff : fourierCoeffOn hab (w s) n = ((n : ℂ) ^ 2 - (n : ℂ) ^ 4) * y s := by
      rw [hws, fourierCoeffOn_neg_sub hab n (hc4 s) (hc2 s), e4, e3, e2, e1]
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      have hI4 : Complex.I ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hI2]
        ring
      simp only [hy]
      calc -(Complex.I * n * (Complex.I * n * (Complex.I * n * (Complex.I * n *
              fourierCoeffOn hab (u s) n))))
            - Complex.I * n * (Complex.I * n * fourierCoeffOn hab (u s) n)
          = -(Complex.I ^ 4 * (n : ℂ) ^ 4 * fourierCoeffOn hab (u s) n)
            - Complex.I ^ 2 * (n : ℂ) ^ 2 * fourierCoeffOn hab (u s) n := by ring
        _ = ((n : ℂ) ^ 2 - (n : ℂ) ^ 4) * fourierCoeffOn hab (u s) n := by
            rw [hI2, hI4]; ring
    rwa [hcoeff] at h0

  set μ : ℂ := (n : ℂ) ^ 2 - (n : ℂ) ^ 4 with hμ
  have hz : ∀ s : ℝ, HasDerivAt (fun τ : ℝ => Complex.exp (-μ * τ) * y τ) 0 s := by
    intro s
    have hlin : HasDerivAt (fun τ : ℝ => -μ * (τ : ℂ)) (-μ) s := by
      have hid := (hasDerivAt_id s).ofReal_comp
      simpa using hid.const_mul (-μ)
    have hexp : HasDerivAt (fun τ : ℝ => Complex.exp (-μ * τ))
        (Complex.exp (-μ * s) * -μ) s := hlin.cexp
    have hmul := hexp.mul (hyd s)
    have hval : Complex.exp (-μ * (s : ℂ)) * -μ * y s
        + Complex.exp (-μ * (s : ℂ)) * (μ * y s) = 0 := by ring
    rw [hval] at hmul
    exact hmul
  have hconst : ∀ s : ℝ, Complex.exp (-μ * s) * y s = Complex.exp (-μ * 0) * y 0 := by
    intro s
    rcases le_total 0 s with h | h
    · exact constant_of_has_deriv_right_zero
        (fun r hr => ((hz r).continuousAt).continuousWithinAt)
        (fun r _ => (hz r).hasDerivWithinAt) s (right_mem_Icc.mpr h)
    · exact (constant_of_has_deriv_right_zero
        (fun r hr => ((hz r).continuousAt).continuousWithinAt)
        (fun r _ => (hz r).hasDerivWithinAt) 0 (right_mem_Icc.mpr h)).symm
  have h0 : Complex.exp (-μ * 0) * y 0 = y 0 := by
    simp
  have hc := hconst t
  rw [h0] at hc
  have hcancel : μ * t + -μ * t = 0 := by ring
  calc y t = Complex.exp (μ * t) * (Complex.exp (-μ * t) * y t) := by
        rw [← mul_assoc, ← Complex.exp_add, hcancel, Complex.exp_zero, one_mul]
    _ = Complex.exp (μ * t) * y 0 := by rw [hc]

theorem spectral_support_invariance {a b : ℝ} (hab : a < b)
    (hlen : b - a = 2 * Real.pi)
    {u u₁ u₂ u₃ u₄ w : ℝ → ℝ → ℂ}
    (hu : Continuous (Function.uncurry u)) (hw : Continuous (Function.uncurry w))
    (hj1 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u t) (u₁ t x) x)
    (hj2 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₁ t) (u₂ t x) x)
    (hj3 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₂ t) (u₃ t x) x)
    (hj4 : ∀ t, ∀ x ∈ uIcc a b, HasDerivAt (u₃ t) (u₄ t x) x)
    (hc1 : ∀ t, ContinuousOn (u₁ t) (uIcc a b))
    (hc2 : ∀ t, ContinuousOn (u₂ t) (uIcc a b))
    (hc3 : ∀ t, ContinuousOn (u₃ t) (uIcc a b))
    (hc4 : ∀ t, ContinuousOn (u₄ t) (uIcc a b))
    (hp0 : ∀ t, u t b = u t a) (hp1 : ∀ t, u₁ t b = u₁ t a)
    (hp2 : ∀ t, u₂ t b = u₂ t a) (hp3 : ∀ t, u₃ t b = u₃ t a)
    (hdiff : ∀ t x, HasDerivAt (fun s => u s x) (w t x) t)
    (hmech : ∀ t x, w t x = -(u₄ t x) - u₂ t x)
    {n : ℤ} (hzero : fourierCoeffOn hab (u 0) n = 0) (t : ℝ) :
    fourierCoeffOn hab (u t) n = 0 := by
  rw [linear_mode_evolution hab hlen hu hw hj1 hj2 hj3 hj4 hc1 hc2 hc3 hc4
    hp0 hp1 hp2 hp3 hdiff hmech n t, hzero, mul_zero]

end PdeFlow

end Qtsl

#print axioms Qtsl.PdeFlow.hasDerivAt_intervalIntegral_of_continuous'
#print axioms Qtsl.PdeFlow.hasDerivAt_fourierCoeffOn
#print axioms Qtsl.PdeFlow.fourierCoeffOn_neg_sub
#print axioms Qtsl.PdeFlow.fourierCoeffOn_deriv_two_pi
#print axioms Qtsl.PdeFlow.linear_mode_evolution
#print axioms Qtsl.PdeFlow.spectral_support_invariance
