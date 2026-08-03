import QtslAux.PdeBridge
import QtslAux.PdeFlow
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Energy decay for weak solutions of a dissipative periodic equation

This module carries out the energy method at the weak-solution level, where
the spatial derivative is characterized only by integration by parts against
periodic test functions.

Principal declarations:

* `WeakEnergySolution ν a b`: a structure packaging a time-indexed pair
  `u, u₁` of `L²` functions on `(a, b]` such that `u₁` is the weak spatial
  derivative of `u` (via smooth periodic test functions), `u` has zero mean at
  every time, the dissipation is locally integrable in time, and the energy
  inequality `E(t) + 2ν ∫ₛᵗ D(τ) dτ ≤ E(s)` holds, where
  `E(t) = ∫ ‖u t‖²` and `D(τ) = ∫ ‖u₁ τ‖²`.
* `fourierCoeffOn_deriv_of_weak`: the Fourier-coefficient identity
  `c_k(u₁) = (2πik/(b-a)) c_k(u)` derived purely from the weak-derivative
  property, by testing against the exponentials.
* `wirtinger_of_weak`: the Wirtinger/Poincaré inequality
  `∫ ‖u‖² ≤ ∫ ‖u₁‖²` for mean-zero weak-`L²` pairs on an interval of length
  at most `2π`.
* `energy_antitone`: the energy is non-increasing in time.
* `energy_step`: the discrete decay step
  `E(t) * (1 + 2ν(t - s)) ≤ E(s)`, combining the energy inequality with the
  Wirtinger bound.
* `energy_decay`: exponential decay `E(t) ≤ E(0) * exp (-2νt)`, obtained by
  iterating `energy_step` over `n` subintervals and letting `n → ∞` against
  the compound-interest limit `(1 + x/n)ⁿ → exp x`.
-/

open MeasureTheory intervalIntegral Set

namespace Qtsl

namespace PdeRungW

structure WeakEnergySolution (ν a b : ℝ) where

  u : ℝ → ℝ → ℂ

  u₁ : ℝ → ℝ → ℂ

  memLp2 : ∀ t, 0 ≤ t → MemLp (u t) 2 (volume.restrict (Ioc a b))

  memLp2_deriv : ∀ t, 0 ≤ t → MemLp (u₁ t) 2 (volume.restrict (Ioc a b))

  weak_deriv : ∀ t, 0 ≤ t → ∀ (φ φ' : ℝ → ℂ), (∀ x, HasDerivAt φ (φ' x) x) →
    Continuous φ' → φ b = φ a →
    ∫ x in a..b, u t x * φ' x = -∫ x in a..b, u₁ t x * φ x

  mean_zero : ∀ t, 0 ≤ t → ∫ x in a..b, u t x = 0

  dissipation_integrable : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    IntervalIntegrable (fun τ => ∫ x in a..b, ‖u₁ τ x‖ ^ 2) volume s t

  energy_inequality : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (∫ x in a..b, ‖u t x‖ ^ 2)
      + 2 * ν * ∫ τ in s..t, ∫ x in a..b, ‖u₁ τ x‖ ^ 2
      ≤ ∫ x in a..b, ‖u s x‖ ^ 2

variable {ν a b : ℝ}

noncomputable def energyOn (S : WeakEnergySolution ν a b) (t : ℝ) : ℝ :=
  ∫ x in a..b, ‖S.u t x‖ ^ 2

theorem energyOn_nonneg (S : WeakEnergySolution ν a b) (hab : a ≤ b) (t : ℝ) :
    0 ≤ energyOn S t :=
  PdeBridge.intervalIntegral_sigma_nonneg hab (fun x _ => sq_nonneg _)

theorem fourierCoeffOn_deriv_of_weak {f f₁ : ℝ → ℂ} (hab : a < b)
    (hweak : ∀ (φ φ' : ℝ → ℂ), (∀ x, HasDerivAt φ (φ' x) x) →
      Continuous φ' → φ b = φ a →
      ∫ x in a..b, f x * φ' x = -∫ x in a..b, f₁ x * φ x)
    (k : ℤ) :
    fourierCoeffOn hab f₁ k
      = (2 * Real.pi * Complex.I * k / ((b - a : ℝ) : ℂ)) * fourierCoeffOn hab f k := by
  haveI : Fact (0 < b - a) := ⟨by linarith⟩
  set c : ℂ := 2 * Real.pi * Complex.I * k / ((b - a : ℝ) : ℂ) with hc

  have hφderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (fourier (-k) (y : AddCircle (b - a)) : ℂ))
      (-c * fourier (-k) (x : AddCircle (b - a))) x := by
    intro x
    have := hasDerivAt_fourier_neg (b - a) k x
    convert this using 1
    rw [hc]
    push_cast
    ring
  have hcoe : Continuous fun x : ℝ => (x : AddCircle (b - a)) := by continuity
  have hφ'cont : Continuous fun x : ℝ =>
      -c * (fourier (-k) (x : AddCircle (b - a)) : ℂ) :=
    continuous_const.mul ((fourier (-k)).continuous.comp hcoe)
  have hφper : (fourier (-k) ((b : ℝ) : AddCircle (b - a)) : ℂ)
      = fourier (-k) ((a : ℝ) : AddCircle (b - a)) := by
    have hcoeq : ((b : ℝ) : AddCircle (b - a)) = ((a : ℝ) : AddCircle (b - a)) := by
      have hb' : (b : ℝ) = a + (b - a) := by ring
      calc ((b : ℝ) : AddCircle (b - a))
          = ((a + (b - a) : ℝ) : AddCircle (b - a)) := by rw [← hb']
        _ = ((a : ℝ) : AddCircle (b - a)) := AddCircle.coe_add_period (b - a) a
    exact congrArg _ hcoeq
  have hpair := hweak (fun y : ℝ => (fourier (-k) (y : AddCircle (b - a)) : ℂ))
    (fun x : ℝ => -c * fourier (-k) (x : AddCircle (b - a)))
    hφderiv hφ'cont hφper

  have hlhs : ∫ x in a..b, f x * (-c * fourier (-k) (x : AddCircle (b - a)))
      = -c * ∫ x in a..b, (fourier (-k) (x : AddCircle (b - a)) : ℂ) * f x := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun x _ => ?_
    ring
  rw [hlhs] at hpair

  have hpair' : ∫ x in a..b, (fourier (-k) (x : AddCircle (b - a)) : ℂ) * f₁ x
      = c * ∫ x in a..b, (fourier (-k) (x : AddCircle (b - a)) : ℂ) * f x := by
    have hswap : ∫ x in a..b, f₁ x * fourier (-k) (x : AddCircle (b - a))
        = ∫ x in a..b, (fourier (-k) (x : AddCircle (b - a)) : ℂ) * f₁ x :=
      integral_congr fun x _ => mul_comm _ _
    rw [← hswap]
    linear_combination hpair
  rw [PdeFlow.fourierCoeffOn_eq_mul_integral hab f₁ k,
    PdeFlow.fourierCoeffOn_eq_mul_integral hab f k, hpair']
  ring

theorem wirtinger_of_weak {f f₁ : ℝ → ℂ} (hab : a < b)
    (hlen : b - a ≤ 2 * Real.pi)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hf₁ : MemLp f₁ 2 (volume.restrict (Ioc a b)))
    (hweak : ∀ (φ φ' : ℝ → ℂ), (∀ x, HasDerivAt φ (φ' x) x) →
      Continuous φ' → φ b = φ a →
      ∫ x in a..b, f x * φ' x = -∫ x in a..b, f₁ x * φ x)
    (hmean : ∫ x in a..b, f x = 0) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ∫ x in a..b, ‖f₁ x‖ ^ 2 := by
  have hbapos : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hPu := hasSum_sq_fourierCoeffOn hab hf
  have hPu' := hasSum_sq_fourierCoeffOn hab hf₁
  have hterm : ∀ k : ℤ, ‖fourierCoeffOn hab f k‖ ^ 2 ≤ ‖fourierCoeffOn hab f₁ k‖ ^ 2 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [PdeBridge.fourierCoeffOn_zero_eq_zero_of_mean_zero hab hmean]
      simp
    · rw [fourierCoeffOn_deriv_of_weak hab hweak k, norm_mul, mul_pow]
      have hk1 : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
        rw [Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs hk
      have hnorm : (1 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b - a : ℝ) : ℂ)‖ := by
        have hden : ‖((b - a : ℝ) : ℂ)‖ = b - a := by
          rw [Complex.norm_real, Real.norm_of_nonneg hbapos.le]
        rw [norm_div, hden, one_le_div hbapos]
        calc b - a ≤ 2 * Real.pi := hlen
          _ = 2 * Real.pi * 1 := (mul_one _).symm
          _ ≤ 2 * Real.pi * ‖(k : ℂ)‖ := by
              have : (0 : ℝ) ≤ 2 * Real.pi := by positivity
              exact mul_le_mul_of_nonneg_left hk1 this
          _ = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * k‖ := by
              simp [Complex.norm_I, Complex.norm_real, abs_of_pos Real.pi_pos]
      calc ‖fourierCoeffOn hab f k‖ ^ 2
          = 1 * ‖fourierCoeffOn hab f k‖ ^ 2 := (one_mul _).symm
        _ ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b - a : ℝ) : ℂ)‖ ^ 2 *
              ‖fourierCoeffOn hab f k‖ ^ 2 := by
            have h1 : (1 : ℝ)
                ≤ ‖2 * (Real.pi : ℂ) * Complex.I * k / ((b - a : ℝ) : ℂ)‖ ^ 2 := by
              nlinarith [hnorm]
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hfin := hasSum_le hterm hPu hPu'
  rw [smul_eq_mul, smul_eq_mul] at hfin
  exact le_of_mul_le_mul_left hfin (inv_pos.mpr hbapos)

theorem energy_antitone (S : WeakEnergySolution ν a b) (hab : a ≤ b) (hν : 0 ≤ ν)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    energyOn S t ≤ energyOn S s := by
  have hEI := S.energy_inequality s t hs hst
  have hD : 0 ≤ ∫ τ in s..t, ∫ x in a..b, ‖S.u₁ τ x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hst
      (fun τ _ => PdeBridge.intervalIntegral_sigma_nonneg hab (fun x _ => sq_nonneg _))
  have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hν) hD
  simp only [energyOn]
  linarith

theorem energy_step (S : WeakEnergySolution ν a b) (hab : a < b)
    (hlen : b - a ≤ 2 * Real.pi) (hν : 0 ≤ ν)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    energyOn S t * (1 + 2 * ν * (t - s)) ≤ energyOn S s := by
  simp only [energyOn]
  have hEI := S.energy_inequality s t hs hst

  have hDE : ∀ τ ∈ Icc s t,
      (∫ x in a..b, ‖S.u t x‖ ^ 2) ≤ ∫ x in a..b, ‖S.u₁ τ x‖ ^ 2 := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hs hτ.1
    have hw := wirtinger_of_weak hab hlen (S.memLp2 τ hτ0) (S.memLp2_deriv τ hτ0)
      (S.weak_deriv τ hτ0) (S.mean_zero τ hτ0)
    have hmono := energy_antitone S hab.le hν hτ0 hτ.2
    simp only [energyOn] at hmono
    exact le_trans hmono hw
  have hconst : IntervalIntegrable (fun _ : ℝ => ∫ x in a..b, ‖S.u t x‖ ^ 2) volume s t :=
    intervalIntegrable_const
  have hDint := S.dissipation_integrable s t hs hst
  have hmono2 := intervalIntegral.integral_mono_on hst hconst hDint hDE
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono2

  have h2ν : (0 : ℝ) ≤ 2 * ν := by linarith
  nlinarith [hEI, mul_le_mul_of_nonneg_left hmono2 h2ν]

theorem energy_decay (S : WeakEnergySolution ν a b) (hab : a < b)
    (hlen : b - a ≤ 2 * Real.pi) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) :
    energyOn S t ≤ energyOn S 0 * Real.exp (-(2 * ν * t)) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  have h2νt : (0 : ℝ) ≤ 2 * ν * t := mul_nonneg (mul_nonneg (by norm_num) hν) ht

  have hiter : ∀ n : ℕ, 0 < n → energyOn S t * (1 + 2 * ν * t / n) ^ n ≤ energyOn S 0 := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hΔ : 0 ≤ t / n := div_nonneg ht hnR.le
    have hcnn : (0 : ℝ) ≤ 1 + 2 * ν * t / n := by
      have := div_nonneg h2νt hnR.le
      linarith
    have key : ∀ j : ℕ, j ≤ n →
        energyOn S ((j : ℝ) * (t / n)) * (1 + 2 * ν * t / n) ^ j ≤ energyOn S 0 := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ i ih =>
        intro hij
        have h1 := ih (Nat.le_of_succ_le hij)
        have hsle : (i : ℝ) * (t / n) ≤ ((i : ℝ) + 1) * (t / n) := by nlinarith
        have hstep := energy_step S hab hlen hν
          (s := (i : ℝ) * (t / n)) (t := ((i : ℝ) + 1) * (t / n))
          (mul_nonneg (Nat.cast_nonneg i) hΔ) hsle
        have hdiff : ((i : ℝ) + 1) * (t / n) - (i : ℝ) * (t / n) = t / n := by ring
        rw [hdiff] at hstep
        have hgap : 2 * ν * (t / n) = 2 * ν * t / n := by ring
        rw [hgap] at hstep
        have hpow : (0 : ℝ) ≤ (1 + 2 * ν * t / n) ^ i := pow_nonneg hcnn i
        calc energyOn S (((i : ℕ) + 1 : ℕ) * (t / n)) * (1 + 2 * ν * t / n) ^ (i + 1)
            = (energyOn S (((i : ℝ) + 1) * (t / n)) * (1 + 2 * ν * t / n))
                * (1 + 2 * ν * t / n) ^ i := by
              push_cast
              ring
          _ ≤ energyOn S ((i : ℝ) * (t / n)) * (1 + 2 * ν * t / n) ^ i :=
              mul_le_mul_of_nonneg_right hstep hpow
          _ ≤ energyOn S 0 := h1
    have hfin := key n le_rfl
    have hnt : (n : ℝ) * (t / n) = t := by
      rw [mul_comm]
      exact div_mul_cancel₀ t hnR.ne'
    rw [hnt] at hfin
    exact hfin

  have hlim : Filter.Tendsto (fun n : ℕ => (1 + 2 * ν * t / n) ^ n)
      Filter.atTop (nhds (Real.exp (2 * ν * t))) := by
    have h := (Real.tendsto_one_add_div_rpow_exp (2 * ν * t)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    exact Real.rpow_natCast (1 + 2 * ν * t / n) n
  have hEt : Filter.Tendsto (fun n : ℕ => energyOn S t * (1 + 2 * ν * t / n) ^ n)
      Filter.atTop (nhds (energyOn S t * Real.exp (2 * ν * t))) :=
    hlim.const_mul _
  have hle : energyOn S t * Real.exp (2 * ν * t) ≤ energyOn S 0 :=
    le_of_tendsto hEt (Filter.eventually_atTop.mpr ⟨1, fun n hn => hiter n hn⟩)
  have hexp : (0 : ℝ) < Real.exp (2 * ν * t) := Real.exp_pos _
  have hdiv : energyOn S t ≤ energyOn S 0 / Real.exp (2 * ν * t) :=
    (le_div_iff₀ hexp).mpr hle
  rwa [div_eq_mul_inv, ← Real.exp_neg] at hdiv

end PdeRungW

end Qtsl

#print axioms Qtsl.PdeRungW.fourierCoeffOn_deriv_of_weak
#print axioms Qtsl.PdeRungW.wirtinger_of_weak
#print axioms Qtsl.PdeRungW.energy_antitone
#print axioms Qtsl.PdeRungW.energy_step
#print axioms Qtsl.PdeRungW.energy_decay
