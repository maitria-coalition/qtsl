import QtslAux.PdeBridge

/-! # Classical periodic solutions: energy identities, uniqueness, symmetry

This module studies classical (jet-carrying) periodic solutions of two
one-dimensional evolution equations and proves energy estimates, uniqueness,
and symmetry-persistence results.

Principal declarations:

* `integral_mul_deriv_eq_neg`: integration by parts over a period.
* `eqOn_zero_of_integral_sq`: a continuous function whose square integrates to
  zero vanishes on the interval.
* `IsClassicalBurgers ν L u u₁ u₂ ut`: the predicate that `u` is a classical
  `L`-periodic solution of the viscous Burgers equation
  `∂ₜ u = ν ∂ₓ² u - u ∂ₓ u`, with continuous space-time jet
  `u₁ = ∂ₓ u`, `u₂ = ∂ₓ² u`, `ut = ∂ₜ u`. For such solutions:
  `energy_hasDerivAt` (the energy `∫ u²` has time derivative
  `-2ν ∫ u₁²`), `mean_const` (the spatial mean is conserved), `energy_le`
  (energy is non-increasing), and `energy_decay_sharp` (for mean-zero data on
  a period of length at most `2π`, `∫ u(t)² ≤ (∫ u(0)²) exp (-2νt)` via the
  Wirtinger inequality).
* `burgers_uniqueness_rungC`: uniqueness of classical periodic Burgers
  solutions with common initial data, by a Grönwall argument on the difference
  energy with the quadratic term absorbed through a completed-square estimate.
* `IsClassicalKSE L u u₁ u₂ u₃ u₄ ut`: the analogous predicate for the
  Kuramoto–Sivashinsky equation `∂ₜ u = -∂ₓ⁴ u - ∂ₓ² u - u ∂ₓ u`, with
  `translate` and `reflect` producing new solutions from old.
* `kse_odd_persistence_of_uniqueness`: given a uniqueness hypothesis, odd
  initial data stays odd — the reflected solution agrees with the original.
-/

open MeasureTheory intervalIntegral Set

namespace Qtsl

namespace PdeUniqueness

theorem integral_mul_deriv_eq_neg {f f' g g' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hf'c : ContinuousOn f' (uIcc a b)) (hg'c : ContinuousOn g' (uIcc a b))
    (hper : f b * g b = f a * g a) :
    ∫ x in a..b, f x * g' x = -∫ x in a..b, f' x * g x := by
  have hfc : ContinuousOn f (uIcc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (uIcc a b) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have h1 : IntervalIntegrable (fun x => f' x * g x) volume a b :=
    (hf'c.mul hgc).intervalIntegrable
  have h2 : IntervalIntegrable (fun x => f x * g' x) volume a b :=
    (hfc.mul hg'c).intervalIntegrable
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun y => f y * g y) (f' x * g x + f x * g' x) x :=
    fun x hx => (hf x hx).mul (hg x hx)
  have hzero : ∫ x in a..b, (f' x * g x + f x * g' x) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt hd (h1.add h2), hper, sub_self]
  rw [integral_add h1 h2] at hzero
  linarith

theorem eqOn_zero_of_integral_sq {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Continuous f) (hzero : ∫ x in a..b, f x ^ 2 = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x => f x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg (f x)
  have hii : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    ((hf.pow 2).intervalIntegrable a b)
  have hnotpos : ¬ (0 < ∫ x in a..b, f x ^ 2) := by
    rw [hzero]
    exact lt_irrefl 0
  rw [integral_pos_iff_support_of_nonneg_ae hnn hii] at hnotpos
  push_neg at hnotpos
  have hμ0 : volume (Function.support (fun x => f x ^ 2) ∩ Ioc a b) = 0 :=
    le_zero_iff.mp (hnotpos hab)
  have hIoo : ∀ x ∈ Ioo a b, f x = 0 := by
    intro x hx
    by_contra hfx
    have hopen : IsOpen (Function.support f ∩ Ioo a b) :=
      hf.isOpen_support.inter isOpen_Ioo
    have hne : (Function.support f ∩ Ioo a b).Nonempty :=
      ⟨x, Function.mem_support.mpr hfx, hx⟩
    have hpos := hopen.measure_pos volume hne
    have hsub : Function.support f ∩ Ioo a b
        ⊆ Function.support (fun x => f x ^ 2) ∩ Ioc a b := by
      rintro y ⟨hy1, hy2⟩
      exact ⟨Function.mem_support.mpr (pow_ne_zero 2 (Function.mem_support.mp hy1)),
        Ioo_subset_Ioc_self hy2⟩
    have hle : volume (Function.support f ∩ Ioo a b)
        ≤ volume (Function.support (fun x => f x ^ 2) ∩ Ioc a b) :=
      measure_mono hsub
    rw [hμ0] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  have hIoo' : Set.EqOn f 0 (Ioo a b) := fun x hx => hIoo x hx
  have hcl : Set.EqOn f 0 (closure (Ioo a b)) := hIoo'.closure hf continuous_const
  rw [closure_Ioo hab.ne] at hcl
  exact fun x hx => hcl hx

private theorem contSlice {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    (t : ℝ) : Continuous (f t) :=
  hf.comp (Continuous.prodMk continuous_const continuous_id)

private theorem congr_value {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {va vb : F} {x : 𝕜}
    (h : HasDerivAt f va x) (hab : va = vb) : HasDerivAt f vb x := hab ▸ h

theorem periodic_deriv {f f' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hp : Function.Periodic f L) :
    Function.Periodic f' L := by
  intro x
  have h2 : HasDerivAt (fun y => f (y + L)) (f' (x + L)) x :=
    (hf (x + L)).comp_add_const x L
  have h3 : (fun y => f (y + L)) = f := funext fun y => hp y
  rw [h3] at h2
  exact h2.unique (hf x)

private theorem eq_const_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : ∀ s, HasDerivAt f 0 s) (t : ℝ) :
    f t = f 0 := by
  rcases le_total 0 t with h | h
  · exact constant_of_has_deriv_right_zero
      (fun r _ => (hf r).continuousAt.continuousWithinAt)
      (fun r _ => (hf r).hasDerivWithinAt) t (right_mem_Icc.mpr h)
  · exact (constant_of_has_deriv_right_zero
      (fun r _ => (hf r).continuousAt.continuousWithinAt)
      (fun r _ => (hf r).hasDerivWithinAt) 0 (right_mem_Icc.mpr h)).symm

structure IsClassicalBurgers (ν L : ℝ) (u u₁ u₂ ut : ℝ → ℝ → ℝ) : Prop where
  contU : Continuous (Function.uncurry u)
  contU₁ : Continuous (Function.uncurry u₁)
  contU₂ : Continuous (Function.uncurry u₂)
  contUt : Continuous (Function.uncurry ut)
  jet1 : ∀ t x, HasDerivAt (u t) (u₁ t x) x
  jet2 : ∀ t x, HasDerivAt (u₁ t) (u₂ t x) x
  timeDeriv : ∀ t x, HasDerivAt (fun s => u s x) (ut t x) t
  periodic : ∀ t, Function.Periodic (u t) L
  mech : ∀ t x, ut t x = ν * u₂ t x - u t x * u₁ t x

namespace IsClassicalBurgers

variable {ν L : ℝ} {u u₁ u₂ ut : ℝ → ℝ → ℝ}

theorem periodic_jet1 (h : IsClassicalBurgers ν L u u₁ u₂ ut) (t : ℝ) :
    Function.Periodic (u₁ t) L :=
  periodic_deriv (h.jet1 t) (h.periodic t)

theorem energy_hasDerivAt (h : IsClassicalBurgers ν L u u₁ u₂ ut)
    {a b : ℝ} (hb : b = a + L) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, (u s x) ^ 2)
      (-(2 * ν) * ∫ x in a..b, (u₁ t x) ^ 2) t := by
  have hup : ∀ τ, u τ b = u τ a := fun τ => by rw [hb]; exact h.periodic τ a
  have hu1p : ∀ τ, u₁ τ b = u₁ τ a := fun τ => by rw [hb]; exact h.periodic_jet1 τ a

  have hE := PdeBridge.hasDerivAt_intervalIntegral_of_continuous
    (F := fun s x => (u s x) ^ 2) (F' := fun s x => 2 * u s x * ut s x)
    (a := a) (b := b)
    (by
      have huc : (Function.uncurry fun s x => (u s x) ^ 2)
          = fun p : ℝ × ℝ => (Function.uncurry u p) ^ 2 := rfl
      rw [huc]
      exact h.contU.pow 2)
    (by
      have huc : (Function.uncurry fun s x => 2 * u s x * ut s x)
          = fun p : ℝ × ℝ => 2 * Function.uncurry u p * Function.uncurry ut p := rfl
      rw [huc]
      exact (continuous_const.mul h.contU).mul h.contUt)
    (fun s x => congr_value ((h.timeDeriv s x).pow 2) (by push_cast; ring)) t

  have hval : (∫ x in a..b, 2 * u t x * ut t x)
      = -(2 * ν) * ∫ x in a..b, (u₁ t x) ^ 2 := by

    have hcongr : ∫ x in a..b, 2 * u t x * ut t x
        = ∫ x in a..b, (2 * ν * (u t x * u₂ t x) - 2 * ((u t x) ^ 2 * u₁ t x)) := by
      refine integral_congr fun x _ => ?_
      rw [h.mech t x]
      ring
    have hi1 : IntervalIntegrable (fun x => u t x * u₂ t x) volume a b :=
      (((contSlice h.contU t).mul (contSlice h.contU₂ t)).intervalIntegrable a b)
    have hi2 : IntervalIntegrable (fun x => (u t x) ^ 2 * u₁ t x) volume a b :=
      ((((contSlice h.contU t).pow 2).mul (contSlice h.contU₁ t)).intervalIntegrable a b)

    have hibp : ∫ x in a..b, u t x * u₂ t x = -∫ x in a..b, u₁ t x * u₁ t x :=
      integral_mul_deriv_eq_neg (fun x _ => h.jet1 t x) (fun x _ => h.jet2 t x)
        ((contSlice h.contU₁ t).continuousOn) ((contSlice h.contU₂ t).continuousOn)
        (by rw [hup t, hu1p t])

    have hcubic : ∫ x in a..b, (u t x) ^ 2 * u₁ t x = 0 := by
      have hd : ∀ x ∈ uIcc a b,
          HasDerivAt (fun y => (u t y) ^ 3 / 3) ((u t x) ^ 2 * u₁ t x) x :=
        fun x _ => congr_value (((h.jet1 t x).pow 3).div_const 3) (by push_cast; ring)
      rw [integral_eq_sub_of_hasDerivAt hd hi2, hup t, sub_self]
    have hsq : ∫ x in a..b, u₁ t x * u₁ t x = ∫ x in a..b, (u₁ t x) ^ 2 :=
      integral_congr fun x _ => (pow_two (u₁ t x)).symm
    calc ∫ x in a..b, 2 * u t x * ut t x
        = ∫ x in a..b, (2 * ν * (u t x * u₂ t x) - 2 * ((u t x) ^ 2 * u₁ t x)) := hcongr
      _ = (∫ x in a..b, 2 * ν * (u t x * u₂ t x))
            - ∫ x in a..b, 2 * ((u t x) ^ 2 * u₁ t x) := by
          rw [integral_sub (hi1.const_mul (2 * ν)) (hi2.const_mul 2)]
      _ = 2 * ν * (∫ x in a..b, u t x * u₂ t x)
            - 2 * ∫ x in a..b, (u t x) ^ 2 * u₁ t x := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = -(2 * ν) * ∫ x in a..b, (u₁ t x) ^ 2 := by
          rw [hibp, hcubic, hsq]
          ring
  rw [← hval]
  exact hE

theorem mean_hasDerivAt (h : IsClassicalBurgers ν L u u₁ u₂ ut)
    {a b : ℝ} (hb : b = a + L) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, u s x) 0 t := by
  have hup : ∀ τ, u τ b = u τ a := fun τ => by rw [hb]; exact h.periodic τ a
  have hu1p : ∀ τ, u₁ τ b = u₁ τ a := fun τ => by rw [hb]; exact h.periodic_jet1 τ a
  have hE := PdeBridge.hasDerivAt_intervalIntegral_of_continuous
    (F := u) (F' := ut) (a := a) (b := b) h.contU h.contUt
    (fun s x => h.timeDeriv s x) t
  have hval : (∫ x in a..b, ut t x) = 0 := by
    have hd : ∀ x ∈ uIcc a b,
        HasDerivAt (fun y => ν * u₁ t y - (u t y) ^ 2 / 2) (ut t x) x :=
      fun x _ => congr_value
        (((h.jet2 t x).const_mul ν).sub (((h.jet1 t x).pow 2).div_const 2))
        (by rw [h.mech t x]; push_cast; ring)
    have hint : IntervalIntegrable (ut t) volume a b :=
      ((contSlice h.contUt t).intervalIntegrable a b)
    rw [integral_eq_sub_of_hasDerivAt hd hint, hup t, hu1p t, sub_self]
  rw [← hval]
  exact hE

theorem mean_const (h : IsClassicalBurgers ν L u u₁ u₂ ut)
    {a b : ℝ} (hb : b = a + L) (t : ℝ) :
    ∫ x in a..b, u t x = ∫ x in a..b, u 0 x :=
  eq_const_of_hasDerivAt_zero (fun s => h.mean_hasDerivAt hb s) t

theorem energy_le (h : IsClassicalBurgers ν L u u₁ u₂ ut) (hν : 0 ≤ ν)
    {a b : ℝ} (hab : a ≤ b) (hb : b = a + L) {s t : ℝ} (hst : s ≤ t) :
    (∫ x in a..b, (u t x) ^ 2) ≤ ∫ x in a..b, (u s x) ^ 2 := by
  set E : ℝ → ℝ := fun τ => ∫ x in a..b, (u τ x) ^ 2 with hE
  have hE' : ∀ τ, HasDerivAt E (-(2 * ν) * ∫ x in a..b, (u₁ τ x) ^ 2) τ :=
    fun τ => h.energy_hasDerivAt hb τ
  have hg : ∀ r, HasDerivAt (fun ρ => E (s + ρ))
      (-(2 * ν) * ∫ x in a..b, (u₁ (s + r) x) ^ 2) r :=
    fun r => (hE' (s + r)).comp_const_add s r
  have hdec := PdeBridge.energy_decay_of_deriv_right_le (α := 0) (b := t - s)
    (En := fun ρ => E (s + ρ))
    (En' := fun ρ => -(2 * ν) * ∫ x in a..b, (u₁ (s + ρ) x) ^ 2)
    (fun ρ _ => (hg ρ).continuousAt.continuousWithinAt)
    (fun ρ _ => (hg ρ).hasDerivWithinAt)
    (fun ρ _ => by
      have h1 : (0 : ℝ) ≤ ∫ x in a..b, (u₁ (s + ρ) x) ^ 2 :=
        PdeBridge.intervalIntegral_sigma_nonneg hab (fun x _ => sq_nonneg _)
      nlinarith)
    (t - s) ⟨by linarith, le_refl _⟩
  have hts : s + (t - s) = t := by ring
  rw [hts] at hdec
  simpa using hdec

theorem energy_decay_sharp (h : IsClassicalBurgers ν L u u₁ u₂ ut)
    (hν : 0 < ν) {a b : ℝ} (hab : a < b) (hb : b = a + L)
    (hlen : b - a ≤ 2 * Real.pi)
    (hmean : ∫ x in a..b, u 0 x = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in a..b, (u t x) ^ 2)
      ≤ (∫ x in a..b, (u 0 x) ^ 2) * Real.exp (-(2 * ν) * t) := by
  have hup : ∀ τ, u τ b = u τ a := fun τ => by rw [hb]; exact h.periodic τ a

  have hmean_t : ∀ τ : ℝ, ∫ x in a..b, u τ x = 0 := fun τ => by
    rw [h.mean_const hb τ]
    exact hmean

  have hwirt : ∀ τ : ℝ, (∫ x in a..b, (u τ x) ^ 2) ≤ ∫ x in a..b, (u₁ τ x) ^ 2 := by
    intro τ
    have hℂ := PdeBridge.wirtinger_interval hab hlen
      (u := fun x => ((u τ x : ℝ) : ℂ)) (u' := fun x => ((u₁ τ x : ℝ) : ℂ))
      (fun x => (h.jet1 τ x).ofReal_comp)
      (Complex.continuous_ofReal.comp (contSlice h.contU₁ τ))
      (by exact_mod_cast hup τ)
      (by rw [intervalIntegral.integral_ofReal, hmean_t τ, Complex.ofReal_zero])
    have c1 : ∫ x in a..b, ‖((u τ x : ℝ) : ℂ)‖ ^ 2 = ∫ x in a..b, (u τ x) ^ 2 :=
      integral_congr fun x _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have c2 : ∫ x in a..b, ‖((u₁ τ x : ℝ) : ℂ)‖ ^ 2 = ∫ x in a..b, (u₁ τ x) ^ 2 :=
      integral_congr fun x _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [c1, c2] at hℂ
    exact hℂ

  have hE' : ∀ τ, HasDerivAt (fun σ => ∫ x in a..b, (u σ x) ^ 2)
      (-(2 * ν) * ∫ x in a..b, (u₁ τ x) ^ 2) τ :=
    fun τ => h.energy_hasDerivAt hb τ
  have hdec := PdeBridge.energy_decay_of_deriv_right_le (α := 2 * ν) (b := t)
    (En := fun σ => ∫ x in a..b, (u σ x) ^ 2)
    (En' := fun τ => -(2 * ν) * ∫ x in a..b, (u₁ τ x) ^ 2)
    (fun τ _ => (hE' τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hE' τ).hasDerivWithinAt)
    (fun τ _ => by
      have := hwirt τ
      nlinarith [hν.le])
    t ⟨ht, le_refl t⟩
  exact hdec

end IsClassicalBurgers

theorem burgers_uniqueness_rungC {ν L a b T : ℝ} (hν : 0 < ν) (hab : a < b)
    (hb : b = a + L)
    {u u₁ u₂ ut v v₁ v₂ vt : ℝ → ℝ → ℝ}
    (hu : IsClassicalBurgers ν L u u₁ u₂ ut)
    (hv : IsClassicalBurgers ν L v v₁ v₂ vt)
    (hdata : ∀ x, u 0 x = v 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Icc a b, u t x = v t x := by

  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ Icc (0:ℝ) T ×ˢ Icc a b,
      ‖Function.uncurry u p + Function.uncurry v p‖ ≤ M :=
    ((isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (hu.contU.add hv.contU).continuousOn)
  set C : ℝ := M ^ 2 / (4 * ν) with hC
  set E : ℝ → ℝ := fun τ => ∫ x in a..b, (u τ x - v τ x) ^ 2 with hE
  have hup : ∀ τ, u τ b = u τ a := fun τ => by rw [hb]; exact hu.periodic τ a
  have hvp : ∀ τ, v τ b = v τ a := fun τ => by rw [hb]; exact hv.periodic τ a
  have hu1p : ∀ τ, u₁ τ b = u₁ τ a := fun τ => by rw [hb]; exact hu.periodic_jet1 τ a
  have hv1p : ∀ τ, v₁ τ b = v₁ τ a := fun τ => by rw [hb]; exact hv.periodic_jet1 τ a

  have hE' : ∀ τ, HasDerivAt E
      (-(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
        + ∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x))) τ := by
    intro τ
    have hL1 := PdeBridge.hasDerivAt_intervalIntegral_of_continuous
      (F := fun s x => (u s x - v s x) ^ 2)
      (F' := fun s x => 2 * (u s x - v s x) * (ut s x - vt s x))
      (a := a) (b := b)
      (by
        have huc : (Function.uncurry fun s x => (u s x - v s x) ^ 2)
            = fun p : ℝ × ℝ => (Function.uncurry u p - Function.uncurry v p) ^ 2 := rfl
        rw [huc]
        exact (hu.contU.sub hv.contU).pow 2)
      (by
        have huc : (Function.uncurry fun s x => 2 * (u s x - v s x) * (ut s x - vt s x))
            = fun p : ℝ × ℝ => 2 * (Function.uncurry u p - Function.uncurry v p)
                * (Function.uncurry ut p - Function.uncurry vt p) := rfl
        rw [huc]
        exact (continuous_const.mul (hu.contU.sub hv.contU)).mul
          (hu.contUt.sub hv.contUt))
      (fun s x => congr_value (((hu.timeDeriv s x).sub (hv.timeDeriv s x)).pow 2)
        (by simp only [Pi.sub_apply]; push_cast; ring)) τ
    have hval : (∫ x in a..b, 2 * (u τ x - v τ x) * (ut τ x - vt τ x))
        = -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
          + ∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)) := by

      have hcongr : ∫ x in a..b, 2 * (u τ x - v τ x) * (ut τ x - vt τ x)
          = ∫ x in a..b,
              (2 * ν * ((u τ x - v τ x) * (u₂ τ x - v₂ τ x))
                - (u τ x - v τ x)
                  * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
                    + (u τ x + v τ x) * (u₁ τ x - v₁ τ x))) := by
        refine integral_congr fun x _ => ?_
        rw [hu.mech τ x, hv.mech τ x]
        ring
      have hcw : Continuous fun x => u τ x - v τ x :=
        (contSlice hu.contU τ).sub (contSlice hv.contU τ)
      have hcw1 : Continuous fun x => u₁ τ x - v₁ τ x :=
        (contSlice hu.contU₁ τ).sub (contSlice hv.contU₁ τ)
      have hcw2 : Continuous fun x => u₂ τ x - v₂ τ x :=
        (contSlice hu.contU₂ τ).sub (contSlice hv.contU₂ τ)
      have hcs : Continuous fun x => u τ x + v τ x :=
        (contSlice hu.contU τ).add (contSlice hv.contU τ)
      have hcs1 : Continuous fun x => u₁ τ x + v₁ τ x :=
        (contSlice hu.contU₁ τ).add (contSlice hv.contU₁ τ)
      have hi1 : IntervalIntegrable
          (fun x => (u τ x - v τ x) * (u₂ τ x - v₂ τ x)) volume a b :=
        ((hcw.mul hcw2).intervalIntegrable a b)
      have hi2 : IntervalIntegrable
          (fun x => (u τ x - v τ x)
            * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
              + (u τ x + v τ x) * (u₁ τ x - v₁ τ x))) volume a b :=
        ((hcw.mul ((hcs1.mul hcw).add (hcs.mul hcw1))).intervalIntegrable a b)

      have hibp1 : ∫ x in a..b, (u τ x - v τ x) * (u₂ τ x - v₂ τ x)
          = -∫ x in a..b, (u₁ τ x - v₁ τ x) * (u₁ τ x - v₁ τ x) :=
        integral_mul_deriv_eq_neg
          (fun x _ => (hu.jet1 τ x).sub (hv.jet1 τ x))
          (fun x _ => (hu.jet2 τ x).sub (hv.jet2 τ x))
          hcw1.continuousOn hcw2.continuousOn
          (by rw [hup τ, hvp τ, hu1p τ, hv1p τ])

      have hibp2 : ∫ x in a..b, (u τ x - v τ x)
            * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
              + (u τ x + v τ x) * (u₁ τ x - v₁ τ x))
          = -∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)) :=
        integral_mul_deriv_eq_neg
          (fun x _ => (hu.jet1 τ x).sub (hv.jet1 τ x))
          (fun x _ => ((hu.jet1 τ x).add (hv.jet1 τ x)).mul
            ((hu.jet1 τ x).sub (hv.jet1 τ x)))
          hcw1.continuousOn
          ((hcs1.mul hcw).add (hcs.mul hcw1)).continuousOn
          (by rw [hup τ, hvp τ])
      have hsq : ∫ x in a..b, (u₁ τ x - v₁ τ x) * (u₁ τ x - v₁ τ x)
          = ∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2 :=
        integral_congr fun x _ => (pow_two _).symm
      calc ∫ x in a..b, 2 * (u τ x - v τ x) * (ut τ x - vt τ x)
          = ∫ x in a..b,
              (2 * ν * ((u τ x - v τ x) * (u₂ τ x - v₂ τ x))
                - (u τ x - v τ x)
                  * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
                    + (u τ x + v τ x) * (u₁ τ x - v₁ τ x))) := hcongr
        _ = (∫ x in a..b, 2 * ν * ((u τ x - v τ x) * (u₂ τ x - v₂ τ x)))
              - ∫ x in a..b, (u τ x - v τ x)
                  * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
                    + (u τ x + v τ x) * (u₁ τ x - v₁ τ x)) := by
            rw [integral_sub (hi1.const_mul (2 * ν)) hi2]
        _ = 2 * ν * (∫ x in a..b, (u τ x - v τ x) * (u₂ τ x - v₂ τ x))
              - ∫ x in a..b, (u τ x - v τ x)
                  * ((u₁ τ x + v₁ τ x) * (u τ x - v τ x)
                    + (u τ x + v τ x) * (u₁ τ x - v₁ τ x)) := by
            rw [intervalIntegral.integral_const_mul]
        _ = -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
              + ∫ x in a..b, (u₁ τ x - v₁ τ x)
                  * ((u τ x + v τ x) * (u τ x - v τ x)) := by
            rw [hibp1, hibp2, hsq]
            ring
    rw [← hval]
    exact hL1

  have hbound : ∀ τ ∈ Ico (0:ℝ) T,
      -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
        + (∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)))
      ≤ -(-C) * E τ := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0:ℝ) T := Ico_subset_Icc_self hτ
    have hptwise : ∀ x ∈ Icc a b,
        (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x))
          ≤ ν * (u₁ τ x - v₁ τ x) ^ 2 + C * (u τ x - v τ x) ^ 2 := by
      intro x hx
      have habs : |u τ x + v τ x| ≤ M := by
        have := hM (τ, x) ⟨hτ', hx⟩
        simpa [Function.uncurry, Real.norm_eq_abs] using this
      have h1 : (u τ x + v τ x) ^ 2 ≤ M ^ 2 :=
        sq_le_sq' (by linarith [(abs_le.mp habs).1]) (abs_le.mp habs).2
      have hfac : ν * (u₁ τ x - v₁ τ x) ^ 2 + C * (u τ x - v τ x) ^ 2
          - (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x))
          = (1 / (4 * ν))
            * ((2 * ν * (u₁ τ x - v₁ τ x) - (u τ x + v τ x) * (u τ x - v τ x)) ^ 2
              + (M ^ 2 - (u τ x + v τ x) ^ 2) * (u τ x - v τ x) ^ 2) := by
        rw [hC]
        field_simp
        ring
      have hkey : 0 ≤ ν * (u₁ τ x - v₁ τ x) ^ 2 + C * (u τ x - v τ x) ^ 2
          - (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)) := by
        rw [hfac]
        apply mul_nonneg (by positivity)
        nlinarith [sq_nonneg (2 * ν * (u₁ τ x - v₁ τ x)
          - (u τ x + v τ x) * (u τ x - v τ x)), sq_nonneg (u τ x - v τ x), h1]
      linarith
    have hcw : Continuous fun x => u τ x - v τ x :=
      (contSlice hu.contU τ).sub (contSlice hv.contU τ)
    have hcw1 : Continuous fun x => u₁ τ x - v₁ τ x :=
      (contSlice hu.contU₁ τ).sub (contSlice hv.contU₁ τ)
    have hcs : Continuous fun x => u τ x + v τ x :=
      (contSlice hu.contU τ).add (contSlice hv.contU τ)
    have hi3 : IntervalIntegrable (fun x : ℝ => ν * (u₁ τ x - v₁ τ x) ^ 2) volume a b :=
      ((hcw1.pow 2).intervalIntegrable a b).const_mul ν
    have hi4 : IntervalIntegrable (fun x : ℝ => C * (u τ x - v τ x) ^ 2) volume a b :=
      ((hcw.pow 2).intervalIntegrable a b).const_mul C
    have hi5 : IntervalIntegrable
        (fun x : ℝ => (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)))
        volume a b :=
      (hcw1.mul (hcs.mul hcw)).intervalIntegrable a b
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hab.le
      hi5 (hi3.add hi4) hptwise
    have hsplit : ∫ x in a..b,
        (ν * (u₁ τ x - v₁ τ x) ^ 2 + C * (u τ x - v τ x) ^ 2)
        = ν * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2) + C * E τ := by
      rw [intervalIntegral.integral_add hi3 hi4,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hd1 : (0:ℝ) ≤ ∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2 :=
      PdeBridge.intervalIntegral_sigma_nonneg hab.le (fun x _ => sq_nonneg _)
    have hνpos : (0:ℝ) < ν := hν
    calc -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
          + (∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)))
        ≤ -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
          + (ν * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2) + C * E τ) := by
          rw [← hsplit]
          linarith [hmono]
      _ ≤ -(-C) * E τ := by nlinarith

  have hE0 : E 0 = 0 := by
    have : ∫ x in a..b, (u 0 x - v 0 x) ^ 2 = ∫ x in a..b, (0:ℝ) := by
      refine integral_congr fun x _ => ?_
      rw [hdata x]
      ring
    rw [hE]
    simpa using this
  intro t ht x hx
  have hdec := PdeBridge.energy_decay_of_deriv_right_le (α := -C) (b := T)
    (En := E)
    (En' := fun τ => -(2 * ν) * (∫ x in a..b, (u₁ τ x - v₁ τ x) ^ 2)
      + ∫ x in a..b, (u₁ τ x - v₁ τ x) * ((u τ x + v τ x) * (u τ x - v τ x)))
    (fun τ _ => (hE' τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hE' τ).hasDerivWithinAt)
    hbound t ht
  rw [hE0] at hdec
  simp only [zero_mul] at hdec
  have hEnn : 0 ≤ E t :=
    PdeBridge.intervalIntegral_sigma_nonneg hab.le (fun x _ => sq_nonneg _)
  have hEt : E t = 0 := le_antisymm hdec hEnn
  have hwc : Continuous fun y : ℝ => u t y - v t y :=
    (contSlice hu.contU t).sub (contSlice hv.contU t)
  have hzero := eqOn_zero_of_integral_sq (f := fun y => u t y - v t y) hab
    hwc (by rw [hE] at hEt; exact hEt)
  have h9 : u t x - v t x = 0 := hzero x hx
  linarith

structure IsClassicalKSE (L : ℝ) (u u₁ u₂ u₃ u₄ ut : ℝ → ℝ → ℝ) : Prop where
  contU : Continuous (Function.uncurry u)
  contU₁ : Continuous (Function.uncurry u₁)
  contU₂ : Continuous (Function.uncurry u₂)
  contU₃ : Continuous (Function.uncurry u₃)
  contU₄ : Continuous (Function.uncurry u₄)
  contUt : Continuous (Function.uncurry ut)
  jet1 : ∀ t x, HasDerivAt (u t) (u₁ t x) x
  jet2 : ∀ t x, HasDerivAt (u₁ t) (u₂ t x) x
  jet3 : ∀ t x, HasDerivAt (u₂ t) (u₃ t x) x
  jet4 : ∀ t x, HasDerivAt (u₃ t) (u₄ t x) x
  timeDeriv : ∀ t x, HasDerivAt (fun s => u s x) (ut t x) t
  periodic : ∀ t, Function.Periodic (u t) L
  mech : ∀ t x, ut t x = -(u₄ t x) - u₂ t x - u t x * u₁ t x

namespace IsClassicalKSE

variable {L : ℝ} {u u₁ u₂ u₃ u₄ ut : ℝ → ℝ → ℝ}

theorem translate (h : IsClassicalKSE L u u₁ u₂ u₃ u₄ ut) (θ : ℝ) :
    IsClassicalKSE L (fun t x => u t (x + θ)) (fun t x => u₁ t (x + θ))
      (fun t x => u₂ t (x + θ)) (fun t x => u₃ t (x + θ))
      (fun t x => u₄ t (x + θ)) (fun t x => ut t (x + θ)) := by
  have hshift : Continuous fun p : ℝ × ℝ => (p.1, p.2 + θ) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  refine ⟨h.contU.comp hshift, h.contU₁.comp hshift, h.contU₂.comp hshift,
    h.contU₃.comp hshift, h.contU₄.comp hshift, h.contUt.comp hshift,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    exact (h.jet1 t (x + θ)).comp_add_const x θ
  · intro t x
    exact (h.jet2 t (x + θ)).comp_add_const x θ
  · intro t x
    exact (h.jet3 t (x + θ)).comp_add_const x θ
  · intro t x
    exact (h.jet4 t (x + θ)).comp_add_const x θ
  · intro t x
    exact h.timeDeriv t (x + θ)
  · intro t x
    have := h.periodic t (x + θ)
    calc u t (x + L + θ) = u t (x + θ + L) := by ring_nf
      _ = u t (x + θ) := this
  · intro t x
    exact h.mech t (x + θ)

theorem reflect (h : IsClassicalKSE L u u₁ u₂ u₃ u₄ ut) :
    IsClassicalKSE L (fun t x => -(u t (-x))) (fun t x => u₁ t (-x))
      (fun t x => -(u₂ t (-x))) (fun t x => u₃ t (-x))
      (fun t x => -(u₄ t (-x))) (fun t x => -(ut t (-x))) := by
  have hflip : Continuous fun p : ℝ × ℝ => (p.1, -p.2) :=
    continuous_fst.prodMk continuous_snd.neg
  refine ⟨(h.contU.comp hflip).neg, h.contU₁.comp hflip,
    (h.contU₂.comp hflip).neg, h.contU₃.comp hflip,
    (h.contU₄.comp hflip).neg, (h.contUt.comp hflip).neg,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    have h0 : HasDerivAt (u t) (u₁ t (-x)) (0 - x) := by
      rw [zero_sub]; exact h.jet1 t (-x)
    have h1 := h0.comp_const_sub 0 x
    rw [show (fun y : ℝ => u t (0 - y)) = fun y : ℝ => u t (-y) from
      funext fun y => by rw [zero_sub]] at h1
    have h2 := h1.neg
    rw [neg_neg] at h2
    exact h2
  · intro t x
    have h0 : HasDerivAt (u₁ t) (u₂ t (-x)) (0 - x) := by
      rw [zero_sub]; exact h.jet2 t (-x)
    have h1 := h0.comp_const_sub 0 x
    rw [show (fun y : ℝ => u₁ t (0 - y)) = fun y : ℝ => u₁ t (-y) from
      funext fun y => by rw [zero_sub]] at h1
    exact h1
  · intro t x
    have h0 : HasDerivAt (u₂ t) (u₃ t (-x)) (0 - x) := by
      rw [zero_sub]; exact h.jet3 t (-x)
    have h1 := h0.comp_const_sub 0 x
    rw [show (fun y : ℝ => u₂ t (0 - y)) = fun y : ℝ => u₂ t (-y) from
      funext fun y => by rw [zero_sub]] at h1
    have h2 := h1.neg
    rw [neg_neg] at h2
    exact h2
  · intro t x
    have h0 : HasDerivAt (u₃ t) (u₄ t (-x)) (0 - x) := by
      rw [zero_sub]; exact h.jet4 t (-x)
    have h1 := h0.comp_const_sub 0 x
    rw [show (fun y : ℝ => u₃ t (0 - y)) = fun y : ℝ => u₃ t (-y) from
      funext fun y => by rw [zero_sub]] at h1
    exact h1
  · intro t x
    exact (h.timeDeriv t (-x)).neg
  · intro t x
    have hstep : -(x + L) = -x - L := by ring
    calc -(u t (-(x + L))) = -(u t (-x - L)) := by rw [hstep]
      _ = -(u t (-x)) := by rw [(h.periodic t).sub_eq]
  · intro t x
    rw [h.mech t (-x)]
    ring

end IsClassicalKSE

theorem kse_odd_persistence_of_uniqueness {L a b T : ℝ}
    {u u₁ u₂ u₃ u₄ ut : ℝ → ℝ → ℝ}
    (h : IsClassicalKSE L u u₁ u₂ u₃ u₄ ut)
    (hodd : ∀ x, u 0 (-x) = -(u 0 x))
    (huniq : ∀ (v v₁ v₂ v₃ v₄ vt : ℝ → ℝ → ℝ),
      IsClassicalKSE L v v₁ v₂ v₃ v₄ vt → (∀ x, v 0 x = u 0 x) →
      ∀ t ∈ Icc (0:ℝ) T, ∀ x ∈ Icc a b, v t x = u t x) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ x ∈ Icc a b, u t (-x) = -(u t x) := by
  have hrefl := h.reflect
  have hdata : ∀ x, -(u 0 (-x)) = u 0 x := fun x => by
    rw [hodd x]
    ring
  intro t ht x hx
  have := huniq _ _ _ _ _ _ hrefl hdata t ht x hx
  linarith

end PdeUniqueness

end Qtsl

#print axioms Qtsl.PdeUniqueness.integral_mul_deriv_eq_neg
#print axioms Qtsl.PdeUniqueness.eqOn_zero_of_integral_sq
#print axioms Qtsl.PdeUniqueness.periodic_deriv
#print axioms Qtsl.PdeUniqueness.IsClassicalBurgers.energy_hasDerivAt
#print axioms Qtsl.PdeUniqueness.IsClassicalBurgers.mean_hasDerivAt
#print axioms Qtsl.PdeUniqueness.IsClassicalBurgers.mean_const
#print axioms Qtsl.PdeUniqueness.IsClassicalBurgers.energy_le
#print axioms Qtsl.PdeUniqueness.IsClassicalBurgers.energy_decay_sharp
#print axioms Qtsl.PdeUniqueness.burgers_uniqueness_rungC
#print axioms Qtsl.PdeUniqueness.IsClassicalKSE.translate
#print axioms Qtsl.PdeUniqueness.IsClassicalKSE.reflect
#print axioms Qtsl.PdeUniqueness.kse_odd_persistence_of_uniqueness
