import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.MeanInequalities
import QtslAux.Ville

/-! # Dwell-time gauges and a stochastic small-gain theorem for jump systems

A Lyapunov function that contracts in expectation along flow steps but may
expand by a factor `c` at jumps can be repaired by a *gauge*: the multiplier
`ψ η δ τ = 1 + η * min τ δ`, where `τ` is the time elapsed since the last
jump and `δ` a guaranteed dwell time. The gauge accumulates credit during
flow (at relative rate at most `1 + η` per step, `gauge_flowTax`) and spends
it at a jump (`gauge_repayment`: if `δ ≤ τ` and `c ≤ 1 + η * δ`, the gauged
value does not increase across the jump).

Main results:

* `discrete_gauged_supermartingale`: for a single system in discrete time —
  with jump indicator `J`, jump counter `N` reset at jumps, dwell-time
  hypothesis `δ ≤ N` at every jump, expansion bound `c ≤ 1 + η * δ`, and
  flow-tax condition `ρ * (1 + η) ≤ 1` — the gauged process
  `k ↦ ψ η δ (N k) * V k` is a supermartingale.
* `discrete_gauge_smallGain_sum`: the small-gain composition of two such
  systems with cross-coupling gains `γ₁, γ₂` in the flow drift: under the
  small-gain inequalities `hA₁` and `hA₂` there is a weighted sum
  `ψ₁ * V₁ + lam * ψ₂ * V₂` of the gauged values that is a supermartingale,
  so the interconnection inherits every reach-avoid bound available for
  nonnegative supermartingales.
* `pnorm` with `pnorm_mono`, `pnorm_coord_lipschitz`, `pnorm_max_le`: the
  two-argument `ℓᵖ` combiner `(a^p + b^p)^(1/p)` used to merge component
  certificates, with monotonicity, per-coordinate Lipschitz translation, and
  its equivalence with `max` up to a factor `2^(1/p)`.
-/

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace Qtsl.Gauge

open MeasureTheory

noncomputable def ψ (η δ τ : ℝ) : ℝ := 1 + η * min τ δ

theorem ψ_zero {η δ : ℝ} (hδ : 0 ≤ δ) : ψ η δ 0 = 1 := by
  simp [ψ, min_eq_left hδ]

theorem one_le_ψ {η δ τ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) :
    1 ≤ ψ η δ τ := by
  have hm : 0 ≤ min τ δ := le_min hτ hδ
  simp only [ψ, le_add_iff_nonneg_right]
  exact mul_nonneg hη hm

theorem ψ_le_cap {η δ τ : ℝ} (hη : 0 ≤ η) : ψ η δ τ ≤ 1 + η * δ := by
  have := min_le_right τ δ
  simp only [ψ, add_le_add_iff_left]
  exact mul_le_mul_of_nonneg_left this hη

theorem ψ_eq_cap {η δ τ : ℝ} (hdwell : δ ≤ τ) : ψ η δ τ = 1 + η * δ := by
  simp [ψ, min_eq_right hdwell]

theorem ψ_continuous (η δ : ℝ) : Continuous (ψ η δ) :=
  continuous_const.add (continuous_const.mul (continuous_id.min continuous_const))

theorem gauge_repayment {η δ τ c V V' : ℝ} (hδ : 0 < δ)
    (hdwell : δ ≤ τ) (hclock : c ≤ 1 + η * δ) (hV : 0 ≤ V) (hjump : V' ≤ c * V) :
    ψ η δ 0 * V' ≤ ψ η δ τ * V := by
  rw [ψ_zero hδ.le, ψ_eq_cap hdwell, one_mul]
  calc V' ≤ c * V := hjump
    _ ≤ (1 + η * δ) * V := mul_le_mul_of_nonneg_right hclock hV

theorem gauge_flowTax {η δ τ τ' : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hle : τ ≤ τ') :
    ψ η δ τ' ≤ ψ η δ τ * (1 + η * (τ' - τ)) := by
  have hmin : min τ' δ ≤ min τ δ + (τ' - τ) := by
    rcases le_total τ' δ with h | h
    · rw [min_eq_left h, min_eq_left (le_trans hle h)]; linarith
    · rw [min_eq_right h]
      rcases le_total τ δ with h2 | h2
      · rw [min_eq_left h2]; linarith
      · rw [min_eq_right h2]; linarith
  have hmn : 0 ≤ min τ δ := le_min hτ hδ
  have h1 : η * min τ' δ ≤ η * (min τ δ + (τ' - τ)) :=
    mul_le_mul_of_nonneg_left hmin hη
  have h2 : 0 ≤ η * η * (min τ δ * (τ' - τ)) :=
    mul_nonneg (mul_nonneg hη hη) (mul_nonneg hmn (sub_nonneg.2 hle))
  simp only [ψ]
  nlinarith [h1, h2]

noncomputable def pnorm (p a b : ℝ) : ℝ := (a ^ p + b ^ p) ^ (1 / p)

theorem pnorm_mono {p a a' b b' : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a') (hb : 0 ≤ b')
    (haa : a' ≤ a) (hbb : b' ≤ b) :
    pnorm p a' b' ≤ pnorm p a b := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have h1 : a' ^ p ≤ a ^ p := Real.rpow_le_rpow ha haa hp0.le
  have h2 : b' ^ p ≤ b ^ p := Real.rpow_le_rpow hb hbb hp0.le
  refine Real.rpow_le_rpow ?_ (by linarith) (div_nonneg zero_le_one hp0.le)
  have := Real.rpow_nonneg ha p
  have := Real.rpow_nonneg hb p
  linarith

theorem pnorm_coord_lipschitz {p a b t : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (ht : 0 ≤ t) :
    pnorm p (a + t) b ≤ pnorm p a b + t := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have key := Real.Lp_add_le_of_nonneg (s := (Finset.univ : Finset (Fin 2)))
    (f := ![a, b]) (g := ![t, 0]) (p := p) hp
    (fun i _ => by fin_cases i <;> simp [ha, hb])
    (fun i _ => by fin_cases i <;> simp [ht])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Real.zero_rpow hp0.ne'] at key
  rw [one_div, Real.rpow_rpow_inv ht hp0.ne'] at key
  simpa [pnorm, one_div] using key

theorem pnorm_max_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ pnorm p a b ∧ pnorm p a b ≤ 2 ^ (1 / p) * max a b := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have hmax : 0 ≤ max a b := le_trans ha (le_max_left a b)
  have hap : 0 ≤ a ^ p := Real.rpow_nonneg ha p
  have hbp : 0 ≤ b ^ p := Real.rpow_nonneg hb p
  constructor
  · refine max_le ?_ ?_
    · calc a = (a ^ p) ^ (1 / p) := by rw [one_div, Real.rpow_rpow_inv ha hp0.ne']
        _ ≤ pnorm p a b :=
          Real.rpow_le_rpow hap (by linarith) (div_nonneg zero_le_one hp0.le)
    · calc b = (b ^ p) ^ (1 / p) := by rw [one_div, Real.rpow_rpow_inv hb hp0.ne']
        _ ≤ pnorm p a b :=
          Real.rpow_le_rpow hbp (by linarith) (div_nonneg zero_le_one hp0.le)
  · have h1 : a ^ p ≤ (max a b) ^ p :=
      Real.rpow_le_rpow ha (le_max_left a b) hp0.le
    have h2 : b ^ p ≤ (max a b) ^ p :=
      Real.rpow_le_rpow hb (le_max_right a b) hp0.le
    calc pnorm p a b ≤ (2 * (max a b) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (by linarith) (by linarith)
            (div_nonneg zero_le_one hp0.le)
      _ = 2 ^ (1 / p) * max a b := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hmax p), one_div,
            Real.rpow_rpow_inv hmax hp0.ne']

section Discrete

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : MeasureTheory.Filtration ℕ m0}

private theorem condExp_pull_bdd {k : ℕ} {f g : Ω → ℝ} {C : ℝ}
    (hf : StronglyMeasurable[𝒢 k] f) (hbdd : ∀ ω, ‖f ω‖ ≤ C)
    (hg : Integrable g μ) :
    Integrable (f * g) μ ∧ μ[f * g | 𝒢 k] =ᵐ[μ] f * μ[g | 𝒢 k] := by
  have hint : Integrable (f * g) μ :=
    hg.bdd_mul ((hf.mono (𝒢.le k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  exact ⟨hint, condExp_mul_of_stronglyMeasurable_left hf hint hg⟩

theorem discrete_gauged_supermartingale [IsFiniteMeasure μ]
    {V : ℕ → Ω → ℝ} {N : ℕ → Ω → ℕ} {J : ℕ → Ω → Prop}
    {ρ c η : ℝ} {δ : ℕ}
    (hadpV : Adapted 𝒢 V) (hadpN : Adapted 𝒢 fun k ω => (N k ω : ℝ))
    (hJmeas : ∀ k, MeasurableSet[𝒢 k] {ω | J k ω})
    (hnonneg : 0 ≤ V) (hη : 0 ≤ η) (hδ : 0 < δ)
    (hint : ∀ k, Integrable (V k) μ)

    (hcontr : ∀ k, ∀ᵐ ω ∂μ, ¬ J k ω →
      (μ[V (k+1) | 𝒢 k]) ω ≤ ρ * V k ω)

    (hjump : ∀ k, ∀ᵐ ω ∂μ, J k ω → V (k+1) ω ≤ c * V k ω)

    (hN0 : ∀ k, ∀ᵐ ω ∂μ, J k ω → N (k+1) ω = 0)
    (hN1 : ∀ k, ∀ᵐ ω ∂μ, ¬ J k ω → N (k+1) ω = N k ω + 1)
    (hdwell : ∀ k, ∀ᵐ ω ∂μ, J k ω → δ ≤ N k ω)

    (hclock : c ≤ 1 + η * δ) (htax : ρ * (1 + η) ≤ 1) :
    Supermartingale (fun k ω => ψ η δ (N k ω) * V k ω) 𝒢 μ := by

  have hδR : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ
  have hψ1 : ∀ k ω, 1 ≤ ψ η δ (N k ω) := fun k ω =>
    one_le_ψ hη hδR (Nat.cast_nonneg _)
  have hψcap : ∀ k ω, ψ η δ (N k ω) ≤ 1 + η * δ := fun k ω => ψ_le_cap hη
  have hψ0 : ∀ k ω, 0 ≤ ψ η δ (N k ω) := fun k ω =>
    le_trans zero_le_one (hψ1 k ω)

  have hψN_sm : ∀ k, StronglyMeasurable[𝒢 k] fun ω => ψ η δ (N k ω) := fun k =>
    (ψ_continuous η δ).comp_stronglyMeasurable (hadpN k).stronglyMeasurable

  have hWadp : StronglyAdapted 𝒢 (fun k ω => ψ η δ (N k ω) * V k ω) := fun k =>
    (hψN_sm k).mul (hadpV k).stronglyMeasurable
  have hWint : ∀ k, Integrable (fun ω => ψ η δ (N k ω) * V k ω) μ := fun k =>
    (hint k).bdd_mul ((hψN_sm k).mono (𝒢.le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 k ω)]; exact hψcap k ω)
  refine supermartingale_nat hWadp hWint fun k => ?_

  set Jset : Set Ω := {ω | J k ω} with hJset
  have hJm : MeasurableSet[𝒢 k] Jset := hJmeas k
  set f₁ : Ω → ℝ := Jset.indicator (fun ω => ψ η δ (N k ω) * V k ω) with hf₁
  set f₂ : Ω → ℝ := Jsetᶜ.indicator (fun ω => (1 + η) * ψ η δ (N k ω)) with hf₂
  have hf₁_sm : StronglyMeasurable[𝒢 k] f₁ := (hWadp k).indicator hJm
  have hf₂_sm : StronglyMeasurable[𝒢 k] f₂ :=
    (stronglyMeasurable_const.mul (hψN_sm k)).indicator hJm.compl
  have hint₁ : Integrable f₁ μ := (hWint k).indicator ((𝒢.le k) _ hJm)
  have hf₂_bdd : ∀ ω, ‖f₂ ω‖ ≤ (1 + η) * (1 + η * δ) := fun ω => by
    rw [hf₂]
    by_cases hω : ω ∈ Jsetᶜ
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith) (hψ0 k ω))]
      exact mul_le_mul_of_nonneg_left (hψcap k ω) (by linarith)
    · rw [Set.indicator_of_notMem hω]
      simp only [norm_zero]
      exact mul_nonneg (by linarith) (by linarith [mul_nonneg hη hδR])
  obtain ⟨hint₂, hpull⟩ := condExp_pull_bdd (μ := μ) hf₂_sm hf₂_bdd (hint (k+1))

  have hdomA : (fun ω => ψ η δ (N (k+1) ω) * V (k+1) ω)
      ≤ᵐ[μ] f₁ + f₂ * V (k+1) := by
    filter_upwards [hjump k, hN0 k, hN1 k, hdwell k] with ω hj h0 h1 hd
    simp only [Pi.add_apply, Pi.mul_apply, hf₁, hf₂]
    by_cases hJ : J k ω
    ·
      have hmem : ω ∈ Jset := hJ
      have hnc : ω ∉ Jsetᶜ := fun hc => hc hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnc, zero_mul,
        add_zero, h0 hJ]
      have hrepay := gauge_repayment (η := η) (τ := ((N k ω : ℕ) : ℝ))
        (by exact_mod_cast hδ) (by exact_mod_cast hd hJ) hclock
        (hnonneg k ω) (hj hJ)
      simpa using hrepay
    ·
      have hnm : ω ∉ Jset := hJ
      have hmem : ω ∈ Jsetᶜ := hnm
      rw [Set.indicator_of_notMem hnm, Set.indicator_of_mem hmem,
        zero_add, h1 hJ]
      have htax1 : ψ η δ ((N k ω : ℕ) + 1 : ℕ) ≤ ψ η δ (N k ω) * (1 + η) := by
        have h := gauge_flowTax (η := η) (δ := (δ : ℝ)) (τ := ((N k ω : ℕ) : ℝ))
          (τ' := ((N k ω : ℕ) : ℝ) + 1) hη hδR (Nat.cast_nonneg _) (by linarith)
        rw [add_sub_cancel_left] at h
        simpa [Nat.cast_add_one] using h
      calc ψ η δ ((N k ω : ℕ) + 1 : ℕ) * V (k+1) ω
          ≤ (ψ η δ (N k ω) * (1 + η)) * V (k+1) ω :=
            mul_le_mul_of_nonneg_right htax1 (hnonneg (k+1) ω)
        _ = (1 + η) * ψ η δ (N k ω) * V (k+1) ω := by ring

  have hstep : μ[f₁ + f₂ * V (k+1) | 𝒢 k]
      ≤ᵐ[μ] fun ω => ψ η δ (N k ω) * V k ω := by
    have hfix : μ[f₁ | 𝒢 k] = f₁ :=
      condExp_of_stronglyMeasurable (𝒢.le k) hf₁_sm hint₁
    calc μ[f₁ + f₂ * V (k+1) | 𝒢 k]
        =ᵐ[μ] μ[f₁ | 𝒢 k] + μ[f₂ * V (k+1) | 𝒢 k] := condExp_add hint₁ hint₂ _
      _ =ᵐ[μ] f₁ + f₂ * μ[V (k+1) | 𝒢 k] := by
          rw [hfix]; exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl hpull
      _ ≤ᵐ[μ] fun ω => ψ η δ (N k ω) * V k ω := by
          filter_upwards [hcontr k] with ω hc
          simp only [Pi.add_apply, Pi.mul_apply, hf₁, hf₂]
          by_cases hJ : J k ω
          · have hmem : ω ∈ Jset := hJ
            have hnc : ω ∉ Jsetᶜ := fun hc' => hc' hmem
            rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnc,
              zero_mul, add_zero]
          · have hnm : ω ∉ Jset := hJ
            have hmem : ω ∈ Jsetᶜ := hnm
            rw [Set.indicator_of_notMem hnm, Set.indicator_of_mem hmem, zero_add]
            have hc' := hc hJ
            have hfac : (0 : ℝ) ≤ (1 + η) * ψ η δ (N k ω) :=
              mul_nonneg (by linarith) (hψ0 k ω)
            have hψV : (0 : ℝ) ≤ ψ η δ (N k ω) * V k ω :=
              mul_nonneg (hψ0 k ω) (hnonneg k ω)
            nlinarith [mul_le_mul_of_nonneg_left hc' hfac,
              mul_le_mul_of_nonneg_right htax hψV]
  exact (condExp_mono (hWint (k+1)) (hint₁.add hint₂) hdomA).trans hstep

theorem discrete_gauge_smallGain_sum [IsFiniteMeasure μ]
    {V₁ V₂ : ℕ → Ω → ℝ} {N₁ N₂ : ℕ → Ω → ℕ} {J₁ J₂ : ℕ → Ω → Prop}
    {ρ₁ ρ₂ γ₁ γ₂ c₁ c₂ η₁ η₂ lam : ℝ} {δ₁ δ₂ : ℕ}
    (hnonneg₁ : 0 ≤ V₁) (hnonneg₂ : 0 ≤ V₂) (hlam : 0 < lam)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hint₁ : ∀ k, Integrable (V₁ k) μ)
    (hint₂ : ∀ k, Integrable (V₂ k) μ)

    (hadp₁ : Adapted 𝒢 V₁) (hadp₂ : Adapted 𝒢 V₂)
    (hadpN₁ : Adapted 𝒢 fun k ω => (N₁ k ω : ℝ))
    (hadpN₂ : Adapted 𝒢 fun k ω => (N₂ k ω : ℝ))
    (hJ₁ : ∀ k, MeasurableSet[𝒢 k] {ω | J₁ k ω})
    (hJ₂ : ∀ k, MeasurableSet[𝒢 k] {ω | J₂ k ω})

    (hflow₁ : ∀ k, ∀ᵐ ω ∂μ, ¬ J₁ k ω → ¬ J₂ k ω →
      (μ[V₁ (k+1) | 𝒢 k]) ω ≤ ρ₁ * V₁ k ω + γ₁ * V₂ k ω)
    (hflow₂ : ∀ k, ∀ᵐ ω ∂μ, ¬ J₁ k ω → ¬ J₂ k ω →
      (μ[V₂ (k+1) | 𝒢 k]) ω ≤ ρ₂ * V₂ k ω + γ₂ * V₁ k ω)

    (hjump₁ : ∀ k, ∀ᵐ ω ∂μ, J₁ k ω →
      V₁ (k+1) ω ≤ c₁ * V₁ k ω ∧ V₂ (k+1) ω = V₂ k ω)
    (hjump₂ : ∀ k, ∀ᵐ ω ∂μ, J₂ k ω →
      V₂ (k+1) ω ≤ c₂ * V₂ k ω ∧ V₁ (k+1) ω = V₁ k ω)

    (hN₁ : ∀ k, ∀ᵐ ω ∂μ,
      (J₁ k ω → N₁ (k+1) ω = 0) ∧
      (¬ J₁ k ω → ¬ J₂ k ω → N₁ (k+1) ω = N₁ k ω + 1) ∧
      (¬ J₁ k ω → J₂ k ω → N₁ (k+1) ω = N₁ k ω))
    (hN₂ : ∀ k, ∀ᵐ ω ∂μ,
      (J₂ k ω → N₂ (k+1) ω = 0) ∧
      (¬ J₂ k ω → ¬ J₁ k ω → N₂ (k+1) ω = N₂ k ω + 1) ∧
      (¬ J₂ k ω → J₁ k ω → N₂ (k+1) ω = N₂ k ω))

    (hdwell₁ : ∀ k, ∀ᵐ ω ∂μ, J₁ k ω → δ₁ ≤ N₁ k ω)
    (hdwell₂ : ∀ k, ∀ᵐ ω ∂μ, J₂ k ω → δ₂ ≤ N₂ k ω)
    (hclock₁ : c₁ ≤ 1 + η₁ * δ₁) (hclock₂ : c₂ ≤ 1 + η₂ * δ₂)

    (hA₁ : (1 + η₁) * ρ₁ + lam * (1 + η₂) * (1 + η₂ * δ₂) * γ₂ ≤ 1)
    (hA₂ : (1 + η₁) * (1 + η₁ * δ₁) * γ₁ + lam * (1 + η₂) * ρ₂ ≤ lam) :
    Supermartingale
      (fun k ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω)
      𝒢 μ := by

  have hδ₁R : (0 : ℝ) ≤ (δ₁ : ℝ) := Nat.cast_nonneg δ₁
  have hδ₂R : (0 : ℝ) ≤ (δ₂ : ℝ) := Nat.cast_nonneg δ₂
  have hψ₁1 : ∀ k ω, 1 ≤ ψ η₁ δ₁ (N₁ k ω) := fun k ω =>
    one_le_ψ hη₁ hδ₁R (Nat.cast_nonneg _)
  have hψ₂1 : ∀ k ω, 1 ≤ ψ η₂ δ₂ (N₂ k ω) := fun k ω =>
    one_le_ψ hη₂ hδ₂R (Nat.cast_nonneg _)
  have hψ₁cap : ∀ k ω, ψ η₁ δ₁ (N₁ k ω) ≤ 1 + η₁ * δ₁ := fun k ω => ψ_le_cap hη₁
  have hψ₂cap : ∀ k ω, ψ η₂ δ₂ (N₂ k ω) ≤ 1 + η₂ * δ₂ := fun k ω => ψ_le_cap hη₂
  have hψ₁0 : ∀ k ω, 0 ≤ ψ η₁ δ₁ (N₁ k ω) := fun k ω =>
    le_trans zero_le_one (hψ₁1 k ω)
  have hψ₂0 : ∀ k ω, 0 ≤ ψ η₂ δ₂ (N₂ k ω) := fun k ω =>
    le_trans zero_le_one (hψ₂1 k ω)

  have hψN₁_sm : ∀ k, StronglyMeasurable[𝒢 k] fun ω => ψ η₁ δ₁ (N₁ k ω) :=
    fun k => (ψ_continuous η₁ δ₁).comp_stronglyMeasurable
      (hadpN₁ k).stronglyMeasurable
  have hψN₂_sm : ∀ k, StronglyMeasurable[𝒢 k] fun ω => ψ η₂ δ₂ (N₂ k ω) :=
    fun k => (ψ_continuous η₂ δ₂).comp_stronglyMeasurable
      (hadpN₂ k).stronglyMeasurable

  have hWadp : StronglyAdapted 𝒢
      (fun k ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω) :=
    fun k => ((hψN₁_sm k).mul (hadp₁ k).stronglyMeasurable).add
      ((stronglyMeasurable_const.mul (hψN₂_sm k)).mul
        (hadp₂ k).stronglyMeasurable)
  have hg₁int : ∀ k, Integrable (fun ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω) μ :=
    fun k => (hint₁ k).bdd_mul ((hψN₁_sm k).mono (𝒢.le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ₁0 k ω)]; exact hψ₁cap k ω)
  have hg₂int : ∀ k, Integrable (fun ω => lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω) μ :=
    fun k => (hint₂ k).bdd_mul
      ((stronglyMeasurable_const.mul (hψN₂_sm k)).mono
        (𝒢.le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hlam.le (hψ₂0 k ω))]
        exact mul_le_mul_of_nonneg_left (hψ₂cap k ω) hlam.le)
  have hWint : ∀ k, Integrable
      (fun ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω) μ :=
    fun k => (hg₁int k).add (hg₂int k)
  refine supermartingale_nat hWadp hWint fun k => ?_

  set U : Set Ω := {ω | J₁ k ω} ∪ {ω | J₂ k ω} with hU
  have hUm : MeasurableSet[𝒢 k] U := (hJ₁ k).union (hJ₂ k)
  set f₀ : Ω → ℝ := U.indicator
    (fun ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω)
    with hf₀
  set f₁ : Ω → ℝ := Uᶜ.indicator (fun ω => (1 + η₁) * ψ η₁ δ₁ (N₁ k ω)) with hf₁
  set f₂ : Ω → ℝ := Uᶜ.indicator (fun ω => lam * (1 + η₂) * ψ η₂ δ₂ (N₂ k ω))
    with hf₂
  have hf₀_sm : StronglyMeasurable[𝒢 k] f₀ := (hWadp k).indicator hUm
  have hf₁_sm : StronglyMeasurable[𝒢 k] f₁ :=
    (stronglyMeasurable_const.mul (hψN₁_sm k)).indicator hUm.compl
  have hf₂_sm : StronglyMeasurable[𝒢 k] f₂ :=
    (stronglyMeasurable_const.mul (hψN₂_sm k)).indicator hUm.compl
  have hint₀ : Integrable f₀ μ := (hWint k).indicator ((𝒢.le k) _ hUm)
  have hf₁_bdd : ∀ ω, ‖f₁ ω‖ ≤ (1 + η₁) * (1 + η₁ * δ₁) := fun ω => by
    rw [hf₁]
    by_cases hω : ω ∈ Uᶜ
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith) (hψ₁0 k ω))]
      exact mul_le_mul_of_nonneg_left (hψ₁cap k ω) (by linarith)
    · rw [Set.indicator_of_notMem hω]; simp only [norm_zero]
      exact mul_nonneg (by linarith) (by linarith [mul_nonneg hη₁ hδ₁R])
  have hf₂_bdd : ∀ ω, ‖f₂ ω‖ ≤ lam * (1 + η₂) * (1 + η₂ * δ₂) := fun ω => by
    rw [hf₂]
    by_cases hω : ω ∈ Uᶜ
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hlam.le (by linarith)) (hψ₂0 k ω))]
      exact mul_le_mul_of_nonneg_left (hψ₂cap k ω)
        (mul_nonneg hlam.le (by linarith))
    · rw [Set.indicator_of_notMem hω]; simp only [norm_zero]
      exact mul_nonneg (mul_nonneg hlam.le (by linarith))
        (by linarith [mul_nonneg hη₂ hδ₂R])
  obtain ⟨hintf₁, hpull₁⟩ := condExp_pull_bdd (μ := μ) hf₁_sm hf₁_bdd (hint₁ (k+1))
  obtain ⟨hintf₂, hpull₂⟩ := condExp_pull_bdd (μ := μ) hf₂_sm hf₂_bdd (hint₂ (k+1))

  have hUnot : ∀ {ω}, ω ∉ U → ¬ J₁ k ω ∧ ¬ J₂ k ω := fun {ω} hω =>
    ⟨fun h => hω (Or.inl h), fun h => hω (Or.inr h)⟩

  have hdomA : (fun ω => ψ η₁ δ₁ (N₁ (k+1) ω) * V₁ (k+1) ω
        + lam * ψ η₂ δ₂ (N₂ (k+1) ω) * V₂ (k+1) ω)
      ≤ᵐ[μ] f₀ + (f₁ * V₁ (k+1) + f₂ * V₂ (k+1)) := by
    filter_upwards [hjump₁ k, hjump₂ k, hN₁ k, hN₂ k, hdwell₁ k, hdwell₂ k]
      with ω hj₁ hj₂ hn₁ hn₂ hd₁ hd₂
    simp only [Pi.add_apply, Pi.mul_apply, hf₀, hf₁, hf₂]
    by_cases h1 : J₁ k ω <;> by_cases h2 : J₂ k ω
    ·
      have hmem : ω ∈ U := Or.inl h1
      have hnc : ω ∉ Uᶜ := fun hc => hc hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnc,
        Set.indicator_of_notMem hnc, zero_mul, zero_mul,
        add_zero, add_zero, hn₁.1 h1, hn₂.1 h2, (hj₁ h1).2, (hj₂ h2).2]
      have e₁ : ψ η₁ δ₁ ((0 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_zero]; exact ψ_zero hδ₁R
      have e₂ : ψ η₂ δ₂ ((0 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_zero]; exact ψ_zero hδ₂R
      rw [e₁, e₂, one_mul, mul_one]
      have t₁ : V₁ k ω ≤ ψ η₁ δ₁ (N₁ k ω) * V₁ k ω :=
        le_mul_of_one_le_left (hnonneg₁ k ω) (hψ₁1 k ω)
      have t₂ : lam * V₂ k ω ≤ lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω := by
        have := le_mul_of_one_le_left (hnonneg₂ k ω) (hψ₂1 k ω)
        nlinarith [hlam.le]
      linarith
    ·
      have hmem : ω ∈ U := Or.inl h1
      have hnc : ω ∉ Uᶜ := fun hc => hc hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnc,
        Set.indicator_of_notMem hnc, zero_mul, zero_mul,
        add_zero, add_zero, hn₁.1 h1, hn₂.2.2 h2 h1, (hj₁ h1).2]
      have hrepay := gauge_repayment (η := η₁) (τ := ((N₁ k ω : ℕ) : ℝ))
        (by exact_mod_cast hδ₁) (by exact_mod_cast hd₁ h1) hclock₁
        (hnonneg₁ k ω) ((hj₁ h1).1)
      have e₁ : ψ η₁ δ₁ ((0 : ℕ) : ℝ) * V₁ (k+1) ω ≤
          ψ η₁ δ₁ (N₁ k ω) * V₁ k ω := by
        rw [Nat.cast_zero]; simpa using hrepay
      linarith
    ·
      have hmem : ω ∈ U := Or.inr h2
      have hnc : ω ∉ Uᶜ := fun hc => hc hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnc,
        Set.indicator_of_notMem hnc, zero_mul, zero_mul,
        add_zero, add_zero, hn₂.1 h2, hn₁.2.2 h1 h2, (hj₂ h2).2]
      have hrepay := gauge_repayment (η := η₂) (τ := ((N₂ k ω : ℕ) : ℝ))
        (by exact_mod_cast hδ₂) (by exact_mod_cast hd₂ h2) hclock₂
        (hnonneg₂ k ω) ((hj₂ h2).1)
      have e₂ : ψ η₂ δ₂ ((0 : ℕ) : ℝ) * V₂ (k+1) ω ≤
          ψ η₂ δ₂ (N₂ k ω) * V₂ k ω := by
        rw [Nat.cast_zero]; simpa using hrepay
      nlinarith [hlam.le]
    ·
      have hnm : ω ∉ U := fun hc => Or.elim hc h1 h2
      have hmem : ω ∈ Uᶜ := hnm
      rw [Set.indicator_of_notMem hnm, Set.indicator_of_mem hmem,
        Set.indicator_of_mem hmem, zero_add, hn₁.2.1 h1 h2, hn₂.2.1 h2 h1]
      have htax₁ : ψ η₁ δ₁ ((N₁ k ω : ℕ) + 1 : ℕ) ≤ ψ η₁ δ₁ (N₁ k ω) * (1 + η₁) := by
        have h := gauge_flowTax (η := η₁) (δ := (δ₁ : ℝ))
          (τ := ((N₁ k ω : ℕ) : ℝ)) (τ' := ((N₁ k ω : ℕ) : ℝ) + 1) hη₁ hδ₁R
          (Nat.cast_nonneg _) (by linarith)
        rw [add_sub_cancel_left] at h
        simpa [Nat.cast_add_one] using h
      have htax₂ : ψ η₂ δ₂ ((N₂ k ω : ℕ) + 1 : ℕ) ≤ ψ η₂ δ₂ (N₂ k ω) * (1 + η₂) := by
        have h := gauge_flowTax (η := η₂) (δ := (δ₂ : ℝ))
          (τ := ((N₂ k ω : ℕ) : ℝ)) (τ' := ((N₂ k ω : ℕ) : ℝ) + 1) hη₂ hδ₂R
          (Nat.cast_nonneg _) (by linarith)
        rw [add_sub_cancel_left] at h
        simpa [Nat.cast_add_one] using h
      have b₁ : ψ η₁ δ₁ ((N₁ k ω : ℕ) + 1 : ℕ) * V₁ (k+1) ω ≤
          (1 + η₁) * ψ η₁ δ₁ (N₁ k ω) * V₁ (k+1) ω := by
        have := mul_le_mul_of_nonneg_right htax₁ (hnonneg₁ (k+1) ω)
        nlinarith
      have b₂ : lam * ψ η₂ δ₂ ((N₂ k ω : ℕ) + 1 : ℕ) * V₂ (k+1) ω ≤
          lam * (1 + η₂) * ψ η₂ δ₂ (N₂ k ω) * V₂ (k+1) ω := by
        have := mul_le_mul_of_nonneg_right htax₂ (hnonneg₂ (k+1) ω)
        nlinarith [hlam.le]
      linarith

  have hstep : μ[f₀ + (f₁ * V₁ (k+1) + f₂ * V₂ (k+1)) | 𝒢 k]
      ≤ᵐ[μ] fun ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω
        + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω := by
    have hfix : μ[f₀ | 𝒢 k] = f₀ :=
      condExp_of_stronglyMeasurable (𝒢.le k) hf₀_sm hint₀
    calc μ[f₀ + (f₁ * V₁ (k+1) + f₂ * V₂ (k+1)) | 𝒢 k]
        =ᵐ[μ] μ[f₀ | 𝒢 k] + μ[f₁ * V₁ (k+1) + f₂ * V₂ (k+1) | 𝒢 k] :=
          condExp_add hint₀ (hintf₁.add hintf₂) _
      _ =ᵐ[μ] μ[f₀ | 𝒢 k] + (μ[f₁ * V₁ (k+1) | 𝒢 k] + μ[f₂ * V₂ (k+1) | 𝒢 k]) :=
          Filter.EventuallyEq.add Filter.EventuallyEq.rfl
            (condExp_add hintf₁ hintf₂ _)
      _ =ᵐ[μ] f₀ + (f₁ * μ[V₁ (k+1) | 𝒢 k] + f₂ * μ[V₂ (k+1) | 𝒢 k]) := by
          rw [hfix]
          exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl
            (Filter.EventuallyEq.add hpull₁ hpull₂)
      _ ≤ᵐ[μ] fun ω => ψ η₁ δ₁ (N₁ k ω) * V₁ k ω
            + lam * ψ η₂ δ₂ (N₂ k ω) * V₂ k ω := by
          filter_upwards [hflow₁ k, hflow₂ k] with ω hc₁ hc₂
          simp only [Pi.add_apply, Pi.mul_apply, hf₀, hf₁, hf₂]
          by_cases hω : ω ∈ U
          · have hnc : ω ∉ Uᶜ := fun hc => hc hω
            rw [Set.indicator_of_mem hω, Set.indicator_of_notMem hnc,
              Set.indicator_of_notMem hnc, zero_mul, zero_mul,
              add_zero, add_zero]
          · obtain ⟨h1, h2⟩ := hUnot hω
            have hmem : ω ∈ Uᶜ := hω
            rw [Set.indicator_of_notMem hω, Set.indicator_of_mem hmem,
              Set.indicator_of_mem hmem, zero_add]
            have hE₁ := hc₁ h1 h2
            have hE₂ := hc₂ h1 h2

            set P₁ := ψ η₁ δ₁ (N₁ k ω) with hP₁
            set P₂ := ψ η₂ δ₂ (N₂ k ω) with hP₂
            have hP₁1 : 1 ≤ P₁ := hψ₁1 k ω
            have hP₂1 : 1 ≤ P₂ := hψ₂1 k ω
            have hP₁c : P₁ ≤ 1 + η₁ * δ₁ := hψ₁cap k ω
            have hP₂c : P₂ ≤ 1 + η₂ * δ₂ := hψ₂cap k ω
            have hP₁0 : (0 : ℝ) ≤ P₁ := le_trans zero_le_one hP₁1
            have hP₂0 : (0 : ℝ) ≤ P₂ := le_trans zero_le_one hP₂1
            have hv₁ : 0 ≤ V₁ k ω := hnonneg₁ k ω
            have hv₂ : 0 ≤ V₂ k ω := hnonneg₂ k ω

            have hc₁' : (1 + η₁) * P₁ * ρ₁ + lam * (1 + η₂) * P₂ * γ₂ ≤ P₁ := by
              have hcoef : (0 : ℝ) ≤ lam * (1 + η₂) * γ₂ :=
                mul_nonneg (mul_nonneg hlam.le (by linarith)) hγ₂
              have e₁ : lam * (1 + η₂) * γ₂ * P₂ ≤
                  lam * (1 + η₂) * γ₂ * (1 + η₂ * δ₂) :=
                mul_le_mul_of_nonneg_left hP₂c hcoef
              have hterm : (0 : ℝ) ≤ lam * (1 + η₂) * γ₂ * (1 + η₂ * δ₂) := by
                have : (0 : ℝ) ≤ 1 + η₂ * δ₂ := by
                  linarith [mul_nonneg hη₂ hδ₂R]
                exact mul_nonneg hcoef this
              have e₂ : lam * (1 + η₂) * γ₂ * (1 + η₂ * δ₂) ≤
                  lam * (1 + η₂) * γ₂ * (1 + η₂ * δ₂) * P₁ :=
                le_mul_of_one_le_right hterm hP₁1
              have e₃ : ((1 + η₁) * ρ₁ + lam * (1 + η₂) * (1 + η₂ * δ₂) * γ₂) * P₁
                  ≤ 1 * P₁ := mul_le_mul_of_nonneg_right hA₁ hP₁0
              nlinarith [e₁, e₂, e₃]

            have hc₂' : (1 + η₁) * P₁ * γ₁ + lam * (1 + η₂) * P₂ * ρ₂ ≤
                lam * P₂ := by
              have hcoef : (0 : ℝ) ≤ (1 + η₁) * γ₁ :=
                mul_nonneg (by linarith) hγ₁
              have e₁ : (1 + η₁) * γ₁ * P₁ ≤ (1 + η₁) * γ₁ * (1 + η₁ * δ₁) :=
                mul_le_mul_of_nonneg_left hP₁c hcoef
              have hterm : (0 : ℝ) ≤ (1 + η₁) * γ₁ * (1 + η₁ * δ₁) := by
                have : (0 : ℝ) ≤ 1 + η₁ * δ₁ := by
                  linarith [mul_nonneg hη₁ hδ₁R]
                exact mul_nonneg hcoef this
              have e₂ : (1 + η₁) * γ₁ * (1 + η₁ * δ₁) ≤
                  (1 + η₁) * γ₁ * (1 + η₁ * δ₁) * P₂ :=
                le_mul_of_one_le_right hterm hP₂1
              have e₃ : ((1 + η₁) * (1 + η₁ * δ₁) * γ₁ + lam * (1 + η₂) * ρ₂) * P₂
                  ≤ lam * P₂ := mul_le_mul_of_nonneg_right hA₂ hP₂0
              nlinarith [e₁, e₂, e₃]

            have hfac₁ : (0 : ℝ) ≤ (1 + η₁) * P₁ :=
              mul_nonneg (by linarith) hP₁0
            have hfac₂ : (0 : ℝ) ≤ lam * (1 + η₂) * P₂ :=
              mul_nonneg (mul_nonneg hlam.le (by linarith)) hP₂0
            nlinarith [mul_le_mul_of_nonneg_left hE₁ hfac₁,
              mul_le_mul_of_nonneg_left hE₂ hfac₂,
              mul_le_mul_of_nonneg_right hc₁' hv₁,
              mul_le_mul_of_nonneg_right hc₂' hv₂]
  exact (condExp_mono (hWint (k+1)) (hint₀.add (hintf₁.add hintf₂)) hdomA).trans
    hstep

end Discrete

end Qtsl.Gauge

#print axioms Qtsl.Gauge.gauge_repayment
#print axioms Qtsl.Gauge.gauge_flowTax
#print axioms Qtsl.Gauge.pnorm_mono
#print axioms Qtsl.Gauge.pnorm_coord_lipschitz
#print axioms Qtsl.Gauge.pnorm_max_le
#print axioms Qtsl.Gauge.discrete_gauged_supermartingale
#print axioms Qtsl.Gauge.discrete_gauge_smallGain_sum
