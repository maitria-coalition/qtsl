import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Ville's inequality

This module proves Ville's inequality for nonnegative supermartingales in
discrete time, together with its randomized variant and the reach-avoidance
corollary that underlies supermartingale certificates for probabilistic
safety.

In the `MeasureTheory` namespace (extending mathlib's martingale library):

* `Supermartingale.expected_stoppedValue_antitone`: optional stopping for
  supermartingales — the expected stopped value is antitone in the stopping
  time (the order-dual of the submartingale version).
* `Supermartingale.maximal_ineq`: the finite-horizon maximal inequality —
  for a nonnegative supermartingale `f`,
  `ε * μ {ω | ε ≤ max_{k ≤ n} f k ω} ≤ E[f 0]`.
* `Supermartingale.ville_ineq`, `Supermartingale.ville_ineq_div`: Ville's
  inequality — the probability that a nonnegative supermartingale ever
  reaches level `ε` is at most `E[f 0] / ε`, obtained from the maximal
  inequality by monotone convergence over horizons.
* `Supermartingale.ville_ineq_randomized`,
  `Supermartingale.ville_ineq_randomized_div`: the randomized variant — an
  independent threshold `u` drawn uniformly from `(0, 1)` is compared
  against the value stopped at a bounded stopping time `τ`, and
  `ε * P (u * ε ≤ f τ) ≤ E[f 0]`; this sharpens the deterministic
  threshold test while keeping the same budget.

In the `Qtsl.Ville` namespace:

* `reach_avoid`, `reach_avoid_div`: the reach-avoidance bound — if `V` is a
  nonnegative supermartingale and `V n ω ≥ a` whenever the process `X`
  visits the bad set `B`, then the probability that `X` ever visits `B` is
  at most `E[V 0] / a`. This is the form in which supermartingale
  certificates discharge probabilistic safety obligations.
-/

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

open Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {τ π : Ω → ℕ∞}

/-- Optional stopping for supermartingales: for bounded stopping times
`τ ≤ π`, the expected stopped value is antitone,
`μ[stoppedValue f π] ≤ μ[stoppedValue f τ]`. Deduced from the
submartingale version by negation. -/
theorem Supermartingale.expected_stoppedValue_antitone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f π] ≤ μ[stoppedValue f τ] := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact hf.neg.expected_stoppedValue_mono hτ hπ hle hbdd

section Maximal

variable {f : ℕ → Ω → ℝ}

/-- Auxiliary step for the maximal inequality: on the event that the
running maximum over times `0, …, n` reaches `ε`, the process stopped at
the first hitting time of `[ε, ∞)` is at least `ε`, so `ε` times the
event's measure is bounded by the integral of the stopped value over the
event. -/
theorem smul_le_stoppedValue_hittingBtwn_of_stronglyAdapted [IsFiniteMeasure μ]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) {ε : ℝ≥0} (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have hmax : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun k _ => ((hadp k).measurable.le (𝒢.le k))))
      (measure_ne_top _ _) hmax (Integrable.integrableOn (integrable_stoppedValue ℕ
        (hadp.adapted.isStoppingTime_hittingBtwn measurableSet_Ici) hint (N := n)
        fun ω => WithTop.coe_le_coe.2 (hittingBtwn_le ω)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

/-- Maximal inequality for nonnegative supermartingales, finite horizon:
`ε * μ {ω | ε ≤ max_{k ≤ n} f k ω} ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ)`.
The proof stops at the first hitting time of `[ε, ∞)` and applies optional
stopping. -/
theorem Supermartingale.maximal_ineq [IsFiniteMeasure μ] (hsup : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) {ε : ℝ≥0} (n : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
      ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := by
  have hst : IsStoppingTime 𝒢 fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ) :=
    hsup.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hint : Integrable
      (stoppedValue f fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) μ :=
    integrable_stoppedValue ℕ hst hsup.integrable (N := n) fun ω =>
      WithTop.coe_le_coe.2 (hittingBtwn_le ω)
  calc
    (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
        ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) :=
      smul_le_stoppedValue_hittingBtwn_of_stronglyAdapted hsup.stronglyAdapted
        hsup.integrable n
    _ ≤ ENNReal.ofReal
          (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) :=
      ENNReal.ofReal_le_ofReal
        (setIntegral_le_integral hint (ae_of_all _ fun ω => hnonneg _ _))
    _ ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f 0]
      exact hsup.expected_stoppedValue_antitone (isStoppingTime_const _ _) hst
        (fun ω => WithTop.coe_le_coe.2 (Nat.zero_le _)) (N := n)
        fun ω => WithTop.coe_le_coe.2 (hittingBtwn_le ω)

/-- **Ville's inequality**: for a nonnegative supermartingale `f`,
`ε * μ {ω | ∃ k, ε ≤ f k ω} ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ)` — the
probability of the running supremum ever reaching `ε` is controlled by the
initial expectation. Obtained from `maximal_ineq` by taking the increasing
union over horizons. -/
theorem Supermartingale.ville_ineq [IsFiniteMeasure μ] (hsup : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) (ε : ℝ≥0) :
    ε * μ {ω | ∃ k, (ε : ℝ) ≤ f k ω} ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := by
  have hmono : Monotone fun n =>
      {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} := by
    intro a b hab ω hω
    simp only [Set.mem_setOf_eq, le_sup'_iff, mem_range, Nat.lt_succ_iff] at hω ⊢
    obtain ⟨k, hka, hεk⟩ := hω
    exact ⟨k, hka.trans hab, hεk⟩
  have hunion : {ω | ∃ k, (ε : ℝ) ≤ f k ω} =
      ⋃ n, {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, le_sup'_iff, mem_range, Nat.lt_succ_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩, fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩⟩
  rw [hunion, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n => hsup.maximal_ineq hnonneg n

/-- Ville's inequality in divided form: the probability that a nonnegative
supermartingale ever reaches level `ε > 0` is at most
`ENNReal.ofReal (∫ ω, f 0 ω ∂μ) / ε`. -/
theorem Supermartingale.ville_ineq_div [IsFiniteMeasure μ] (hsup : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ {ω | ∃ k, (ε : ℝ) ≤ f k ω} ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ) / ε := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hε))
    (Or.inl ENNReal.coe_ne_top), mul_comm]
  exact hsup.ville_ineq hnonneg ε

end Maximal

section Randomized

variable {f : ℕ → Ω → ℝ}

/-- Auxiliary estimate for the randomized variant: the average (over `ω`)
Lebesgue measure of the set of thresholds `u ∈ (0, 1)` with `u * ε ≤ X ω`
is at most `E[X] / ε` — a fiberwise Markov bound. -/
theorem lintegral_volume_inter_Ioo_le {X : Ω → ℝ} (hX : Integrable X μ) (hnonneg : 0 ≤ X)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∫⁻ ω, volume ({u : ℝ | u * ε ≤ X ω} ∩ Set.Ioo (0 : ℝ) 1) ∂μ ≤
      ENNReal.ofReal (∫ ω, X ω ∂μ) / ε := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hpt : ∀ ω, volume ({u : ℝ | u * ε ≤ X ω} ∩ Set.Ioo (0 : ℝ) 1) ≤
      ENNReal.ofReal (X ω / ε) := by
    intro ω
    have hsub : {u : ℝ | u * ε ≤ X ω} ∩ Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) (X ω / ε) := by
      rintro u ⟨hthr, hu0, -⟩
      exact ⟨hu0, (le_div_iff₀ hεpos).2 hthr⟩
    calc
      volume ({u : ℝ | u * ε ≤ X ω} ∩ Set.Ioo (0 : ℝ) 1) ≤
          volume (Set.Ioc (0 : ℝ) (X ω / ε)) := measure_mono hsub
      _ = ENNReal.ofReal (X ω / ε) := by rw [Real.volume_Ioc, sub_zero]
  calc
    ∫⁻ ω, volume ({u : ℝ | u * ε ≤ X ω} ∩ Set.Ioo (0 : ℝ) 1) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (X ω / ε) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ω, X ω / ε ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hX.div_const _)
          (ae_of_all _ fun ω => div_nonneg (hnonneg ω) hεpos.le)).symm
    _ = ENNReal.ofReal (∫ ω, X ω ∂μ) / ε := by
        rw [integral_div, ENNReal.ofReal_div_of_pos hεpos, ENNReal.ofReal_coe_nnreal]

/-- Randomized Ville inequality: comparing the value stopped at a bounded
stopping time `τ` against a threshold `u * ε` with `u` drawn uniformly and
independently from `(0, 1)`, the rejection probability still satisfies
`ε * P (u * ε ≤ stoppedValue f τ) ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ)` —
the randomized threshold sharpens the test at no cost in budget. -/
theorem Supermartingale.ville_ineq_randomized [IsFiniteMeasure μ]
    (hsup : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) (hτ : IsStoppingTime 𝒢 τ) {N : ℕ}
    (hbdd : ∀ ω, τ ω ≤ N) (ε : ℝ≥0) :
    ε * (μ.prod (volume.restrict (Set.Ioo (0 : ℝ) 1)))
        {p : Ω × ℝ | p.2 * ε ≤ stoppedValue f τ p.1} ≤
      ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := by
  rcases eq_or_ne ε 0 with rfl | hε
  · rw [ENNReal.coe_zero, zero_mul]
    exact zero_le
  · have hmeas : Measurable (stoppedValue f τ) :=
      (measurable_stoppedValue hsup.stronglyAdapted.isStronglyProgressive_of_discrete
        hτ).mono hτ.measurableSpace_le le_rfl
    have hset : MeasurableSet {p : Ω × ℝ | p.2 * ε ≤ stoppedValue f τ p.1} :=
      measurableSet_le (measurable_snd.mul_const _) (hmeas.comp measurable_fst)
    have hconst : ∀ ω, MeasurableSet {u : ℝ | u * (ε : ℝ) ≤ stoppedValue f τ ω} := fun _ =>
      measurableSet_le (measurable_id.mul_const _) measurable_const
    have hslice : ∀ ω, (volume.restrict (Set.Ioo (0 : ℝ) 1))
        (Prod.mk ω ⁻¹' {p : Ω × ℝ | p.2 * ε ≤ stoppedValue f τ p.1}) =
        volume ({u : ℝ | u * ε ≤ stoppedValue f τ ω} ∩ Set.Ioo (0 : ℝ) 1) := fun ω =>
      Measure.restrict_apply (hconst ω)
    rw [Measure.prod_apply hset, lintegral_congr hslice]
    calc
      (ε : ℝ≥0∞) *
          ∫⁻ ω, volume ({u : ℝ | u * ε ≤ stoppedValue f τ ω} ∩ Set.Ioo (0 : ℝ) 1) ∂μ ≤
          ε * (ENNReal.ofReal (∫ ω, stoppedValue f τ ω ∂μ) / ε) := by
        gcongr
        exact lintegral_volume_inter_Ioo_le
          (integrable_stoppedValue ℕ hτ hsup.integrable hbdd) (fun ω => hnonneg _ _) hε
      _ ≤ ENNReal.ofReal (∫ ω, stoppedValue f τ ω ∂μ) := ENNReal.mul_div_le
      _ ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← stoppedValue_const f 0]
          exact hsup.expected_stoppedValue_antitone (isStoppingTime_const _ _) hτ
            (fun _ => zero_le) hbdd

/-- Divided form of the randomized Ville inequality. -/
theorem Supermartingale.ville_ineq_randomized_div [IsFiniteMeasure μ]
    (hsup : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) (hτ : IsStoppingTime 𝒢 τ) {N : ℕ}
    (hbdd : ∀ ω, τ ω ≤ N) {ε : ℝ≥0} (hε : ε ≠ 0) :
    (μ.prod (volume.restrict (Set.Ioo (0 : ℝ) 1)))
        {p : Ω × ℝ | p.2 * ε ≤ stoppedValue f τ p.1} ≤
      ENNReal.ofReal (∫ ω, f 0 ω ∂μ) / ε := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hε))
    (Or.inl ENNReal.coe_ne_top), mul_comm]
  exact hsup.ville_ineq_randomized hnonneg hτ hbdd ε

end Randomized

end MeasureTheory

namespace Qtsl.Ville

open MeasureTheory

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {V : ℕ → Ω → ℝ} {X : ℕ → Ω → S} {B : Set S}

/-- Reach-avoidance from a supermartingale certificate: if `V` is a
nonnegative supermartingale that is at least `a` whenever the process `X`
visits the bad set `B`, then
`ENNReal.ofReal a * μ {ω | ∃ n, X n ω ∈ B} ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ)`. -/
theorem reach_avoid [IsFiniteMeasure μ] (hV : Supermartingale V 𝒢 μ) (hnonneg : 0 ≤ V)
    {a : ℝ} (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) :
    ENNReal.ofReal a * μ {ω | ∃ n, X n ω ∈ B} ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [ENNReal.ofReal_eq_zero.2 ha, zero_mul]
    exact zero_le
  · have hsubset : {ω | ∃ n, X n ω ∈ B} ⊆ {ω | ∃ n, (a.toNNReal : ℝ) ≤ V n ω} := by
      rintro ω ⟨n, hn⟩
      exact ⟨n, by rw [Real.coe_toNNReal a ha.le]; exact hbarrier n ω hn⟩
    calc
      ENNReal.ofReal a * μ {ω | ∃ n, X n ω ∈ B} ≤
          ENNReal.ofReal a * μ {ω | ∃ n, (a.toNNReal : ℝ) ≤ V n ω} :=
        mul_le_mul_right (measure_mono hsubset) _
      _ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := hV.ville_ineq hnonneg a.toNNReal

/-- Divided form of `reach_avoid`: for a barrier level `a > 0`, the
probability that `X` ever visits `B` is at most `E[V 0] / a`. -/
theorem reach_avoid_div [IsFiniteMeasure μ] (hV : Supermartingale V 𝒢 μ) (hnonneg : 0 ≤ V)
    {a : ℝ} (ha : 0 < a) (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) :
    μ {ω | ∃ n, X n ω ∈ B} ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) / ENNReal.ofReal a := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 ha).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact reach_avoid hV hnonneg hbarrier

end Qtsl.Ville
