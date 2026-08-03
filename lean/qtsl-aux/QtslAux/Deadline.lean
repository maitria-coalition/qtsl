import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Deadline bounds from geometrically decaying Lyapunov processes

For an adapted nonnegative process `V` and a state process `X`, suppose the
conditional drift satisfies `E[V (n+1) | 𝒢 n] ≤ β * V n` on the event that
`X n` has not yet entered the target set `B`, and `V` is at least `a` off
`B`. This module derives quantitative bounds on how long the process can
avoid `B`.

Main results:

* `MeasureTheory.supermartingale_inv_pow_mul`: rescaling a `β`-decaying
  process by `β⁻¹ ^ n` produces a supermartingale.
* `setIntegral_survival_le`: the integral of `V n` over the survival event
  (no visit to `B` before time `n`) is at most `β ^ n * ∫ V 0`.
* `expMoment_hitting`: an exponential-moment bound on the first hitting time
  of `B` — the series `∑ₖ β⁻ᵏ · μ(first hit at time k)`, weighted by the
  barrier level `a`, is bounded by `∫ V 0`.
* `deadline_tail`, `deadline_tail_div`: the tail bound
  `a * μ {∀ k ≤ n, X k ∉ B} ≤ β ^ n * ∫ V 0` and its divided form — the
  quantitative engine behind deadline certificates.
* `ae_hits`: for `β < 1`, the process almost surely reaches `B`.
-/

open scoped NNReal ENNReal MeasureTheory
open Filter Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

theorem supermartingale_inv_pow_mul [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {β : ℝ}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ n, Integrable (f n) μ) (hβ : 0 < β)
    (hdrift : ∀ n, μ[f (n + 1) | 𝒢 n] ≤ᵐ[μ] fun ω => β * f n ω) :
    Supermartingale (fun n ω => β⁻¹ ^ n * f n ω) 𝒢 μ := by
  refine supermartingale_nat (fun n => (hadp n).const_mul _)
    (fun n => (hint n).const_mul _) fun n => ?_
  have hsmul : μ[fun ω => β⁻¹ ^ (n + 1) * f (n + 1) ω | 𝒢 n]
      =ᵐ[μ] fun ω => β⁻¹ ^ (n + 1) * (μ[f (n + 1) | 𝒢 n]) ω := by
    have hfun : (fun ω => β⁻¹ ^ (n + 1) * f (n + 1) ω) = β⁻¹ ^ (n + 1) • f (n + 1) :=
      funext fun ω => (smul_eq_mul _ _).symm
    rw [hfun]
    filter_upwards [condExp_smul (μ := μ) (β⁻¹ ^ (n + 1)) (f (n + 1)) (𝒢 n)] with ω hω
    simpa [smul_eq_mul] using hω
  filter_upwards [hsmul, hdrift n] with ω h₁ h₂
  calc (μ[fun ω => β⁻¹ ^ (n + 1) * f (n + 1) ω | 𝒢 n]) ω
      = β⁻¹ ^ (n + 1) * (μ[f (n + 1) | 𝒢 n]) ω := h₁
    _ ≤ β⁻¹ ^ (n + 1) * (β * f n ω) :=
        mul_le_mul_of_nonneg_left h₂ (pow_nonneg (inv_nonneg.2 hβ.le) _)
    _ = β⁻¹ ^ n * (β⁻¹ * β) * f n ω := by ring
    _ = β⁻¹ ^ n * f n ω := by rw [inv_mul_cancel₀ hβ.ne', mul_one]

end MeasureTheory

namespace Qtsl.Deadline

open MeasureTheory Finset

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {V : ℕ → Ω → ℝ} {X : ℕ → Ω → S} {B : Set S} {β a : ℝ}

private lemma measurableSet_survival (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    {n m : ℕ} (h : n ≤ m + 1) : MeasurableSet[𝒢 m] {ω | ∀ k < n, X k ω ∉ B} := by
  have hset : {ω | ∀ k < n, X k ω ∉ B} = ⋂ k, ⋂ (_ : k < n), {ω | X k ω ∈ B}ᶜ := by
    ext ω; simp
  rw [hset]
  exact .iInter fun k => .iInter fun hk =>
    (𝒢.mono (Nat.lt_succ_iff.1 (hk.trans_le h)) _ (hmB k)).compl

private lemma firstHit_union_survival (n : ℕ) :
    {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B} ∪ {ω | ∀ k < n + 1, X k ω ∉ B}
      = {ω | ∀ k < n, X k ω ∉ B} := by
  ext ω
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact h
    · exact fun k hk => h k (hk.trans n.lt_succ_self)
  · intro h
    by_cases hB : X n ω ∈ B
    · exact Or.inl ⟨hB, h⟩
    · refine Or.inr fun k hk => ?_
      rcases (Nat.lt_succ_iff.1 hk).lt_or_eq with h' | rfl
      · exact h k h'
      · exact hB

private lemma disjoint_firstHit_survival (n : ℕ) :
    Disjoint {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B} {ω | ∀ k < n + 1, X k ω ∉ B} :=
  Set.disjoint_left.2 fun _ hω h => h n n.lt_succ_self hω.1

section Engine

variable [IsFiniteMeasure μ]

theorem setIntegral_survival_le (hβ : 0 ≤ β)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ β * V n ω) (n : ℕ) :
    ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ ≤ β ^ n * ∫ ω, V 0 ω ∂μ := by
  induction n with
  | zero =>
    have huniv : {ω | ∀ k < 0, X k ω ∉ B} = Set.univ :=
      Set.eq_univ_of_forall fun ω k hk => absurd hk k.not_lt_zero
    rw [huniv, setIntegral_univ, pow_zero, one_mul]
  | succ n ih =>
    have hSmeas : MeasurableSet {ω | ∀ k < n + 1, X k ω ∉ B} :=
      (𝒢.le n) _ (measurableSet_survival hmB le_rfl)
    calc ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
        = ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, (μ[V (n + 1) | 𝒢 n]) ω ∂μ :=
          (setIntegral_condExp (𝒢.le n) (hint (n + 1))
            (measurableSet_survival hmB le_rfl)).symm
      _ ≤ ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, β * V n ω ∂μ := by
          refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
            (((hint n).const_mul β).integrableOn) ?_
          filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (hdrift n)]
            with ω hmem himp
          exact himp (hmem n n.lt_succ_self)
      _ = β * ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ := integral_const_mul β _
      _ ≤ β * ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ := by
          refine mul_le_mul_of_nonneg_left ?_ hβ
          exact setIntegral_mono_set (hint n).integrableOn
            (ae_restrict_of_ae (Eventually.of_forall fun ω => hnonneg n ω))
            (Eventually.of_forall fun ω hω k hk => hω k (hk.trans n.lt_succ_self))
      _ ≤ β * (β ^ n * ∫ ω, V 0 ω ∂μ) := mul_le_mul_of_nonneg_left ih hβ
      _ = β ^ (n + 1) * ∫ ω, V 0 ω ∂μ := by ring

theorem expMoment_hitting (hβ : 0 < β)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ β * V n ω)
    (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) :
    ENNReal.ofReal a *
        ∑' k, ENNReal.ofReal (β⁻¹ ^ k) * μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}
      ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [ENNReal.ofReal_eq_zero.2 ha, zero_mul]
    exact zero_le

  have hDmeas : ∀ k, MeasurableSet {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B} := fun k =>
    (𝒢.le k) _ ((hmB k).inter (measurableSet_survival hmB k.le_succ))
  have hSmeas : ∀ k, MeasurableSet {ω | ∀ j < k, X j ω ∉ B} := fun k =>
    (𝒢.le k) _ (measurableSet_survival hmB k.le_succ)

  have key : ∀ n : ℕ,
      (∑ k ∈ range n,
          β⁻¹ ^ k * ∫ ω in {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}, V k ω ∂μ) +
        β⁻¹ ^ n * ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ ≤ ∫ ω, V 0 ω ∂μ := by
    intro n
    induction n with
    | zero =>
      have huniv : {ω | ∀ k < 0, X k ω ∉ B} = Set.univ :=
        Set.eq_univ_of_forall fun ω k hk => absurd hk k.not_lt_zero
      rw [sum_range_zero, huniv, setIntegral_univ, pow_zero, one_mul, zero_add]
    | succ n ih =>
      refine le_trans ?_ ih
      rw [sum_range_succ, add_assoc]
      refine _root_.add_le_add_right ?_ _

      have hstep : ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
          ≤ β * ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ := by
        calc ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
            = ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, (μ[V (n + 1) | 𝒢 n]) ω ∂μ :=
              (setIntegral_condExp (𝒢.le n) (hint (n + 1))
                (measurableSet_survival hmB le_rfl)).symm
          _ ≤ ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, β * V n ω ∂μ := by
              refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
                (((hint n).const_mul β).integrableOn) ?_
              filter_upwards [ae_restrict_mem (hSmeas (n + 1)),
                ae_restrict_of_ae (hdrift n)] with ω hmem himp
              exact himp (hmem n n.lt_succ_self)
          _ = β * ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ := integral_const_mul β _
      have hsplit : ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ
          = (∫ ω in {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B}, V n ω ∂μ) +
            ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ := by
        rw [← setIntegral_union (disjoint_firstHit_survival n) (hSmeas (n + 1))
          (hint n).integrableOn (hint n).integrableOn, firstHit_union_survival n]
      calc β⁻¹ ^ n * ∫ ω in {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B}, V n ω ∂μ +
            β⁻¹ ^ (n + 1) * ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
          ≤ β⁻¹ ^ n * ∫ ω in {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B}, V n ω ∂μ +
            β⁻¹ ^ (n + 1) *
              (β * ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ) := by
            refine _root_.add_le_add_right (mul_le_mul_of_nonneg_left hstep ?_) _
            exact pow_nonneg (inv_nonneg.2 hβ.le) _
        _ = β⁻¹ ^ n * ∫ ω in {ω | X n ω ∈ B ∧ ∀ j < n, X j ω ∉ B}, V n ω ∂μ +
            β⁻¹ ^ n * (β⁻¹ * β) *
              ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ := by ring
        _ = β⁻¹ ^ n * ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ := by
            rw [inv_mul_cancel₀ hβ.ne', mul_one, hsplit]; ring

  have key' : ∀ n : ℕ,
      (∑ k ∈ range n,
        β⁻¹ ^ k * ∫ ω in {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}, V k ω ∂μ)
        ≤ ∫ ω, V 0 ω ∂μ := fun n =>
    le_trans (le_add_of_nonneg_right (mul_nonneg (pow_nonneg (inv_nonneg.2 hβ.le) _)
      (setIntegral_nonneg (hSmeas n) fun ω _ => hnonneg n ω))) (key n)
  rw [← ENNReal.tsum_mul_left, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have hterm : ∀ k, ENNReal.ofReal a *
      (ENNReal.ofReal (β⁻¹ ^ k) * μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B})
      = ENNReal.ofReal (β⁻¹ ^ k *
          (a * (μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}).toReal)) := by
    intro k
    rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hβ.le) _), ENNReal.ofReal_mul ha.le,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
    ring
  calc ∑ k ∈ range n, ENNReal.ofReal a *
        (ENNReal.ofReal (β⁻¹ ^ k) * μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B})
      = ∑ k ∈ range n, ENNReal.ofReal (β⁻¹ ^ k *
          (a * (μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}).toReal)) := by
        exact Finset.sum_congr rfl fun k _ => hterm k
    _ = ENNReal.ofReal (∑ k ∈ range n, β⁻¹ ^ k *
          (a * (μ {ω | X k ω ∈ B ∧ ∀ j < k, X j ω ∉ B}).toReal)) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ =>
          mul_nonneg (pow_nonneg (inv_nonneg.2 hβ.le) _)
            (mul_nonneg ha.le ENNReal.toReal_nonneg)).symm
    _ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
        refine ENNReal.ofReal_le_ofReal (le_trans (Finset.sum_le_sum fun k _ => ?_)
          (key' n))
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_nonneg.2 hβ.le) _)
        have := setIntegral_ge_of_const_le_real (hDmeas k) (measure_ne_top μ _)
          (fun ω hω => hbarrier k ω hω.1) (hint k).integrableOn
        simpa [Measure.real] using this

end Engine

section Deadline

variable [IsFiniteMeasure μ]

theorem deadline_tail (hβ : 0 ≤ β)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ β * V n ω)
    (hbarrier : ∀ n ω, X n ω ∉ B → a ≤ V n ω) (n : ℕ) :
    ENNReal.ofReal a * μ {ω | ∀ k ≤ n, X k ω ∉ B}
      ≤ ENNReal.ofReal (β ^ n * ∫ ω, V 0 ω ∂μ) := by
  have hset : {ω | ∀ k ≤ n, X k ω ∉ B} = {ω | ∀ k < n + 1, X k ω ∉ B} := by
    ext ω; simp
  rw [hset]
  rcases le_or_gt a 0 with ha | ha
  · rw [ENNReal.ofReal_eq_zero.2 ha, zero_mul]
    exact zero_le
  have hSmeas : MeasurableSet {ω | ∀ k < n + 1, X k ω ∉ B} :=
    (𝒢.le n) _ (measurableSet_survival hmB le_rfl)

  have hbar : a * μ.real {ω | ∀ k < n + 1, X k ω ∉ B}
      ≤ ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ :=
    setIntegral_ge_of_const_le_real hSmeas (measure_ne_top μ _)
      (fun ω hω => hbarrier n ω (hω n n.lt_succ_self)) (hint n).integrableOn

  have hmono : ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
      ≤ ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ :=
    setIntegral_mono_set (hint n).integrableOn
      (ae_restrict_of_ae (Eventually.of_forall fun ω => hnonneg n ω))
      (Eventually.of_forall fun ω hω k hk => hω k (hk.trans n.lt_succ_self))
  have hchain : a * μ.real {ω | ∀ k < n + 1, X k ω ∉ B} ≤ β ^ n * ∫ ω, V 0 ω ∂μ :=
    hbar.trans (hmono.trans (setIntegral_survival_le hβ hint hnonneg hmB hdrift n))
  calc ENNReal.ofReal a * μ {ω | ∀ k < n + 1, X k ω ∉ B}
      = ENNReal.ofReal (a * μ.real {ω | ∀ k < n + 1, X k ω ∉ B}) := by
        rw [ENNReal.ofReal_mul ha.le, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (β ^ n * ∫ ω, V 0 ω ∂μ) := ENNReal.ofReal_le_ofReal hchain

theorem deadline_tail_div (hβ : 0 ≤ β)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ β * V n ω)
    (ha : 0 < a) (hbarrier : ∀ n ω, X n ω ∉ B → a ≤ V n ω) (n : ℕ) :
    μ {ω | ∀ k ≤ n, X k ω ∉ B}
      ≤ ENNReal.ofReal (β ^ n * ∫ ω, V 0 ω ∂μ) / ENNReal.ofReal a := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 ha).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact deadline_tail hβ hint hnonneg hmB hdrift hbarrier n

theorem ae_hits (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ β * V n ω)
    (ha : 0 < a) (hbarrier : ∀ n ω, X n ω ∉ B → a ≤ V n ω) :
    ∀ᵐ ω ∂μ, ∃ n, X n ω ∈ B := by
  have hsub : ∀ n : ℕ, {ω | ∀ k, X k ω ∉ B} ⊆ {ω | ∀ k ≤ n, X k ω ∉ B} :=
    fun _ _ hω k _ => hω k
  have key : ∀ n : ℕ, ENNReal.ofReal a * μ {ω | ∀ k, X k ω ∉ B}
      ≤ ENNReal.ofReal (β ^ n * ∫ ω, V 0 ω ∂μ) := fun n =>
    le_trans (mul_le_mul_right (measure_mono (hsub n)) _)
      (deadline_tail hβ0 hint hnonneg hmB hdrift hbarrier n)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (β ^ n * ∫ ω, V 0 ω ∂μ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => β ^ n * ∫ ω, V 0 ω ∂μ) atTop (𝓝 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (∫ ω, V 0 ω ∂μ)
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h1
  have hμ0 : μ {ω | ∀ k, X k ω ∉ B} = 0 := by
    have h0 : ENNReal.ofReal a * μ {ω | ∀ k, X k ω ∉ B} = 0 :=
      le_antisymm (ge_of_tendsto' hlim key) zero_le
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (ENNReal.ofReal_pos.2 ha).ne'
    · exact h
  have hset : {ω | ¬∃ n, X n ω ∈ B} = {ω | ∀ k, X k ω ∉ B} := by
    ext ω; simp
  rw [ae_iff, hset]
  exact hμ0

end Deadline

end Qtsl.Deadline
