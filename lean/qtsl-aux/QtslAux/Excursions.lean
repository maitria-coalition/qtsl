import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Ranking supermartingales, excursion sums, and Streett conditions

This module derives almost-sure liveness and fairness properties from
Lyapunov processes with strict expected decrease, in two settings.

*Ranking.* For a nonnegative adapted `V` whose conditional drift satisfies
`E[V (n+1) | 𝒢 n] ≤ V n - ε₀` while the state process `X` has not entered the
target set `B`:

* `survival_ranking_invariant`: the invariant
  `∫_{survival} V n + ε₀ * ∑_{k<n} μ(survival to k+1) ≤ ∫ V 0`.
* `ranking_hitting_sum_le`: the summed survival probabilities are bounded by
  `∫ V 0 / ε₀`.
* `ae_hits_of_ranking`: for `ε₀ > 0`, the process almost surely reaches `B`.

*Streett.* For a `V` that is non-increasing in conditional mean off the goal
set `G` and strictly decreasing (by `ε₀`) off `G` at visits to the request
set `R`:

* `streett_window_invariant`, `streett_window_sum_le`: windowed versions of
  the invariant, summing request-visits over `G`-free windows starting at an
  arbitrary time `N`.
* `streett_ae_frequently_response`: the Streett (request-response fairness)
  condition holds almost surely — if `R` is visited infinitely often then
  `G` is visited infinitely often — proved via a Borel-Cantelli argument.

The module also provides
`MeasureTheory.Supermartingale.exists_ae_tendsto_of_nonneg`: a nonnegative
supermartingale converges almost everywhere.
-/

open scoped NNReal ENNReal MeasureTheory
open Filter Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

theorem Supermartingale.exists_ae_tendsto_of_nonneg [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  have hmean : ∀ n, ∫ ω, f n ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := fun n => by
    simpa [setIntegral_univ] using
      hf.setIntegral_le (Nat.zero_le n) (MeasurableSet.univ : MeasurableSet[𝒢 0] _)
  have hbdd : ∀ n, eLpNorm ((-f) n) 1 μ ≤ (∫ ω, f 0 ω ∂μ).toNNReal := by
    intro n
    have h2 : eLpNorm (f n) 1 μ = ENNReal.ofReal (∫ ω, f n ω ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ofReal_integral_eq_lintegral_ofReal (hf.integrable n)
          (Eventually.of_forall (hnonneg n))]
      exact lintegral_congr fun ω => Real.enorm_of_nonneg (hnonneg n ω)
    calc eLpNorm ((-f) n) 1 μ = ENNReal.ofReal (∫ ω, f n ω ∂μ) := by
          rw [← h2]; exact eLpNorm_neg (f n) 1 μ
      _ ≤ ENNReal.ofReal (∫ ω, f 0 ω ∂μ) := ENNReal.ofReal_le_ofReal (hmean n)
      _ = ((∫ ω, f 0 ω ∂μ).toNNReal : ℝ≥0∞) := rfl
  filter_upwards [hf.neg.exists_ae_tendsto_of_bdd hbdd] with ω hc
  obtain ⟨c, hc⟩ := hc
  exact ⟨-c, by simpa using hc.neg⟩

end MeasureTheory

namespace Qtsl.Excursions

open MeasureTheory Finset

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {V : ℕ → Ω → ℝ} {X : ℕ → Ω → S} {B R G : Set S} {ε₀ : ℝ}

private lemma measurableSet_survival (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    {n m : ℕ} (h : n ≤ m + 1) : MeasurableSet[𝒢 m] {ω | ∀ k < n, X k ω ∉ B} := by
  have hset : {ω | ∀ k < n, X k ω ∉ B} = ⋂ k, ⋂ (_ : k < n), {ω | X k ω ∈ B}ᶜ := by
    ext ω; simp
  rw [hset]
  exact .iInter fun k => .iInter fun hk =>
    (𝒢.mono (Nat.lt_succ_iff.1 (hk.trans_le h)) _ (hmB k)).compl

private lemma measurableSet_window (hmG : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ G})
    {N n m : ℕ} (h : n ≤ m + 1) :
    MeasurableSet[𝒢 m] {ω | ∀ k, N ≤ k → k < n → X k ω ∉ G} := by
  have hset : {ω | ∀ k, N ≤ k → k < n → X k ω ∉ G}
      = ⋂ k, ⋂ (_ : N ≤ k), ⋂ (_ : k < n), {ω | X k ω ∈ G}ᶜ := by
    ext ω; simp
  rw [hset]
  exact .iInter fun k => .iInter fun _ => .iInter fun hk =>
    (𝒢.mono (Nat.lt_succ_iff.1 (hk.trans_le h)) _ (hmG k)).compl

section Ranking

variable [IsFiniteMeasure μ]

theorem survival_ranking_invariant
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀) (n : ℕ) :
    ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ
        + ε₀ * ∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B}
      ≤ ∫ ω, V 0 ω ∂μ := by
  induction n with
  | zero =>
    have huniv : {ω | ∀ k < 0, X k ω ∉ B} = Set.univ :=
      Set.eq_univ_of_forall fun ω k hk => absurd hk k.not_lt_zero
    rw [huniv, setIntegral_univ, sum_range_zero, mul_zero, add_zero]
  | succ n ih =>
    have hS𝒢 : MeasurableSet[𝒢 n] {ω | ∀ k < n + 1, X k ω ∉ B} :=
      measurableSet_survival hmB le_rfl
    have hSmeas : MeasurableSet {ω | ∀ k < n + 1, X k ω ∉ B} := (𝒢.le n) _ hS𝒢
    have hstep : ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
        ≤ ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
          - ε₀ * μ.real {ω | ∀ k < n + 1, X k ω ∉ B} := by
      calc ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
          = ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, (μ[V (n + 1) | 𝒢 n]) ω ∂μ :=
            (setIntegral_condExp (𝒢.le n) (hint (n + 1)) hS𝒢).symm
        _ ≤ ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, (V n ω - ε₀) ∂μ := by
            refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
              (((hint n).sub (integrable_const ε₀)).integrableOn) ?_
            filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (hdrift n)]
              with ω hmem himp
            exact himp (hmem n n.lt_succ_self)
        _ = ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
              - ε₀ * μ.real {ω | ∀ k < n + 1, X k ω ∉ B} := by
            rw [integral_sub (hint n).integrableOn (integrable_const ε₀).integrableOn,
              setIntegral_const, smul_eq_mul, measureReal_def]
            ring
    have hmono : ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
        ≤ ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ :=
      setIntegral_mono_set (hint n).integrableOn
        (ae_restrict_of_ae (Eventually.of_forall fun ω => hnonneg n ω))
        (Eventually.of_forall fun ω hω k hk => hω k (hk.trans n.lt_succ_self))
    rw [sum_range_succ]
    calc ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V (n + 1) ω ∂μ
          + ε₀ * ((∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B})
              + μ.real {ω | ∀ j < n + 1, X j ω ∉ B})
        ≤ (∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
            - ε₀ * μ.real {ω | ∀ k < n + 1, X k ω ∉ B})
          + ε₀ * ((∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B})
              + μ.real {ω | ∀ j < n + 1, X j ω ∉ B}) := add_le_add hstep le_rfl
      _ = ∫ ω in {ω | ∀ k < n + 1, X k ω ∉ B}, V n ω ∂μ
          + ε₀ * ∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B} := by ring
      _ ≤ ∫ ω in {ω | ∀ k < n, X k ω ∉ B}, V n ω ∂μ
          + ε₀ * ∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B} :=
          add_le_add hmono le_rfl
      _ ≤ ∫ ω, V 0 ω ∂μ := ih

theorem ranking_hitting_sum_le (hε : 0 ≤ ε₀)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀) :
    ENNReal.ofReal ε₀ * ∑' k, μ {ω | ∀ j < k + 1, X j ω ∉ B}
      ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
  have hreal : ∀ n : ℕ, ε₀ * ∑ k ∈ range n, μ.real {ω | ∀ j < k + 1, X j ω ∉ B}
      ≤ ∫ ω, V 0 ω ∂μ := by
    intro n
    refine le_trans (le_add_of_nonneg_left ?_)
      (survival_ranking_invariant hint hnonneg hmB hdrift n)
    exact setIntegral_nonneg ((𝒢.le n) _ (measurableSet_survival hmB n.le_succ))
      fun ω _ => hnonneg n ω
  rw [← ENNReal.tsum_mul_left, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  calc ∑ k ∈ range n, ENNReal.ofReal ε₀ * μ {ω | ∀ j < k + 1, X j ω ∉ B}
      = ENNReal.ofReal (∑ k ∈ range n, ε₀ * μ.real {ω | ∀ j < k + 1, X j ω ∉ B}) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ =>
          mul_nonneg hε measureReal_nonneg]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.ofReal_mul hε, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact hreal n

theorem ae_hits_of_ranking (hε : 0 < ε₀)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀) :
    ∀ᵐ ω ∂μ, ∃ n, X n ω ∈ B := by
  have hsum : ∑' k, μ {ω | ∀ j < k + 1, X j ω ∉ B} ≠ ∞ := by
    intro htop
    have h := ranking_hitting_sum_le hε.le hint hnonneg hmB hdrift
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hε).ne'] at h
    exact absurd (h.trans_lt ENNReal.ofReal_lt_top) (lt_irrefl _)
  have hlim : Tendsto (fun k : ℕ => μ {ω | ∀ j < k + 1, X j ω ∉ B}) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hnever : μ {ω | ∀ n, X n ω ∉ B} = 0 := by
    have hle : ∀ k : ℕ, μ {ω | ∀ n, X n ω ∉ B} ≤ μ {ω | ∀ j < k + 1, X j ω ∉ B} :=
      fun k => measure_mono fun ω hω j _ => hω j
    exact le_antisymm (ge_of_tendsto' hlim hle) zero_le
  rw [ae_iff]
  have hset : {ω | ¬∃ n, X n ω ∈ B} = {ω | ∀ n, X n ω ∉ B} := by ext ω; simp
  rw [hset]
  exact hnever

end Ranking

section Streett

variable [IsFiniteMeasure μ]

theorem streett_window_invariant
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmR : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ R})
    (hmG : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ G})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω)
    (hdriftR : ∀ n, ∀ᵐ ω ∂μ,
      X n ω ∈ R → X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀)
    (N : ℕ) : ∀ n, N ≤ n →
    ∫ ω in {ω | ∀ k, N ≤ k → k < n → X k ω ∉ G}, V n ω ∂μ
        + ε₀ * ∑ k ∈ Ico N n,
            μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R})
      ≤ ∫ ω, V N ω ∂μ := by
  refine Nat.le_induction ?_ ?_
  · have huniv : {ω | ∀ k, N ≤ k → k < N → X k ω ∉ G} = Set.univ :=
      Set.eq_univ_of_forall fun ω k hk1 hk2 => absurd (hk1.trans_lt hk2) (lt_irrefl N)
    rw [huniv, setIntegral_univ, Finset.Ico_self, sum_empty, mul_zero, add_zero]
  · intro n hNn ih
    have hA𝒢 : MeasurableSet[𝒢 n] {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} :=
      measurableSet_window hmG le_rfl
    have hAmeas : MeasurableSet {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} :=
      (𝒢.le n) _ hA𝒢
    have hDmeas : MeasurableSet
        ({ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R}) :=
      (𝒢.le n) _ (hA𝒢.inter (hmR n))
    have hCmeas : MeasurableSet
        ({ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} \ {ω | X n ω ∈ R}) :=
      (𝒢.le n) _ (hA𝒢.diff (hmR n))
    have hdisj : Disjoint
        ({ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R})
        ({ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} \ {ω | X n ω ∈ R}) :=
      Set.disjoint_left.2 fun ω h1 h2 => h2.2 h1.2

    have hsplit : ∀ {g : Ω → ℝ}, Integrable g μ →
        ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, g ω ∂μ
          = (∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
              g ω ∂μ)
            + ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} \ {ω | X n ω ∈ R},
              g ω ∂μ := by
      intro g hg
      rw [← setIntegral_union hdisj hCmeas hg.integrableOn hg.integrableOn,
        Set.inter_union_sdiff]
    have hstep : ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V (n + 1) ω ∂μ
        ≤ ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V n ω ∂μ
          - ε₀ * μ.real
              ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R}) := by
      calc ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V (n + 1) ω ∂μ
          = ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G},
              (μ[V (n + 1) | 𝒢 n]) ω ∂μ :=
            (setIntegral_condExp (𝒢.le n) (hint (n + 1)) hA𝒢).symm
        _ = (∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
              (μ[V (n + 1) | 𝒢 n]) ω ∂μ)
            + ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} \ {ω | X n ω ∈ R},
              (μ[V (n + 1) | 𝒢 n]) ω ∂μ := hsplit integrable_condExp
        _ ≤ ((∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
              V n ω ∂μ)
              - ε₀ * μ.real
                  ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R}))
            + ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} \ {ω | X n ω ∈ R},
              V n ω ∂μ := by
            refine add_le_add ?_ ?_
            · calc ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
                    (μ[V (n + 1) | 𝒢 n]) ω ∂μ
                  ≤ ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
                    (V n ω - ε₀) ∂μ := by
                    refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
                      (((hint n).sub (integrable_const ε₀)).integrableOn) ?_
                    filter_upwards [ae_restrict_mem hDmeas,
                      ae_restrict_of_ae (hdriftR n)] with ω hmem himp
                    exact himp hmem.2 (hmem.1 n hNn n.lt_succ_self)
                _ = (∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G} ∩ {ω | X n ω ∈ R},
                      V n ω ∂μ)
                    - ε₀ * μ.real
                        ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩
                          {ω | X n ω ∈ R}) := by
                    rw [integral_sub (hint n).integrableOn
                      (integrable_const ε₀).integrableOn,
                      setIntegral_const, smul_eq_mul, measureReal_def]
                    ring
            · refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
                (hint n).integrableOn ?_
              filter_upwards [ae_restrict_mem hCmeas,
                ae_restrict_of_ae (hdrift n)] with ω hmem himp
              exact himp (hmem.1 n hNn n.lt_succ_self)
        _ = ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V n ω ∂μ
            - ε₀ * μ.real
                ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R}) := by
            rw [hsplit (hint n)]
            ring
    have hmono : ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V n ω ∂μ
        ≤ ∫ ω in {ω | ∀ k, N ≤ k → k < n → X k ω ∉ G}, V n ω ∂μ :=
      setIntegral_mono_set (hint n).integrableOn
        (ae_restrict_of_ae (Eventually.of_forall fun ω => hnonneg n ω))
        (Eventually.of_forall fun ω hω k hk1 hk2 =>
          hω k hk1 (hk2.trans n.lt_succ_self))
    rw [Finset.sum_Ico_succ_top hNn]
    calc ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V (n + 1) ω ∂μ
          + ε₀ * ((∑ k ∈ Ico N n,
              μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R}))
              + μ.real
                  ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R}))
        ≤ (∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V n ω ∂μ
            - ε₀ * μ.real
                ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R}))
          + ε₀ * ((∑ k ∈ Ico N n,
              μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R}))
              + μ.real
                  ({ω | ∀ j, N ≤ j → j < n + 1 → X j ω ∉ G} ∩ {ω | X n ω ∈ R})) :=
          add_le_add hstep le_rfl
      _ = ∫ ω in {ω | ∀ k, N ≤ k → k < n + 1 → X k ω ∉ G}, V n ω ∂μ
          + ε₀ * ∑ k ∈ Ico N n,
              μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R}) := by
          ring
      _ ≤ ∫ ω in {ω | ∀ k, N ≤ k → k < n → X k ω ∉ G}, V n ω ∂μ
          + ε₀ * ∑ k ∈ Ico N n,
              μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R}) :=
          add_le_add hmono le_rfl
      _ ≤ ∫ ω, V N ω ∂μ := ih

theorem streett_window_sum_le (hε : 0 ≤ ε₀)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmR : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ R})
    (hmG : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ G})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω)
    (hdriftR : ∀ n, ∀ᵐ ω ∂μ,
      X n ω ∈ R → X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀)
    (N : ℕ) :
    ENNReal.ofReal ε₀ * ∑' j : ℕ,
        μ ({ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩ {ω | X (N + j) ω ∈ R})
      ≤ ENNReal.ofReal (∫ ω, V N ω ∂μ) := by
  have hreal : ∀ m : ℕ, ε₀ * ∑ j ∈ range m,
      μ.real ({ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩ {ω | X (N + j) ω ∈ R})
      ≤ ∫ ω, V N ω ∂μ := by
    intro m
    have hIco : ∑ k ∈ Ico N (N + m),
        μ.real ({ω | ∀ j, N ≤ j → j < k + 1 → X j ω ∉ G} ∩ {ω | X k ω ∈ R})
        = ∑ j ∈ range m,
          μ.real ({ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩
            {ω | X (N + j) ω ∈ R}) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
    rw [← hIco]
    refine le_trans (le_add_of_nonneg_left ?_)
      (streett_window_invariant hint hnonneg hmR hmG hdrift hdriftR N (N + m)
        (Nat.le_add_right N m))
    exact setIntegral_nonneg
      ((𝒢.le (N + m)) _ (measurableSet_window hmG (N + m).le_succ))
      fun ω _ => hnonneg (N + m) ω
  rw [← ENNReal.tsum_mul_left, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun m => ?_
  calc ∑ j ∈ range m, ENNReal.ofReal ε₀ *
        μ ({ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩ {ω | X (N + j) ω ∈ R})
      = ENNReal.ofReal (∑ j ∈ range m, ε₀ *
          μ.real ({ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩
            {ω | X (N + j) ω ∈ R})) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
          mul_nonneg hε measureReal_nonneg]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul hε, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (∫ ω, V N ω ∂μ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact hreal m

theorem streett_ae_frequently_response (hε : 0 < ε₀)
    (hint : ∀ n, Integrable (V n) μ) (hnonneg : 0 ≤ V)
    (hmR : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ R})
    (hmG : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ G})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω)
    (hdriftR : ∀ n, ∀ᵐ ω ∂μ,
      X n ω ∈ R → X n ω ∉ G → (μ[V (n + 1) | 𝒢 n]) ω ≤ V n ω - ε₀) :
    ∀ᵐ ω ∂μ, (∃ᶠ n in atTop, X n ω ∈ R) → ∃ᶠ n in atTop, X n ω ∈ G := by

  have hBC : ∀ N : ℕ, μ (Filter.limsup (fun j : ℕ =>
      {ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩ {ω | X (N + j) ω ∈ R})
        atTop) = 0 := by
    intro N
    refine measure_limsup_atTop_eq_zero ?_
    intro htop
    have h := streett_window_sum_le hε.le hint hnonneg hmR hmG hdrift hdriftR N
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hε).ne'] at h
    exact absurd (h.trans_lt ENNReal.ofReal_lt_top) (lt_irrefl _)

  have hsub : ∀ N : ℕ,
      {ω | (∀ M, ∃ n, M ≤ n ∧ X n ω ∈ R) ∧ ∀ k, N ≤ k → X k ω ∉ G}
        ⊆ Filter.limsup (fun j : ℕ =>
            {ω | ∀ k, N ≤ k → k < N + j + 1 → X k ω ∉ G} ∩ {ω | X (N + j) ω ∈ R})
            atTop := by
    intro N ω hω
    rw [Filter.mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
    intro j₀
    obtain ⟨n, hn, hnR⟩ := hω.1 (N + j₀)
    have hNn : N ≤ n := le_trans (Nat.le_add_right N j₀) hn
    refine ⟨n - N, by omega, fun k hk _ => hω.2 k hk, ?_⟩
    have hidx : N + (n - N) = n := by omega
    rw [Set.mem_setOf_eq, hidx]
    exact hnR
  have hnull : μ (⋃ N : ℕ,
      {ω | (∀ M, ∃ n, M ≤ n ∧ X n ω ∈ R) ∧ ∀ k, N ≤ k → X k ω ∉ G}) = 0 :=
    measure_iUnion_null fun N => measure_mono_null (hsub N) (hBC N)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro ω hω
  rw [Set.mem_setOf_eq, Filter.frequently_atTop, Filter.frequently_atTop] at hω
  push Not at hω
  obtain ⟨hR, M, hM⟩ := hω
  exact Set.mem_iUnion.2 ⟨M, hR, hM⟩

end Streett

end Qtsl.Excursions
