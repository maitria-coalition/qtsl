import Mathlib

/-! # Optional sampling for right-continuous nonnegative supermartingales

Mathlib's optional stopping theory is developed for discrete time or for
stopping times with countable range. This module proves the continuous-time
inequalities needed to evaluate a nonnegative right-continuous supermartingale
indexed by `ℝ≥0` at an arbitrary stopping time, together with pathwise
groundwork for the `e^{-ct}`-discounting constructions of Dynkin-formula
arguments. See Karatzas–Shreve, *Brownian Motion and
Stochastic Calculus*, §1.3 (optional sampling) and §5.4 (the martingale
problem), or Revuz–Yor, *Continuous Martingales and Brownian Motion*, Ch. II.

Stopping times appear through their defining measurability family
`∀ t, MeasurableSet[ℱ t] {ω | τ ω ≤ t}`, stated explicitly so that the
results do not depend on any particular bundled stopping-time API.

## Main results

* `lintegral_stoppedValue_min_le`: for a nonnegative right-continuous
  supermartingale `Z`, a stopping time `τ`, and a deterministic horizon `T`,
  `∫⁻ ω, ofReal (Z (min (τ ω) T) ω) ∂μ ≤ ∫⁻ ω, ofReal (Z 0 ω) ∂μ`.
  The proof approximates `min (τ ω) T` from above by dyadic discretisations
  taking finitely many values, applies discrete optional sampling on the
  finite grid, and passes to the limit by right-continuity of paths and
  Fatou's lemma (only an upper bound is claimed, so no uniform integrability
  is needed).
* `lintegral_stoppedValue_le`: the horizon-free version for a stopping time
  with values in `ℝ≥0∞`; paths with `τ = ∞` contribute `0`. Follows by
  monotone convergence along `T → ∞`, discarding the `{τ > T}` remainder by
  nonnegativity.
* `integral_stoppedValue_min_ge`: the lower-bound companion — for a
  *uniformly bounded* right-continuous supermartingale, sampling at
  `min (τ ω) T` is at least the expected value at the horizon,
  `∫ ω, Z T ω ∂μ ≤ ∫ ω, Z (min (τ ω) T) ω ∂μ`. The same dyadic scheme, with
  the discrete pair `(dyadicCeil (τ ∧ T), dyadicCeil T)` in place of
  `(0, dyadicCeil (τ ∧ T))`, and dominated convergence (the uniform bound)
  in place of Fatou on both sides of the inequality.
  `integral_stoppedValue_min_eq` combines the two directions (applied to
  `Z` and `-Z`) into the classical optional-sampling *equality* for
  uniformly bounded right-continuous martingales.
* `discount_pathwise_identity` and companions (`discounted_stronglyAdapted`,
  `discounted_integrable`, `discount_drift_nonpos`): the pathwise
  integration-by-parts identity for `e^{-ct}`-discounting, with the
  adaptedness, integrability, and drift-sign lemmas around it.
* `supermartingale_exp_discount`: the discounting construction — if
  `W t - ∫ s in 0..t, g s` is a martingale (the martingale-problem
  formulation of `g` being the generator drift of `W`), `g ≤ c • W`
  pointwise, `W` has continuous paths, and `W`, `g` are uniformly bounded,
  then `fun t ω => exp (-c * t) * W t ω` is a supermartingale. This
  packages the `e^{-ct}`-discounting step of Dynkin-formula arguments
  without any stochastic integration: pathwise integration by parts
  against `s ↦ exp (-c * s)` plus a conditional Fubini argument.
* `supermartingale_of_compensator_nonpos`: the discount-free core — a
  process whose compensated version is a martingale with nonpositive
  compensation density is a supermartingale. Per-time integrability only;
  no uniform bound and no path regularity are required.
-/

open MeasureTheory Real NNReal ENNReal

namespace OptionalSamplingRC

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℝ≥0 m0}

/-- The dyadic grid point `k / 2^n`. -/
noncomputable def dyadicTime (n k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (2 ^ n : ℝ≥0)

/-- The restriction of a continuous-time filtration to the `n`-th dyadic grid. -/
noncomputable def dyadicFiltration (n : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (dyadicTime n k)
  mono' := fun _ _ h => ℱ.mono (by exact div_le_div_of_nonneg_right (mod_cast h) (by positivity))
  le' := fun k => ℱ.le (dyadicTime n k)

lemma supermartingale_dyadic (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ) (n : ℕ) :
    Supermartingale (fun k => Z (dyadicTime n k)) (dyadicFiltration (ℱ := ℱ) n) μ := by
  refine' ⟨ _, _, _ ⟩;
  · intro k;
    exact hZ.stronglyAdapted _ |> fun h => h.mono ( ℱ.mono <| by exact div_le_div_of_nonneg_right ( Nat.cast_le.mpr <| Nat.le_refl _ ) <| by positivity );
  · intro i j hij; exact hZ.2.1 _ _ (div_le_div_of_nonneg_right (mod_cast hij) (by positivity)) ;
  · exact fun k => hZ.integrable _

/-- The index of the upper dyadic approximation to a nonnegative real:
`dyadicTime n (dyadicCeil n x)` is the smallest grid point `≥ x`. -/
noncomputable def dyadicCeil (n : ℕ) (x : ℝ≥0) : ℕ :=
  ⌈x * (2 ^ n : ℝ≥0)⌉₊

lemma dyadicCeil_time_tendsto (x : ℝ≥0) :
    Filter.Tendsto (fun n => dyadicTime n (dyadicCeil n x)) Filter.atTop (nhds x) := by

  have h_bounds : ∀ n : ℕ, x ≤ (dyadicCeil n x : ℝ≥0) / 2^n ∧ (dyadicCeil n x : ℝ≥0) / 2^n ≤ x + 1 / 2^n := by
    intro n
    simp [dyadicCeil, dyadicTime];
    rw [ le_div_iff₀, div_le_iff₀ ] <;> norm_num;
    exact ⟨ Nat.le_ceil _, by rw [ add_mul, inv_mul_cancel₀ ( by positivity ) ] ; exact_mod_cast Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ⟩;
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _ ( Filter.Eventually.of_forall fun n => h_bounds n |>.1 ) ( Filter.Eventually.of_forall fun n => h_bounds n |>.2 );
  convert tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt ( show ( 1 : ℝ≥0 ) < 2 by norm_num ) ) ) using 2 ; norm_num;
  exacts [ rfl, by rw [ add_zero ] ]

lemma dyadicCeil_time_mem_Ici (n : ℕ) (x : ℝ≥0) :
    dyadicTime n (dyadicCeil n x) ∈ Set.Ici x := by
  unfold dyadicTime dyadicCeil;
  exact Set.mem_Ici.mpr ( by rw [ le_div_iff₀ ( by positivity ) ] ; exact Nat.le_ceil _ )

lemma dyadicCeil_le_iff (n k : ℕ) (x : ℝ≥0) :
    dyadicCeil n x ≤ k ↔ x ≤ dyadicTime n k := by
  rw [dyadicCeil, Nat.ceil_le, dyadicTime, le_div_iff₀ (by positivity)]

lemma dyadicCeil_stoppingTime
    (τ : Ω → ℝ≥0) (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) (n : ℕ) :
    IsStoppingTime (dyadicFiltration (ℱ := ℱ) n)
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞)) := by
  intro k
  by_cases hT : T ≤ dyadicTime n k
  · refine MeasurableSet.univ.congr ?_
    refine (Set.eq_univ_of_forall fun ω => ?_).symm
    show (dyadicCeil n (min (τ ω) T) : ℕ∞) ≤ (k : ℕ∞)
    exact_mod_cast (dyadicCeil_le_iff n k (min (τ ω) T)).mpr ((min_le_right _ _).trans hT)
  · refine (hτ (dyadicTime n k)).congr ?_
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      show (dyadicCeil n (min (τ ω) T) : ℕ∞) ≤ (k : ℕ∞)
      exact_mod_cast (dyadicCeil_le_iff n k (min (τ ω) T)).mpr ((min_le_left _ _).trans h)
    · intro h
      have h' : (dyadicCeil n (min (τ ω) T) : ℕ∞) ≤ (k : ℕ∞) := h
      have hnk : dyadicCeil n (min (τ ω) T) ≤ k := by exact_mod_cast h'
      have := (dyadicCeil_le_iff n k (min (τ ω) T)).mp hnk
      exact ((min_le_iff.mp this).resolve_right hT)

lemma dyadicCeil_bounded (τ : Ω → ℝ≥0) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    (dyadicCeil n (min (τ ω) T) : ℕ∞) ≤ dyadicCeil n T := by
  exact_mod_cast Nat.ceil_mono ( mul_le_mul_of_nonneg_right ( min_le_right _ _ ) ( by positivity ) )

lemma integral_dyadic_stopped_le
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) (n : ℕ) :
    ∫ ω, Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω ∂μ
      ≤ ∫ ω, Z 0 ω ∂μ := by
  have h_submartingale :
      Submartingale (fun k => -Z (dyadicTime n k)) (dyadicFiltration (ℱ := ℱ) n) μ :=
    (supermartingale_dyadic Z hZ n).neg
  have h_stopping_time : IsStoppingTime (dyadicFiltration (ℱ := ℱ) n)
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞)) := dyadicCeil_stoppingTime τ hτ T n
  have h0 : IsStoppingTime (dyadicFiltration (ℱ := ℱ) n) (fun _ : Ω => ((0 : ℕ) : ℕ∞)) := by
    intro k
    refine MeasurableSet.univ.congr ?_
    refine (Set.eq_univ_of_forall fun ω => ?_).symm
    show ((0 : ℕ) : ℕ∞) ≤ (k : ℕ∞)
    exact_mod_cast Nat.zero_le k
  have key := h_submartingale.expected_stoppedValue_mono h0 h_stopping_time
    (fun ω => by
      show ((0 : ℕ) : ℕ∞) ≤ (dyadicCeil n (min (τ ω) T) : ℕ∞)
      exact_mod_cast Nat.zero_le _)
    (N := dyadicCeil n T) (fun ω => by exact_mod_cast dyadicCeil_bounded τ T n ω)
  have hL : stoppedValue (fun k => -Z (dyadicTime n k)) (fun _ : Ω => ((0 : ℕ) : ℕ∞))
      = fun ω => -Z (dyadicTime n 0) ω := rfl
  have hd0 : dyadicTime n 0 = 0 := by simp [dyadicTime]
  have hR : stoppedValue (fun k => -Z (dyadicTime n k))
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞))
      = fun ω => -Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω := rfl
  rw [hL, hR, hd0] at key
  simp only [integral_neg] at key
  exact neg_le_neg_iff.mp key

lemma integrable_dyadic_stopped
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω) μ := by
  have h_sub : Submartingale (fun k => -Z (dyadicTime n k)) (dyadicFiltration (ℱ := ℱ) n) μ :=
    (supermartingale_dyadic Z hZ n).neg
  have h_int := h_sub.integrable_stoppedValue (dyadicCeil_stoppingTime τ hτ T n)
    (N := dyadicCeil n T) (fun ω => by exact_mod_cast dyadicCeil_bounded τ T n ω)
  have hR : stoppedValue (fun k => -Z (dyadicTime n k))
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞))
      = fun ω => -Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω := rfl
  rw [hR] at h_int
  simpa using h_int.neg

lemma dyadic_stopped_tendsto
    (Z : ℝ≥0 → Ω → ℝ)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    Filter.Tendsto
      (fun n => Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω)
      Filter.atTop (nhds (Z (min (τ ω) T) ω)) := by
  refine' Filter.Tendsto.comp ( hZrc ω ( min ( τ ω ) T ) ) _;
  rw [ tendsto_nhdsWithin_iff ];
  exact ⟨ dyadicCeil_time_tendsto _, Filter.Eventually.of_forall fun n => dyadicCeil_time_mem_Ici _ _ ⟩

/-- **Optional sampling up to a deterministic horizon.** For a nonnegative
right-continuous supermartingale `Z`, a stopping time `τ` (given by its
measurability family), and a horizon `T`, the expected value of `Z` sampled
at `min (τ ω) T` is at most the expected initial value:
`∫⁻ ω, ofReal (Z (min (τ ω) T) ω) ∂μ ≤ ∫⁻ ω, ofReal (Z 0 ω) ∂μ`. -/
theorem lintegral_stoppedValue_min_le
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (hZnn : ∀ t ω, 0 ≤ Z t ω)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Z (min (τ ω) T) ω) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ := by
  set fn : ℕ → Ω → ENNReal := fun n ω =>
    ENNReal.ofReal (Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω) with hfn
  have hmeas : ∀ n, AEMeasurable (fn n) μ := fun n =>
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (integrable_dyadic_stopped Z hZ τ hτ T n).1.aemeasurable
  have hlim : ∀ ω, Filter.Tendsto (fun n => fn n ω) Filter.atTop
      (nhds (ENNReal.ofReal (Z (min (τ ω) T) ω))) := fun ω =>
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (dyadic_stopped_tendsto Z hZrc τ T ω)
  have h_each : ∀ n : ℕ, ∫⁻ ω, fn n ω ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ := by
    intro n
    rw [hfn]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_dyadic_stopped Z hZ τ hτ T n)
        (Filter.Eventually.of_forall fun ω => hZnn _ _),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hZ.integrable 0)
        (Filter.Eventually.of_forall fun ω => hZnn 0 ω)]
    exact ENNReal.ofReal_le_ofReal (integral_dyadic_stopped_le Z hZ τ hτ T n)
  calc ∫⁻ ω, ENNReal.ofReal (Z (min (τ ω) T) ω) ∂μ
      = ∫⁻ ω, Filter.liminf (fun n => fn n ω) Filter.atTop ∂μ := by
        refine lintegral_congr fun ω => ?_
        exact ((hlim ω).liminf_eq).symm
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, fn n ω ∂μ) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le' hmeas
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ :=
        Filter.liminf_le_of_frequently_le'
          (Filter.Eventually.frequently (Filter.Eventually.of_forall h_each))

lemma aemeasurable_stoppedValue_min
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) :
    AEMeasurable (fun ω => Z (min (τ ω) T) ω) μ := by
  have h_converge : ∀ ω, Filter.Tendsto (fun n => Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω) Filter.atTop (nhds (Z (min (τ ω) T) ω)) := by
    exact fun ω => dyadic_stopped_tendsto Z hZrc τ T ω;
  have h_aemeasurable : ∀ n, MeasureTheory.Integrable (fun ω => Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω) μ := by
    intro n
    have h_sub : Submartingale (fun k => -Z (dyadicTime n k)) (dyadicFiltration (ℱ := ℱ) n) μ :=
      (supermartingale_dyadic Z hZ n).neg
    have h_int := h_sub.integrable_stoppedValue (dyadicCeil_stoppingTime τ hτ T n)
      (N := dyadicCeil n T) (fun ω => by exact_mod_cast dyadicCeil_bounded τ T n ω)
    have hR : stoppedValue (fun k => -Z (dyadicTime n k))
        (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞))
        = fun ω => -Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω := rfl
    rw [hR] at h_int
    simpa using h_int.neg
  exact ( aestronglyMeasurable_of_tendsto_ae _ ( fun n => ( h_aemeasurable n |> MeasureTheory.Integrable.aestronglyMeasurable ) ) ( Filter.Eventually.of_forall h_converge ) ) |> fun h => h.aemeasurable

noncomputable def ennrealTrunc (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if τ ω ≤ (T : ℝ≥0∞) then (τ ω).toNNReal else T

lemma ennrealTrunc_le_iff (τ : Ω → ℝ≥0∞) (T t : ℝ≥0) (ht : t < T) :
    {ω | ennrealTrunc τ T ω ≤ t} = {ω | τ ω ≤ (t : ℝ≥0∞)} := by
  ext ω;
  by_cases h : τ ω ≤ T <;> simp +decide [ h, ennrealTrunc ];
  · cases h' : τ ω <;> aesop;
  · exact iff_of_false ( not_le_of_gt ht ) ( fun h' => h <| le_trans h' <| mod_cast ht.le )

lemma ennrealTrunc_eq_of_le (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (h : τ ω ≤ (T : ℝ≥0∞)) :
    ennrealTrunc τ T ω = (τ ω).toNNReal := by
  exact if_pos h

/-- **Optional sampling at an extended-valued stopping time.** For a
nonnegative right-continuous supermartingale `Z` and a stopping time `τ`
with values in `ℝ≥0∞`, the expected sampled value — with paths on which
`τ = ∞` contributing `0` — is at most the expected initial value. Obtained
from `lintegral_stoppedValue_min_le` by monotone convergence along
`T → ∞`. -/
theorem lintegral_stoppedValue_le
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (hZnn : ∀ t ω, 0 ≤ Z t ω)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ (t : ℝ≥0∞)}) :
    ∫⁻ ω, (if τ ω = ∞ then 0
           else ENNReal.ofReal (Z (τ ω).toNNReal ω)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ := by
  have h_fatou : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Z (min (ennrealTrunc τ (n + 1) ω) (n + 1)) ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ := by
    intro n;
    convert lintegral_stoppedValue_min_le Z hZ hZnn hZrc ( fun ω => ennrealTrunc τ ( n + 1 ) ω ) _ ( n + 1 ) using 1;
    intro t;
    by_cases ht : t < ( n + 1 : ℝ≥0 ) <;> simp_all +decide [ ennrealTrunc_le_iff ];
    convert MeasurableSet.mem ( MeasurableSet.univ ) using 1;
    ext ω; simp [ennrealTrunc];
    split_ifs <;> norm_cast at *;
    exact le_trans ( ENNReal.toNNReal_mono ( by aesop ) ‹τ ω ≤ ↑ ( n + 1 ) › ) ( mod_cast ht );
  have h_fatou : ∫⁻ ω, Filter.liminf (fun n : ℕ => ENNReal.ofReal (Z (min (ennrealTrunc τ (n + 1) ω) (n + 1)) ω)) Filter.atTop ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ := by
    refine' le_trans ( MeasureTheory.lintegral_liminf_le' _ ) _;
    · intro n
      have h_aemeasurable : AEMeasurable (fun ω => Z (min (ennrealTrunc τ (n + 1) ω) (n + 1)) ω) μ := by
        apply_rules [ aemeasurable_stoppedValue_min ];
        intro t
        by_cases ht : t < n + 1;
        · convert hτ t using 1;
          convert ennrealTrunc_le_iff τ ( n + 1 ) t ht using 1;
        · convert MeasurableSet.univ using 1 ; ext ω ; simp +decide [ ennrealTrunc ];
          split_ifs <;> norm_num at *;
          · exact le_trans ( ENNReal.toNNReal_mono ( by aesop ) ‹τ ω ≤ ↑n + 1› ) ( mod_cast ht );
          · exact ht
      exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable h_aemeasurable;
    · exact le_trans ( Filter.liminf_le_of_frequently_le' <| Filter.Eventually.frequently <| Filter.Eventually.of_forall h_fatou ) le_rfl;
  refine' le_trans ( MeasureTheory.lintegral_mono _ ) h_fatou;
  intro ω; by_cases hω : τ ω = ∞ <;> simp +decide [ hω ] ;
  refine' le_csSup _ _;
  · simp +zetaDelta at *;
  · simp +decide [ ennrealTrunc ];
    refine' ⟨ ⌈ ( τ ω |> ENNReal.toReal ) ⌉₊, fun n hn => _ ⟩ ; split_ifs <;> simp_all +decide [ Nat.le_ceil ];
    · rw [ min_eq_left ];
      exact_mod_cast hn.trans ( Nat.cast_le.mpr ( Nat.le_succ _ ) );
    · rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
      · norm_num [ ENNReal.toReal_add ] at * ; linarith;
      · exact hω

/-! ## Lower-bound optional sampling (bounded case)

For a *uniformly bounded* right-continuous supermartingale, sampling at the
stopped time `min (τ ω) T` is bounded *below* by the expected value at the
deterministic horizon `T`. The dyadic scheme is the one above, run on the
pair `(dyadicCeil (τ ∧ T), dyadicCeil T)` instead of
`(0, dyadicCeil (τ ∧ T))`; the passage to the limit is dominated convergence
on both sides (only an upper bound survives Fatou, so the lower bound is
where the uniform bound genuinely binds). Combining the two directions for
`Z` and `-Z` yields the classical optional-sampling equality for bounded
right-continuous martingales. -/

lemma integral_dyadic_stopped_ge
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) (n : ℕ) :
    ∫ ω, Z (dyadicTime n (dyadicCeil n T)) ω ∂μ
      ≤ ∫ ω, Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω ∂μ := by
  have h_submartingale :
      Submartingale (fun k => -Z (dyadicTime n k)) (dyadicFiltration (ℱ := ℱ) n) μ :=
    (supermartingale_dyadic Z hZ n).neg
  have h_stopping_time : IsStoppingTime (dyadicFiltration (ℱ := ℱ) n)
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞)) := dyadicCeil_stoppingTime τ hτ T n
  have h_const : IsStoppingTime (dyadicFiltration (ℱ := ℱ) n)
      (fun _ : Ω => (dyadicCeil n T : ℕ∞)) := by
    intro k
    by_cases h : (dyadicCeil n T : ℕ∞) ≤ (k : ℕ∞)
    · refine MeasurableSet.univ.congr ?_
      exact (Set.eq_univ_of_forall fun ω => h).symm
    · exact MeasurableSet.congr
        (@MeasurableSet.empty Ω ((dyadicFiltration (ℱ := ℱ) n) k))
        (Set.subset_empty_iff.mp fun ω hω => absurd hω h).symm
  have key := h_submartingale.expected_stoppedValue_mono h_stopping_time h_const
    (fun ω => dyadicCeil_bounded τ T n ω)
    (N := dyadicCeil n T) (fun ω => le_rfl)
  have hL : stoppedValue (fun k => -Z (dyadicTime n k))
      (fun ω => (dyadicCeil n (min (τ ω) T) : ℕ∞))
      = fun ω => -Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω := rfl
  have hR : stoppedValue (fun k => -Z (dyadicTime n k))
      (fun _ : Ω => (dyadicCeil n T : ℕ∞))
      = fun ω => -Z (dyadicTime n (dyadicCeil n T)) ω := rfl
  rw [hL, hR] at key
  simp only [integral_neg] at key
  exact neg_le_neg_iff.mp key

/-- **Lower-bound optional sampling up to a deterministic horizon (bounded
case).** For a uniformly bounded right-continuous supermartingale `Z`, a
stopping time `τ` (given by its measurability family), and a horizon `T`,
the expected value of `Z` sampled at `min (τ ω) T` is at least the expected
value at the horizon: `∫ ω, Z T ω ∂μ ≤ ∫ ω, Z (min (τ ω) T) ω ∂μ`.
The uniform bound is consumed by dominated convergence along the dyadic
approximations — the direction Fatou cannot serve. -/
theorem integral_stoppedValue_min_ge
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Supermartingale Z ℱ μ) (C : ℝ)
    (hZb : ∀ t ω, |Z t ω| ≤ C)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) :
    ∫ ω, Z T ω ∂μ ≤ ∫ ω, Z (min (τ ω) T) ω ∂μ := by
  have hLtend : Filter.Tendsto
      (fun n : ℕ => ∫ ω, Z (dyadicTime n (dyadicCeil n T)) ω ∂μ)
      Filter.atTop (nhds (∫ ω, Z T ω ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hZ.integrable _).aestronglyMeasurable) (integrable_const C)
      (fun n => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hZb _ ω)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := dyadic_stopped_tendsto Z hZrc (fun _ => T) T ω
    simpa using h
  have hRtend : Filter.Tendsto
      (fun n : ℕ => ∫ ω, Z (dyadicTime n (dyadicCeil n (min (τ ω) T))) ω ∂μ)
      Filter.atTop (nhds (∫ ω, Z (min (τ ω) T) ω ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (integrable_dyadic_stopped Z hZ τ hτ T n).aestronglyMeasurable)
      (integrable_const C)
      (fun n => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hZb _ ω)
      (Filter.Eventually.of_forall fun ω => dyadic_stopped_tendsto Z hZrc τ T ω)
  exact le_of_tendsto_of_tendsto' hLtend hRtend
    (fun n => integral_dyadic_stopped_ge Z hZ τ hτ T n)

/-- **Optional sampling equality for bounded right-continuous martingales.**
For a uniformly bounded right-continuous martingale `Z` and a stopping time
`τ`, sampling at `min (τ ω) T` preserves the expected initial value:
`∫ ω, Z (min (τ ω) T) ω ∂μ = ∫ ω, Z 0 ω ∂μ`. Both directions of
`integral_stoppedValue_min_ge` (applied to `Z` and `-Z`), closed by the
constancy of a martingale's expectation. -/
theorem integral_stoppedValue_min_eq
    [IsProbabilityMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ) (hZ : Martingale Z ℱ μ) (C : ℝ)
    (hZb : ∀ t ω, |Z t ω| ≤ C)
    (hZrc : ∀ ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[ℱ t] {ω | τ ω ≤ t})
    (T : ℝ≥0) :
    ∫ ω, Z (min (τ ω) T) ω ∂μ = ∫ ω, Z 0 ω ∂μ := by
  have hconst : ∫ ω, Z T ω ∂μ = ∫ ω, Z 0 ω ∂μ := by
    have h := hZ.2 0 T (by simp)
    calc ∫ ω, Z T ω ∂μ
        = ∫ ω, (μ[Z T | ℱ 0]) ω ∂μ := (integral_condExp (ℱ.le 0)).symm
      _ = ∫ ω, Z 0 ω ∂μ := integral_congr_ae h
  have hge : ∫ ω, Z T ω ∂μ ≤ ∫ ω, Z (min (τ ω) T) ω ∂μ :=
    integral_stoppedValue_min_ge Z hZ.supermartingale C hZb hZrc τ hτ T
  have hle : ∫ ω, Z (min (τ ω) T) ω ∂μ ≤ ∫ ω, Z T ω ∂μ := by
    have hneg := integral_stoppedValue_min_ge (fun t ω => -Z t ω)
      hZ.neg.supermartingale C
      (fun t ω => by rw [abs_neg]; exact hZb t ω)
      (fun ω t => (hZrc ω t).neg) τ hτ T
    simp only [integral_neg] at hneg
    linarith
  rw [← hconst]
  exact le_antisymm hle hge

lemma exp_neg_mul_absolutelyContinuous (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => Real.exp (-c * s)) a b := by
  have h_lip : LipschitzOnWith (⟨|c| * Real.exp (|c| * (|a| + |b|)), by
    positivity⟩ : NNReal) (fun s => Real.exp (-c * s)) (Set.uIcc a b) := by
    have h_deriv : ∀ s ∈ Set.uIcc a b, ‖deriv (fun s => Real.exp (-c * s)) s‖ ≤ |c| * Real.exp (|c| * (|a| + |b|)) := by
      norm_num [ mul_comm c ];
      intro s hs; rw [ mul_comm ] ; gcongr;
      cases abs_cases c <;> cases abs_cases a <;> cases abs_cases b <;> cases Set.mem_uIcc.mp hs <;> nlinarith;
    apply_rules [ Convex.lipschitzOnWith_of_nnnorm_deriv_le ];
    · exact fun x hx => DifferentiableAt.exp ( differentiableAt_id.const_mul _ );
    · exact convex_uIcc a b
  generalize_proofs at *;
  convert h_lip.absolutelyContinuousOnInterval using 1

set_option maxHeartbeats 1000000 in
lemma discount_pathwise_identity
    (W g : ℝ≥0 → ℝ) (c : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hWcont : Continuous W)
    (hgint : IntervalIntegrable (fun s : ℝ => g s.toNNReal) volume (0 : ℝ) (t : ℝ)) :
    let Y : ℝ≥0 → ℝ := fun u =>
      W u - ∫ s in (0 : ℝ)..(u : ℝ), g s.toNNReal
    Real.exp (-c * (t : ℝ)) * W t - Real.exp (-c * (r : ℝ)) * W r =
      (∫ s in (r : ℝ)..(t : ℝ),
        Real.exp (-c * s) * (g s.toNNReal - c * W s.toNNReal)) +
      (Real.exp (-c * (t : ℝ)) * Y t - Real.exp (-c * (r : ℝ)) * Y r +
        c * ∫ s in (r : ℝ)..(t : ℝ),
          Real.exp (-c * s) * Y s.toNNReal) := by
  by_cases hc : c = 0 <;> simp_all +decide [ mul_sub ];
  · rw [ ← intervalIntegral.integral_add_adjacent_intervals ];
    rw [ intervalIntegral.integral_symm ] ; ring;
    · rw [ intervalIntegrable_iff ] at *;
      simp_all +decide [ Set.uIoc ];
      exact hgint.mono_set <| Set.Ioc_subset_Ioc_right <| mod_cast hrt;
    · exact hgint;
  · rw [ intervalIntegral.integral_sub, intervalIntegral.integral_sub ];
    ·
      have h_parts : ∫ x in (r : ℝ)..t, Real.exp (-c * x) * (∫ s in (0 : ℝ)..max x 0, g s.toNNReal) = (∫ x in (r : ℝ)..t, ∫ s in (0 : ℝ)..x, Real.exp (-c * x) * g s.toNNReal) := by
        refine' intervalIntegral.integral_congr fun x hx => _;
        rw [ max_eq_left ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( r : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ), intervalIntegral.integral_const_mul ];

      have h_fubini : ∫ x in (r : ℝ)..t, ∫ s in (0 : ℝ)..x, Real.exp (-c * x) * g s.toNNReal = ∫ s in (0 : ℝ)..t, ∫ x in (max r s)..t, Real.exp (-c * x) * g s.toNNReal := by
        have h_fubini : ∫ x in (Set.Icc (r : ℝ) t), ∫ s in (Set.Icc (0 : ℝ) x), Real.exp (-c * x) * g s.toNNReal = ∫ s in (Set.Icc (0 : ℝ) t), ∫ x in (Set.Icc (max (r : ℝ) s) t), Real.exp (-c * x) * g s.toNNReal := by
          have h_fubini : ∫ x in (Set.Icc (r : ℝ) t), ∫ s in (Set.Icc (0 : ℝ) t), (if s ≤ x then Real.exp (-c * x) * g s.toNNReal else 0) = ∫ s in (Set.Icc (0 : ℝ) t), ∫ x in (Set.Icc (r : ℝ) t), (if s ≤ x then Real.exp (-c * x) * g s.toNNReal else 0) := by
            rw [ MeasureTheory.integral_integral_swap ];
            refine' MeasureTheory.Integrable.indicator _ _;
            · have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-c * x)) (Set.Icc (r : ℝ) t) ∧ MeasureTheory.IntegrableOn (fun x => g x.toNNReal) (Set.Icc (0 : ℝ) t) := by
                constructor;
                · exact Continuous.integrableOn_Icc ( by continuity );
                · rw [ intervalIntegrable_iff_integrableOn_Icc_of_le ] at hgint <;> aesop;
              exact MeasureTheory.Integrable.mul_prod h_integrable.1 h_integrable.2;
            · exact measurableSet_le measurable_snd measurable_fst;
          convert h_fubini using 1;
          · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => _;
            rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
            grind;
          · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => _;
            rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
            grind;
        convert h_fubini using 1;
        · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( mod_cast hrt ) ];
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( by linarith [ hx.1, show ( r : ℝ ) ≥ 0 by positivity ] ) ] ;
        · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( by positivity ) ];
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( max_le ( by linarith [ hx.1, show ( r : ℝ ) ≤ t from mod_cast hrt ] ) ( by linarith [ hx.2, show ( r : ℝ ) ≤ t from mod_cast hrt ] ) ) ] ;
      simp_all +decide [ intervalIntegral.integral_comp_mul_left, mul_assoc, mul_comm c ];
      rw [ show ( ∫ s in ( 0 : ℝ )..t, ( ∫ x in max ( r : ℝ ) s..t, Real.exp ( - ( x * c ) ) ) * g s.toNNReal ) = ( ∫ s in ( 0 : ℝ )..t, ( Real.exp ( - ( t * c ) ) - Real.exp ( - ( max ( r : ℝ ) s * c ) ) ) / -c * g s.toNNReal ) from ?_ ];
      · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hc ];
        rw [ show ( ∫ x in ( 0 : ℝ )..t, ( Real.exp ( - ( c * t ) ) - Real.exp ( - ( c * max ( r : ℝ ) x ) ) ) * g x.toNNReal ) = ( ∫ x in ( 0 : ℝ )..t, Real.exp ( - ( c * t ) ) * g x.toNNReal ) - ( ∫ x in ( 0 : ℝ )..t, Real.exp ( - ( c * max ( r : ℝ ) x ) ) * g x.toNNReal ) from ?_ ];
        · rw [ show ( ∫ x in ( 0 : ℝ )..t, Real.exp ( - ( c * max ( r : ℝ ) x ) ) * g x.toNNReal ) = ( ∫ x in ( 0 : ℝ )..r, Real.exp ( - ( c * r ) ) * g x.toNNReal ) + ( ∫ x in ( r : ℝ )..t, Real.exp ( - ( c * x ) ) * g x.toNNReal ) from ?_ ];
          · norm_num [ mul_assoc, mul_comm c, hc ] ; ring;
            grind;
          · rw [ ← intervalIntegral.integral_add_adjacent_intervals ];
            refine' congrArg₂ ( · + · ) _ _ <;> refine' intervalIntegral.integral_congr fun x hx => _ <;> norm_num at *;
            · aesop;
            · exact Or.inl <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( r : ℝ ) ≤ t from mod_cast hrt ] ;
            · have h_integrable : IntervalIntegrable (fun x => g x.toNNReal) volume 0 r := by
                apply_rules [ hgint.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hrt ];
              convert h_integrable.mul_continuousOn ( Continuous.continuousOn ( show Continuous fun x : ℝ => Real.exp ( - ( c * max ( r : ℝ ) x ) ) from Real.continuous_exp.comp <| Continuous.neg <| Continuous.mul continuous_const <| continuous_const.max continuous_id' ) ) using 1;
              ac_rfl;
            · have h_integrable : IntervalIntegrable (fun x => g x.toNNReal) volume (r : ℝ) t := by
                apply_rules [ hgint.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hrt ];
              convert h_integrable.mul_continuousOn ( Continuous.continuousOn ( show Continuous fun x : ℝ => Real.exp ( - ( c * max ( r : ℝ ) x ) ) from Real.continuous_exp.comp <| Continuous.neg <| Continuous.mul continuous_const <| continuous_const.max continuous_id' ) ) using 1;
              ac_rfl;
        · rw [ ← intervalIntegral.integral_sub ] ; congr ; ext ; ring;
          · exact hgint.const_mul _;
          · convert hgint.mul_continuousOn ( Continuous.continuousOn <| show Continuous fun x : ℝ => Real.exp ( - ( c * max ( r : ℝ ) x ) ) from ?_ ) using 1;
            · ac_rfl;
            · fun_prop;
      · refine' intervalIntegral.integral_congr fun s hs => _;
        rw [ intervalIntegral.integral_comp_mul_right ( fun x => Real.exp ( -x ) ) ] <;> norm_num [ hc ];
        exact Or.inl <| by ring;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      fun_prop;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' ContinuousOn.mul ( Continuous.continuousOn ( by continuity ) ) _;
      have h_cont : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, g u.toNNReal) (Set.Icc 0 (t : ℝ)) := by
        intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, hgint ] ; aesop;
        aesop;
      exact h_cont.comp ( continuousOn_id.sup continuousOn_const ) fun x hx => ⟨ by cases max_cases x 0 <;> cases Set.mem_uIcc.mp hx <;> linarith [ show ( r : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ r by exact_mod_cast hrt ], by cases max_cases x 0 <;> cases Set.mem_uIcc.mp hx <;> linarith [ show ( r : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ r by exact_mod_cast hrt ] ⟩;
    · have := hgint.mul_continuousOn ( Continuous.continuousOn ( by continuity : Continuous fun s : ℝ => Real.exp ( - ( c * s ) ) ) );
      convert this.mono_set _ using 1;
      · ac_rfl;
      · rw [ Set.uIcc_of_le ( by simpa ), Set.uIcc_of_le ( by simp ) ] ; exact Set.Icc_subset_Icc ( by simp ) le_rfl;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      fun_prop

lemma discounted_stronglyAdapted
    (W : ℝ≥0 → Ω → ℝ) (c : ℝ) (hWadp : Adapted ℱ W) :
    StronglyAdapted ℱ
      (fun (t : ℝ≥0) (ω : Ω) => Real.exp (-c * (t : ℝ)) * W t ω) := by
  intro t;
  have := hWadp t;
  exact Measurable.stronglyMeasurable ( by measurability )

lemma discounted_integrable
    [IsProbabilityMeasure μ]
    (W : ℝ≥0 → Ω → ℝ) (c C : ℝ)
    (hWadp : Adapted ℱ W) (hWb : ∀ t ω, |W t ω| ≤ C) :
    ∀ t : ℝ≥0, Integrable (fun ω => Real.exp (-c * (t : ℝ)) * W t ω) μ := by
  intro t
  have h_integrable : MeasureTheory.Integrable (fun ω => W t ω) μ := by
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exact fun _ => C;
    · norm_num;
    · exact MeasureTheory.StronglyMeasurable.aestronglyMeasurable ( hWadp t |> Measurable.stronglyMeasurable |> fun h => h.mono ( ℱ.le t ) );
    · exact Filter.Eventually.of_forall ( hWb t );
  exact h_integrable.const_mul _

lemma discount_drift_nonpos
    (W g : ℝ≥0 → ℝ) (c : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hdom : ∀ u, g u ≤ c * W u) :
    ∫ s in (r : ℝ)..(t : ℝ),
      Real.exp (-c * s) * (g s.toNNReal - c * W s.toNNReal) ≤ 0 := by
  rw [ intervalIntegral.integral_of_le ( by aesop ) ];
  exact MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun x hx => mul_nonpos_of_nonneg_of_nonpos ( Real.exp_nonneg _ ) ( sub_nonpos_of_le ( hdom _ ) )

/-! ## The exponential-discounting construction -/

lemma setIntegral_integral_swap
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν] [SFinite μ]
    (f : S → Ω → ℝ)
    (hfint : Integrable (Function.uncurry f) (@MeasureTheory.Measure.prod S Ω _ m0 ν μ))
    (A : Set Ω) (_hA : MeasurableSet A) :
    ∫ ω in A, (∫ s, f s ω ∂ν) ∂μ = ∫ s, (∫ ω in A, f s ω ∂μ) ∂ν := by
  letI : MeasurableSpace Ω := m0
  have h1 : Integrable (Function.uncurry f) (ν.prod (μ.restrict A)) := by
    rw [show ν.prod (μ.restrict A) = (ν.prod μ).restrict (Set.univ ×ˢ A) by
      rw [← Measure.prod_restrict, Measure.restrict_univ]]
    exact hfint.restrict
  exact (MeasureTheory.integral_integral_swap h1).symm

/-- Conditional Fubini: if for `ν`-a.e. `s` the conditional expectation of
`f s` given `m` is `q s • z`, then the conditional expectation of
`ω ↦ ∫ s, f s ω ∂ν` is `(∫ s, q s ∂ν) • z`. -/
lemma condExp_integral_eq_integral_mul
    [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (f : S → Ω → ℝ) (q : S → ℝ) (z : Ω → ℝ)
    (hfint : Integrable (Function.uncurry f) (@MeasureTheory.Measure.prod S Ω _ m0 ν μ))
    (hzint : Integrable z μ) (hzmeas : StronglyMeasurable[m] z)
    (hcond : ∀ᵐ s ∂ν, μ[f s | m] =ᵐ[μ] fun ω => q s * z ω) :
    μ[(fun ω => ∫ s, f s ω ∂ν) | m] =ᵐ[μ]
      fun ω => (∫ s, q s ∂ν) * z ω := by
  letI : MeasurableSpace Ω := m0
  have hfiber : ∀ᵐ s ∂ν, Integrable (f s) μ :=
    hfint.prod_right_ae (μ := ν) (ν := μ)
  have hsource : Integrable (fun ω => ∫ s, f s ω ∂ν) μ :=
    hfint.integral_prod_right (μ := ν) (ν := μ)
  have hset : ∀ A : Set Ω, MeasurableSet[m] A →
      ∫ ω in A, (∫ s, q s ∂ν) * z ω ∂μ =
        ∫ ω in A, (∫ s, f s ω ∂ν) ∂μ := by
    intro A hA
    have hfiber_set : ∀ᵐ s ∂ν,
        ∫ ω in A, q s * z ω ∂μ = ∫ ω in A, f s ω ∂μ := by
      filter_upwards [hcond, hfiber] with s hs hsint
      calc
        ∫ ω in A, q s * z ω ∂μ = ∫ ω in A, (μ[f s | m]) ω ∂μ :=
          MeasureTheory.setIntegral_congr_ae (hm A hA)
            (hs.symm.mono fun _ h _ => h)
        _ = ∫ ω in A, f s ω ∂μ :=
          MeasureTheory.setIntegral_condExp hm hsint hA
    calc
      ∫ ω in A, (∫ s, q s ∂ν) * z ω ∂μ =
          (∫ s, q s ∂ν) * ∫ ω in A, z ω ∂μ := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ s, q s * (∫ ω in A, z ω ∂μ) ∂ν := by
            rw [MeasureTheory.integral_mul_const]
      _ = ∫ s, (∫ ω in A, q s * z ω ∂μ) ∂ν := by
            congr 1
            funext s
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ s, (∫ ω in A, f s ω ∂μ) ∂ν :=
            MeasureTheory.integral_congr_ae hfiber_set
      _ = ∫ ω in A, (∫ s, f s ω ∂ν) ∂μ :=
            (setIntegral_integral_swap ν f hfint A (hm A hA)).symm
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hsource
    (fun A _ _ => (hzint.const_mul _).integrableOn)
    (fun A hA _ => hset A hA) ?_
  exact (hzmeas.const_mul _).aestronglyMeasurable

/-- Pull a real constant out of a conditional expectation (multiplication
form of `condExp_smul`). -/
lemma condExp_const_mul (a : ℝ) (f : Ω → ℝ) (m : MeasurableSpace Ω) :
    μ[(fun ω => a * f ω) | m] =ᵐ[μ] fun ω => a * (μ[f | m]) ω :=
  condExp_smul (𝕜 := ℝ) a f m

/-- Joint measurability of the compensated process `(t, ω) ↦ W t ω - ∫_0^t g`. -/
lemma compensated_joint_measurable
    (W g : ℝ≥0 → Ω → ℝ)
    (hWcont : ∀ ω, Continuous fun t => W t ω)
    (hWadp : Adapted ℱ W)
    (hgmeas : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (fun (t : ℝ≥0) (ω : Ω) =>
      W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω)) := by
  -- Apply the fact that the integral of a measurable function over a measurable set is measurable.
  have h_int_measurable : Measurable (fun (p : ℝ≥0 × Ω) => ∫ s in (0 : ℝ)..(p.1 : ℝ), g s.toNNReal p.2) := by
    have h_int_measurable : Measurable (fun (p : ℝ × Ω) => ∫ s in (Set.Icc (0 : ℝ) p.1), g s.toNNReal p.2) := by
      have h_int_measurable : Measurable (fun (p : ℝ × Ω) => ∫ s in Set.univ, (if 0 ≤ s ∧ s ≤ p.1 then g s.toNNReal p.2 else 0)) := by
        refine' MeasureTheory.StronglyMeasurable.measurable _;
        refine' MeasureTheory.StronglyMeasurable.integral_prod_right _;
        refine' Measurable.stronglyMeasurable _;
        refine' Measurable.ite _ _ measurable_const;
        · exact measurableSet_le measurable_const measurable_snd |> MeasurableSet.inter <| measurableSet_le measurable_snd <| measurable_fst.fst;
        · fun_prop;
      convert h_int_measurable using 1;
      ext p; rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ] ;
    convert h_int_measurable.comp ( show Measurable ( fun p : ℝ≥0 × Ω => ( p.1.val, p.2 ) ) from measurable_subtype_coe.comp measurable_fst |> Measurable.prodMk <| measurable_snd ) using 1;
    ext ⟨t, ω⟩; simp [intervalIntegral.integral_of_le];
    rw [ MeasureTheory.integral_Icc_eq_integral_Ioc ];
  have h_sub := Measurable.sub
    ( measurable_uncurry_of_continuous_of_measurable ( fun ω => hWcont ω )
      ( fun u => (hWadp u).mono (ℱ.le u) le_rfl ) )
    h_int_measurable
  exact h_sub

set_option maxHeartbeats 400000 in
/-- Integrability of the discounted compensated process on the strip
`Ioc r t × Ω`, jointly in `(s, ω)`. -/
lemma compensated_weighted_integrable
    [IsProbabilityMeasure μ]
    (W g : ℝ≥0 → Ω → ℝ) (c C : ℝ) (r t : ℝ≥0) (_hrt : r ≤ t)
    (hWcont : ∀ ω, Continuous fun u => W u ω)
    (hWadp : Adapted ℱ W) (hgmeas : Measurable (Function.uncurry g))
    (hWb : ∀ u ω, |W u ω| ≤ C) (hgb : ∀ u ω, |g u ω| ≤ C) :
    Integrable (Function.uncurry (fun (s : ℝ) (ω : Ω) =>
      Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)))
      ((volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ) := by
  letI : MeasurableSpace Ω := m0
  have hΩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact zero_ne_one (α := ℝ≥0∞) (by
      calc (0 : ℝ≥0∞) = μ Set.univ := by
            rw [Set.univ_eq_empty_iff.mpr hne]; simp
        _ = 1 := measure_univ)
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hWb 0 hΩ.some)
  haveI hfin : IsFiniteMeasure ((volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    infer_instance
  -- a globally measurable representative (route the time argument through ℝ≥0)
  have hYmeas := compensated_joint_measurable W g hWcont hWadp hgmeas
  have hq : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    ((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk measurable_snd
  have hGmeas : Measurable (fun p : ℝ × Ω =>
      Real.exp (-c * p.1) *
        (W p.1.toNNReal p.2 -
          ∫ v in (0 : ℝ)..((p.1.toNNReal : ℝ≥0) : ℝ), g v.toNNReal p.2)) :=
    ((Real.continuous_exp.measurable).comp (measurable_fst.const_mul (-c))).mul
      (hYmeas.comp hq)
  have hmem : ∀ᵐ p ∂((volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ),
      p.1 ∈ Set.Ioc (r : ℝ) (t : ℝ) := by
    rw [show (volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ
        = (volume.prod μ).restrict (Set.Ioc (r : ℝ) (t : ℝ) ×ˢ Set.univ) by
      rw [← Measure.prod_restrict, Measure.restrict_univ]]
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)]
      with p hp using hp.1
  have hae : (fun p : ℝ × Ω =>
        Real.exp (-c * p.1) *
          (W p.1.toNNReal p.2 -
            ∫ v in (0 : ℝ)..((p.1.toNNReal : ℝ≥0) : ℝ), g v.toNNReal p.2))
      =ᵐ[(volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ]
      Function.uncurry (fun (s : ℝ) (ω : Ω) =>
        Real.exp (-c * s) * (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) := by
    filter_upwards [hmem] with p hp
    have h0 : (0 : ℝ) ≤ p.1 := le_trans (NNReal.coe_nonneg r) hp.1.le
    simp only [Function.uncurry, Real.coe_toNNReal _ h0]
  have haesm : AEStronglyMeasurable (Function.uncurry (fun (s : ℝ) (ω : Ω) =>
      Real.exp (-c * s) * (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)))
      ((volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))).prod μ) :=
    hGmeas.aestronglyMeasurable.congr hae
  refine Integrable.mono'
    (integrable_const (Real.exp (|c| * (t : ℝ)) * (C + C * (t : ℝ)))) haesm ?_
  filter_upwards [hmem] with p hp
  have hp1 : (0 : ℝ) ≤ p.1 := le_trans (NNReal.coe_nonneg r) hp.1.le
  have h1 : -c * p.1 ≤ |c| * (t : ℝ) :=
    calc -c * p.1 ≤ |c| * p.1 := mul_le_mul_of_nonneg_right (neg_le_abs c) hp1
      _ ≤ |c| * (t : ℝ) := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg c)
  have h2 : |∫ u in (0 : ℝ)..p.1, g u.toNNReal p.2| ≤ C * (t : ℝ) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C) (f := fun u : ℝ => g u.toNNReal p.2) (a := (0 : ℝ)) (b := p.1)
      (fun x _ => by simpa [Real.norm_eq_abs] using hgb x.toNNReal p.2)
    rw [Real.norm_eq_abs] at hb
    calc |∫ u in (0 : ℝ)..p.1, g u.toNNReal p.2| ≤ C * |p.1 - 0| := hb
      _ = C * p.1 := by rw [sub_zero, abs_of_nonneg hp1]
      _ ≤ C * (t : ℝ) := mul_le_mul_of_nonneg_left hp.2 hC0
  have h3 : |W p.1.toNNReal p.2 - ∫ u in (0 : ℝ)..p.1, g u.toNNReal p.2|
      ≤ C + C * (t : ℝ) := by
    have hw := abs_le.mp (hWb p.1.toNNReal p.2)
    have hi := abs_le.mp h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ‖Function.uncurry (fun (s : ℝ) (ω : Ω) =>
        Real.exp (-c * s) * (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) p‖
      = Real.exp (-c * p.1) *
          |W p.1.toNNReal p.2 - ∫ u in (0 : ℝ)..p.1, g u.toNNReal p.2| := by
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (|c| * (t : ℝ)) * (C + C * (t : ℝ)) :=
        mul_le_mul (Real.exp_le_exp.mpr h1) h3 (abs_nonneg _) (Real.exp_nonneg _)

set_option maxHeartbeats 400000 in
/-- Conditional expectation of the time integral of the discounted
compensated process: since the compensated process is a martingale, this
collapses to the deterministic exponential weight times the value at `r`. -/
lemma condExp_compensated_weighted_integral
    [IsProbabilityMeasure μ]
    (W g : ℝ≥0 → Ω → ℝ) (c C : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hWcont : ∀ ω, Continuous fun u => W u ω)
    (hWadp : Adapted ℱ W) (hgmeas : Measurable (Function.uncurry g))
    (hWb : ∀ u ω, |W u ω| ≤ C) (hgb : ∀ u ω, |g u ω| ≤ C)
    (hmart : Martingale (fun (u : ℝ≥0) (ω : Ω) =>
      W u ω - ∫ s in (0 : ℝ)..(u : ℝ), g s.toNNReal ω) ℱ μ) :
    μ[(fun ω => ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] =ᵐ[μ]
      fun ω => (∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s)) *
        (W r ω - ∫ u in (0 : ℝ)..(r : ℝ), g u.toNNReal ω) := by
  letI : MeasurableSpace Ω := m0
  have hle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have h_integrable := compensated_weighted_integrable (μ := μ) W g c C r t hrt
    hWcont hWadp hgmeas hWb hgb
  have h_condExp_smul : ∀ᵐ s ∂(volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))),
      μ[(fun ω => Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] =ᵐ[μ]
        fun ω => Real.exp (-c * s) *
          (W r ω - ∫ u in (0 : ℝ)..(r : ℝ), g u.toNNReal ω) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans (NNReal.coe_nonneg r) hs.1.le
    have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
    have hsr : r ≤ s.toNNReal := by
      have h : (r : ℝ) ≤ ((s.toNNReal : ℝ≥0) : ℝ) := by rw [hcoe]; exact hs.1.le
      exact_mod_cast h
    have hYcond : μ[(fun ω => W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω) | ℱ r]
        =ᵐ[μ] fun ω => W r ω - ∫ u in (0 : ℝ)..(r : ℝ), g u.toNNReal ω := by
      simpa only [hcoe] using hmart.2 r s.toNNReal hsr
    refine (condExp_const_mul (Real.exp (-c * s)) _ (ℱ r)).trans ?_
    filter_upwards [hYcond] with ω hω
    rw [hω]
  have key := condExp_integral_eq_integral_mul (μ := μ)
    (ν := volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))) (ℱ r) (ℱ.le r)
    (fun s ω => Real.exp (-c * s) * (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω))
    (fun s => Real.exp (-c * s))
    (fun ω => W r ω - ∫ u in (0 : ℝ)..(r : ℝ), g u.toNNReal ω)
    h_integrable (hmart.integrable r) (hmart.stronglyAdapted r) h_condExp_smul
  have h1 : (fun ω => ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω))
      = fun ω => ∫ s, Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)
          ∂(volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))) := by
    funext ω
    exact intervalIntegral.integral_of_le hle
  have h2 : (∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s))
      = ∫ s, Real.exp (-c * s) ∂(volume.restrict (Set.Ioc (r : ℝ) (t : ℝ))) :=
    intervalIntegral.integral_of_le hle
  rw [h1, h2]
  exact key

set_option maxHeartbeats 400000 in
/-- The martingale group in the discounting identity has vanishing
conditional expectation given `ℱ r`. -/
lemma condExp_discount_martingale_group_zero
    [IsProbabilityMeasure μ]
    (W g : ℝ≥0 → Ω → ℝ) (c C : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hWcont : ∀ ω, Continuous fun u => W u ω)
    (hWadp : Adapted ℱ W) (hgmeas : Measurable (Function.uncurry g))
    (hWb : ∀ u ω, |W u ω| ≤ C) (hgb : ∀ u ω, |g u ω| ≤ C)
    (hmart : Martingale (fun (u : ℝ≥0) (ω : Ω) =>
      W u ω - ∫ s in (0 : ℝ)..(u : ℝ), g s.toNNReal ω) ℱ μ) :
    μ[(fun ω =>
        Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
        Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
        c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] =ᵐ[μ] 0 := by
  letI : MeasurableSpace Ω := m0
  have hle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have hint_t : Integrable (fun ω => W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) μ :=
    hmart.integrable t
  have hint_r : Integrable (fun ω => W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) μ :=
    hmart.integrable r
  have hprod := compensated_weighted_integrable (μ := μ) W g c C r t hrt
    hWcont hWadp hgmeas hWb hgb
  have hint_I : Integrable (fun ω => ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
      (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) μ := by
    refine (hprod.integral_prod_right (μ := volume.restrict (Set.Ioc (r : ℝ) (t : ℝ)))
      (ν := μ)).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (intervalIntegral.integral_of_le hle).symm
  have hA : μ[(fun ω => Real.exp (-c * (t : ℝ)) *
      (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω)) | ℱ r] =ᵐ[μ]
      fun ω => Real.exp (-c * (t : ℝ)) *
        (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) := by
    refine (condExp_const_mul (Real.exp (-c * (t : ℝ))) _ (ℱ r)).trans ?_
    filter_upwards [hmart.2 r t hrt] with ω hω
    rw [hω]
  have hB : μ[(fun ω => Real.exp (-c * (r : ℝ)) *
      (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω)) | ℱ r]
      = fun ω => Real.exp (-c * (r : ℝ)) *
        (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) :=
    condExp_of_stronglyMeasurable (ℱ.le r)
      (StronglyMeasurable.const_mul (hmart.stronglyAdapted r) _) (hint_r.const_mul _)
  have hI := condExp_compensated_weighted_integral (μ := μ) W g c C r t hrt
    hWcont hWadp hgmeas hWb hgb hmart
  have hcI : μ[(fun ω => c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
      (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] =ᵐ[μ]
      fun ω => c * ((∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s)) *
        (W r ω - ∫ u in (0 : ℝ)..(r : ℝ), g u.toNNReal ω)) := by
    refine (condExp_const_mul c _ (ℱ r)).trans ?_
    filter_upwards [hI] with ω hω
    rw [hω]
  have hftc : Real.exp (-c * (t : ℝ)) - Real.exp (-c * (r : ℝ)) +
      c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) = 0 := by
    have hd : ∀ x ∈ Set.uIcc (r : ℝ) (t : ℝ),
        HasDerivAt (fun s => -Real.exp (-c * s)) (c * Real.exp (-c * x)) x := by
      intro x _
      have hlin : HasDerivAt (fun s : ℝ => -c * s) (-c) x := by
        simpa using (hasDerivAt_id x).const_mul (-c)
      have hrw : c * Real.exp (-c * x) = -(Real.exp (-c * x) * -c) := by ring
      rw [hrw]
      exact (hlin.exp).neg
    have hci : IntervalIntegrable (fun x => c * Real.exp (-c * x)) volume (r : ℝ) (t : ℝ) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hci
    rw [intervalIntegral.integral_const_mul] at hsub
    have hsub' : c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s)
        = -Real.exp (-c * (t : ℝ)) - -Real.exp (-c * (r : ℝ)) := hsub
    linarith [hsub']
  have hsplit1 : μ[(fun ω =>
      Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
      Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
      c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] =ᵐ[μ]
      μ[(fun ω => Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
        Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω)) | ℱ r] +
      μ[(fun ω => c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] :=
    condExp_add ((hint_t.const_mul _).sub (hint_r.const_mul _)) (hint_I.const_mul _) _
  have hsplit2 : μ[(fun ω => Real.exp (-c * (t : ℝ)) *
      (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
      Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω)) | ℱ r] =ᵐ[μ]
      μ[(fun ω => Real.exp (-c * (t : ℝ)) *
        (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω)) | ℱ r] -
      μ[(fun ω => Real.exp (-c * (r : ℝ)) *
        (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω)) | ℱ r] :=
    condExp_sub (hint_t.const_mul _) (hint_r.const_mul _) _
  filter_upwards [hsplit1, hsplit2, hA, hcI] with ω h1 h2 h3 h4
  have hBω : μ[(fun ω => Real.exp (-c * (r : ℝ)) *
      (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω)) | ℱ r] ω
      = Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) := by
    rw [hB]
  rw [h1]
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [h2]
  simp only [Pi.sub_apply]
  rw [h3, h4, hBω]
  linear_combination (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) * hftc

set_option maxHeartbeats 400000 in
/-- Integrability of the drift contribution to the discounting identity. -/
lemma discount_drift_integrable
    [IsProbabilityMeasure μ]
    (W g : ℝ≥0 → Ω → ℝ) (c C : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hWcont : ∀ ω, Continuous fun u => W u ω)
    (hWadp : Adapted ℱ W) (hgmeas : Measurable (Function.uncurry g))
    (hWb : ∀ u ω, |W u ω| ≤ C) (hgb : ∀ u ω, |g u ω| ≤ C) :
    Integrable (fun ω => ∫ s in (r : ℝ)..(t : ℝ),
      Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) μ := by
  letI : MeasurableSpace Ω := m0
  have hle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have hq : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    ((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk measurable_snd
  have hWuc : Measurable (Function.uncurry W) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hWcont ω)
      (fun u => (hWadp u).mono (ℱ.le u) le_rfl)
  have hFmeas : Measurable (fun p : ℝ × Ω =>
      Real.exp (-c * p.1) * (g p.1.toNNReal p.2 - c * W p.1.toNNReal p.2)) :=
    ((Real.continuous_exp.measurable).comp (measurable_fst.const_mul (-c))).mul
      ((hgmeas.comp hq).sub ((hWuc.comp hq).const_mul c))
  have hmeas1 : StronglyMeasurable (fun ω => ∫ s, Real.exp (-c * s) *
      (g s.toNNReal ω - c * W s.toNNReal ω)
      ∂(volume.restrict (Set.Ioc (r : ℝ) (t : ℝ)))) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (ω : Ω) (s : ℝ) => Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω))
      ((hFmeas.comp measurable_swap).stronglyMeasurable)
  refine Integrable.mono'
    (integrable_const (Real.exp (|c| * (t : ℝ)) * (C + |c| * C) * ((t : ℝ) - (r : ℝ)))) ?_ ?_
  · refine hmeas1.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (intervalIntegral.integral_of_le hle).symm
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := Real.exp (|c| * (t : ℝ)) * (C + |c| * C))
      (f := fun s : ℝ => Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω))
      (a := (r : ℝ)) (b := (t : ℝ)) ?_
    · rw [Real.norm_eq_abs] at hb
      calc ‖∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
            (g s.toNNReal ω - c * W s.toNNReal ω)‖
          = |∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
            (g s.toNNReal ω - c * W s.toNNReal ω)| := Real.norm_eq_abs _
        _ ≤ Real.exp (|c| * (t : ℝ)) * (C + |c| * C) * |(t : ℝ) - (r : ℝ)| := hb
        _ = Real.exp (|c| * (t : ℝ)) * (C + |c| * C) * ((t : ℝ) - (r : ℝ)) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    · intro x hx
      rw [Set.uIoc_of_le hle] at hx
      have hx0 : (0 : ℝ) ≤ x := le_trans (NNReal.coe_nonneg r) hx.1.le
      have h1 : -c * x ≤ |c| * (t : ℝ) :=
        calc -c * x ≤ |c| * x := mul_le_mul_of_nonneg_right (neg_le_abs c) hx0
          _ ≤ |c| * (t : ℝ) := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg c)
      have h2 : |g x.toNNReal ω - c * W x.toNNReal ω| ≤ C + |c| * C := by
        have hg1 := abs_le.mp (hgb x.toNNReal ω)
        have hcw : |c * W x.toNNReal ω| ≤ |c| * C := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hWb x.toNNReal ω) (abs_nonneg c)
        have hcw' := abs_le.mp hcw
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      calc ‖Real.exp (-c * x) * (g x.toNNReal ω - c * W x.toNNReal ω)‖
          = Real.exp (-c * x) * |g x.toNNReal ω - c * W x.toNNReal ω| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (|c| * (t : ℝ)) * (C + |c| * C) :=
            mul_le_mul (Real.exp_le_exp.mpr h1) h2 (abs_nonneg _) (Real.exp_nonneg _)

set_option maxHeartbeats 400000 in
/-- Conditional-expectation inequality for the discounted increment. -/
lemma condExp_discount_increment_nonpos
    [IsProbabilityMeasure μ]
    (W g : ℝ≥0 → Ω → ℝ) (c C : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (hWadp : Adapted ℱ W) (hWcont : ∀ ω, Continuous fun u => W u ω)
    (hWb : ∀ u ω, |W u ω| ≤ C)
    (hgmeas : Measurable (Function.uncurry g)) (hgb : ∀ u ω, |g u ω| ≤ C)
    (hmart : Martingale (fun (u : ℝ≥0) (ω : Ω) =>
      W u ω - ∫ s in (0 : ℝ)..(u : ℝ), g s.toNNReal ω) ℱ μ)
    (hdom : ∀ u ω, g u ω ≤ c * W u ω) :
    μ[(fun ω => Real.exp (-c * (t : ℝ)) * W t ω -
      Real.exp (-c * (r : ℝ)) * W r ω) | ℱ r] ≤ᵐ[μ] 0 := by
  letI : MeasurableSpace Ω := m0
  have hle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have hDint : Integrable (fun ω => ∫ s in (r : ℝ)..(t : ℝ),
      Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) μ :=
    discount_drift_integrable W g c C r t hrt hWcont hWadp hgmeas hWb hgb
  have hMcond := condExp_discount_martingale_group_zero (μ := μ) W g c C r t hrt
    hWcont hWadp hgmeas hWb hgb hmart
  have hprod := compensated_weighted_integrable (μ := μ) W g c C r t hrt
    hWcont hWadp hgmeas hWb hgb
  have hint : Integrable (fun ω => ∫ s in (r : ℝ)..(t : ℝ),
      Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) μ := by
    refine (hprod.integral_prod_right (μ := volume.restrict (Set.Ioc (r : ℝ) (t : ℝ)))
      (ν := μ)).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (intervalIntegral.integral_of_le hle).symm
  have hMint : Integrable (fun ω =>
      Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
      Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
      c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
        (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) μ :=
    (((hmart.integrable t).const_mul _).sub ((hmart.integrable r).const_mul _)).add
      (hint.const_mul _)
  have hgint : ∀ ω, IntervalIntegrable (fun s : ℝ => g s.toNNReal ω)
      volume (0 : ℝ) (t : ℝ) := by
    intro ω
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (hgmeas.comp
        (continuous_real_toNNReal.measurable.prodMk measurable_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun s => by
        simpa [Real.norm_eq_abs] using hgb s.toNNReal ω
  have heq : (fun ω => Real.exp (-c * (t : ℝ)) * W t ω -
      Real.exp (-c * (r : ℝ)) * W r ω) = fun ω =>
      (∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) +
      (Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
        Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
        c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) := by
    funext ω
    have hyi : (∫ x in (r : ℝ)..(t : ℝ), Real.exp (-c * x) *
        (W x.toNNReal ω - ∫ u in (0 : ℝ)..x, g u.toNNReal ω)) =
        ∫ x in (r : ℝ)..(t : ℝ), Real.exp (-c * x) *
          (W x.toNNReal ω - ∫ u in (0 : ℝ)..((x.toNNReal : ℝ≥0) : ℝ), g u.toNNReal ω) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx0 : (0 : ℝ) ≤ x := by
        rcases Set.mem_uIcc.mp hx with h | h
        · linarith [NNReal.coe_nonneg r, h.1]
        · linarith [NNReal.coe_nonneg t, h.1]
      rw [Real.coe_toNNReal _ hx0]
    rw [hyi]
    exact discount_pathwise_identity (fun u => W u ω) (fun u => g u ω) c r t hrt
      (hWcont ω) (hgint ω)
  have hDcond : μ[(fun ω => ∫ s in (r : ℝ)..(t : ℝ),
      Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) | ℱ r] ≤ᵐ[μ] 0 :=
    condExp_nonpos (Filter.Eventually.of_forall fun ω =>
      discount_drift_nonpos (fun u => W u ω) (fun u => g u ω) c r t hrt
        (fun u => hdom u ω))
  have hsum : μ[(fun ω =>
      (∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) +
      (Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
        Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
        c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω))) | ℱ r] =ᵐ[μ]
      μ[(fun ω => ∫ s in (r : ℝ)..(t : ℝ),
        Real.exp (-c * s) * (g s.toNNReal ω - c * W s.toNNReal ω)) | ℱ r] +
      μ[(fun ω =>
        Real.exp (-c * (t : ℝ)) * (W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) -
        Real.exp (-c * (r : ℝ)) * (W r ω - ∫ s in (0 : ℝ)..(r : ℝ), g s.toNNReal ω) +
        c * ∫ s in (r : ℝ)..(t : ℝ), Real.exp (-c * s) *
          (W s.toNNReal ω - ∫ u in (0 : ℝ)..s, g u.toNNReal ω)) | ℱ r] :=
    condExp_add hDint hMint _
  rw [heq]
  filter_upwards [hsum, hDcond, hMcond] with ω hs hd hm
  rw [hs]
  simp only [Pi.add_apply, Pi.zero_apply] at hd hm ⊢
  linarith [hd, hm]

/-- **Exponential discounting of a drift-dominated process.** Suppose
`W : ℝ≥0 → Ω → ℝ` is adapted with continuous paths, `g : ℝ≥0 → Ω → ℝ` is
jointly measurable, both are uniformly bounded, the compensated process
`fun t ω => W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω` is a
martingale (the martingale-problem formulation of `g` being the generator
drift of `W`), and `g t ω ≤ c * W t ω` pointwise. Then

`fun t ω => Real.exp (-c * t) * W t ω` is a supermartingale.

This is the discounting step of Dynkin-formula arguments, carried out with
pathwise Riemann–Stieltjes integration by parts against the `C¹` function
`s ↦ exp (-c * s)` and a conditional Fubini argument — no stochastic
integral is involved. -/
theorem supermartingale_exp_discount
    [IsProbabilityMeasure μ]
    (W : ℝ≥0 → Ω → ℝ) (g : ℝ≥0 → Ω → ℝ) (c : ℝ) (C : ℝ)
    (hWadp : Adapted ℱ W)
    (hWcont : ∀ ω, Continuous fun t => W t ω)
    (hWb : ∀ t ω, |W t ω| ≤ C)
    (hgmeas : Measurable (Function.uncurry g))
    (hgb : ∀ t ω, |g t ω| ≤ C)
    (hmart : Martingale
      (fun (t : ℝ≥0) (ω : Ω) =>
        W t ω - ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω) ℱ μ)
    (hdom : ∀ t ω, g t ω ≤ c * W t ω) :
    Supermartingale
      (fun (t : ℝ≥0) (ω : Ω) => Real.exp (-c * (t : ℝ)) * W t ω) ℱ μ := by
  refine ⟨discounted_stronglyAdapted W c hWadp, ?_,
    discounted_integrable W c C hWadp hWb⟩
  intro r t hrt
  have hinc := condExp_discount_increment_nonpos W g c C r t hrt hWadp
    hWcont hWb hgmeas hgb hmart hdom
  have htint := discounted_integrable (μ := μ) W c C hWadp hWb t
  have hrint := discounted_integrable (μ := μ) W c C hWadp hWb r
  have hsub : μ[(fun ω => Real.exp (-c * (t : ℝ)) * W t ω -
      Real.exp (-c * (r : ℝ)) * W r ω) | ℱ r] =ᵐ[μ]
      μ[(fun ω => Real.exp (-c * (t : ℝ)) * W t ω) | ℱ r] -
      μ[(fun ω => Real.exp (-c * (r : ℝ)) * W r ω) | ℱ r] :=
    condExp_sub htint hrint _
  have hrcond : μ[(fun ω => Real.exp (-c * (r : ℝ)) * W r ω) | ℱ r]
      = fun ω => Real.exp (-c * (r : ℝ)) * W r ω :=
    condExp_of_stronglyMeasurable (ℱ.le r)
      (StronglyMeasurable.const_mul ((hWadp r).stronglyMeasurable) _) hrint
  filter_upwards [hinc, hsub] with ω hi hs
  rw [hs] at hi
  simp only [Pi.sub_apply, Pi.zero_apply, hrcond] at hi
  show μ[(fun ω => Real.exp (-c * (t : ℝ)) * W t ω) | ℱ r] ω ≤
    Real.exp (-c * (r : ℝ)) * W r ω
  linarith [hi]

/-! ## Supermartingales from martingale-problem compensation -/

/-- **Supermartingale from a nonpositive compensation density.** If the
compensated process `fun t ω => W t ω - ∫ s in 0..t, g s ω` is a martingale,
the compensator `fun t ω => ∫ s in 0..t, g s ω` is adapted, `W` is integrable
at each time, and the density `g` is pathwise interval-integrable and
nonpositive at nonnegative times, then `W` is a supermartingale.

This is the discount-free core of Dynkin-formula arguments: the generator
drift enters as the density of the compensator, and the drift row's sign is
consumed exactly here. In contrast to `supermartingale_exp_discount`, no
uniform bound and no path regularity are required, so this form also serves
processes carrying an unbounded deterministic weight. -/
theorem supermartingale_of_compensator_nonpos
    [IsProbabilityMeasure μ]
    (W : ℝ≥0 → Ω → ℝ) (g : ℝ → Ω → ℝ)
    (hmart : Martingale
      (fun (t : ℝ≥0) (ω : Ω) => W t ω - ∫ s in (0:ℝ)..(t:ℝ), g s ω) ℱ μ)
    (hGadp : Adapted ℱ
      (fun (t : ℝ≥0) (ω : Ω) => ∫ s in (0:ℝ)..(t:ℝ), g s ω))
    (hWint : ∀ t : ℝ≥0, Integrable (W t) μ)
    (hgint : ∀ ω, ∀ t : ℝ, IntervalIntegrable (fun s => g s ω) volume 0 t)
    (hg0 : ∀ ω, ∀ s : ℝ, 0 ≤ s → g s ω ≤ 0) :
    Supermartingale W ℱ μ := by
  have hW_eq : ∀ t : ℝ≥0, W t = fun ω =>
      (W t ω - ∫ s in (0:ℝ)..(t:ℝ), g s ω) + ∫ s in (0:ℝ)..(t:ℝ), g s ω := by
    intro t; funext ω; ring
  have hGint : ∀ t : ℝ≥0,
      Integrable (fun ω => ∫ s in (0:ℝ)..(t:ℝ), g s ω) μ := by
    intro t
    have h : (fun ω => ∫ s in (0:ℝ)..(t:ℝ), g s ω) = fun ω =>
        W t ω - (W t ω - ∫ s in (0:ℝ)..(t:ℝ), g s ω) := by
      funext ω; ring
    rw [h]
    exact (hWint t).sub (hmart.integrable t)
  refine ⟨fun t => ?_, fun r t hrt => ?_, hWint⟩
  · rw [hW_eq t]
    exact (hmart.stronglyAdapted t).add (hGadp t).stronglyMeasurable
  · have hrt' : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
    have hGle : ∀ ω, (∫ s in (0:ℝ)..(t:ℝ), g s ω)
        ≤ ∫ s in (0:ℝ)..(r:ℝ), g s ω := by
      intro ω
      have hint_rt : IntervalIntegrable (fun s => g s ω) volume (r:ℝ) (t:ℝ) :=
        (hgint ω t).mono_set (by
          rw [Set.uIcc_of_le hrt', Set.uIcc_of_le (NNReal.coe_nonneg t)]
          exact Set.Icc_subset_Icc (NNReal.coe_nonneg r) le_rfl)
      have hsplit :
          (∫ s in (0:ℝ)..(r:ℝ), g s ω) + ∫ s in (r:ℝ)..(t:ℝ), g s ω
            = ∫ s in (0:ℝ)..(t:ℝ), g s ω :=
        intervalIntegral.integral_add_adjacent_intervals (hgint ω r) hint_rt
      have htail : (∫ s in (r:ℝ)..(t:ℝ), g s ω) ≤ 0 := by
        rw [intervalIntegral.integral_of_le hrt']
        exact MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun s hs =>
          hg0 ω s (le_of_lt (lt_of_le_of_lt (NNReal.coe_nonneg r) hs.1))
      linarith
    have h1 : μ[W t | ℱ r] =ᵐ[μ]
        μ[(fun ω => W t ω - ∫ s in (0:ℝ)..(t:ℝ), g s ω) | ℱ r]
          + μ[(fun ω => ∫ s in (0:ℝ)..(t:ℝ), g s ω) | ℱ r] := by
      conv_lhs => rw [hW_eq t]
      exact condExp_add (hmart.integrable t) (hGint t) _
    have h2 : μ[(fun ω => W t ω - ∫ s in (0:ℝ)..(t:ℝ), g s ω) | ℱ r] =ᵐ[μ]
        fun ω => W r ω - ∫ s in (0:ℝ)..(r:ℝ), g s ω := hmart.2 r t hrt
    have h3 : μ[(fun ω => ∫ s in (0:ℝ)..(t:ℝ), g s ω) | ℱ r] ≤ᵐ[μ]
        μ[(fun ω => ∫ s in (0:ℝ)..(r:ℝ), g s ω) | ℱ r] :=
      condExp_mono (hGint t) (hGint r) (Filter.Eventually.of_forall hGle)
    have h4 : μ[(fun ω => ∫ s in (0:ℝ)..(r:ℝ), g s ω) | ℱ r]
        = fun ω => ∫ s in (0:ℝ)..(r:ℝ), g s ω :=
      condExp_of_stronglyMeasurable (ℱ.le r)
        (hGadp r).stronglyMeasurable (hGint r)
    filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
    have hω4 := congrFun h4 ω
    simp only [Pi.add_apply] at hω1
    show μ[W t | ℱ r] ω ≤ W r ω
    linarith [hω1, hω2, hω3, hω4]


end OptionalSamplingRC
