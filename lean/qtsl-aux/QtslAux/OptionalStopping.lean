import QtslAux.Battery

/-! # Submartingale reach lower bounds for Markov chains

This module complements the supermartingale (avoidance) bounds of
`QtslAux.Battery` with *lower* bounds on reachability probabilities,
obtained by optional stopping of submartingale certificates.

Throughout, `K` is a Markov kernel on a state space `S`,
`Battery.pathMeasure K x` is the law of the chain started at `x` on the path
space `ℕ → S` (the Ionescu-Tulcea trajectory measure), and `Battery.stopped f A`
is the running value of `f` along the chain, frozen at the first entry
into `A`.

Main results:

* `submartingale_stopped`: if `0 ≤ f ≤ C` is measurable and subharmonic off `A`
  (`f y ≤ ∫ f dK y` for `y ∉ A`), then the process `f` stopped at `A` is a
  submartingale; proved by reflecting the supermartingale statement for
  `C - f`.
* `measure_survive_le_pow`: geometric absorption — if from every state outside
  `E` the next step lands outside `E` with probability at most `β`, then the
  probability of avoiding `E` through time `n` is at most `β ^ n`.
* `measure_reach_ge`: the reach lower bound. For a certificate `W ≤ 1` that is
  subharmonic outside `E` and nonpositive on `E \ A`, under geometric
  absorption into `E` at rate `β < 1`, the probability of ever reaching `A`
  from `x` is at least `W x`. The proof stops `max W 0` at `E`, compares the
  stopped submartingale at time `n` with the indicators of the events
  "reached `A` by `n`" and "survived outside `E` to `n`", and lets `n → ∞`.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function

namespace Qtsl.OptionalStopping

open Qtsl

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
/-- Stopping commutes with the reflection `f ↦ C - f`: the process `C - f`
stopped at `A` is `C` minus the process `f` stopped at `A`. -/
lemma stopped_const_sub (C : ℝ) (f : S → ℝ) (A : Set S) :
    ∀ (n : ℕ) (ω : ℕ → S),
      Battery.stopped (fun y => C - f y) A n ω = C - Battery.stopped f A n ω := by
  intro n
  induction n with
  | zero => intro ω; rfl
  | succ n ih =>
    intro ω
    by_cases h : ω ∈ Battery.survive A n
    · rw [Battery.stopped_succ_of_survive h, Battery.stopped_succ_of_survive h]
    · rw [Battery.stopped_succ_of_not_survive h, Battery.stopped_succ_of_not_survive h,
        ih]

omit [MeasurableSpace S] in
/-- If `f ≤ 0` on `E \ A`, then along a path that has visited `E` by time `n`
while avoiding `A` throughout, the process `f` stopped at `E` is nonpositive at
time `n`. -/
lemma stopped_nonpos_of_first_exit {f : S → ℝ} {A E : Set S}
    (hsafe : ∀ y ∈ E, y ∉ A → f y ≤ 0) :
    ∀ (n : ℕ) (ω : ℕ → S), (∀ k ≤ n, ω k ∉ A) → (∃ k ≤ n, ω k ∈ E) →
      Battery.stopped f E n ω ≤ 0 := by
  intro n
  induction n with
  | zero =>
    rintro ω hnA ⟨k, hk, hkE⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact hsafe _ hkE (hnA 0 le_rfl)
  | succ n ih =>
    rintro ω hnA ⟨k, hk, hkE⟩
    by_cases h : ω ∈ Battery.survive E n
    · rw [Battery.stopped_succ_of_survive h]
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
      · exact absurd hkE (h k (Nat.lt_succ_iff.1 hlt))
      · exact hsafe _ hkE (hnA (n + 1) le_rfl)
    · rw [Battery.stopped_succ_of_not_survive h]
      rw [Battery.mem_survive] at h
      push Not at h
      obtain ⟨j, hjn, hjE⟩ := h
      exact ih ω (fun k hk => hnA k (hk.trans n.le_succ)) ⟨j, hjn, hjE⟩

variable {K : Kernel S S} [IsMarkovKernel K]

/-- If `0 ≤ f ≤ C` is measurable and subharmonic off `A`
(`f y ≤ ∫ f dK y` for `y ∉ A`), then `f` stopped at the first entry into `A` is
a submartingale of the canonical filtration under the path measure. -/
theorem submartingale_stopped {f : S → ℝ} {A : Set S} {C : ℝ}
    (hA : MeasurableSet A) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hdrift : ∀ y, y ∉ A → f y ≤ ∫ z, f z ∂K y) (x : S) :
    Submartingale (Battery.stopped f A) (Filtration.piLE (X := fun _ : ℕ => S))
      (Battery.pathMeasure K x) := by
  have hfint : ∀ y : S, Integrable f (K y) := fun y =>
    (integrable_const C).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hfC z)
  have hsup := Battery.supermartingale_stopped (K := K)
    (f := fun y => C - f y) (A := A) (C := C) hA (measurable_const.sub hf)
    (fun y => sub_nonneg.2 (hfC y))
    (fun y => by have := hf0 y; linarith)
    (fun y hy => by
      rw [integral_sub (integrable_const C) (hfint y)]
      have hconst : ∫ _z, C ∂K y = C := by simp [measureReal_def]
      have := hdrift y hy
      rw [hconst]
      linarith) x
  have heq : Battery.stopped (fun y => C - f y) A
      = fun n ω => C - Battery.stopped f A n ω := by
    funext n ω; exact stopped_const_sub C f A n ω
  rw [heq] at hsup
  have hfinal := hsup.neg.add_martingale
    (martingale_const (Filtration.piLE (X := fun _ : ℕ => S)) (Battery.pathMeasure K x) C)
  have heq2 : (-(fun n ω => C - Battery.stopped f A n ω)
      + fun (_ : ℕ) (_ : ℕ → S) => C) = Battery.stopped f A := by
    funext n ω
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rwa [heq2] at hfinal

/-- Integrating a function of the initial coordinate against the path measure
evaluates it at the start state. -/
lemma integral_coord_zero {g : S → ℝ} (hg : Measurable g) (x : S) :
    ∫ ω, g (ω 0) ∂Battery.pathMeasure K x = g x := by
  have hmeas : AEStronglyMeasurable (fun ω : ℕ → S => g (ω 0))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := Battery.mchain K) 0 (fun _ => x)) :=
    (hg.comp (measurable_pi_apply 0)).aestronglyMeasurable
  rw [show Battery.pathMeasure K x
      = Kernel.traj (X := fun _ : ℕ => S) (κ := Battery.mchain K) 0 (fun _ => x) from rfl]
  rw [Kernel.integral_traj _ hmeas]
  have hval : ∀ y : ℕ → S,
      g (updateFinset y (Iic 0) (fun _ => x) 0) = g x := fun y => by
    have h0 : updateFinset y (Iic 0) (fun _ => x) 0 = x := by
      simp [updateFinset, mem_Iic]
    rw [h0]
  rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const]
  simp [measureReal_def]

/-- Starting inside `A`, the chain reaches `A` with probability one. -/
lemma measure_reach_of_mem {A : Set S} (hA : MeasurableSet A) {x : S} (hx : x ∈ A) :
    Battery.pathMeasure K x {ω | ∃ n, ω n ∈ A} = 1 := by
  refine le_antisymm prob_le_one ?_
  have hpre : ((fun ω : ℕ → S => ω 0) ⁻¹' A : Set (ℕ → S)) ⊆ {ω | ∃ n, ω n ∈ A} :=
    fun ω h => ⟨0, h⟩
  refine le_trans ?_ (measure_mono hpre)
  have hind := integral_coord_zero (K := K)
    (g := A.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hA) x
  have hcomp : (fun ω : ℕ → S => A.indicator (fun _ => (1 : ℝ)) (ω 0))
      = ((fun ω : ℕ → S => ω 0) ⁻¹' A).indicator fun _ => (1 : ℝ) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_preimage]
  rw [hcomp, integral_indicator_const (1 : ℝ) ((measurable_pi_apply 0) hA),
    Set.indicator_of_mem hx, smul_eq_mul, mul_one, measureReal_def] at hind
  rw [ENNReal.toReal_eq_one_iff] at hind
  exact hind.ge

/-- Geometric absorption: if from every state outside `E` the kernel assigns
mass at most `β` to the complement of `E`, then the probability of avoiding `E`
through time `n` is at most `β ^ n`. -/
lemma measure_survive_le_pow {E : Set S} {β : ℝ}
    (hE : MeasurableSet E) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hesc : ∀ y, y ∉ E → K y Eᶜ ≤ ENNReal.ofReal β)
    {x : S} (hx : x ∉ E) (n : ℕ) :
    Battery.pathMeasure K x (Battery.survive E n) ≤ ENNReal.ofReal (β ^ n) := by
  set c : S → ℝ := E.piecewise (fun _ => (0 : ℝ)) (fun _ => 1) with hc
  have hcmeas : Measurable c := Measurable.piecewise hE measurable_const measurable_const
  have hc_of_mem : ∀ y ∈ E, c y = 0 := fun y hy => Set.piecewise_eq_of_mem _ _ _ hy
  have hc_of_notMem : ∀ y, y ∉ E → c y = 1 := fun y hy =>
    Set.piecewise_eq_of_notMem _ _ _ hy
  have hc01 : ∀ y, 0 ≤ c y ∧ c y ≤ 1 := by
    intro y
    by_cases hy : y ∈ E
    · rw [hc_of_mem y hy]; exact ⟨le_rfl, zero_le_one⟩
    · rw [hc_of_notMem y hy]; exact ⟨zero_le_one, le_rfl⟩
  have hcind : c = Eᶜ.indicator fun _ => (1 : ℝ) := by
    funext y
    by_cases hy : y ∈ E
    · rw [hc_of_mem y hy, Set.indicator_of_notMem (by simpa using hy)]
    · rw [hc_of_notMem y hy, Set.indicator_of_mem (by simpa using hy)]
  have hhit := Battery.sound_QDeadline_hit (K := K) (D := Eᶜ) (Dbar := Set.univ) (B := E)
    (V := c) (β := β) (p := 1 - β ^ n) (thr := 1) (T := n) (M := 1) (x := x)
    hE.compl MeasurableSet.univ hE hcmeas hβ0
    (le_of_eq (by ring))
    (Set.subset_univ _)
    (fun y _ _ => by simp)
    (fun y hyD _ => by rw [Set.compl_union_self]; simp)
    (fun y _ _ => (integrable_const (1 : ℝ)).mono' hcmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hc01 z).1]; exact (hc01 z).2))
    (fun y hyD hyB => by
      rw [hc_of_notMem y hyB, mul_one, hcind,
        integral_indicator_const (1 : ℝ) hE.compl, smul_eq_mul, mul_one, measureReal_def]
      calc (K y Eᶜ).toReal ≤ (ENNReal.ofReal β).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hesc y hyB)
        _ = β := ENNReal.toReal_ofReal hβ0)
    (fun y _ hyB => (hc_of_notMem y hyB).symm.le)
    (fun y _ => (hc01 y).1)
    (fun y _ => (hc01 y).2)
    hx ((hc01 x).2)

  have hhitMeas : MeasurableSet {ω : ℕ → S | ∃ k ≤ n, ω k ∈ E} := by
    have h : {ω : ℕ → S | ∃ k ≤ n, ω k ∈ E}
        = ⋃ k, ⋃ (_ : k ≤ n), (fun ω : ℕ → S => ω k) ⁻¹' E := by
      ext ω; simp
    rw [h]
    exact .iUnion fun k => .iUnion fun _ => (measurable_pi_apply k) hE
  have hcompl : Battery.survive E n = {ω : ℕ → S | ∃ k ≤ n, ω k ∈ E}ᶜ := by
    ext ω
    simp [Battery.survive]
  rw [hcompl, prob_compl_eq_one_sub hhitMeas]
  have hβn1 : ENNReal.ofReal (β ^ n) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (pow_le_one₀ hβ0 hβ1)
  calc (1 : ℝ≥0∞) - Battery.pathMeasure K x {ω : ℕ → S | ∃ k ≤ n, ω k ∈ E}
      ≤ 1 - ENNReal.ofReal (1 - β ^ n) := tsub_le_tsub_left hhit 1
    _ = 1 - (1 - ENNReal.ofReal (β ^ n)) := by
        rw [ENNReal.ofReal_sub _ (pow_nonneg hβ0 n), ENNReal.ofReal_one]
    _ = ENNReal.ofReal (β ^ n) := ENNReal.sub_sub_cancel ENNReal.one_ne_top hβn1

/-- Reachability lower bound by optional stopping. Let `W ≤ 1` be measurable,
subharmonic outside `E` (`W y ≤ ∫ W dK y` for `y ∉ E`), nonpositive on `E \ A`,
and one-step integrable from outside `E`; assume the chain is absorbed into `E`
geometrically (mass at most `β < 1` escapes `E` in one step from outside `E`).
Then the probability that the chain started at `x` ever reaches `A` is at least
`W x`. -/
theorem measure_reach_ge {A E : Set S} {W : S → ℝ} {β : ℝ}
    (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hW : Measurable W) (hW1 : ∀ y, W y ≤ 1)
    (hWE : ∀ y ∈ E, y ∉ A → W y ≤ 0)
    (hWint : ∀ y, y ∉ E → Integrable W (K y))
    (hdrift : ∀ y, y ∉ E → W y ≤ ∫ z, W z ∂K y)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hesc : ∀ y, y ∉ E → K y Eᶜ ≤ ENNReal.ofReal β) (x : S) :
    ENNReal.ofReal (W x) ≤ Battery.pathMeasure K x {ω | ∃ n, ω n ∈ A} := by
  by_cases hxA : x ∈ A
  · rw [measure_reach_of_mem hA hxA, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hW1 x)
  by_cases hxE : x ∈ E
  · rw [ENNReal.ofReal_eq_zero.2 (hWE x hxE hxA)]
    exact zero_le

  set g : S → ℝ := fun y => max (W y) 0 with hgdef
  have hg : Measurable g := hW.max measurable_const
  have hg0 : ∀ y, 0 ≤ g y := fun y => le_max_right _ _
  have hg1 : ∀ y, g y ≤ 1 := fun y => max_le (hW1 y) zero_le_one
  have hgE : ∀ y ∈ E, y ∉ A → g y ≤ 0 := fun y hy hy' =>
    max_le (hWE y hy hy') le_rfl
  have hgdrift : ∀ y, y ∉ E → g y ≤ ∫ z, g z ∂K y := by
    intro y hy
    have hgint : Integrable g (K y) := (integrable_const (1 : ℝ)).mono'
      hg.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hg1 z)
    have h1 : ∫ z, W z ∂K y ≤ ∫ z, g z ∂K y :=
      integral_mono (hWint y hy) hgint fun z => le_max_left _ _
    exact max_le (le_trans (hdrift y hy) h1) (integral_nonneg hg0)
  have hsub := submartingale_stopped (C := 1) hE hg hg0 hg1 hgdrift x

  set R : Set (ℕ → S) := {ω | ∃ n, ω n ∈ A} with hR
  have key : ∀ n : ℕ, g x ≤ (Battery.pathMeasure K x R).toReal + β ^ n := by
    intro n

    have hmono := hsub.setIntegral_le (Nat.zero_le n) (MeasurableSet.univ)
    rw [setIntegral_univ, setIntegral_univ] at hmono
    have h0 : ∫ ω, Battery.stopped g E 0 ω ∂Battery.pathMeasure K x = g x := by
      have hz : (fun ω : ℕ → S => Battery.stopped g E 0 ω) = fun ω => g (ω 0) := rfl
      rw [hz]
      exact integral_coord_zero hg x

    set hit : Set (ℕ → S) := {ω | ∃ k ≤ n, ω k ∈ A} with hhit
    have hhitMeas : MeasurableSet hit := by
      have h : hit = ⋃ k, ⋃ (_ : k ≤ n), (fun ω : ℕ → S => ω k) ⁻¹' A := by
        ext ω; simp [hhit]
      rw [h]
      exact .iUnion fun k => .iUnion fun _ => (measurable_pi_apply k) hA
    have hsurvMeas : MeasurableSet (Battery.survive E n) :=
      (Filtration.piLE (X := fun _ : ℕ => S)).le n _
        (Battery.measurableSet_survive_piLE hE n)

    have hpt : ∀ ω, Battery.stopped g E n ω
        ≤ hit.indicator (fun _ => (1 : ℝ)) ω
          + (Battery.survive E n).indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      have hcap : Battery.stopped g E n ω ≤ 1 :=
        Battery.stopped_pred (fun r => r ≤ 1) hg1 n ω
      by_cases hh : ω ∈ hit
      · have h2 : (0 : ℝ) ≤ (Battery.survive E n).indicator (fun _ => (1 : ℝ)) ω :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        rw [Set.indicator_of_mem hh]
        linarith
      · by_cases hs : ω ∈ Battery.survive E n
        · rw [Set.indicator_of_notMem hh, Set.indicator_of_mem hs]
          linarith
        · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hs]
          simp only [hhit, Set.mem_setOf_eq, not_exists, not_and] at hh
          rw [Battery.mem_survive] at hs
          push Not at hs
          obtain ⟨j, hjn, hjE⟩ := hs
          have := stopped_nonpos_of_first_exit hgE n ω hh ⟨j, hjn, hjE⟩
          linarith

    have hint_hit : Integrable (hit.indicator fun _ => (1 : ℝ))
        (Battery.pathMeasure K x) := (integrable_const (1 : ℝ)).indicator hhitMeas
    have hint_surv : Integrable ((Battery.survive E n).indicator fun _ => (1 : ℝ))
        (Battery.pathMeasure K x) := (integrable_const (1 : ℝ)).indicator hsurvMeas
    have hInt := integral_mono (hsub.integrable n) (hint_hit.add hint_surv) hpt
    simp only [Pi.add_apply] at hInt
    rw [integral_add hint_hit hint_surv,
      integral_indicator_const (1 : ℝ) hhitMeas, integral_indicator_const (1 : ℝ) hsurvMeas,
      smul_eq_mul, mul_one, smul_eq_mul, mul_one] at hInt

    have hsubRe : hit ⊆ R := by
      rw [hhit, hR]
      rintro ω ⟨k, -, hk⟩
      exact ⟨k, hk⟩
    have hhitR : (Battery.pathMeasure K x).real hit
        ≤ (Battery.pathMeasure K x R).toReal := by
      rw [measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubRe)
    have hsurvR : (Battery.pathMeasure K x).real (Battery.survive E n) ≤ β ^ n := by
      rw [measureReal_def]
      calc (Battery.pathMeasure K x (Battery.survive E n)).toReal
          ≤ (ENNReal.ofReal (β ^ n)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top
              (measure_survive_le_pow hE hβ0 hβ1.le hesc hxE n)
        _ = β ^ n := ENNReal.toReal_ofReal (pow_nonneg hβ0 n)
    calc g x = ∫ ω, Battery.stopped g E 0 ω ∂Battery.pathMeasure K x := h0.symm
      _ ≤ ∫ ω, Battery.stopped g E n ω ∂Battery.pathMeasure K x := hmono
      _ ≤ (Battery.pathMeasure K x).real hit
            + (Battery.pathMeasure K x).real (Battery.survive E n) := hInt
      _ ≤ (Battery.pathMeasure K x R).toReal + β ^ n := add_le_add hhitR hsurvR

  have hlim : g x - (Battery.pathMeasure K x R).toReal ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1)
      fun n => by have := key n; linarith
  calc ENNReal.ofReal (W x) ≤ ENNReal.ofReal (g x) :=
        ENNReal.ofReal_le_ofReal (le_max_left _ _)
    _ ≤ ENNReal.ofReal ((Battery.pathMeasure K x R).toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = Battery.pathMeasure K x R := ENNReal.ofReal_toReal (measure_ne_top _ _)

end Qtsl.OptionalStopping
