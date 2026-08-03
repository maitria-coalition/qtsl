import QtslAux.Battery
import QtslAux.QtslCompose.Presentation
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.MeasureTheory.Integral.Prod

/-! # Assume-guarantee composition for discrete-time Markov chains

This module instantiates quantitative assume-guarantee composition on the
path space of a discrete-time Markov chain with kernel `K`, using
supermartingale certificates and Ville's inequality.

Each component `j` designates a bad set `bad j` in the state space and a
certificate `V j : S → ℝ`, bounded, nonnegative, at least `1` on `bad j`,
and non-increasing in expectation (a supermartingale drift condition) while
the chain has not yet entered any bad set.

* `firstFail bad j` is the set of paths whose first visit to `⋃ i, bad i`
  lands in `bad j`; `reach_subset_iUnion_firstFail` shows these events cover
  the reachability event.
* `measure_firstFail_le`: the probability of first failure at component `j`
  is at most `V j x` at the initial state `x`, by Ville's inequality applied
  to the stopped certificate process.
* `fail_bound`: summing over components, the probability of ever entering
  any bad set is at most `∑ j, V j x`.
* `fail_bound_wired`: the same bound when each drift condition is only
  assumed on the component's conformance set `conf j`, provided avoiding all
  upstream bad sets entails conformance (the wiring condition of a
  `System`).
* `ae_avoid_of_zero`: if every certificate vanishes at the initial state,
  the chain almost surely never enters any bad set.
* `drift_parallelComp`, `avoid_parallelComp`: for a parallel composition
  `K₁ ∥ₖ K₂`, the weighted sum `V₁ + lam * V₂` of component certificates is a
  certificate for the union of the two (lifted) bad sets.
* `smallGain_drift`, `avoid_smallGain`: a small-gain theorem — two coupled
  dissipation inequalities with supply rates `sigma₁, sigma₂` and decay rates
  `alpha₁, alpha₂` satisfying the cross-gain conditions combine, again via a
  weighted sum, into a single certificate with strict decay margin `theta`.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function
open Qtsl.Battery

namespace Qtsl.QtslCompose.Discrete

variable {S : Type*} {m : ℕ}

/-- The event that the path's first entry into the union `⋃ i, bad i` occurs
through `bad j`: some time `n` has `ω n ∈ bad j` while every earlier state
avoids all bad sets. -/
def firstFail (bad : Fin m → Set S) (j : Fin m) : Set (ℕ → S) :=
  {ω | ∃ n, ω n ∈ bad j ∧ ∀ k < n, ω k ∉ ⋃ i, bad i}

/-- Any path that ever enters some bad set has a first such entry, so the
reachability event is covered by the `firstFail` events. -/
theorem reach_subset_iUnion_firstFail (bad : Fin m → Set S) :
    {ω : ℕ → S | ∃ n, ω n ∈ ⋃ i, bad i} ⊆ ⋃ j, firstFail bad j := by
  rintro ω ⟨n, hn⟩
  have hex : ∃ k, ω k ∈ ⋃ i, bad i := ⟨n, hn⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (Nat.find_spec hex)
  exact Set.mem_iUnion.2 ⟨j, Nat.find hex, hj, fun k hk => Nat.find_min hex hk⟩

variable [MeasurableSpace S] {K : Kernel S S} [IsMarkovKernel K]

private lemma integral_stopped_zero {f : S → ℝ} {A : Set S} (hf : Measurable f)
    (x : S) : ∫ ω, stopped f A 0 ω ∂pathMeasure K x = f x := by
  have hmeas : AEStronglyMeasurable (stopped f A 0)
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
  unfold pathMeasure
  rw [Kernel.integral_traj _ hmeas]
  have hval : ∀ y : ℕ → S,
      stopped f A 0 (updateFinset y (Iic 0) (fun _ => x)) = f x := fun y => by
    rw [stopped_zero]
    congr 1
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hval y), integral_const]
  simp [measureReal_def]

/-- Certificate bound for first failure at component `j`: if `V` is
measurable, bounded, nonnegative, at least `1` on `bad j`, and satisfies the
supermartingale drift condition `∫ z, V z ∂K y ≤ V y` outside `⋃ i, bad i`,
then the probability that the chain started at `x` first fails through
`bad j` is at most `V x`. The proof stops `V` at the first entry into any
bad set and applies Ville's inequality to the stopped supermartingale. -/
theorem measure_firstFail_le {bad : Fin m → Set S} {V : S → ℝ} {C : ℝ} {j : Fin m}
    (hA : MeasurableSet (⋃ i, bad i)) (hV : Measurable V)
    (hV0 : ∀ y, 0 ≤ V y) (hVC : ∀ y, V y ≤ C)
    (hbar : ∀ y ∈ bad j, 1 ≤ V y)
    (hdrift : ∀ y, y ∉ (⋃ i, bad i) → ∫ z, V z ∂K y ≤ V y) (x : S) :
    pathMeasure K x (firstFail bad j) ≤ ENNReal.ofReal (V x) := by
  have hsub : firstFail bad j ⊆
      {ω : ℕ → S | ∃ k, ((1 : ℝ≥0) : ℝ) ≤ stopped V (⋃ i, bad i) k ω} := by
    rintro ω ⟨n, hbadj, hbefore⟩
    refine ⟨n, ?_⟩
    rw [NNReal.coe_one]
    cases n with
    | zero => rw [stopped_zero]; exact hbar _ hbadj
    | succ k =>
      have hs : ω ∈ survive (⋃ i, bad i) k :=
        fun i hik => hbefore i (Nat.lt_succ_of_le hik)
      rw [stopped_succ_of_survive hs]
      exact hbar _ hbadj
  have hville := (supermartingale_stopped (K := K) hA hV hV0 hVC hdrift x).ville_ineq
    (fun n ω => stopped_pred (fun r => 0 ≤ r) hV0 n ω) 1
  rw [ENNReal.coe_one, one_mul] at hville
  calc pathMeasure K x (firstFail bad j)
      ≤ pathMeasure K x
        {ω | ∃ k, ((1 : ℝ≥0) : ℝ) ≤ stopped V (⋃ i, bad i) k ω} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (∫ ω, stopped V (⋃ i, bad i) 0 ω ∂pathMeasure K x) := hville
    _ = ENNReal.ofReal (V x) := by rw [integral_stopped_zero hV x]

/-- Compositional reachability bound: with one certificate `V j` per
component, the probability that the chain started at `x` ever enters any bad
set is at most `∑ j, V j x`. Combines `reach_subset_iUnion_firstFail` with
`measure_firstFail_le` for each component. -/
theorem fail_bound {bad : Fin m → Set S} {V : Fin m → S → ℝ} {C : Fin m → ℝ}
    (hA : MeasurableSet (⋃ i, bad i))
    (hV : ∀ j, Measurable (V j)) (hV0 : ∀ j y, 0 ≤ V j y)
    (hVC : ∀ j y, V j y ≤ C j)
    (hbar : ∀ j, ∀ y ∈ bad j, 1 ≤ V j y)
    (hdrift : ∀ j, ∀ y, y ∉ (⋃ i, bad i) → ∫ z, V j z ∂K y ≤ V j y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ ⋃ i, bad i}
      ≤ ∑ j, ENNReal.ofReal (V j x) :=
  (measure_mono (reach_subset_iUnion_firstFail bad)).trans
    (((measure_iUnion_le _).trans_eq (tsum_fintype _)).trans
      (Finset.sum_le_sum fun j _ =>
        measure_firstFail_le hA (hV j) (hV0 j) (hVC j) (hbar j) (hdrift j) x))

/-- **QWireCompose B-row, wired form at its honest hypothesis** (an r1
finding of the cyclic-tier design, enacted: the proof of the wired form consumes
only the wiring ORDER — `System.rank`/`causality` were never used — so the
discrete row's statement generalizes to a bare upstream family, documenting
its cyclic capability: nothing here refuses a cyclic `upstream`). -/
theorem fail_bound_upstream (upstream : Fin m → Finset (Fin m))
    {conf bad : Fin m → Set S}
    {V : Fin m → S → ℝ} {C : Fin m → ℝ}
    (hA : MeasurableSet (⋃ i, bad i))
    (hw : ∀ j, (⋂ i ∈ upstream j, (bad i)ᶜ) ⊆ conf j)
    (hV : ∀ j, Measurable (V j)) (hV0 : ∀ j y, 0 ≤ V j y)
    (hVC : ∀ j y, V j y ≤ C j)
    (hbar : ∀ j, ∀ y ∈ bad j, 1 ≤ V j y)
    (hdrift : ∀ j, ∀ y ∈ conf j, y ∉ bad j → ∫ z, V j z ∂K y ≤ V j y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ ⋃ i, bad i}
      ≤ ∑ j, ENNReal.ofReal (V j x) := by
  refine fail_bound hA hV hV0 hVC hbar (fun j y hy => ?_) x
  have hnot : ∀ i, y ∉ bad i := fun i hi => hy (Set.mem_iUnion.2 ⟨i, hi⟩)
  exact hdrift j y (hw j (Set.mem_iInter₂.2 fun i _ => hnot i)) (hnot j)

/-- Assume-guarantee form of `fail_bound`: each component's drift condition
is only required on its conformance set `conf j`, and the wiring condition
`hw` guarantees that a state avoiding all upstream bad sets is conformant.
Since a state outside every bad set is in particular outside the upstream
ones, the pointwise hypotheses of `fail_bound` follow. -/
theorem fail_bound_wired (Sys : System m) {conf bad : Fin m → Set S}
    {V : Fin m → S → ℝ} {C : Fin m → ℝ}
    (hA : MeasurableSet (⋃ i, bad i))
    (hw : ∀ j, (⋂ i ∈ Sys.upstream j, (bad i)ᶜ) ⊆ conf j)
    (hV : ∀ j, Measurable (V j)) (hV0 : ∀ j y, 0 ≤ V j y)
    (hVC : ∀ j y, V j y ≤ C j)
    (hbar : ∀ j, ∀ y ∈ bad j, 1 ≤ V j y)
    (hdrift : ∀ j, ∀ y ∈ conf j, y ∉ bad j → ∫ z, V j z ∂K y ≤ V j y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ ⋃ i, bad i}
      ≤ ∑ j, ENNReal.ofReal (V j x) :=
  fail_bound_upstream Sys.upstream hA hw hV hV0 hVC hbar hdrift x

/-- Qualitative corollary: if every certificate vanishes at the initial
state, the reachability probability is zero, so the chain almost surely
avoids all bad sets forever. -/
theorem ae_avoid_of_zero {bad : Fin m → Set S} {V : Fin m → S → ℝ}
    {C : Fin m → ℝ}
    (hA : MeasurableSet (⋃ i, bad i))
    (hV : ∀ j, Measurable (V j)) (hV0 : ∀ j y, 0 ≤ V j y)
    (hVC : ∀ j y, V j y ≤ C j)
    (hbar : ∀ j, ∀ y ∈ bad j, 1 ≤ V j y)
    (hdrift : ∀ j, ∀ y, y ∉ (⋃ i, bad i) → ∫ z, V j z ∂K y ≤ V j y) {x : S}
    (hzero : ∀ j, V j x = 0) :
    ∀ᵐ ω ∂pathMeasure K x, ∀ n, ω n ∉ ⋃ i, bad i := by
  have hnull : pathMeasure K x {ω | ∃ n, ω n ∈ ⋃ i, bad i} = 0 :=
    le_antisymm
      ((fail_bound hA hV hV0 hVC hbar hdrift x).trans_eq (by simp [hzero]))
      zero_le
  rw [ae_iff]
  convert hnull using 2
  ext ω
  simp

section Parallel

variable {S₁ S₂ : Type*} [MeasurableSpace S₁] [MeasurableSpace S₂]
variable {K₁ : Kernel S₁ S₁} {K₂ : Kernel S₂ S₂}
variable [IsMarkovKernel K₁] [IsMarkovKernel K₂]

lemma integral_fst_parallelComp (f : S₁ → ℝ) (p : S₁ × S₂) :
    ∫ q, f q.1 ∂(K₁ ∥ₖ K₂) p = ∫ z, f z ∂K₁ p.1 := by
  rw [Kernel.parallelComp_apply, integral_fun_fst, probReal_univ, one_smul]

lemma integral_snd_parallelComp (f : S₂ → ℝ) (p : S₁ × S₂) :
    ∫ q, f q.2 ∂(K₁ ∥ₖ K₂) p = ∫ z, f z ∂K₂ p.2 := by
  rw [Kernel.parallelComp_apply, integral_fun_snd, probReal_univ, one_smul]

/-- Drift condition for a parallel composition: if `V₁` and `V₂` satisfy the
supermartingale drift condition for `K₁` and `K₂` outside their respective
bad sets, then the weighted sum `V₁ q.1 + lam * V₂ q.2` satisfies it for
`K₁ ∥ₖ K₂` outside the union of the lifted bad sets. -/
theorem drift_parallelComp {bad₁ : Set S₁} {bad₂ : Set S₂}
    {V₁ : S₁ → ℝ} {V₂ : S₂ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hint₁ : ∀ y, y ∉ bad₁ → Integrable V₁ (K₁ y))
    (hint₂ : ∀ y, y ∉ bad₂ → Integrable V₂ (K₂ y))
    (hd₁ : ∀ y, y ∉ bad₁ → ∫ z, V₁ z ∂K₁ y ≤ V₁ y)
    (hd₂ : ∀ y, y ∉ bad₂ → ∫ z, V₂ z ∂K₂ y ≤ V₂ y) :
    ∀ p : S₁ × S₂, p ∉ (Prod.fst ⁻¹' bad₁ ∪ Prod.snd ⁻¹' bad₂) →
      ∫ q, (V₁ q.1 + lam * V₂ q.2) ∂(K₁ ∥ₖ K₂) p
        ≤ V₁ p.1 + lam * V₂ p.2 := by
  rintro p hp
  have hp₁ : p.1 ∉ bad₁ := fun h => hp (Set.mem_union_left _ h)
  have hp₂ : p.2 ∉ bad₂ := fun h => hp (Set.mem_union_right _ h)
  have hi₁ : Integrable (fun q : S₁ × S₂ => V₁ q.1) ((K₁ p.1).prod (K₂ p.2)) :=
    (hint₁ _ hp₁).comp_fst _
  have hi₂ : Integrable (fun q : S₁ × S₂ => V₂ q.2) ((K₁ p.1).prod (K₂ p.2)) :=
    (hint₂ _ hp₂).comp_snd _
  rw [Kernel.parallelComp_apply,
    integral_add hi₁ (hi₂.const_mul lam), integral_const_mul,
    integral_fun_fst, integral_fun_snd, probReal_univ, probReal_univ,
    one_smul, one_smul]
  exact add_le_add (hd₁ _ hp₁) (mul_le_mul_of_nonneg_left (hd₂ _ hp₂) hlam)

/-- Reachability bound for a parallel composition: given component
certificates with barriers `1 ≤ V₁` on `bad₁` and `1 ≤ lam * V₂` on `bad₂`,
the probability that the product chain `K₁ ∥ₖ K₂` ever enters either lifted
bad set is at most `V₁ x.1 + lam * V₂ x.2`. -/
theorem avoid_parallelComp {bad₁ : Set S₁} {bad₂ : Set S₂}
    {V₁ : S₁ → ℝ} {V₂ : S₂ → ℝ} {C₁ C₂ lam : ℝ} (hlam : 0 ≤ lam)
    (hbad₁ : MeasurableSet bad₁) (hbad₂ : MeasurableSet bad₂)
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hV₁0 : ∀ y, 0 ≤ V₁ y) (hV₂0 : ∀ y, 0 ≤ V₂ y)
    (hV₁C : ∀ y, V₁ y ≤ C₁) (hV₂C : ∀ y, V₂ y ≤ C₂)
    (hbar₁ : ∀ y ∈ bad₁, 1 ≤ V₁ y) (hbar₂ : ∀ y ∈ bad₂, 1 ≤ lam * V₂ y)
    (hd₁ : ∀ y, y ∉ bad₁ → ∫ z, V₁ z ∂K₁ y ≤ V₁ y)
    (hd₂ : ∀ y, y ∉ bad₂ → ∫ z, V₂ z ∂K₂ y ≤ V₂ y) (x : S₁ × S₂) :
    pathMeasure (K₁ ∥ₖ K₂) x
        {ω | ∃ n, ω n ∈ (Prod.fst ⁻¹' bad₁ ∪ Prod.snd ⁻¹' bad₂ : Set (S₁ × S₂))}
      ≤ ENNReal.ofReal (V₁ x.1 + lam * V₂ x.2) := by
  have hint₁ : ∀ y, y ∉ bad₁ → Integrable V₁ (K₁ y) := fun y _ =>
    (integrable_const C₁).mono' hV₁.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV₁0 z)]; exact hV₁C z)
  have hint₂ : ∀ y, y ∉ bad₂ → Integrable V₂ (K₂ y) := fun y _ =>
    (integrable_const C₂).mono' hV₂.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV₂0 z)]; exact hV₂C z)
  refine measure_reach_le (C := C₁ + lam * C₂)
    ((hbad₁.preimage measurable_fst).union (hbad₂.preimage measurable_snd))
    ((hV₁.comp measurable_fst).add (measurable_const.mul (hV₂.comp measurable_snd)))
    (fun p => add_nonneg (hV₁0 _) (mul_nonneg hlam (hV₂0 _)))
    (fun p => add_le_add (hV₁C _) (mul_le_mul_of_nonneg_left (hV₂C _) hlam))
    (fun p hp => ?_)
    (fun p hp => drift_parallelComp hlam hint₁ hint₂ hd₁ hd₂ p hp) x
  rcases hp with h1 | h2
  · exact (hbar₁ _ h1).trans (le_add_of_nonneg_right (mul_nonneg hlam (hV₂0 _)))
  · exact (hbar₂ _ h2).trans (le_add_of_nonneg_left (hV₁0 _))

end Parallel

section SmallGain

variable {A : Set S} {V₁ V₂ alpha₁ alpha₂ sigma₁ sigma₂ : S → ℝ} {lam theta : ℝ}

omit [IsMarkovKernel K] in

/-- Small-gain drift combination: from two dissipation inequalities
`∫ V₁ ∂K ≤ V₁ - alpha₁ + sigma₁` and `∫ V₂ ∂K ≤ V₂ - alpha₂ + sigma₂` and
the cross-gain conditions `lam * sigma₂ ≤ (1 - theta) * alpha₁` and
`sigma₁ ≤ lam * ((1 - theta) * alpha₂)`, the weighted sum `V₁ + lam * V₂`
dissipates with margin `theta * (alpha₁ + lam * alpha₂)`: each certificate's
supply is absorbed by the other's decay. -/
theorem smallGain_drift (hlam : 0 ≤ lam)
    (hint₁ : ∀ y, y ∉ A → Integrable V₁ (K y))
    (hint₂ : ∀ y, y ∉ A → Integrable V₂ (K y))
    (hd₁ : ∀ y, y ∉ A → ∫ z, V₁ z ∂K y ≤ V₁ y - alpha₁ y + sigma₁ y)
    (hd₂ : ∀ y, y ∉ A → ∫ z, V₂ z ∂K y ≤ V₂ y - alpha₂ y + sigma₂ y)
    (hm₁ : ∀ y, y ∉ A → lam * sigma₂ y ≤ (1 - theta) * alpha₁ y)
    (hm₂ : ∀ y, y ∉ A → sigma₁ y ≤ lam * ((1 - theta) * alpha₂ y)) :
    ∀ y, y ∉ A → ∫ z, (V₁ z + lam * V₂ z) ∂K y
      ≤ (V₁ y + lam * V₂ y) - theta * (alpha₁ y + lam * alpha₂ y) := by
  intro y hy
  rw [integral_add (hint₁ y hy) ((hint₂ y hy).const_mul lam), integral_const_mul]
  have h₁ := hd₁ y hy
  have h₂ := mul_le_mul_of_nonneg_left (hd₂ y hy) hlam
  have hm₁' := hm₁ y hy
  have hm₂' := hm₂ y hy
  have e₁ : lam * (V₂ y - alpha₂ y + sigma₂ y)
      = lam * V₂ y - lam * alpha₂ y + lam * sigma₂ y := by ring
  have e₂ : lam * ((1 - theta) * alpha₂ y)
      = lam * alpha₂ y - theta * (lam * alpha₂ y) := by ring
  have e₃ : (1 - theta) * alpha₁ y = alpha₁ y - theta * alpha₁ y := by ring
  have e₄ : theta * (alpha₁ y + lam * alpha₂ y)
      = theta * alpha₁ y + theta * (lam * alpha₂ y) := by ring
  rw [e₁] at h₂
  rw [e₂] at hm₂'
  rw [e₃] at hm₁'
  rw [e₄]
  linarith

/-- Small-gain reachability bound: under the hypotheses of
`smallGain_drift`, with nonnegative decay rates and the barrier
`1 ≤ V₁ + lam * V₂` on `A`, the probability that the chain started at `x`
ever enters `A` is at most `V₁ x + lam * V₂ x`. -/
theorem avoid_smallGain (hlam : 0 ≤ lam) (htheta : 0 ≤ theta)
    {C₁ C₂ : ℝ} (hA : MeasurableSet A)
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hV₁0 : ∀ y, 0 ≤ V₁ y) (hV₂0 : ∀ y, 0 ≤ V₂ y)
    (hV₁C : ∀ y, V₁ y ≤ C₁) (hV₂C : ∀ y, V₂ y ≤ C₂)
    (hbar : ∀ y ∈ A, 1 ≤ V₁ y + lam * V₂ y)
    (halpha₁ : ∀ y, y ∉ A → 0 ≤ alpha₁ y)
    (halpha₂ : ∀ y, y ∉ A → 0 ≤ alpha₂ y)
    (hd₁ : ∀ y, y ∉ A → ∫ z, V₁ z ∂K y ≤ V₁ y - alpha₁ y + sigma₁ y)
    (hd₂ : ∀ y, y ∉ A → ∫ z, V₂ z ∂K y ≤ V₂ y - alpha₂ y + sigma₂ y)
    (hm₁ : ∀ y, y ∉ A → lam * sigma₂ y ≤ (1 - theta) * alpha₁ y)
    (hm₂ : ∀ y, y ∉ A → sigma₁ y ≤ lam * ((1 - theta) * alpha₂ y)) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ A}
      ≤ ENNReal.ofReal (V₁ x + lam * V₂ x) := by
  have hint₁ : ∀ y, y ∉ A → Integrable V₁ (K y) := fun y _ =>
    (integrable_const C₁).mono' hV₁.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV₁0 z)]; exact hV₁C z)
  have hint₂ : ∀ y, y ∉ A → Integrable V₂ (K y) := fun y _ =>
    (integrable_const C₂).mono' hV₂.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV₂0 z)]; exact hV₂C z)
  refine measure_reach_le (C := C₁ + lam * C₂)
    (f := fun y => V₁ y + lam * V₂ y) hA
    (by fun_prop)
    (fun y => add_nonneg (hV₁0 y) (mul_nonneg hlam (hV₂0 y)))
    (fun y => add_le_add (hV₁C y) (mul_le_mul_of_nonneg_left (hV₂C y) hlam))
    hbar (fun y hy => ?_) x
  have h := smallGain_drift hlam hint₁ hint₂ hd₁ hd₂ hm₁ hm₂ y hy
  have hnn : 0 ≤ theta * (alpha₁ y + lam * alpha₂ y) :=
    mul_nonneg htheta (add_nonneg (halpha₁ y hy) (mul_nonneg hlam (halpha₂ y hy)))
  linarith

end SmallGain

/-! ## B3′ — feedback at any n (SmallGainN, discrete sum-form)

The n-component quantitative small-gain rule's semantic face, beside its
binary instance above — the drift row `smallGainN_drift`, its assembled
avoid bound, and the binary recovery ON THE NOSE (`smallGain_drift_of_N`).
Data per the catalogue row `SmallGainN` (BL-rules.toml, composition rules): weights `lam`,
repayment matrix `B` with exact column sums `∑ i, B i j = lam j`, margin
`theta`. Width facts, reproducing the binary find at any n: soundness
consumes only `0 ≤ lam` and the column condition — `0 < lam`,
`theta ∈ (0,1)`, and `0 ≤ B` are rule-level well-formedness, never
hypotheses (the membership rows self-police: `B`'s sign never enters the
algebra, which is why the mutant `colSum_deleted_refuted` below can break
soundness only by breaking the COLUMN condition). -/

section SmallGainN

variable {A : Set S} {V alpha sigma : Fin m → S → ℝ} {lam : Fin m → ℝ}
  {B : Fin m → Fin m → ℝ} {theta : ℝ}

omit [IsMarkovKernel K] in
/-- **B3′, the cancellation row at any n** (the semantic face of the
checker-level `(λ₁, …, λₙ, 1, …, 1)` syzygy fold): per-component dissipation
rows with cross-supplies on the joint closed-loop kernel, under the n-ary
membership rows and the exact column condition, yield the `θ`-margin drift
row for `W = ∑ i, lam i * V i`. The cross-supplies cancel by construction:
`∑ i, lam i * sigma i ≤ (1-θ) ∑ i ∑ j, B i j * alpha j = (1-θ) ∑ j, lam j * alpha j`
(swap the double sum, then the column condition). -/
theorem smallGainN_drift (hlam : ∀ i, 0 ≤ lam i)
    (hcol : ∀ j, ∑ i, B i j = lam j)
    (hint : ∀ i, ∀ y, y ∉ A → Integrable (V i) (K y))
    (hd : ∀ i, ∀ y, y ∉ A →
        ∫ z, V i z ∂K y ≤ V i y - alpha i y + sigma i y)
    (hm : ∀ i, ∀ y, y ∉ A →
        lam i * sigma i y ≤ (1 - theta) * ∑ j, B i j * alpha j y) :
    ∀ y, y ∉ A → ∫ z, (∑ i, lam i * V i z) ∂K y
      ≤ (∑ i, lam i * V i y) - theta * ∑ j, lam j * alpha j y := by
  intro y hy
  rw [integral_finset_sum _ (fun i _ => ((hint i y hy).const_mul (lam i)))]
  simp_rw [integral_const_mul]
  have step1 : ∑ i, lam i * ∫ z, V i z ∂K y
      ≤ ∑ i, (lam i * V i y - lam i * alpha i y + lam i * sigma i y) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hd i y hy) (hlam i)
    have hr : lam i * (V i y - alpha i y + sigma i y)
        = lam i * V i y - lam i * alpha i y + lam i * sigma i y := by ring
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at step1
  have step2 : ∑ i, lam i * sigma i y ≤ (1 - theta) * ∑ j, lam j * alpha j y := by
    calc ∑ i, lam i * sigma i y
        ≤ ∑ i, (1 - theta) * ∑ j, B i j * alpha j y :=
          Finset.sum_le_sum fun i _ => hm i y hy
      _ = (1 - theta) * ∑ i, ∑ j, B i j * alpha j y := by
          rw [Finset.mul_sum]
      _ = (1 - theta) * ∑ j, (∑ i, B i j) * alpha j y := by
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = (1 - theta) * ∑ j, lam j * alpha j y := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [hcol j]
  linarith

omit [IsMarkovKernel K] in
/-- **Binary recovery, on the nose**: `smallGain_drift`'s exact statement
re-derived from `smallGainN_drift` at `m = 2`, `lam = ![1, λ]`,
`B = ![![0, λ], ![1, 0]]` (column sums `0 + 1 = 1` and `λ + 0 = λ`). One
bookkeeping disanalogy, inherited from the catalogue commentary: the n-ary
membership row at `i = 0` reads `1 * σ₁ ≤ (1-θ)·λ·α₂` — the binary `hm₂`
with its factors reassociated — and at `i = 1` reads `λ * σ₂ ≤ (1-θ)·α₁` =
the binary `hm₁`; the two rows arrive order-swapped vs the binary labels,
set-equal. -/
theorem smallGain_drift_of_N {V₁ V₂ alpha₁ alpha₂ sigma₁ sigma₂ : S → ℝ}
    {lam theta : ℝ} (hlam : 0 ≤ lam)
    (hint₁ : ∀ y, y ∉ A → Integrable V₁ (K y))
    (hint₂ : ∀ y, y ∉ A → Integrable V₂ (K y))
    (hd₁ : ∀ y, y ∉ A → ∫ z, V₁ z ∂K y ≤ V₁ y - alpha₁ y + sigma₁ y)
    (hd₂ : ∀ y, y ∉ A → ∫ z, V₂ z ∂K y ≤ V₂ y - alpha₂ y + sigma₂ y)
    (hm₁ : ∀ y, y ∉ A → lam * sigma₂ y ≤ (1 - theta) * alpha₁ y)
    (hm₂ : ∀ y, y ∉ A → sigma₁ y ≤ lam * ((1 - theta) * alpha₂ y)) :
    ∀ y, y ∉ A → ∫ z, (V₁ z + lam * V₂ z) ∂K y
      ≤ (V₁ y + lam * V₂ y) - theta * (alpha₁ y + lam * alpha₂ y) := by
  intro y hy
  have h := smallGainN_drift (m := 2) (A := A)
    (V := ![V₁, V₂]) (alpha := ![alpha₁, alpha₂]) (sigma := ![sigma₁, sigma₂])
    (lam := ![1, lam]) (B := ![![0, lam], ![1, 0]]) (theta := theta)
    (fun i => by
      fin_cases i
      · norm_num
      · simpa using hlam)
    (fun j => by
      fin_cases j <;>
        simp [Fin.sum_univ_two])
    (fun i y' hy' => by
      fin_cases i
      · simpa using hint₁ y' hy'
      · simpa using hint₂ y' hy')
    (fun i y' hy' => by
      fin_cases i
      · simpa using hd₁ y' hy'
      · simpa using hd₂ y' hy')
    (fun i y' hy' => by
      fin_cases i
      · have h2 := hm₂ y' hy'
        rw [Fin.sum_univ_two]
        show (1 : ℝ) * sigma₁ y'
          ≤ (1 - theta) * ((0 : ℝ) * alpha₁ y' + lam * alpha₂ y')
        have hr : lam * ((1 - theta) * alpha₂ y')
            = (1 - theta) * ((0 : ℝ) * alpha₁ y' + lam * alpha₂ y') := by ring
        linarith
      · have h1 := hm₁ y' hy'
        rw [Fin.sum_univ_two]
        show lam * sigma₂ y'
          ≤ (1 - theta) * ((1 : ℝ) * alpha₁ y' + (0 : ℝ) * alpha₂ y')
        have hr : (1 - theta) * alpha₁ y'
            = (1 - theta) * ((1 : ℝ) * alpha₁ y' + (0 : ℝ) * alpha₂ y') := by ring
        linarith)
    y hy
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, one_mul] at h
  exact h

/-- **B3′, assembled**: on the closed loop, the n-ary small-gain data yields
the composite avoid bound for the weighted-sum certificate (the discrete face
of the catalogue rule end-to-end; Foster–Lyapunov metatheory through
`Battery.measure_reach_le`, exactly as the binary `avoid_smallGain`). -/
theorem avoid_smallGainN (hlam : ∀ i, 0 ≤ lam i) (htheta : 0 ≤ theta)
    {C : Fin m → ℝ} (hA : MeasurableSet A)
    (hcol : ∀ j, ∑ i, B i j = lam j)
    (hV : ∀ i, Measurable (V i))
    (hV0 : ∀ i y, 0 ≤ V i y) (hVC : ∀ i y, V i y ≤ C i)
    (hbar : ∀ y ∈ A, 1 ≤ ∑ i, lam i * V i y)
    (halpha : ∀ i, ∀ y, y ∉ A → 0 ≤ alpha i y)
    (hd : ∀ i, ∀ y, y ∉ A →
        ∫ z, V i z ∂K y ≤ V i y - alpha i y + sigma i y)
    (hm : ∀ i, ∀ y, y ∉ A →
        lam i * sigma i y ≤ (1 - theta) * ∑ j, B i j * alpha j y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ A}
      ≤ ENNReal.ofReal (∑ i, lam i * V i x) := by
  have hint : ∀ i, ∀ y, y ∉ A → Integrable (V i) (K y) := fun i y _ =>
    (integrable_const (C i)).mono' (hV i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV0 i z)]; exact hVC i z)
  refine measure_reach_le (C := ∑ i, lam i * C i)
    (f := fun y => ∑ i, lam i * V i y) hA
    (Finset.measurable_sum _ fun i _ => measurable_const.mul (hV i))
    (fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (hV0 i y))
    (fun y => Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hVC i y) (hlam i))
    hbar (fun y hy => ?_) x
  have h := smallGainN_drift hlam hcol hint hd hm y hy
  have hnn : 0 ≤ theta * ∑ j, lam j * alpha j y :=
    mul_nonneg htheta (Finset.sum_nonneg fun j _ =>
      mul_nonneg (hlam j) (halpha j y hy))
  linarith

omit [IsMarkovKernel K] in
/-- **M-N1 (the column condition deleted): the n-ary drift row without
`hcol` is UNSOUND** — with `B` unmoored from `lam`, the membership rows can
draw on decay budgets nobody granted. Witness: two components on `Unit`
under the Dirac kernel, `V = 0`, `alpha = 1`, `sigma = 1`, `lam = ![1, 1]`,
`theta = 1/2`, `B` constant `2` (column sums `4 ≠ 1`): every dissipation and
membership row holds, and the conclusion demands `0 ≤ -1`. -/
theorem colSum_deleted_refuted :
    ¬ (∀ (S' : Type) (_ : MeasurableSpace S') (K' : Kernel S' S')
        (_ : IsMarkovKernel K')
        (A : Set S') (V alpha sigma : Fin 2 → S' → ℝ) (lam : Fin 2 → ℝ)
        (B : Fin 2 → Fin 2 → ℝ) (theta : ℝ),
        (∀ i, 0 ≤ lam i) →
        (∀ i, ∀ y, y ∉ A → Integrable (V i) (K' y)) →
        (∀ i, ∀ y, y ∉ A →
          ∫ z, V i z ∂K' y ≤ V i y - alpha i y + sigma i y) →
        (∀ i, ∀ y, y ∉ A →
          lam i * sigma i y ≤ (1 - theta) * ∑ j, B i j * alpha j y) →
        ∀ y, y ∉ A → ∫ z, (∑ i, lam i * V i z) ∂K' y
          ≤ (∑ i, lam i * V i y) - theta * ∑ j, lam j * alpha j y) := by
  intro hrule
  have h := hrule Unit inferInstance (Kernel.const Unit (Measure.dirac ()))
    inferInstance ∅
    (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 1) ![1, 1]
    (fun _ _ => 2) (1/2)
    (fun i => by fin_cases i <;> norm_num)
    (fun i y _ => by simpa using integrable_const (0 : ℝ))
    (fun i y _ => by simp)
    (fun i y _ => by
      simp only [Fin.sum_univ_two]
      fin_cases i <;> norm_num)
    () (by simp)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  norm_num at h

end SmallGainN

end Qtsl.QtslCompose.Discrete

#print axioms Qtsl.QtslCompose.Discrete.reach_subset_iUnion_firstFail
#print axioms Qtsl.QtslCompose.Discrete.measure_firstFail_le
#print axioms Qtsl.QtslCompose.Discrete.fail_bound
#print axioms Qtsl.QtslCompose.Discrete.fail_bound_wired
#print axioms Qtsl.QtslCompose.Discrete.ae_avoid_of_zero
#print axioms Qtsl.QtslCompose.Discrete.integral_fst_parallelComp
#print axioms Qtsl.QtslCompose.Discrete.integral_snd_parallelComp
#print axioms Qtsl.QtslCompose.Discrete.drift_parallelComp
#print axioms Qtsl.QtslCompose.Discrete.avoid_parallelComp
#print axioms Qtsl.QtslCompose.Discrete.smallGain_drift
#print axioms Qtsl.QtslCompose.Discrete.avoid_smallGain
#print axioms Qtsl.QtslCompose.Discrete.fail_bound_upstream
#print axioms Qtsl.QtslCompose.Discrete.smallGainN_drift
#print axioms Qtsl.QtslCompose.Discrete.smallGain_drift_of_N
#print axioms Qtsl.QtslCompose.Discrete.avoid_smallGainN
#print axioms Qtsl.QtslCompose.Discrete.colSum_deleted_refuted
