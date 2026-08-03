import QtslAux.LayerD.D3Faces
import QtslAux.LayerD.PDMPDischarge
import Mathlib.Probability.Martingale.BorelCantelli

/-! # Zeno-freedom: divergence of jump times for GSHS outcome chains

This module shows that, under a uniform dwell-time gap condition, almost every
path of the outcome chain `outStep M` either terminates (a `halt` or `live`
outcome) or has divergent cumulative jump times — that is, the system exhibits
no Zeno behaviour.

* `GapEvent c`: outcomes that are terminal or dwell at least `c`;
  `UniformGapAfter M trig c ε` demands that from every outcome in the trigger
  set the next outcome lies in `GapEvent c` with probability at least `ε`.
* `terminal_or_tendsto_of_frequently_gapEvent` and `wz_free_sure`: the
  deterministic core — a path with infinitely many `c`-gap events either meets
  a terminal outcome or satisfies `jumpTimes · ω → ∞`.
* `ae_frequently_gapEvent`: the probabilistic core — by a conditional
  (second) Borel–Cantelli argument at Lévy's zero–one level, almost surely,
  infinitely many visits to the trigger set force infinitely many gap events.
* `wz_free_of_forced_gap` (trigger set: `guard` exits) and
  `wz_free_of_uniform_gap` (trigger set: everything): almost surely, terminate
  or diverge.
* Quantitative suppliers of the gap hypothesis: `le_reach_time_of_lipschitz`
  (a `v`-Lipschitz flow needs time at least `δ / v` to reach a set at distance
  `δ`) and `le_segMeasureFin_gapEvent` (a finite-horizon PDMP segment with
  jump rate bounded by `Λ` and horizon at least `c` lands in `GapEvent c`
  with probability at least `exp (-Λ * c)`).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

def isTerminal (k : ExitKind) : Prop := k = ExitKind.halt ∨ k = ExitKind.live

def GapEvent (c : ℝ≥0) : Set (ℝ≥0 × State × ExitKind) :=
  {o | c ≤ o.1 ∨ isTerminal o.2.2}

lemma measurableSet_gapEvent (c : ℝ≥0) :
    MeasurableSet (GapEvent (State := State) c) := by
  have h : GapEvent (State := State) c
      = (fun o : ℝ≥0 × State × ExitKind => o.1) ⁻¹' Set.Ici c
        ∪ ((fun o : ℝ≥0 × State × ExitKind => o.2.2) ⁻¹' {ExitKind.halt}
          ∪ (fun o : ℝ≥0 × State × ExitKind => o.2.2) ⁻¹' {ExitKind.live}) := by
    ext o
    simp [GapEvent, isTerminal]
  rw [h]
  exact (measurable_fst measurableSet_Ici).union
    (((measurable_snd.comp measurable_snd) (measurableSet_singleton _)).union
      ((measurable_snd.comp measurable_snd) (measurableSet_singleton _)))

def UniformGapAfter (M : SegmentModel State)
    (trig : Set (ℝ≥0 × State × ExitKind)) (c : ℝ≥0) (ε : ℝ) : Prop :=
  ∀ o ∈ trig, ENNReal.ofReal ε ≤ outStep M o (GapEvent c)

omit [MeasurableSpace State] in

theorem terminal_or_tendsto_of_frequently_gapEvent {c : ℝ≥0} (hc : 0 < c)
    (ω : ℕ → ℝ≥0 × State × ExitKind)
    (h : ∃ᶠ n in atTop, ω n ∈ GapEvent c) :
    (∃ n, isTerminal (ω n).2.2)
      ∨ Tendsto (fun n => jumpTimes n ω) atTop atTop := by
  by_cases hterm : ∃ n, isTerminal (ω n).2.2
  · exact Or.inl hterm
  push Not at hterm
  right
  have hdur : ∀ n, ω n ∈ GapEvent c → c ≤ (ω n).1 := fun n hn =>
    hn.resolve_right (hterm n)
  have hinf : {n | c ≤ (ω n).1}.Infinite :=
    Nat.frequently_atTop_iff_infinite.1 (h.mono fun n hn => hdur n hn)
  refine tendsto_atTop_atTop_of_monotone (jumpTimes_monotone ω) fun b => ?_

  obtain ⟨m, hm⟩ := exists_nat_ge (b / c)
  have hbm : b ≤ (m : ℝ≥0) * c := by
    calc b = b / c * c := (div_mul_cancel₀ b hc.ne').symm
    _ ≤ (m : ℝ≥0) * c := mul_le_mul_left hm c
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq m
  rcases t.eq_empty_or_nonempty with rfl | htne
  · refine ⟨0, hbm.trans ?_⟩
    simp only [Finset.card_empty] at htc
    subst htc
    simp
  refine ⟨t.max' htne, hbm.trans ?_⟩
  have hsub : t ⊆ Finset.range (t.max' htne + 1) := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (t.le_max' i hi))
  calc (m : ℝ≥0) * c = t.card • c := by rw [htc, nsmul_eq_mul]
    _ = ∑ _i ∈ t, c := (Finset.sum_const c).symm
    _ ≤ ∑ i ∈ t, (ω i).1 := Finset.sum_le_sum fun i hi => hts (Finset.mem_coe.mpr hi)
    _ ≤ ∑ i ∈ Finset.range (t.max' htne + 1), (ω i).1 :=
        Finset.sum_le_sum_of_subset hsub
    _ = jumpTimes (t.max' htne) ω := rfl

omit [MeasurableSpace State] in

theorem wz_free_sure {c : ℝ≥0} (hc : 0 < c)
    (ω : ℕ → ℝ≥0 × State × ExitKind) (h : ∀ n, ω n ∈ GapEvent c) :
    (∃ n, isTerminal (ω n).2.2)
      ∨ Tendsto (fun n => jumpTimes n ω) atTop atTop :=
  terminal_or_tendsto_of_frequently_gapEvent hc ω
    (Filter.Frequently.of_forall h)

section MarkovCondExp

variable {S : Type*} [MeasurableSpace S] {K : Kernel S S} [IsMarkovKernel K]

private lemma integral_comp_coord_succ {g : S → ℝ} (hg : Measurable g) (n : ℕ)
    (u : Π _i : Iic n, S) :
    ∫ y, g (y (n + 1))
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := Battery.mchain K) n u
      = ∫ z, g z ∂K (u ⟨n, mem_Iic.2 le_rfl⟩) := by
  have hmapK := DFunLike.congr_fun
    (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := Battery.mchain K) (a := n)) u
  rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
  rw [← Battery.mchain_apply, ← hmapK,
    integral_map_of_stronglyMeasurable (measurable_pi_apply _) hg.stronglyMeasurable]

private lemma condExp_comp_coord_succ {g : S → ℝ} {C : ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) (hgC : ∀ y, g y ≤ C) (x : S) (n : ℕ) :
    (Battery.pathMeasure K x)[fun ω : ℕ → S => g (ω (n + 1)) |
        Filtration.piLE (X := fun _ : ℕ => S) n]
      =ᵐ[Battery.pathMeasure K x] fun ω => ∫ z, g z ∂K (ω n) := by
  have hint : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (Battery.pathMeasure K x) := by
    refine (integrable_const C).mono'
      ((hg.comp (measurable_pi_apply (n + 1))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
    exact hgC _
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := Battery.mchain K)
    (Nat.zero_le n) (x₀ := fun _ => x) hint
  exact hcond.trans (Filter.Eventually.of_forall fun ω =>
    integral_comp_coord_succ hg n (Preorder.frestrictLe n ω))

end MarkovCondExp

private def bcSets (trig : Set (ℝ≥0 × State × ExitKind)) (c : ℝ≥0) :
    ℕ → Set (ℕ → ℝ≥0 × State × ExitKind)
  | 0 => ∅
  | k + 1 => (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig
      ∩ (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹' GapEvent c

variable (M : SegmentModel State) [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]

theorem ae_frequently_gapEvent {trig : Set (ℝ≥0 × State × ExitKind)}
    (htrig : MeasurableSet trig) {c : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (hgap : UniformGapAfter M trig c ε) (o₀ : ℝ≥0 × State × ExitKind) :
    ∀ᵐ ω ∂Battery.pathMeasure (outStep M) o₀,
      (∃ᶠ n in atTop, ω n ∈ trig) → ∃ᶠ n in atTop, ω n ∈ GapEvent c := by
  classical
  have hAmeas : ∀ k, MeasurableSet
      ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig) := fun k =>
    (measurable_pi_apply k) htrig
  have hBmeas : ∀ k, MeasurableSet
      ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹' GapEvent c) := fun k =>
    (measurable_pi_apply (k + 1)) (measurableSet_gapEvent c)
  have hsmeas : ∀ n, MeasurableSet[Filtration.piLE
      (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) n] (bcSets (State := State) trig c n) := by
    rintro (_ | k)
    · exact @MeasurableSet.empty _
        ((Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind)) 0)
    · exact ((Battery.measurable_coord_piLE k.le_succ) htrig).inter
        ((Battery.measurable_coord_piLE le_rfl) (measurableSet_gapEvent c))

  have hlevy := MeasureTheory.ae_mem_limsup_atTop_iff
    (Battery.pathMeasure (outStep M) o₀) hsmeas

  have hbound : ∀ k, ∀ᵐ ω ∂Battery.pathMeasure (outStep M) o₀,
      ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig).indicator
          (fun _ => ε) ω
        ≤ ((Battery.pathMeasure (outStep M) o₀)[
            (bcSets (State := State) trig c (k + 1)).indicator
              (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ) |
            Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) k]) ω := by
    intro k

    have hsplit : (bcSets (State := State) trig c (k + 1)).indicator
        (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ)
        = ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig).indicator 1
          * ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
              GapEvent c).indicator 1 := by
      rw [bcSets]
      exact Set.inter_indicator_one

    have hpull : (Battery.pathMeasure (outStep M) o₀)[
        (bcSets (State := State) trig c (k + 1)).indicator
          (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ) |
        Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) k]
        =ᵐ[Battery.pathMeasure (outStep M) o₀]
          ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig).indicator 1
            * (Battery.pathMeasure (outStep M) o₀)[
                ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
                  GapEvent c).indicator (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ) |
                Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) k] := by
      rw [hsplit]
      refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
      · exact stronglyMeasurable_const.indicator
          ((Battery.measurable_coord_piLE le_rfl) htrig)
      · rw [← Set.inter_indicator_one]
        exact (integrable_const (1 : ℝ)).indicator ((hAmeas k).inter (hBmeas k))
      · exact (integrable_const (1 : ℝ)).indicator (hBmeas k)

    have hcoordB : ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
        GapEvent c).indicator (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ)
        = fun ω => (GapEvent (State := State) c).indicator
            (1 : (ℝ≥0 × State × ExitKind) → ℝ) (ω (k + 1)) := by
      funext ω
      by_cases hω : ω (k + 1) ∈ GapEvent c
      · rw [Set.indicator_of_mem hω,
          Set.indicator_of_mem
            (show ω ∈ (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
              GapEvent c from hω)]
        simp only [Pi.one_apply]
      · rw [Set.indicator_of_notMem hω,
          Set.indicator_of_notMem
            (show ω ∉ (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
              GapEvent c from hω)]
    have hmarkov : (Battery.pathMeasure (outStep M) o₀)[
        ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω (k + 1)) ⁻¹'
          GapEvent c).indicator (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ) |
        Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) k]
        =ᵐ[Battery.pathMeasure (outStep M) o₀]
          fun ω => ∫ z, (GapEvent (State := State) c).indicator
            (1 : (ℝ≥0 × State × ExitKind) → ℝ) z ∂(outStep M (ω k)) := by
      rw [hcoordB]
      exact condExp_comp_coord_succ (C := 1)
        (measurable_const.indicator (measurableSet_gapEvent c))
        (fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
        (fun y => by
          by_cases hy : y ∈ GapEvent (State := State) c
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy]; exact zero_le_one) o₀ k
    filter_upwards [hpull, hmarkov] with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2, integral_indicator_one (measurableSet_gapEvent c)]
    by_cases hωA : ω ∈ (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig
    · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem hωA, Pi.one_apply, one_mul,
        measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hgap (ω k) hωA)
    · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωA, zero_mul]

  filter_upwards [hlevy, ae_all_iff.2 hbound] with ω hω hb hfreq

  have hinfA : Tendsto
      (fun n => ∑ k ∈ Finset.range n,
        ((fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig).indicator
          (fun _ => ε) ω)
      atTop atTop := by
    have hmem : ω ∈ atTop.limsup
        (fun k => (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω k) ⁻¹' trig) :=
      Filter.mem_limsup_iff_frequently_mem.2 (hfreq.mono fun n hn => hn)
    rw [Set.limsup_eq_tendsto_sum_indicator_atTop hε] at hmem
    exact hmem

  have hcond : Tendsto
      (fun n => ∑ k ∈ Finset.range n,
        ((Battery.pathMeasure (outStep M) o₀)[
          (bcSets (State := State) trig c (k + 1)).indicator
            (1 : (ℕ → ℝ≥0 × State × ExitKind) → ℝ) |
          Filtration.piLE (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) k]) ω)
      atTop atTop :=
    tendsto_atTop_mono (fun n => Finset.sum_le_sum fun k _ => hb k) hinfA
  have hfreqs : ∃ᶠ n in atTop, ω ∈ bcSets (State := State) trig c n :=
    Filter.mem_limsup_iff_frequently_mem.1 (hω.2 hcond)
  refine hfreqs.mono fun n hn => ?_
  rcases n with _ | k
  · exact absurd hn (Set.notMem_empty ω)
  · exact hn.2

theorem wz_free_of_forced_gap {c : ℝ≥0} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε)
    (hgap : UniformGapAfter M {o | o.2.2 = ExitKind.guard} c ε)
    (o₀ : ℝ≥0 × State × ExitKind) :
    ∀ᵐ ω ∂Battery.pathMeasure (outStep M) o₀,
      (∃ᶠ n in atTop, (ω n).2.2 = ExitKind.guard) →
        (∃ n, isTerminal (ω n).2.2)
          ∨ Tendsto (fun n => jumpTimes n ω) atTop atTop := by
  have htrig : MeasurableSet {o : ℝ≥0 × State × ExitKind | o.2.2 = ExitKind.guard} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton _)
  filter_upwards [ae_frequently_gapEvent M htrig hε hgap o₀] with ω hω hfreq
  exact terminal_or_tendsto_of_frequently_gapEvent hc ω (hω hfreq)

theorem wz_free_of_uniform_gap {c : ℝ≥0} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε)
    (hgap : UniformGapAfter M Set.univ c ε) (o₀ : ℝ≥0 × State × ExitKind) :
    ∀ᵐ ω ∂Battery.pathMeasure (outStep M) o₀,
      (∃ n, isTerminal (ω n).2.2)
        ∨ Tendsto (fun n => jumpTimes n ω) atTop atTop := by
  filter_upwards [ae_frequently_gapEvent M MeasurableSet.univ hε hgap o₀] with ω hω
  exact terminal_or_tendsto_of_frequently_gapEvent hc ω
    (hω (Filter.Frequently.of_forall fun n => Set.mem_univ _))

theorem le_reach_time_of_lipschitz {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {v : ℝ≥0} (hγ : LipschitzWith v γ)
    {G : Set E} {δ : ℝ} (hδ : ∀ y ∈ G, δ ≤ dist (γ 0) y)
    {t : ℝ} (ht : 0 ≤ t) (hG : γ t ∈ G) :
    δ / v ≤ t := by
  rcases eq_or_lt_of_le v.coe_nonneg with hv | hv
  · rw [← hv, div_zero]
    exact ht
  rw [div_le_iff₀ hv]
  calc δ ≤ dist (γ 0) (γ t) := hδ _ hG
    _ = dist (γ t) (γ 0) := dist_comm _ _
    _ ≤ v * dist t 0 := hγ.dist_le_mul t 0
    _ = v * t := by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht]
    _ = t * v := mul_comm _ _

theorem le_segMeasureFin_gapEvent {γ : ℝ → State} {r : ℝ → ℝ} {T Λ : ℝ}
    {k : ExitKind} (hr : Continuous r) (hr0 : ∀ u, 0 ≤ r u) (hrΛ : ∀ u, r u ≤ Λ)
    (hγ : Measurable γ) {c : ℝ≥0} (hcT : (c : ℝ) ≤ T) :
    ENNReal.ofReal (Real.exp (-(Λ * c))) ≤ segMeasureFin γ r T k (GapEvent c) := by
  have hmap : Measurable fun u : ℝ => (Real.toNNReal u, γ u, ExitKind.alarm) :=
    measurable_real_toNNReal.prodMk (hγ.prodMk measurable_const)
  have hGap := measurableSet_gapEvent (State := State) c

  have hatom : (Real.toNNReal T, γ T, k) ∈ GapEvent (State := State) c := by
    refine Or.inl ?_
    calc c = Real.toNNReal (c : ℝ) := (Real.toNNReal_coe).symm
    _ ≤ Real.toNNReal T := Real.toNNReal_mono hcT

  have hpre : Set.Ioc (c : ℝ) T ⊆
      ((fun u : ℝ => (Real.toNNReal u, γ u, ExitKind.alarm)) ⁻¹'
        GapEvent (State := State) c) ∩ Set.Ioc 0 T := by
    intro u hu
    refine ⟨Or.inl ?_, ⟨lt_of_le_of_lt c.coe_nonneg hu.1, hu.2⟩⟩
    calc c = Real.toNNReal (c : ℝ) := (Real.toNNReal_coe).symm
    _ ≤ Real.toNNReal u := Real.toNNReal_mono hu.1.le

  have hcont : Continuous fun u => r u * Real.exp (-(cumInt r u)) :=
    hr.mul (Real.continuous_exp.comp (cumInt_continuous hr).neg)
  have hFTC : ∫ u in (c : ℝ)..T, r u * Real.exp (-(cumInt r u))
      = Real.exp (-(cumInt r c)) - Real.exp (-(cumInt r T)) := by
    have hderiv : ∀ u ∈ Set.uIcc (c : ℝ) T,
        HasDerivAt (fun s => -Real.exp (-(cumInt r s)))
          (r u * Real.exp (-(cumInt r u))) u := by
      intro u _
      have h1 := ((Real.hasDerivAt_exp (-(cumInt r u))).comp u
        (cumInt_hasDerivAt hr u).neg).neg
      have heq : -(Real.exp (-(cumInt r u)) * -(r u))
          = r u * Real.exp (-(cumInt r u)) := by ring
      rw [heq] at h1
      exact h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable _ _)]
    ring

  rw [segMeasureFin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hmap hGap, Measure.dirac_apply' _ hGap,
    Set.indicator_of_mem hatom, Pi.one_apply, mul_one]
  have halarm : ENNReal.ofReal
      (Real.exp (-(cumInt r c)) - Real.exp (-(cumInt r T)))
      ≤ ((volume.restrict (Set.Ioc 0 T)).withDensity
          fun u => ENNReal.ofReal (r u * Real.exp (-(cumInt r u))))
        ((fun u : ℝ => (Real.toNNReal u, γ u, ExitKind.alarm)) ⁻¹'
          GapEvent (State := State) c) := by
    have hdens : Measurable fun u : ℝ =>
        ENNReal.ofReal (r u * Real.exp (-(cumInt r u))) :=
      ENNReal.measurable_ofReal.comp hcont.measurable
    rw [withDensity_apply _ (hmap hGap), Measure.restrict_restrict (hmap hGap)]
    have hint : MeasureTheory.IntegrableOn
        (fun u => r u * Real.exp (-(cumInt r u))) (Set.Ioc (c : ℝ) T) volume :=
      (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    calc ENNReal.ofReal (Real.exp (-(cumInt r c)) - Real.exp (-(cumInt r T)))
        = ∫⁻ u in Set.Ioc (c : ℝ) T,
            ENNReal.ofReal (r u * Real.exp (-(cumInt r u))) ∂volume := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun u =>
              mul_nonneg (hr0 u) (Real.exp_pos _).le),
            ← intervalIntegral.integral_of_le hcT, hFTC]
      _ ≤ _ := lintegral_mono_set hpre
  refine le_trans ?_ (add_le_add halarm le_rfl)

  have hRc : cumInt r c ≤ Λ * c := by
    calc cumInt r c ≤ ∫ _u in (0 : ℝ)..c, Λ :=
          intervalIntegral.integral_mono_on c.coe_nonneg
            (hr.intervalIntegrable _ _) intervalIntegrable_const
            (fun u _ => hrΛ u)
    _ = Λ * c := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  have hRcT : cumInt r c ≤ cumInt r T := by
    have : cumInt r T - cumInt r c = ∫ u in (c : ℝ)..T, r u := by
      rw [cumInt, cumInt, ← intervalIntegral.integral_add_adjacent_intervals
        (hr.intervalIntegrable 0 c) (hr.intervalIntegrable c T)]
      ring
    linarith [intervalIntegral.integral_nonneg (μ := volume) hcT (fun u _ => hr0 u), this]
  calc ENNReal.ofReal (Real.exp (-(Λ * c)))
      ≤ ENNReal.ofReal (Real.exp (-(cumInt r c))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg hRc))
    _ = ENNReal.ofReal ((Real.exp (-(cumInt r c)) - Real.exp (-(cumInt r T)))
          + Real.exp (-(cumInt r T))) := by congr 1; ring
    _ = ENNReal.ofReal (Real.exp (-(cumInt r c)) - Real.exp (-(cumInt r T)))
          + ENNReal.ofReal (Real.exp (-(cumInt r T))) :=
        ENNReal.ofReal_add
          (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg hRcT))) (Real.exp_pos _).le

end Qtsl.LayerD
