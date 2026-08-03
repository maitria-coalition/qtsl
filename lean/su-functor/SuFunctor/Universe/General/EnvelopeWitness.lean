import Mathlib.Topology.Instances.Nat
import SuFunctor.Universe.General.EnvelopeCoherent

/-! # The excluded class is inhabited: witnesses on `ℕ`

Two coherent lower previsions on the bounded (continuous) gambles of the
discrete carrier `ℕ` calibrate the σ-smoothness hypothesis of the
countably additive envelope theorem.  On a discrete carrier every
bounded gamble is continuous, so the continuous-face and Borel-face
gamble domains coincide and no domain quibble survives.

* `liminfLP`, the limit-inferior prevision: coherent
  (`isCoherentLP_liminfLP`), **not** σ-smooth
  (`not_sigmaSmoothAtZero_conjUpper_liminfLP`), and its countably
  additive credal set is **empty** (`caCredal_liminfLP_eq_empty`) — the
  identification with a countably additive envelope fails maximally.
  Classically its dominating functionals are the diffuse finitely
  additive charges vanishing on finite sets (the Banach-limit family);
  none of them is a measure, and this module kernel-checks exactly that
  none of them is.
* Consequently the envelope representation **without** the σ-smoothness
  hypothesis is false as stated
  (`not_forall_coherent_caCredal_nonempty`) — the semantic form of the
  hypothesis-deletion mutant, itself a theorem.
* `vacuousLP`, the vacuous prevision `g ↦ ⨅ k, g k`: coherent, its
  credal set is everything (`caCredal_vacuousLP_eq_univ`) and the
  countably additive envelope does represent it — but attainment fails
  at the strictly positive gamble `k ↦ 1/(k+1)`
  (`vacuousLP_not_attained`), and it is not σ-smooth either
  (`not_sigmaSmoothAtZero_conjUpper_vacuousLP`).  Representation and
  attainment are separated.
-/

namespace SuFunctor.Universe.General

open BoundedContinuousFunction Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

namespace EnvelopeWitness

/-! ## Bounded gambles on a discrete carrier -/

/-- Package a bounded function on `ℕ` as a bounded continuous gamble. -/
noncomputable def ofBounded (f : ℕ → ℝ) (C : ℝ) (hC : ∀ k, |f k| ≤ C) :
    ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f
    (continuous_of_discreteTopology) C
    (fun k => by simpa [Real.norm_eq_abs] using hC k)

@[simp] theorem ofBounded_apply (f : ℕ → ℝ) (C : ℝ) (hC : ∀ k, |f k| ≤ C)
    (k : ℕ) : ofBounded f C hC k = f k := rfl

/-- The tail indicator gamble of `{k | n ≤ k}`. -/
noncomputable def tailInd (n : ℕ) : ℕ →ᵇ ℝ :=
  ofBounded (Set.indicator {k : ℕ | n ≤ k} 1) 1 (fun k => by
    by_cases h : n ≤ k <;>
      simp [Set.mem_setOf_eq, h])

theorem tailInd_apply_of_le {n k : ℕ} (h : n ≤ k) : tailInd n k = 1 := by
  simp [tailInd, Set.mem_setOf_eq, h]

theorem tailInd_apply_of_lt {n k : ℕ} (h : k < n) : tailInd n k = 0 := by
  simp [tailInd, Set.mem_setOf_eq, not_le.mpr h]

theorem tailInd_antitone (n k : ℕ) : tailInd (n + 1) k ≤ tailInd n k := by
  rcases le_or_gt (n + 1) k with h | h
  · rw [tailInd_apply_of_le h, tailInd_apply_of_le (le_trans (Nat.le_succ n) h)]
  · rw [tailInd_apply_of_lt h]
    rcases le_or_gt n k with h' | h'
    · rw [tailInd_apply_of_le h']; norm_num
    · rw [tailInd_apply_of_lt h']

theorem tailInd_tendsto_zero (k : ℕ) :
    Tendsto (fun n => tailInd n k) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop k] with n hn
  exact (tailInd_apply_of_lt hn).symm

/-! ## Boundedness bookkeeping for sequences from gambles -/

theorem isBoundedUnder_le_bcf (g : ℕ →ᵇ ℝ) :
    IsBoundedUnder (· ≤ ·) atTop (fun k => g k) :=
  ⟨‖g‖, eventually_map.mpr (Eventually.of_forall fun k => bcf_le_norm g k)⟩

theorem isBoundedUnder_ge_bcf (g : ℕ →ᵇ ℝ) :
    IsBoundedUnder (· ≥ ·) atTop (fun k => g k) :=
  ⟨-‖g‖, eventually_map.mpr (Eventually.of_forall fun k => bcf_neg_norm_le g k)⟩

/-! ## The limit-inferior prevision -/

/-- The limit-inferior prevision on bounded gambles over `ℕ`. -/
noncomputable def liminfLP : (ℕ →ᵇ ℝ) → ℝ :=
  fun g => liminf (fun k => g k) atTop

theorem isCoherentLP_liminfLP : IsCoherentLP liminfLP where
  inf_le g := by
    refine le_liminf_of_le (isBoundedUnder_le_bcf g).isCoboundedUnder_ge ?_
    exact Eventually.of_forall fun k => ciInf_le (bddBelow_range_bcf g) k
  homog c hc g := by
    rcases eq_or_lt_of_le hc with rfl | hc
    · simp only [liminfLP, zero_smul, zero_mul]
      have : (fun k => (0 : ℕ →ᵇ ℝ) k) = fun _ => (0 : ℝ) := by
        funext k; simp
      rw [this, liminf_const]
    · have hmono : Monotone fun x : ℝ => c * x :=
        fun a b hab => mul_le_mul_of_nonneg_left hab (le_of_lt hc)
    -- `c * liminf u = liminf (c * u)` via the monotone-map lemma
      have hmap := hmono.map_liminf_of_continuousAt (F := atTop)
        (fun k => g k)
        ((continuous_const.mul continuous_id).continuousAt)
        (isBoundedUnder_le_bcf g).isCoboundedUnder_ge
        (isBoundedUnder_ge_bcf g)
      simp only [liminfLP]
      have hcoe : (fun k => (c • g) k) = fun k => c * g k := by
        funext k; simp
      rw [hcoe]
      simpa [Function.comp_def] using hmap.symm
  superadd f g := by
    have hadd := le_liminf_add (f := atTop)
      (u := fun k => f k) (v := fun k => g k)
      (isBoundedUnder_ge_bcf f) (isBoundedUnder_le_bcf f)
      (isBoundedUnder_ge_bcf g) (isBoundedUnder_le_bcf g).isCoboundedUnder_ge
    have hcoe : (fun k => (f + g) k) = (fun k => f k) + fun k => g k := by
      funext k; simp
    simp only [liminfLP]
    rw [hcoe]
    exact hadd

/-- The conjugate of the limit-inferior prevision holds the tail
indicators at height one. -/
theorem conjUpper_liminfLP_tailInd (n : ℕ) :
    conjUpper liminfLP (tailInd n) = 1 := by
  have hev : (fun k => (-(tailInd n)) k) =ᶠ[atTop] fun _ => (-1 : ℝ) := by
    filter_upwards [eventually_ge_atTop n] with k hk
    simp [tailInd_apply_of_le hk]
  simp only [conjUpper, liminfLP]
  rw [liminf_congr hev, liminf_const]
  norm_num

/-- The limit-inferior prevision is not σ-smooth: the tail indicators
are antitone and pointwise null, but the conjugate holds them at one. -/
theorem not_sigmaSmoothAtZero_conjUpper_liminfLP :
    ¬ SigmaSmoothAtZero (conjUpper liminfLP) := by
  intro hs
  have h := hs tailInd (fun n k => tailInd_antitone n k) tailInd_tendsto_zero
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    refine h.congr fun n => ?_
    exact conjUpper_liminfLP_tailInd n
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hone)

/-- The tail sets shrink to nothing. -/
theorem iInter_tail_eq_empty : (⋂ n : ℕ, {k : ℕ | n ≤ k}) = ∅ := by
  ext k
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_forall, not_le]
  exact ⟨k + 1, Nat.lt_succ_self k⟩

/-- **The countably additive credal set of the limit-inferior prevision
is empty**: a countably additive probability dominating it would give
every tail set full mass, against continuity from above at the empty
intersection.  (Classically the dominating set is the nonempty family
of diffuse finitely additive charges — Banach limits; none is a
measure, and this is the kernel-checked half of that statement.) -/
theorem caCredal_liminfLP_eq_empty : caCredal (X := ℕ) liminfLP = ∅ := by
  ext μ
  simp only [mem_caCredal_iff, Set.mem_empty_iff_false, iff_false, not_forall]
  by_contra hall
  push Not at hall
  have htail : ∀ n : ℕ, (μ : Measure ℕ) {k : ℕ | n ≤ k} = 1 := by
    intro n
    have hdom := hall (tailInd n)
    have hlim : liminfLP (tailInd n) = 1 := by
      have hev : (fun k => tailInd n k) =ᶠ[atTop] fun _ => (1 : ℝ) := by
        filter_upwards [eventually_ge_atTop n] with k hk
        exact tailInd_apply_of_le hk
      simp only [liminfLP]
      rw [liminf_congr hev, liminf_const]
    have hint : ∫ k, tailInd n k ∂(μ : Measure ℕ)
        = (μ : Measure ℕ).real {k : ℕ | n ≤ k} := by
      have : (fun k => tailInd n k) = Set.indicator {k : ℕ | n ≤ k} 1 := by
        funext k; simp [tailInd]
      rw [this]
      exact integral_indicator_one (MeasurableSet.of_discrete)
    rw [hlim, hint] at hdom
    have hle : (μ : Measure ℕ).real {k : ℕ | n ≤ k} ≤ 1 := by
      have hmono := measure_mono (μ := (μ : Measure ℕ))
        (Set.subset_univ {k : ℕ | n ≤ k})
      have huniv : (μ : Measure ℕ) Set.univ = 1 := measure_univ
      have : ((μ : Measure ℕ) {k : ℕ | n ≤ k}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) (huniv ▸ hmono)
      simp at this
      exact this
    have hreal : (μ : Measure ℕ).real {k : ℕ | n ≤ k} = 1 := le_antisymm hle hdom
    have hreal' : ((μ : Measure ℕ) {k : ℕ | n ≤ k}).toReal = 1 := hreal
    exact (ENNReal.toReal_eq_one_iff _).mp hreal'
  have hcont := tendsto_measure_iInter_atTop (μ := (μ : Measure ℕ))
    (s := fun n => {k : ℕ | n ≤ k})
    (fun n => (MeasurableSet.of_discrete).nullMeasurableSet)
    (fun a b hab => Set.setOf_subset_setOf.mpr fun k hk => le_trans hab hk)
    ⟨0, measure_ne_top _ _⟩
  rw [iInter_tail_eq_empty] at hcont
  simp only [measure_empty] at hcont
  have hconst : Tendsto (fun n => (μ : Measure ℕ) {k : ℕ | n ≤ k})
      atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr fun n => ?_
    exact (htail n).symm
  have : (1 : ℝ≥0∞) = 0 :=
    tendsto_nhds_unique hconst hcont
  exact one_ne_zero this

/-- **The identification without σ-smoothness is false**: the semantic
form of the hypothesis-deletion mutant, itself a theorem.  There is a
coherent lower prevision on the bounded gambles of a Polish carrier
whose countably additive credal set is empty. -/
theorem not_forall_coherent_caCredal_nonempty :
    ¬ ∀ P : (ℕ →ᵇ ℝ) → ℝ, IsCoherentLP P → (caCredal P).Nonempty := by
  intro h
  have hne := h liminfLP isCoherentLP_liminfLP
  rw [caCredal_liminfLP_eq_empty] at hne
  exact Set.not_nonempty_empty hne

/-! ## The vacuous prevision: representation without attainment -/

/-- The vacuous lower prevision on bounded gambles over `ℕ`. -/
noncomputable def vacuousLP : (ℕ →ᵇ ℝ) → ℝ := fun g => ⨅ k, g k

theorem isCoherentLP_vacuousLP : IsCoherentLP vacuousLP where
  inf_le g := le_refl _
  homog c hc g := by
    simp only [vacuousLP]
    have hcoe : ∀ k, (c • g) k = c * g k := fun k => by simp
    calc ⨅ k, (c • g) k = ⨅ k, c * g k := by simp only [hcoe]
      _ = c * ⨅ k, g k := by
          rcases eq_or_lt_of_le hc with rfl | hc
          · simp
          · exact (Real.mul_iInf_of_nonneg (le_of_lt hc) _).symm
  superadd f g := by
    simp only [vacuousLP]
    refine le_ciInf fun k => ?_
    have := add_le_add (ciInf_le (bddBelow_range_bcf f) k)
      (ciInf_le (bddBelow_range_bcf g) k)
    simpa using this

/-- Every countably additive probability dominates the vacuous
prevision: its credal set is everything. -/
theorem caCredal_vacuousLP_eq_univ :
    caCredal (X := ℕ) vacuousLP = Set.univ := by
  ext μ
  simp only [mem_caCredal_iff, Set.mem_univ, iff_true]
  intro g
  have hint : ∫ k, (⨅ j, g j) ∂(μ : Measure ℕ) = ⨅ j, g j := by
    simp
  calc vacuousLP g = ∫ _, (⨅ j, g j) ∂(μ : Measure ℕ) := (hint).symm
    _ ≤ ∫ k, g k ∂(μ : Measure ℕ) := by
        refine integral_mono (integrable_const _) (g.integrable _) ?_
        exact fun k => ciInf_le (bddBelow_range_bcf g) k

/-- The vacuous prevision is represented by its credal set: the
envelope display holds with an infimum (Dirac evaluations approximate),
even though — next theorem — the infimum is not attained. -/
theorem vacuousLP_eq_iInf_dirac (g : ℕ →ᵇ ℝ) :
    vacuousLP g = ⨅ k, ∫ x, g x ∂((MeasureTheory.Measure.dirac k :
      Measure ℕ)) := by
  have hdir : (fun k : ℕ => ∫ x, g x ∂(MeasureTheory.Measure.dirac k))
      = fun k => g k := funext fun k => integral_dirac _ k
  simp only [vacuousLP, hdir]

/-- The strictly positive gamble `k ↦ 1/(k+1)`. -/
noncomputable def strictPos : ℕ →ᵇ ℝ :=
  ofBounded (fun k => 1 / (k + 1)) 1 (fun k => by
    rw [abs_of_pos (by positivity)]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) k])

theorem strictPos_apply (k : ℕ) : strictPos k = 1 / (k + 1) := rfl

theorem strictPos_pos (k : ℕ) : 0 < strictPos k := by
  rw [strictPos_apply]; positivity

theorem vacuousLP_strictPos : vacuousLP strictPos = 0 := by
  simp only [vacuousLP]
  refine le_antisymm ?_ (le_ciInf fun k => (strictPos_pos k).le)
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (⨅ k, strictPos k))
  have hpos : 0 < ⨅ k, strictPos k := hlt
  have hle : (⨅ k, strictPos k) ≤ strictPos n :=
    ciInf_le (bddBelow_range_bcf strictPos) n
  rw [strictPos_apply] at hle
  have hn' : 1 / (⨅ k, strictPos k) < n + 1 := hn.trans (by linarith)
  have := (div_lt_iff₀ hpos).mp hn'
  have h2 : (1 : ℝ) / (n + 1) < ⨅ k, strictPos k := by
    rw [div_lt_iff₀ (by positivity)]
    linarith [mul_comm ((n : ℝ) + 1) (⨅ k, strictPos k)]
  linarith

/-- Every countably additive probability on `ℕ` charges some point. -/
theorem exists_singleton_pos (μ : ProbabilityMeasure ℕ) :
    ∃ k : ℕ, 0 < (μ : Measure ℕ) {k} := by
  by_contra h
  push Not at h
  have hz : ∀ k : ℕ, (μ : Measure ℕ) {k} = 0 := fun k =>
    le_antisymm (h k) zero_le
  have huniv : (μ : Measure ℕ) Set.univ = 0 := by
    have hcover : (Set.univ : Set ℕ) = ⋃ k : ℕ, {k} := by
      simp [Set.iUnion_of_singleton]
    rw [hcover]
    refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le
    simp [hz]
  rw [measure_univ] at huniv
  exact one_ne_zero huniv

/-- **Attainment fails for the vacuous prevision**: on the strictly
positive gamble the envelope value `0` is approached but never attained
— every countably additive probability on `ℕ` charges an atom, so its
expectation stays strictly positive.  Representation and attainment
come apart exactly where σ-smoothness fails. -/
theorem vacuousLP_not_attained (μ : ProbabilityMeasure ℕ) :
    vacuousLP strictPos < ∫ k, strictPos k ∂(μ : Measure ℕ) := by
  rw [vacuousLP_strictPos]
  obtain ⟨k, hk⟩ := exists_singleton_pos μ
  have hmeas : (μ : Measure ℕ).real {k} ≠ 0 := by
    simp only [Measure.real]
    exact ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hk, measure_ne_top _ _⟩
  have hmr : 0 < (μ : Measure ℕ).real {k} :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmeas)
  have hlow : ∀ j, strictPos k * Set.indicator {k} (1 : ℕ → ℝ) j
      ≤ strictPos j := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj, (strictPos_pos j).le]
  have hint : ∫ j, strictPos k * Set.indicator {k} (1 : ℕ → ℝ) j
      ∂(μ : Measure ℕ) = strictPos k * (μ : Measure ℕ).real {k} := by
    rw [integral_const_mul]
    rw [integral_indicator_one (MeasurableSet.of_discrete)]
  have hmono : ∫ j, strictPos k * Set.indicator {k} (1 : ℕ → ℝ) j
      ∂(μ : Measure ℕ) ≤ ∫ j, strictPos j ∂(μ : Measure ℕ) := by
    refine integral_mono ?_ (strictPos.integrable _) hlow
    have : Integrable (Set.indicator {k} (1 : ℕ → ℝ)) (μ : Measure ℕ) := by
      refine Integrable.indicator ?_ MeasurableSet.of_discrete
      exact integrable_const _
    exact this.const_mul _
  have hpos : 0 < strictPos k * (μ : Measure ℕ).real {k} :=
    mul_pos (strictPos_pos k) hmr
  linarith [hint ▸ hmono]

/-- The vacuous prevision is not σ-smooth either. -/
theorem not_sigmaSmoothAtZero_conjUpper_vacuousLP :
    ¬ SigmaSmoothAtZero (conjUpper vacuousLP) := by
  intro hs
  have h := hs tailInd (fun n k => tailInd_antitone n k) tailInd_tendsto_zero
  have hval : ∀ n, conjUpper vacuousLP (tailInd n) = 1 := by
    intro n
    simp only [conjUpper, vacuousLP]
    have hinf : (⨅ k, (-(tailInd n)) k) = -1 := by
      refine le_antisymm ?_ (le_ciInf fun k => ?_)
      · have hle := ciInf_le (bddBelow_range_bcf (-(tailInd n))) n
        have hval : (-(tailInd n)) n = -1 := by
          simp [tailInd_apply_of_le (le_refl n)]
        rw [hval] at hle
        exact hle
      · have hb : (-(tailInd n)) k = -(tailInd n k) := by simp
        rw [hb]
        rcases le_or_gt n k with hk | hk
        · rw [tailInd_apply_of_le hk]
        · rw [tailInd_apply_of_lt hk]; norm_num
    rw [hinf]
    norm_num
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    refine h.congr fun n => hval n
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hone)

end EnvelopeWitness

end SuFunctor.Universe.General
