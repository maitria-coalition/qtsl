import QtslAux.LayerD.Deadline

/-! # Timed until: avoidance within a deadline for GSHS

This module combines an untimed avoidance certificate (rate `θ = 0`) with the
exponential deadline certificate of `QtslAux.LayerD.Deadline` to
bound timed until/safety properties of the timed skeleton `tskel M`.

* `tCert_zero_eq`, `tCert_zero_le`, `tbadIn_floor_zero`: at rate `θ = 0` the
  clock weight is trivial, so an avoidance certificate transfers to the timed
  skeleton unchanged.
* `sound_GSHS_avoid_timed`: the probability that the timed skeleton ever
  visits a state of `Us` is at most `Va x`, for `Va` bounded, at least `1` on
  `Us`, and satisfying `SegmentDynkin M 0 Va` with `ForcedNonexpansion`.
* `sound_GSHS_until`: a union bound combining avoidance with a deadline
  certificate `Vd ≥ ε` at rate `θ`: the probability of ever visiting `Us` or
  ever exceeding the deadline `T` is at most
  `Va x + exp (-θT) * Vd x / ε`.
* `sound_GSHS_until_battery`: the complementary lower bound — the probability
  that the path forever avoids `Us` while the clock stays within `T` is at
  least `p`, given thresholds `Va x ≤ thra`, `Vd x ≤ thrd` and
  `p + (thra + exp (-θT) * thrd / ε) ≤ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

variable {M : SegmentModel State}

omit [MeasurableSpace State] in

lemma tCert_zero_eq (V : State → ℝ) : ∀ q : TSkelState State,
    tCert 0 V q = Sum.elim (fun p : ℝ≥0 × State => V p.2)
      (Sum.elim (fun p : ℝ≥0 × State => V p.2) fun _ => 0) q := by
  rintro (p | p | u) <;> simp [tCert]

omit [MeasurableSpace State] in
lemma tCert_zero_le {V : State → ℝ} {C : ℝ} (hVC : ∀ y, V y ≤ C)
    (hC0 : 0 ≤ C) : ∀ q : TSkelState State, tCert 0 V q ≤ C := by
  intro q
  rw [tCert_zero_eq]
  rcases q with p | p | u
  · exact hVC p.2
  · exact hVC p.2
  · exact hC0

omit [MeasurableSpace State] in

lemma tbadIn_floor_zero {V : State → ℝ} {Us : Set State}
    (hFloor : ∀ y ∈ Us, 1 ≤ V y) :
    ∀ q ∈ tbadIn (State := State) Us, 1 ≤ tCert 0 V q := by
  rintro (p | p | u) hq
  · rw [tCert_zero_eq]; exact hFloor p.2 hq
  · rw [tCert_zero_eq]; exact hFloor p.2 hq
  · exact hq.elim

lemma tskel_drift_real [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ : ℝ} (hV : Measurable V)
    (hSegD : SegmentDynkin M θ V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (q : TSkelState State) :
    ∫ w, tCert θ V w ∂(tskel M q) ≤ tCert θ V q := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w => tCert_nonneg hNonneg θ w)
    ((measurable_tCert hV θ).aestronglyMeasurable)]
  calc (∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tskel M q)).toReal
      ≤ (ENNReal.ofReal (tCert θ V q)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (tskel_drift hV hSegD hForce hNonneg q)
    _ = tCert θ V q := ENNReal.toReal_ofReal (tCert_nonneg hNonneg θ q)

theorem sound_GSHS_avoid_timed [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va : State → ℝ} {Us : Set State}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hSegD : SegmentDynkin M 0 Va) (hForce : ForcedNonexpansion M Va)
    (hNonneg : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloor : ∀ y ∈ Us, 1 ≤ Va y) (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, ω n ∈ tbadIn Us}
      ≤ ENNReal.ofReal (Va x) := by
  have h := Battery.measure_reach_le (K := tskel M)
    (measurableSet_tbadIn hUs) (measurable_tCert hVa 0)
    (tCert_nonneg hNonneg 0) (tCert_zero_le hVC hC0)
    (tbadIn_floor_zero hFloor)
    (fun q _ => tskel_drift_real hVa hSegD hForce hNonneg q)
    (TSkelState.alive (0, x))
  have hstart : tCert 0 Va (TSkelState.alive (0, x)) = Va x := by
    rw [tCert_zero_eq]
    rfl
  rw [hstart] at h
  exact h

theorem sound_GSHS_until [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va Vd : State → ℝ} {Us : Set State} {θ ε : ℝ} {T : ℝ≥0}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hSegDa : SegmentDynkin M 0 Va) (hForcea : ForcedNonexpansion M Va)
    (hNonnega : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloora : ∀ y ∈ Us, 1 ≤ Va y)
    (hVd : Measurable Vd) (hθ : 0 ≤ θ)
    (hSegDd : SegmentDynkin M θ Vd) (hForced : ForcedNonexpansion M Vd)
    (hNonnegd : NonnegV Vd) (hε : 0 < ε) (hFloord : ∀ y, ε ≤ Vd y)
    (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)}
      ≤ ENNReal.ofReal (Va x)
        + ENNReal.ofReal (Real.exp (-(θ * T)) * Vd x / ε) := by
  have hsplit : {ω : ℕ → TSkelState State |
        ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)}
      = {ω : ℕ → TSkelState State | ∃ n, ω n ∈ tbadIn Us}
        ∪ {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n)} := by
    ext ω
    constructor
    · rintro ⟨n, h | h⟩
      · exact Or.inl ⟨n, h⟩
      · exact Or.inr ⟨n, h⟩
    · rintro (⟨n, h⟩ | ⟨n, h⟩)
      · exact ⟨n, Or.inl h⟩
      · exact ⟨n, Or.inr h⟩
  rw [hsplit]
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · exact sound_GSHS_avoid_timed hVa hUs hSegDa hForcea hNonnega hC0 hVC
      hFloora x
  · exact sound_GSHS_deadline hVd hθ hSegDd hForced hNonnegd hε hFloord x

lemma measurableSet_untilFail {Us : Set State} (hUs : MeasurableSet Us)
    (T : ℝ≥0) :
    MeasurableSet {ω : ℕ → TSkelState State |
      ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)} := by
  have h : {ω : ℕ → TSkelState State | ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)}
      = ⋃ n, (fun ω : ℕ → TSkelState State => ω n) ⁻¹'
          (tbadIn Us ∪ tbad T) := by
    ext ω
    constructor
    · rintro ⟨n, h | h⟩
      · exact Set.mem_iUnion.2 ⟨n, Or.inl h⟩
      · refine Set.mem_iUnion.2 ⟨n, Or.inr ?_⟩
        rw [tbad_eq_clock]
        exact h
    · intro hmem
      rcases Set.mem_iUnion.1 hmem with ⟨n, hn | hn⟩
      · exact ⟨n, Or.inl hn⟩
      · rw [tbad_eq_clock] at hn
        exact ⟨n, Or.inr hn⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => (measurable_pi_apply n)
    ((measurableSet_tbadIn hUs).union measurableSet_tbad)

theorem sound_GSHS_until_battery [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Va Vd : State → ℝ} {Us : Set State} {θ ε p thra thrd : ℝ} {T : ℝ≥0}
    (hVa : Measurable Va) (hUs : MeasurableSet Us)
    (hSegDa : SegmentDynkin M 0 Va) (hForcea : ForcedNonexpansion M Va)
    (hNonnega : NonnegV Va) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, Va y ≤ C)
    (hFloora : ∀ y ∈ Us, 1 ≤ Va y)
    (hVd : Measurable Vd) (hθ : 0 ≤ θ)
    (hSegDd : SegmentDynkin M θ Vd) (hForced : ForcedNonexpansion M Vd)
    (hNonnegd : NonnegV Vd) (hε : 0 < ε) (hFloord : ∀ y, ε ≤ Vd y)
    (hΘ : p + (thra + Real.exp (-(θ * T)) * thrd / ε) ≤ 1)
    (x : State) (hthra : Va x ≤ thra) (hthrd : Vd x ≤ thrd) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
      {ω | ∀ n, ω n ∉ tbadIn Us ∧ tclock (ω n) ≤ T} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]
    exact zero_le
  have hthra0 : 0 ≤ thra := (hNonnega x).trans hthra
  have hthrd0 : 0 ≤ thrd := (hNonnegd x).trans hthrd
  have hq0 : 0 ≤ thra + Real.exp (-(θ * T)) * thrd / ε := by
    have : 0 ≤ Real.exp (-(θ * T)) * thrd / ε :=
      div_nonneg (mul_nonneg (Real.exp_nonneg _) hthrd0) hε.le
    linarith

  have hfail := sound_GSHS_until (T := T) hVa hUs hSegDa hForcea hNonnega
    hC0 hVC hFloora hVd hθ hSegDd hForced hNonnegd hε hFloord x
  have hmono : ENNReal.ofReal (Va x)
      + ENNReal.ofReal (Real.exp (-(θ * T)) * Vd x / ε)
      ≤ ENNReal.ofReal (thra + Real.exp (-(θ * T)) * thrd / ε) := by
    have h1 : Real.exp (-(θ * T)) * Vd x / ε
        ≤ Real.exp (-(θ * T)) * thrd / ε := by gcongr
    rw [ENNReal.ofReal_add hthra0
      (div_nonneg (mul_nonneg (Real.exp_nonneg _) hthrd0) hε.le)]
    exact add_le_add (ENNReal.ofReal_le_ofReal hthra)
      (ENNReal.ofReal_le_ofReal h1)
  have h1 := hfail.trans hmono

  have hnever : {ω : ℕ → TSkelState State |
        ∀ n, ω n ∉ tbadIn Us ∧ tclock (ω n) ≤ T}
      = {ω : ℕ → TSkelState State |
          ∃ n, ω n ∈ tbadIn Us ∨ T < tclock (ω n)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_or,
      not_lt]
  rw [hnever, prob_compl_eq_one_sub (measurableSet_untilFail hUs T)]
  refine le_trans ?_ (tsub_le_tsub_left h1 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add hq0 hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Qtsl.LayerD
