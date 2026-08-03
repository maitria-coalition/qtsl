import QtslAux.LayerD.Skeleton
import QtslAux.QStreett

/-! # Streett acceptance for GSHS skeletons via ranking supermartingales

This module proves soundness of Streett (recurrence–response) acceptance
conditions for the skeleton chain of a segment model: along almost every path
that stays confined, every Streett pair `(Rq i, G i)` that is requested
infinitely often is granted infinitely often.

Structural side conditions on the segment model over the confinement region:
`NoVanish` (no `live` exits), `HaltsCaught` (halts land in a designated set),
and `ResetsInto` (resets land in a designated set almost surely). These combine
through `skel_step_full` into the one-step certainty statements `skel_R3` and
`skel_R4` for the skeleton kernel.

Quantitative certificates: `RankingSegmentDynkin M Sc V ε` strengthens the
segment Dynkin inequality by an additive drop `ε` on the region `Sc`, and
`skel_drift_ranking` / `skel_drift_ranking_real` transfer this strict drift to
the skeleton. `skelIn A` lifts a state set to alive skeleton states only.

Main results, for a countable family of Streett pairs (`Bundle` section):

* `sound_GSHS_streett_bundle_confined` / `sound_GSHS_streett_bundle`: given a
  confinement certificate `V₀` (bounding the escape probability through the
  threshold `thr`) and, for each pair `i`, a bounded ranking certificate `W i`
  that never increases outside `G i` and strictly drops by `ε i` on
  requested-but-ungranted states, the probability that the path stays confined
  and satisfies every Streett pair is at least `p` whenever `p + thr ≤ 1`.
* `sound_GSHS_streett_bundle_carved_discharged(_confined)`: the carved
  variants, in which each ranking certificate may additionally ignore an
  exception set `J i`, itself shown to be visited only finitely often by an
  absorption certificate `Va i` through the `QStreett` absorption-bound
  machinery.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*}

def skelIn (A : Set State) : Set (SkelState State) :=
  fun z => Sum.elim (· ∈ A) (fun _ => False) z

@[simp] lemma skelIn_alive {A : Set State} (x : State) :
    SkelState.alive x ∈ skelIn A ↔ x ∈ A := Iff.rfl

@[simp] lemma skelIn_halted {A : Set State} (y : State) :
    SkelState.halted y ∉ skelIn A := fun h => h

@[simp] lemma skelIn_liveSt {A : Set State} :
    SkelState.liveSt (State := State) ∉ skelIn A := fun h => h

lemma mem_skelIn_union {A B : Set State} {z : SkelState State}
    (h : z ∈ skelIn (A ∪ B)) : z ∈ skelIn A ∨ z ∈ skelIn B := by
  rcases z with x | y | u
  · exact h
  · exact (h : False).elim
  · exact (h : False).elim

lemma skelIn_subset_skelBad {A B : Set State} (h : A ⊆ B) :
    skelIn A ⊆ skelBad B := by
  rintro (x | y | u) hz
  · exact h hz
  · exact hz.elim
  · exact hz.elim

lemma skelIn_floor {V : State → ℝ} {A : Set State} (h : ∀ y ∈ A, 1 ≤ V y) :
    ∀ z ∈ skelIn A, 1 ≤ skelCert V z := by
  rintro (x | y | u) hz
  · exact h x hz
  · exact hz.elim
  · exact hz.elim

lemma skelBad_floor₂ {V : State → ℝ} {U Dbar : Set State}
    (h : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V y) :
    ∀ z ∈ skelBad U, z ∈ skelBad Dbar → 1 ≤ skelCert V z := by
  rintro (x | y | u) hz hz'
  · exact h x hz hz'
  · exact h y hz hz'
  · exact hz.elim

variable [MeasurableSpace State]

lemma measurableSet_skelIn {A : Set State} (hA : MeasurableSet A) :
    MeasurableSet (skelIn A) := by
  rw [measurableSet_sum_iff]
  constructor
  · show MeasurableSet (Sum.inl ⁻¹' skelIn A)
    have h : Sum.inl ⁻¹' skelIn A = A := rfl
    rw [h]; exact hA
  · show MeasurableSet (Sum.inr ⁻¹' skelIn A)
    have h : (Sum.inr ⁻¹' skelIn A : Set (State ⊕ Unit)) = ∅ := by
      ext z
      rcases z with y | u
      · exact ⟨fun h => h, fun h => h.elim⟩
      · exact ⟨fun h => h, fun h => h.elim⟩
    rw [h]; exact MeasurableSet.empty

def RankingSegmentDynkin (M : SegmentModel State) (Sc : Set State)
    (V : State → ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ Sc,
    (∫⁻ o, outcomeRead M 0 V o ∂(M.seg x)) + ENNReal.ofReal ε
      ≤ ENNReal.ofReal (V x)

lemma rankingSegmentDynkin_of_segmentDynkin {M : SegmentModel State}
    {V : State → ℝ} (h : SegmentDynkin M 0 V) (Sc : Set State) :
    RankingSegmentDynkin M Sc V 0 := fun x _ => by
  simpa using h x

def NoVanish (M : SegmentModel State) (Sc : Set State) : Prop :=
  ∀ x ∈ Sc, M.seg x {o | o.2.2 = ExitKind.live} = 0

def HaltsCaught (M : SegmentModel State) (Sc T : Set State) : Prop :=
  ∀ x ∈ Sc, M.seg x {o | o.2.2 = ExitKind.halt ∧ o.2.1 ∉ T} = 0

def ResetsInto (M : SegmentModel State) (Sc T : Set State) : Prop :=
  ∀ x ∈ Sc,
    M.seg x {o | (o.2.2 = ExitKind.alarm ∨ o.2.2 = ExitKind.guard) ∧
      M.jump (o.2.1, o.2.2) T ≠ 1} = 0

variable {M : SegmentModel State}

lemma stepRead_le_outcomeRead {V : State → ℝ} (hForce : ForcedNonexpansion M V)
    (θ : ℝ) (o : ℝ≥0 × State × ExitKind) :
    stepRead M θ V o ≤ outcomeRead M θ V o := by
  rcases o with ⟨t, y, k⟩
  cases k with
  | alarm => exact le_rfl
  | halt => exact le_rfl
  | live => exact le_rfl
  | guard => exact mul_le_mul_right (hForce y) _

lemma ranking_step_bound {V : State → ℝ} {Sc : Set State} {ε : ℝ}
    (hSegD : RankingSegmentDynkin M Sc V ε) (hForce : ForcedNonexpansion M V)
    {x : State} (hx : x ∈ Sc) :
    (∫⁻ o, stepRead M 0 V o ∂(M.seg x)) + ENNReal.ofReal ε
      ≤ ENNReal.ofReal (V x) :=
  le_trans
    (add_le_add (lintegral_mono fun o => stepRead_le_outcomeRead hForce 0 o)
      le_rfl)
    (hSegD x hx)

theorem skel_drift_ranking {V : State → ℝ} {Sc : Set State} {ε : ℝ}
    (hV : Measurable V)
    (hSegD : RankingSegmentDynkin M Sc V ε) (hForce : ForcedNonexpansion M V)
    {x : State} (hx : x ∈ Sc) :
    (∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(skel M (SkelState.alive x)))
        + ENNReal.ofReal ε
      ≤ ENNReal.ofReal (V x) := by
  have hmeas : Measurable fun z => ENNReal.ofReal (skelCert V z) :=
    ENNReal.measurable_ofReal.comp (measurable_skelCert hV)
  rw [skel_alive, Kernel.lintegral_comp _ _ _ hmeas]
  have h0 : ∫⁻ o, ∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(dispatch M o) ∂(M.seg x)
      = ∫⁻ o, stepRead M 0 V o ∂(M.seg x) :=
    lintegral_congr fun o => lintegral_skelCert_dispatch hV o
  rw [h0]
  exact ranking_step_bound hSegD hForce hx

theorem skel_drift_ranking_real {V : State → ℝ} {Sc : Set State} {ε : ℝ}
    (hV : Measurable V) (hε : 0 ≤ ε)
    (hSegD : RankingSegmentDynkin M Sc V ε) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) {x : State} (hx : x ∈ Sc) :
    ∫ w, skelCert V w ∂(skel M (SkelState.alive x)) ≤ V x - ε := by
  have hkey := skel_drift_ranking hV hSegD hForce hx
  have hεV : ε ≤ V x := by
    have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal (V x) :=
      le_trans le_add_self hkey
    exact (ENNReal.ofReal_le_ofReal_iff (hNonneg x)).1 h1
  have h2 : (∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(skel M (SkelState.alive x)))
      ≤ ENNReal.ofReal (V x - ε) := by
    rw [ENNReal.ofReal_sub _ hε]
    exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hkey
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w => skelCert_nonneg hNonneg w)
    ((measurable_skelCert hV).aestronglyMeasurable)]
  calc (∫⁻ w, ENNReal.ofReal (skelCert V w)
        ∂(skel M (SkelState.alive x))).toReal
      ≤ (ENNReal.ofReal (V x - ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    _ = V x - ε := ENNReal.toReal_ofReal (by linarith)

lemma integrable_skelCert [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {C : ℝ} (hV : Measurable V) (hNonneg : NonnegV V)
    (hC0 : 0 ≤ C) (hVC : ∀ y, V y ≤ C) (z : SkelState State) :
    Integrable (skelCert V) (skel M z) := by
  refine (integrable_const C).mono' (measurable_skelCert hV).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (skelCert_nonneg hNonneg w)]
  exact skelCert_le hVC hC0 w

lemma skel_integral_halted {V : State → ℝ} (hV : Measurable V) (y : State) :
    ∫ w, skelCert V w ∂(skel M (SkelState.halted y)) = V y := by
  rw [skel_halted,
    integral_dirac' _ _ (Measurable.stronglyMeasurable (measurable_skelCert hV))]
  exact skelCert_halted V y

lemma skel_integral_liveSt {V : State → ℝ} (hV : Measurable V) :
    ∫ w, skelCert V w ∂(skel M (SkelState.liveSt (State := State))) = 0 := by
  rw [skel_liveSt,
    integral_dirac' _ _ (Measurable.stronglyMeasurable (measurable_skelCert hV))]
  exact skelCert_liveSt V

lemma skel_step_full [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {Z : Set (SkelState State)} {Sc Tj Th : Set State}
    (hZ : MeasurableSet Z)
    (hLive : NoVanish M Sc) (hHalt : HaltsCaught M Sc Th)
    (hReset : ResetsInto M Sc Tj)
    (hTjZ : ∀ z ∈ Tj, SkelState.alive z ∈ Z)
    (hThZ : ∀ y ∈ Th, SkelState.halted y ∈ Z)
    {x : State} (hx : x ∈ Sc) :
    skel M (SkelState.alive x) Z = 1 := by
  rw [skel_alive, Kernel.comp_apply' _ _ _ hZ]
  have hbad : M.seg x ({o : ℝ≥0 × State × ExitKind | o.2.2 = ExitKind.live} ∪
      ({o : ℝ≥0 × State × ExitKind | o.2.2 = ExitKind.halt ∧ o.2.1 ∉ Th} ∪
        {o : ℝ≥0 × State × ExitKind |
          (o.2.2 = ExitKind.alarm ∨ o.2.2 = ExitKind.guard) ∧
            M.jump (o.2.1, o.2.2) Tj ≠ 1})) = 0 :=
    measure_union_null (hLive x hx)
      (measure_union_null (hHalt x hx) (hReset x hx))
  have hae : ∀ᵐ o ∂(M.seg x), dispatch M o Z = 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun o ho => ?_) hbad
    rcases o with ⟨t, y, k⟩
    cases k with
    | live => exact Or.inl rfl
    | halt =>
        refine Or.inr (Or.inl ⟨rfl, fun hyT => ho ?_⟩)
        have happly : dispatch M (t, y, ExitKind.halt)
            = dispatchFun M (t, y, ExitKind.halt) := rfl
        show dispatch M (t, y, ExitKind.halt) Z = 1
        rw [happly]
        show Measure.dirac (SkelState.halted y) Z = 1
        rw [Measure.dirac_apply' _ hZ, Set.indicator_of_mem (hThZ y hyT)]
        rfl
    | alarm =>
        refine Or.inr (Or.inr ⟨Or.inl rfl, fun h1 => ho ?_⟩)
        have happly : dispatch M (t, y, ExitKind.alarm)
            = dispatchFun M (t, y, ExitKind.alarm) := rfl
        show dispatch M (t, y, ExitKind.alarm) Z = 1
        rw [happly]
        show (M.jump (y, ExitKind.alarm)).map SkelState.alive Z = 1
        rw [Measure.map_apply measurable_inl hZ]
        refine le_antisymm prob_le_one ?_
        calc (1 : ℝ≥0∞) = M.jump (y, ExitKind.alarm) Tj := h1.symm
          _ ≤ M.jump (y, ExitKind.alarm) (SkelState.alive ⁻¹' Z) :=
              measure_mono fun z hz => hTjZ z hz
    | guard =>
        refine Or.inr (Or.inr ⟨Or.inr rfl, fun h1 => ho ?_⟩)
        have happly : dispatch M (t, y, ExitKind.guard)
            = dispatchFun M (t, y, ExitKind.guard) := rfl
        show dispatch M (t, y, ExitKind.guard) Z = 1
        rw [happly]
        show (M.jump (y, ExitKind.guard)).map SkelState.alive Z = 1
        rw [Measure.map_apply measurable_inl hZ]
        refine le_antisymm prob_le_one ?_
        calc (1 : ℝ≥0∞) = M.jump (y, ExitKind.guard) Tj := h1.symm
          _ ≤ M.jump (y, ExitKind.guard) (SkelState.alive ⁻¹' Z) :=
              measure_mono fun z hz => hTjZ z hz
  calc ∫⁻ o, dispatch M o Z ∂(M.seg x)
      = ∫⁻ _o, (1 : ℝ≥0∞) ∂(M.seg x) := lintegral_congr_ae hae
    _ = 1 := by rw [lintegral_one, measure_univ]

lemma skel_R3 [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {D Dbar U : Set State} (hDbar : MeasurableSet Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar)) :
    ∀ z ∈ skelIn D, z ∉ skelBad U → skel M z (skelBad Dbar) = 1 := by
  rintro (x | y | u) hz hzU
  · exact skel_step_full (measurableSet_skelBad hDbar) hLive hHalt hReset
      (fun z hz => hz.2) (fun y hy => hy.2) ⟨hz, hzU⟩
  · exact hz.elim
  · exact hz.elim

lemma skel_R4 [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {D Dbar U : Set State} (hD : MeasurableSet D) (hU : MeasurableSet U)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar)) :
    ∀ z ∈ skelIn D, z ∉ skelBad U →
      skel M z (skelIn D ∪ skelBad U) = 1 := by
  rintro (x | y | u) hz hzU
  · refine skel_step_full ((measurableSet_skelIn hD).union (measurableSet_skelBad hU))
      hLive hHalt hReset (fun z hz => ?_) (fun y hy => Or.inr hy.1) ⟨hz, hzU⟩
    rcases hz.1 with hzD | hzU'
    · exact Or.inl hzD
    · exact Or.inr hzU'
  · exact hz.elim
  · exact hz.elim

section Bundle

variable {ι : Type*} [Countable ι]
variable {D Dbar U : Set State} {V₀ : State → ℝ} {Rq G J : ι → Set State}
variable {W Va : ι → State → ℝ} {p thr C₀ : ℝ} {ε C γ Ca : ι → ℝ} {x : State}

theorem sound_GSHS_streett_bundle_confined
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hSegD₀ : RankingSegmentDynkin M (D \ U) V₀ 0)
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hSegDW : ∀ i, RankingSegmentDynkin M ((D \ U) \ G i) (W i) 0)
    (hSegDWR : ∀ i, RankingSegmentDynkin M (((D \ U) ∩ Rq i) \ G i) (W i) (ε i))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | (∀ n, ω n ∈ skelIn D \ skelBad U) ∧
        ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
          ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} := by
  have hR3s := skel_R3 (M := M) hDbar hLive hHalt hReset
  have hconf : ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ n, ω n ∈ skelIn D \ skelBad U} :=
    Battery.sound_QSafetyBattery_failClosed (K := skel M)
      (measurableSet_skelIn hD) (measurableSet_skelBad hDbar)
      (measurableSet_skelBad hU) (measurable_skelCert hV₀) hΘ
      (skelIn_subset_skelBad hDsub) hR3s
      (skel_R4 hD hU hLive hHalt hReset)
      (fun z _ _ => integrable_skelCert hV₀ hNonneg₀ hC₀0 hV₀C z)
      (by
        rintro (x' | y | u) hz hzU
        · have h := skel_drift_ranking_real hV₀ le_rfl hSegD₀ hForce₀ hNonneg₀
            (show x' ∈ D \ U from ⟨hz, hzU⟩)
          simpa using h
        · exact hz.elim
        · exact hz.elim)
      (skelBad_floor₂ hFloor₀)
      (fun z _ => skelCert_nonneg hNonneg₀ z)
      hx hthr
  have hpairs : ∀ᵐ ω ∂(Battery.pathMeasure (skel M) (SkelState.alive x)), ∀ i,
      (∀ n, ω n ∈ skelIn D \ skelBad U) →
      (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i) := by
    refine ae_all_iff.2 fun i => ?_
    exact QStreett.streett_pair_localized (K := skel M)
      (measurableSet_skelIn hD) (measurableSet_skelBad hDbar)
      (measurableSet_skelBad hU) (measurableSet_skelIn (hRq i))
      (measurableSet_skelIn (hG i)) (measurable_skelCert (hW i)) (hε i)
      (skelIn_subset_skelBad hDsub) hR3s
      (fun z _ => skelCert_nonneg (hNonnegW i) z)
      (fun z _ => skelCert_le (hWC i) (hC0 i) z)
      (fun z _ _ _ => integrable_skelCert (hW i) (hNonnegW i) (hC0 i) (hWC i) z)
      (by
        rintro (x' | y | u) hz hzU hzG
        · have h := skel_drift_ranking_real (hW i) le_rfl (hSegDW i) (hForceW i)
            (hNonnegW i) (show x' ∈ (D \ U) \ G i from ⟨⟨hz, hzU⟩, hzG⟩)
          simpa using h
        · exact hz.elim
        · exact hz.elim)
      (by
        rintro (x' | y | u) hz hzU hzR hzG
        · exact skel_drift_ranking_real (hW i) (hε i).le (hSegDWR i) (hForceW i)
            (hNonnegW i)
            (show x' ∈ ((D \ U) ∩ Rq i) \ G i from ⟨⟨⟨hz, hzU⟩, hzR⟩, hzG⟩)
        · exact hz.elim
        · exact hz.elim)
  refine hconf.trans (measure_mono_ae ?_)
  filter_upwards [hpairs] with ω hω hconfω
  exact ⟨hconfω, fun i => hω i hconfω⟩

theorem sound_GSHS_streett_bundle
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hSegD₀ : RankingSegmentDynkin M (D \ U) V₀ 0)
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hSegDW : ∀ i, RankingSegmentDynkin M ((D \ U) \ G i) (W i) 0)
    (hSegDWR : ∀ i, RankingSegmentDynkin M (((D \ U) ∩ Rq i) \ G i) (W i) (ε i))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} :=
  (sound_GSHS_streett_bundle_confined hD hDbar hU hV₀ hRq hG hW hΘ hDsub
    hLive hHalt hReset hSegD₀ hForce₀ hNonneg₀ hC₀0 hV₀C hFloor₀ hε hSegDW
    hSegDWR hForceW hNonnegW hC0 hWC hx hthr).trans
    (measure_mono fun _ω hω => hω.2)

theorem sound_GSHS_streett_bundle_carved_discharged_confined
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hJ : ∀ i, MeasurableSet (J i)) (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hSegD₀ : RankingSegmentDynkin M (D \ U) V₀ 0)
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i) (hγ : ∀ i, 0 < γ i)
    (hSegDW : ∀ i, RankingSegmentDynkin M ((D \ U) \ (G i ∪ J i)) (W i) 0)
    (hSegDWR : ∀ i,
      RankingSegmentDynkin M (((D \ U) ∩ Rq i) \ (G i ∪ J i)) (W i) (ε i))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hVa : ∀ i, Measurable (Va i)) (hNonnegVa : ∀ i, NonnegV (Va i))
    (hCa0 : ∀ i, 0 ≤ Ca i) (hVaC : ∀ i, ∀ y, Va i y ≤ Ca i)
    (hVaFloor : ∀ i, ∀ y ∈ Rq i, 1 ≤ Va i y)
    (hSegDVa : ∀ i, RankingSegmentDynkin M ((Rq i)ᶜ) (Va i) 0)
    (hForceVa : ∀ i, ForcedNonexpansion M (Va i))
    (hVaJ : ∀ i, ∀ y ∈ J i, Va i y ≤ 1 - γ i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | (∀ n, ω n ∈ skelIn D \ skelBad U) ∧
        ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
          ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} := by
  have hR3s := skel_R3 (M := M) hDbar hLive hHalt hReset
  have hconf : ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ n, ω n ∈ skelIn D \ skelBad U} :=
    Battery.sound_QSafetyBattery_failClosed (K := skel M)
      (measurableSet_skelIn hD) (measurableSet_skelBad hDbar)
      (measurableSet_skelBad hU) (measurable_skelCert hV₀) hΘ
      (skelIn_subset_skelBad hDsub) hR3s
      (skel_R4 hD hU hLive hHalt hReset)
      (fun z _ _ => integrable_skelCert hV₀ hNonneg₀ hC₀0 hV₀C z)
      (by
        rintro (x' | y | u) hz hzU
        · have h := skel_drift_ranking_real hV₀ le_rfl hSegD₀ hForce₀ hNonneg₀
            (show x' ∈ D \ U from ⟨hz, hzU⟩)
          simpa using h
        · exact hz.elim
        · exact hz.elim)
      (skelBad_floor₂ hFloor₀)
      (fun z _ => skelCert_nonneg hNonneg₀ z)
      hx hthr
  have hpairs : ∀ᵐ ω ∂(Battery.pathMeasure (skel M) (SkelState.alive x)), ∀ i,
      (∀ n, ω n ∈ skelIn D \ skelBad U) →
      (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i) := by
    refine ae_all_iff.2 fun i => ?_

    have hK5c := QStreett.streett_pair_localized (K := skel M)
      (x := SkelState.alive x)
      (measurableSet_skelIn hD) (measurableSet_skelBad hDbar)
      (measurableSet_skelBad hU) (measurableSet_skelIn (hRq i))
      (measurableSet_skelIn ((hG i).union (hJ i)))
      (measurable_skelCert (hW i)) (hε i)
      (skelIn_subset_skelBad hDsub) hR3s
      (fun z _ => skelCert_nonneg (hNonnegW i) z)
      (fun z _ => skelCert_le (hWC i) (hC0 i) z)
      (fun z _ _ _ => integrable_skelCert (hW i) (hNonnegW i) (hC0 i) (hWC i) z)
      (by
        rintro (x' | y | u) hz hzU hzGJ
        · have h := skel_drift_ranking_real (hW i) le_rfl (hSegDW i) (hForceW i)
            (hNonnegW i)
            (show x' ∈ (D \ U) \ (G i ∪ J i) from ⟨⟨hz, hzU⟩, hzGJ⟩)
          simpa using h
        · exact hz.elim
        · exact hz.elim)
      (by
        rintro (x' | y | u) hz hzU hzR hzGJ
        · exact skel_drift_ranking_real (hW i) (hε i).le (hSegDWR i) (hForceW i)
            (hNonnegW i)
            (show x' ∈ ((D \ U) ∩ Rq i) \ (G i ∪ J i) from
              ⟨⟨⟨hz, hzU⟩, hzR⟩, hzGJ⟩)
        · exact hz.elim
        · exact hz.elim)

    have habs : QStreett.AbsorptionBound (skel M) (SkelState.alive x)
        (skelBad U ∪ (skelIn D)ᶜ) (skelIn (J i)) (skelIn (Rq i)) (γ i) :=
      QStreett.absorptionBound_of_kernel (measurableSet_skelIn (hRq i))
        (measurable_skelCert (hVa i))
        (skelCert_nonneg (hNonnegVa i))
        (skelCert_le (hVaC i) (hCa0 i))
        (skelIn_floor (hVaFloor i))
        (by
          rintro (x' | y | u) hz
          · have h := skel_drift_ranking_real (hVa i) le_rfl (hSegDVa i)
              (hForceVa i) (hNonnegVa i) (show x' ∈ (Rq i)ᶜ from hz)
            simpa using h
          · exact le_of_eq (skel_integral_halted (hVa i) y)
          · exact le_of_eq (skel_integral_liveSt (hVa i)))
        (by
          rintro (x' | y | u) hz
          · exact hVaJ i x' hz
          · exact (hz : False).elim
          · exact (hz : False).elim)
    have hlevy := QStreett.ae_not_frequently_of_absorption (K := skel M)
      (x := SkelState.alive x) (A := skelBad U ∪ (skelIn D)ᶜ)
      (J := skelIn (J i)) (measurableSet_skelIn (hRq i)) (hγ i) habs
    filter_upwards [hK5c, hlevy] with ω h1 h2 hconfω hfreq
    have hsurvive : ∀ n, ω ∈ Battery.survive (skelBad U ∪ (skelIn D)ᶜ) n := by
      intro n k _
      rintro (hU' | hD')
      · exact (hconfω k).2 hU'
      · exact hD' (hconfω k).1
    rcases Filter.frequently_or_distrib.1
        ((h1 hconfω hfreq).mono fun n hn => mem_skelIn_union hn) with
      hGfreq | hJfreq
    · exact hGfreq
    · exact absurd hfreq (h2 (hJfreq.mono fun n hn => ⟨hsurvive n, hn⟩))
  refine hconf.trans (measure_mono_ae ?_)
  filter_upwards [hpairs] with ω hω hconfω
  exact ⟨hconfω, fun i => hω i hconfω⟩

theorem sound_GSHS_streett_bundle_carved_discharged
    [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hJ : ∀ i, MeasurableSet (J i)) (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1) (hDsub : D ⊆ Dbar)
    (hLive : NoVanish M (D \ U)) (hHalt : HaltsCaught M (D \ U) (U ∩ Dbar))
    (hReset : ResetsInto M (D \ U) ((D ∪ U) ∩ Dbar))
    (hSegD₀ : RankingSegmentDynkin M (D \ U) V₀ 0)
    (hForce₀ : ForcedNonexpansion M V₀) (hNonneg₀ : NonnegV V₀)
    (hC₀0 : 0 ≤ C₀) (hV₀C : ∀ y, V₀ y ≤ C₀)
    (hFloor₀ : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i) (hγ : ∀ i, 0 < γ i)
    (hSegDW : ∀ i, RankingSegmentDynkin M ((D \ U) \ (G i ∪ J i)) (W i) 0)
    (hSegDWR : ∀ i,
      RankingSegmentDynkin M (((D \ U) ∩ Rq i) \ (G i ∪ J i)) (W i) (ε i))
    (hForceW : ∀ i, ForcedNonexpansion M (W i)) (hNonnegW : ∀ i, NonnegV (W i))
    (hC0 : ∀ i, 0 ≤ C i) (hWC : ∀ i, ∀ y, W i y ≤ C i)
    (hVa : ∀ i, Measurable (Va i)) (hNonnegVa : ∀ i, NonnegV (Va i))
    (hCa0 : ∀ i, 0 ≤ Ca i) (hVaC : ∀ i, ∀ y, Va i y ≤ Ca i)
    (hVaFloor : ∀ i, ∀ y ∈ Rq i, 1 ≤ Va i y)
    (hSegDVa : ∀ i, RankingSegmentDynkin M ((Rq i)ᶜ) (Va i) 0)
    (hForceVa : ∀ i, ForcedNonexpansion M (Va i))
    (hVaJ : ∀ i, ∀ y ∈ J i, Va i y ≤ 1 - γ i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ skelIn (Rq i)) →
        ∃ᶠ n in atTop, ω n ∈ skelIn (G i)} :=
  (sound_GSHS_streett_bundle_carved_discharged_confined hD hDbar hU hV₀ hRq
    hG hJ hW hΘ hDsub hLive hHalt hReset hSegD₀ hForce₀ hNonneg₀ hC₀0 hV₀C
    hFloor₀ hε hγ hSegDW hSegDWR hForceW hNonnegW hC0 hWC hVa hNonnegVa hCa0
    hVaC hVaFloor hSegDVa hForceVa hVaJ hx hthr).trans
    (measure_mono fun _ω hω => hω.2)

end Bundle

end Qtsl.LayerD
