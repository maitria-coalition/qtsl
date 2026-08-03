import QtslAux.LayerD
import QtslAux.Battery

/-! # The untimed skeleton chain of a segment model and safety soundness

This module builds the discrete-time skeleton of a segment model — the Markov
chain that observes the hybrid system only at segment boundaries — and proves
the basic safety (avoidance) soundness theorem.

* `SkelState State`: skeleton states `alive x`, `halted y`, and the absorbing
  `liveSt` (reached when a segment never exits). `skelCert V` extends a
  certificate `V` by `V` on halted states and `0` on `liveSt`; `skelBad U`
  lifts a bad set `U` to both alive and halted states.
* `dispatch M`: the kernel routing a segment outcome — reset through `M.jump`
  into an `alive` state on `alarm`/`guard` exits, freeze to `halted` on `halt`,
  absorb to `liveSt` on `live`. `skel M` is the skeleton kernel: one segment
  followed by `dispatch` from alive states, Dirac on the absorbing states.
* `skel_drift` / `skel_drift_real`: if `V` satisfies `SegmentDynkin M 0 V` and
  `ForcedNonexpansion M V`, then `skelCert V` is a one-step supermartingale
  for `skel M`.
* `sound_GSHS_safety`: for such a `V`, bounded above and with `V ≥ 1` on `U`,
  the probability that the skeleton path ever enters `skelBad U` is at most
  `V x`. `sound_GSHS_safety_battery` restates this as the lower bound
  `p ≤ ℙ(always outside U)` whenever `V x ≤ thr` and `p + thr ≤ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*}

abbrev SkelState (State : Type*) := State ⊕ (State ⊕ Unit)

abbrev SkelState.alive : State → SkelState State := Sum.inl

abbrev SkelState.halted : State → SkelState State := fun y => Sum.inr (Sum.inl y)

abbrev SkelState.liveSt : SkelState State := Sum.inr (Sum.inr ())

noncomputable def skelCert (V : State → ℝ) : SkelState State → ℝ :=
  Sum.elim V (Sum.elim V fun _ => 0)

@[simp] lemma skelCert_alive (V : State → ℝ) (x : State) :
    skelCert V (SkelState.alive x) = V x := rfl

@[simp] lemma skelCert_halted (V : State → ℝ) (y : State) :
    skelCert V (SkelState.halted y) = V y := rfl

@[simp] lemma skelCert_liveSt (V : State → ℝ) :
    skelCert V (SkelState.liveSt (State := State)) = 0 := rfl

lemma skelCert_nonneg {V : State → ℝ} (hNonneg : NonnegV V) :
    ∀ z : SkelState State, 0 ≤ skelCert V z := by
  rintro (x | y | u)
  · exact hNonneg x
  · exact hNonneg y
  · exact le_rfl

lemma skelCert_le {V : State → ℝ} {C : ℝ} (hVC : ∀ y, V y ≤ C) (hC0 : 0 ≤ C) :
    ∀ z : SkelState State, skelCert V z ≤ C := by
  rintro (x | y | u)
  · exact hVC x
  · exact hVC y
  · exact hC0

def skelBad (U : Set State) : Set (SkelState State) :=
  fun z => Sum.elim (· ∈ U) (Sum.elim (· ∈ U) fun _ => False) z

@[simp] lemma skelBad_alive {U : Set State} (x : State) :
    SkelState.alive x ∈ skelBad U ↔ x ∈ U := Iff.rfl

@[simp] lemma skelBad_halted {U : Set State} (y : State) :
    SkelState.halted y ∈ skelBad U ↔ y ∈ U := Iff.rfl

@[simp] lemma skelBad_liveSt {U : Set State} :
    SkelState.liveSt (State := State) ∉ skelBad U := fun h => h

lemma skelBad_floor {V : State → ℝ} {U : Set State} (hFloor : ∀ y ∈ U, 1 ≤ V y) :
    ∀ z ∈ skelBad U, 1 ≤ skelCert V z := by
  rintro (x | y | u) hz
  · exact hFloor x hz
  · exact hFloor y hz
  · exact hz.elim

variable [MeasurableSpace State]

lemma measurable_skelCert {V : State → ℝ} (hV : Measurable V) :
    Measurable (skelCert V) :=
  hV.sumElim (hV.sumElim measurable_const)

lemma measurableSet_skelBad {U : Set State} (hU : MeasurableSet U) :
    MeasurableSet (skelBad U) := by
  rw [measurableSet_sum_iff]
  constructor
  · show MeasurableSet (Sum.inl ⁻¹' skelBad U)
    have : Sum.inl ⁻¹' skelBad U = U := rfl
    rw [this]; exact hU
  · rw [measurableSet_sum_iff]
    constructor
    · show MeasurableSet ((Sum.inr ∘ Sum.inl) ⁻¹' skelBad U)
      have : (Sum.inr ∘ Sum.inl : State → SkelState State) ⁻¹' skelBad U = U := rfl
      rw [this]; exact hU
    · show MeasurableSet ((Sum.inr ∘ Sum.inr) ⁻¹' skelBad U)
      have : (Sum.inr ∘ Sum.inr : Unit → SkelState State) ⁻¹' skelBad U = ∅ := by
        ext u; exact ⟨fun h => h, fun h => h.elim⟩
      rw [this]; exact MeasurableSet.empty

variable (M : SegmentModel State)

noncomputable def dispatchFun : ℝ≥0 × State × ExitKind → Measure (SkelState State) :=
  fun o =>
    if o.2.2 = ExitKind.alarm ∨ o.2.2 = ExitKind.guard then
      (M.jump (o.2.1, o.2.2)).map SkelState.alive
    else if o.2.2 = ExitKind.halt then Measure.dirac (SkelState.halted o.2.1)
    else Measure.dirac SkelState.liveSt

lemma measurable_dispatchFun : Measurable (dispatchFun M) := by
  have hval : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.1 :=
    measurable_fst.comp measurable_snd
  have hkind : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.2 :=
    measurable_snd.comp measurable_snd
  have hpair : Measurable fun o : ℝ≥0 × State × ExitKind => (o.2.1, o.2.2) :=
    hval.prodMk hkind
  refine Measurable.ite ?_ ?_ (Measurable.ite ?_ ?_ measurable_const)
  · exact ((hkind (measurableSet_singleton ExitKind.alarm)).union
      (hkind (measurableSet_singleton ExitKind.guard)))
  · exact (Measure.measurable_map _ measurable_inl).comp (M.jump.measurable.comp hpair)
  · exact hkind (measurableSet_singleton ExitKind.halt)
  · exact Measure.measurable_dirac.comp ((measurable_inr.comp measurable_inl).comp hval)

noncomputable def dispatch : Kernel (ℝ≥0 × State × ExitKind) (SkelState State) where
  toFun := dispatchFun M
  measurable' := measurable_dispatchFun M

instance [IsMarkovKernel M.jump] : IsMarkovKernel (dispatch M) := by
  constructor
  intro o
  show IsProbabilityMeasure (dispatchFun M o)
  unfold dispatchFun
  split_ifs
  · exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  · exact Measure.dirac.isProbabilityMeasure
  · exact Measure.dirac.isProbabilityMeasure

noncomputable def skel : Kernel (SkelState State) (SkelState State) where
  toFun :=
    Sum.elim (fun x => (dispatch M ∘ₖ M.seg) x)
      (Sum.elim (fun y => Measure.dirac (SkelState.halted y))
        (fun _ => Measure.dirac SkelState.liveSt))
  measurable' :=
    ((dispatch M ∘ₖ M.seg).measurable).sumElim
      ((Measure.measurable_dirac.comp (measurable_inr.comp measurable_inl)).sumElim
        measurable_const)

@[simp] lemma skel_alive (x : State) :
    skel M (SkelState.alive x) = (dispatch M ∘ₖ M.seg) x := rfl

@[simp] lemma skel_halted (y : State) :
    skel M (SkelState.halted y) = Measure.dirac (SkelState.halted y) := rfl

@[simp] lemma skel_liveSt :
    skel M (SkelState.liveSt (State := State)) = Measure.dirac SkelState.liveSt := rfl

instance [IsMarkovKernel M.seg] [IsMarkovKernel M.jump] : IsMarkovKernel (skel M) := by
  constructor
  rintro (x | y | u)
  · rw [skel_alive]; infer_instance
  · rw [skel_halted]; infer_instance
  · rw [skel_liveSt]; infer_instance

variable {M}

lemma lintegral_skelCert_dispatch {V : State → ℝ} (hV : Measurable V)
    (o : ℝ≥0 × State × ExitKind) :
    ∫⁻ z, ENNReal.ofReal (skelCert V z) ∂(dispatch M o) = stepRead M 0 V o := by
  have hmeas : Measurable fun z => ENNReal.ofReal (skelCert V z) :=
    ENNReal.measurable_ofReal.comp (measurable_skelCert hV)
  rcases o with ⟨t, y, k⟩
  have happly : dispatch M (t, y, k) = dispatchFun M (t, y, k) := rfl
  cases k
  case alarm =>
    rw [happly]
    show ∫⁻ z, ENNReal.ofReal (skelCert V z)
        ∂((M.jump (y, ExitKind.alarm)).map SkelState.alive) = _
    rw [lintegral_map hmeas measurable_inl]
    simp [stepRead, skelCert]
  case guard =>
    rw [happly]
    show ∫⁻ z, ENNReal.ofReal (skelCert V z)
        ∂((M.jump (y, ExitKind.guard)).map SkelState.alive) = _
    rw [lintegral_map hmeas measurable_inl]
    simp [stepRead, skelCert]
  case halt =>
    rw [happly]
    show ∫⁻ z, ENNReal.ofReal (skelCert V z)
        ∂(Measure.dirac (SkelState.halted y)) = _
    rw [lintegral_dirac' _ hmeas]
    simp [stepRead]
  case live =>
    rw [happly]
    show ∫⁻ z, ENNReal.ofReal (skelCert V z)
        ∂(Measure.dirac (SkelState.liveSt (State := State))) = _
    rw [lintegral_dirac' _ hmeas]
    simp [stepRead]

theorem skel_drift {V : State → ℝ} (hV : Measurable V)
    (hSegD : SegmentDynkin M 0 V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (z : SkelState State) :
    ∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(skel M z)
      ≤ ENNReal.ofReal (skelCert V z) := by
  have hmeas : Measurable fun z => ENNReal.ofReal (skelCert V z) :=
    ENNReal.measurable_ofReal.comp (measurable_skelCert hV)
  rcases z with x | y | u
  · rw [skel_alive, Kernel.lintegral_comp _ _ _ hmeas]
    calc ∫⁻ o, ∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(dispatch M o) ∂(M.seg x)
        = ∫⁻ o, stepRead M 0 V o ∂(M.seg x) :=
          lintegral_congr fun o => lintegral_skelCert_dispatch hV o
      _ ≤ ENNReal.ofReal (V x) := iBridge M 0 V hSegD hForce hNonneg x
      _ = ENNReal.ofReal (skelCert V (SkelState.alive x)) := by simp
  · rw [skel_halted, lintegral_dirac' _ hmeas]
  · rw [skel_liveSt, lintegral_dirac' _ hmeas]

theorem skel_drift_real {V : State → ℝ} (hV : Measurable V)
    (hSegD : SegmentDynkin M 0 V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (z : SkelState State) :
    ∫ w, skelCert V w ∂(skel M z) ≤ skelCert V z := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w => skelCert_nonneg hNonneg w)
    ((measurable_skelCert hV).aestronglyMeasurable)]
  calc (∫⁻ w, ENNReal.ofReal (skelCert V w) ∂(skel M z)).toReal
      ≤ (ENNReal.ofReal (skelCert V z)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (skel_drift hV hSegD hForce hNonneg z)
    _ = skelCert V z := ENNReal.toReal_ofReal (skelCert_nonneg hNonneg z)

theorem sound_GSHS_safety [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {U : Set State} (hV : Measurable V) (hU : MeasurableSet U)
    (hSegD : SegmentDynkin M 0 V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, V y ≤ C)
    (hFloor : ∀ y ∈ U, 1 ≤ V y) (x : State) :
    Battery.pathMeasure (skel M) (SkelState.alive x)
        {ω | ∃ n, ω n ∈ skelBad U}
      ≤ ENNReal.ofReal (V x) := by
  have h := Battery.measure_reach_le (K := skel M)
    (measurableSet_skelBad hU) (measurable_skelCert hV)
    (skelCert_nonneg hNonneg) (skelCert_le hVC hC0) (skelBad_floor hFloor)
    (fun z _ => skel_drift_real hV hSegD hForce hNonneg z)
    (SkelState.alive x)
  simpa using h

theorem sound_GSHS_safety_battery [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {U : Set State} {p thr : ℝ}
    (hV : Measurable V) (hU : MeasurableSet U)
    (hSegD : SegmentDynkin M 0 V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) {C : ℝ} (hC0 : 0 ≤ C) (hVC : ∀ y, V y ≤ C)
    (hFloor : ∀ y ∈ U, 1 ≤ V y)
    (hΘ : p + thr ≤ 1) (x : State) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∀ n, ω n ∉ skelBad U} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]
    exact zero_le
  have hreach := sound_GSHS_safety hV hU hSegD hForce hNonneg hC0 hVC hFloor x
  have h1 : Battery.pathMeasure (skel M) (SkelState.alive x)
      {ω | ∃ n, ω n ∈ skelBad U} ≤ ENNReal.ofReal thr :=
    hreach.trans (ENNReal.ofReal_le_ofReal hthr)
  have hnever : {ω : ℕ → SkelState State | ∀ n, ω n ∉ skelBad U}
      = {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad U}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists]
  have hreachMeas : MeasurableSet
      {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad U} := by
    have h : {ω : ℕ → SkelState State | ∃ n, ω n ∈ skelBad U}
        = ⋃ n, (fun ω : ℕ → SkelState State => ω n) ⁻¹' skelBad U := by
      ext ω; simp
    rw [h]
    exact MeasurableSet.iUnion fun n =>
      (measurable_pi_apply n) (measurableSet_skelBad hU)
  have hthr0 : 0 ≤ thr := le_trans (hNonneg x) hthr
  rw [hnever, prob_compl_eq_one_sub hreachMeas]
  refine le_trans ?_ (tsub_le_tsub_left h1 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add hthr0 hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Qtsl.LayerD
