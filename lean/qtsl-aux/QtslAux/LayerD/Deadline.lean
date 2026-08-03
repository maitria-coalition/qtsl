import QtslAux.LayerD
import QtslAux.LayerD.Skeleton

/-! # Timed skeleton and exponential deadline bounds for GSHS

This module augments the skeleton of a segment model with an explicit clock and
proves deadline (time-bound) soundness theorems.

* `TSkelState State`: clock-carrying skeleton states — `alive (τ, x)`,
  `halted (τ, y)`, and the absorbing `liveT`; `tclock` reads the clock.
* `tskel M`: the timed skeleton Markov kernel — from an `alive` state, run one
  segment, add its dwell time to the clock (`tsegStep`, `clockUpd`), and
  dispatch on the exit kind (`tdispatch`, using `tcont` for the reset cases);
  `halted` and `liveT` states are absorbing.
* `tCert θ V (alive (τ, x)) = exp (θ * τ) * V x`: the exponentially
  clock-weighted certificate. The key drift result `tskel_drift` shows
  `tCert θ V` is a one-step supermartingale for `tskel M` whenever `V`
  satisfies `SegmentDynkin M θ V` and `ForcedNonexpansion M V`.
* `tbad T` (clock exceeds `T`) and `tbadIn B` (state lies in `B`), with
  measurability lemmas; `tCertCap θ T ε V` is the `[0, 1]`-valued capped and
  normalized certificate fed to the generic reachability bound.

Main results: `sound_GSHS_deadline` — for a certificate `V ≥ ε > 0` at rate
`θ ≥ 0`, the probability that the clock ever exceeds `T` is at most
`exp (-θT) * V x / ε`; `sound_GSHS_deadline_offTarget`, the same bound
restricted to paths that exceed the deadline outside a target set `B`; and
`sound_GSHS_deadline_battery`, the complementary lower bound `p` on the
probability that the clock stays within `T`, given a threshold `V x ≤ thr` and
`p + exp (-θT) * thr / ε ≤ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*}

abbrev TSkelState (State : Type*) := (ℝ≥0 × State) ⊕ ((ℝ≥0 × State) ⊕ Unit)

abbrev TSkelState.alive : ℝ≥0 × State → TSkelState State := Sum.inl

abbrev TSkelState.halted : ℝ≥0 × State → TSkelState State :=
  fun p => Sum.inr (Sum.inl p)

abbrev TSkelState.liveT : TSkelState State := Sum.inr (Sum.inr ())

def tclock : TSkelState State → ℝ≥0 :=
  Sum.elim Prod.fst (Sum.elim Prod.fst fun _ => 0)

@[simp] lemma tclock_alive (p : ℝ≥0 × State) :
    tclock (TSkelState.alive p) = p.1 := rfl

@[simp] lemma tclock_halted (p : ℝ≥0 × State) :
    tclock (TSkelState.halted p) = p.1 := rfl

@[simp] lemma tclock_liveT : tclock (TSkelState.liveT (State := State)) = 0 := rfl

noncomputable def tCert (θ : ℝ) (V : State → ℝ) : TSkelState State → ℝ :=
  Sum.elim (fun p => Real.exp (θ * p.1) * V p.2)
    (Sum.elim (fun p => Real.exp (θ * p.1) * V p.2) fun _ => 0)

@[simp] lemma tCert_alive (θ : ℝ) (V : State → ℝ) (p : ℝ≥0 × State) :
    tCert θ V (TSkelState.alive p) = Real.exp (θ * p.1) * V p.2 := rfl

@[simp] lemma tCert_halted (θ : ℝ) (V : State → ℝ) (p : ℝ≥0 × State) :
    tCert θ V (TSkelState.halted p) = Real.exp (θ * p.1) * V p.2 := rfl

@[simp] lemma tCert_liveT (θ : ℝ) (V : State → ℝ) :
    tCert θ V (TSkelState.liveT (State := State)) = 0 := rfl

lemma tCert_nonneg {V : State → ℝ} (hNonneg : NonnegV V) (θ : ℝ) :
    ∀ q : TSkelState State, 0 ≤ tCert θ V q := by
  rintro (p | p | u)
  · exact mul_nonneg (Real.exp_nonneg _) (hNonneg p.2)
  · exact mul_nonneg (Real.exp_nonneg _) (hNonneg p.2)
  · exact le_rfl

lemma expWeight_add (θ : ℝ) (s t : ℝ≥0) :
    expWeight θ (s + t) = expWeight θ s * expWeight θ t := by
  rw [expWeight, expWeight, expWeight,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  push_cast
  ring

variable [MeasurableSpace State]

lemma measurable_tclock : Measurable (tclock (State := State)) :=
  measurable_fst.sumElim (measurable_fst.sumElim measurable_const)

lemma measurable_tCert {V : State → ℝ} (hV : Measurable V) (θ : ℝ) :
    Measurable (tCert θ V) := by
  have hcoe : Measurable fun p : ℝ≥0 × State => (p.1 : ℝ) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hcomp : Measurable fun p : ℝ≥0 × State => Real.exp (θ * p.1) * V p.2 :=
    (Real.measurable_exp.comp (hcoe.const_mul θ)).mul (hV.comp measurable_snd)
  exact hcomp.sumElim (hcomp.sumElim measurable_const)

variable (M : SegmentModel State)

def clockUpd : ℝ≥0 × (ℝ≥0 × State × ExitKind) → (ℝ≥0 × State) × ExitKind :=
  fun p => ((p.1 + p.2.1, p.2.2.1), p.2.2.2)

lemma measurable_clockUpd : Measurable (clockUpd (State := State)) :=
  ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_fst.comp measurable_snd).comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_snd).comp measurable_snd)

noncomputable def tsegStep : Kernel (ℝ≥0 × State) ((ℝ≥0 × State) × ExitKind) :=
  (Kernel.deterministic clockUpd measurable_clockUpd) ∘ₖ
    ((Kernel.deterministic Prod.fst measurable_fst).prod
      (M.seg.comap Prod.snd measurable_snd))

instance [IsMarkovKernel M.seg] : IsMarkovKernel (tsegStep M) := by
  unfold tsegStep; infer_instance

noncomputable def tcont : Kernel ((ℝ≥0 × State) × ExitKind) (TSkelState State) :=
  (Kernel.deterministic (TSkelState.alive (State := State)) measurable_inl) ∘ₖ
    ((Kernel.deterministic (fun q => q.1.1) (measurable_fst.comp measurable_fst)).prod
      (M.jump.comap (fun q => (q.1.2, q.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

instance [IsMarkovKernel M.jump] : IsMarkovKernel (tcont M) := by
  unfold tcont; infer_instance

noncomputable def tdispatchFun :
    (ℝ≥0 × State) × ExitKind → Measure (TSkelState State) := fun q =>
  if q.2 = ExitKind.alarm ∨ q.2 = ExitKind.guard then tcont M q
  else if q.2 = ExitKind.halt then Measure.dirac (TSkelState.halted q.1)
  else Measure.dirac TSkelState.liveT

lemma measurable_tdispatchFun : Measurable (tdispatchFun M) := by
  refine Measurable.ite ?_ (tcont M).measurable
    (Measurable.ite ?_ ?_ measurable_const)
  · exact ((measurable_snd (measurableSet_singleton ExitKind.alarm)).union
      (measurable_snd (measurableSet_singleton ExitKind.guard)))
  · exact measurable_snd (measurableSet_singleton ExitKind.halt)
  · exact Measure.measurable_dirac.comp
      ((measurable_inr.comp measurable_inl).comp measurable_fst)

noncomputable def tdispatch : Kernel ((ℝ≥0 × State) × ExitKind) (TSkelState State) where
  toFun := tdispatchFun M
  measurable' := measurable_tdispatchFun M

instance [IsMarkovKernel M.jump] : IsMarkovKernel (tdispatch M) := by
  constructor
  intro q
  show IsProbabilityMeasure (tdispatchFun M q)
  unfold tdispatchFun
  split_ifs
  · infer_instance
  · exact Measure.dirac.isProbabilityMeasure
  · exact Measure.dirac.isProbabilityMeasure

noncomputable def tstepAlive : Kernel (ℝ≥0 × State) (TSkelState State) :=
  (tdispatch M) ∘ₖ (tsegStep M)

instance [IsMarkovKernel M.seg] [IsMarkovKernel M.jump] :
    IsMarkovKernel (tstepAlive M) := by
  unfold tstepAlive; infer_instance

noncomputable def tskel : Kernel (TSkelState State) (TSkelState State) where
  toFun :=
    Sum.elim (fun p => tstepAlive M p)
      (Sum.elim (fun p => Measure.dirac (TSkelState.halted p))
        (fun _ => Measure.dirac TSkelState.liveT))
  measurable' :=
    (tstepAlive M).measurable.sumElim
      ((Measure.measurable_dirac.comp (measurable_inr.comp measurable_inl)).sumElim
        measurable_const)

@[simp] lemma tskel_alive (p : ℝ≥0 × State) :
    tskel M (TSkelState.alive p) = tstepAlive M p := rfl

@[simp] lemma tskel_halted (p : ℝ≥0 × State) :
    tskel M (TSkelState.halted p) = Measure.dirac (TSkelState.halted p) := rfl

@[simp] lemma tskel_liveT :
    tskel M (TSkelState.liveT (State := State)) = Measure.dirac TSkelState.liveT := rfl

instance [IsMarkovKernel M.seg] [IsMarkovKernel M.jump] :
    IsMarkovKernel (tskel M) := by
  constructor
  rintro (p | p | u)
  · rw [tskel_alive]; infer_instance
  · rw [tskel_halted]; infer_instance
  · rw [tskel_liveT]; infer_instance

variable {M}

lemma lintegral_tCert_tdispatch [IsMarkovKernel M.jump]
    {V : State → ℝ} (hV : Measurable V) (θ : ℝ)
    (s : ℝ≥0) (o : ℝ≥0 × State × ExitKind) :
    ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tdispatch M (clockUpd (s, o)))
      = expWeight θ s * stepRead M θ V o := by
  have hmeas : Measurable fun w => ENNReal.ofReal (tCert θ V w) :=
    ENNReal.measurable_ofReal.comp (measurable_tCert hV θ)
  have hprod : ∀ q : (ℝ≥0 × State) × ExitKind,
      ((Kernel.deterministic (fun q : (ℝ≥0 × State) × ExitKind => q.1.1)
          (measurable_fst.comp measurable_fst)).prod
        (M.jump.comap (fun q => (q.1.2, q.2))
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))) q
      = (Measure.dirac q.1.1).prod (M.jump (q.1.2, q.2)) := fun q => by
    rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply]
  have hcont : ∀ (s' : ℝ≥0) (y : State) (k : ExitKind),
      ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tcont M ((s', y), k))
        = expWeight θ s' * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, k)) := by
    intro s' y k
    unfold tcont
    rw [Kernel.lintegral_comp _ _ _ hmeas,
      lintegral_congr fun r => Kernel.lintegral_deterministic' measurable_inl hmeas,
      hprod ((s', y), k)]
    rw [Measure.dirac_prod,
      lintegral_map
        (show Measurable fun r : ℝ≥0 × State =>
            ENNReal.ofReal (tCert θ V (Sum.inl r)) from hmeas.comp measurable_inl)
        measurable_prodMk_left]
    calc ∫⁻ z, ENNReal.ofReal (tCert θ V (TSkelState.alive (s', z)))
          ∂(M.jump (y, k))
        = ∫⁻ z, expWeight θ s' * ENNReal.ofReal (V z) ∂(M.jump (y, k)) := by
          refine lintegral_congr fun z => ?_
          rw [tCert_alive, ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rfl
      _ = expWeight θ s' * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, k)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rcases o with ⟨t, y, k⟩
  have happly : ∀ q, tdispatch M q = tdispatchFun M q := fun _ => rfl
  cases k
  case alarm =>
    rw [happly]
    show ∫⁻ w, ENNReal.ofReal (tCert θ V w)
        ∂(tcont M ((s + t, y), ExitKind.alarm)) = _
    rw [hcont (s + t) y ExitKind.alarm]
    show expWeight θ (s + t) * _
        = expWeight θ s * (expWeight θ t
            * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, ExitKind.alarm)))
    rw [expWeight_add, mul_assoc]
  case guard =>
    rw [happly]
    show ∫⁻ w, ENNReal.ofReal (tCert θ V w)
        ∂(tcont M ((s + t, y), ExitKind.guard)) = _
    rw [hcont (s + t) y ExitKind.guard]
    show expWeight θ (s + t) * _
        = expWeight θ s * (expWeight θ t
            * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, ExitKind.guard)))
    rw [expWeight_add, mul_assoc]
  case halt =>
    rw [happly]
    show ∫⁻ w, ENNReal.ofReal (tCert θ V w)
        ∂(Measure.dirac (TSkelState.halted (s + t, y))) = _
    rw [lintegral_dirac' _ hmeas, tCert_halted,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    show expWeight θ (s + t) * ENNReal.ofReal (V y)
        = expWeight θ s * (expWeight θ t * ENNReal.ofReal (V y))
    rw [expWeight_add, mul_assoc]
  case live =>
    rw [happly]
    show ∫⁻ w, ENNReal.ofReal (tCert θ V w)
        ∂(Measure.dirac (TSkelState.liveT (State := State))) = _
    rw [lintegral_dirac' _ hmeas, tCert_liveT]
    show ENNReal.ofReal 0 = expWeight θ s * 0
    simp

lemma lintegral_tCert_tstepAlive [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} (hV : Measurable V) (θ : ℝ) (p : ℝ≥0 × State) :
    ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tstepAlive M p)
      = expWeight θ p.1 * ∫⁻ o, stepRead M θ V o ∂(M.seg p.2) := by
  have hmeas : Measurable fun w => ENNReal.ofReal (tCert θ V w) :=
    ENNReal.measurable_ofReal.comp (measurable_tCert hV θ)
  have hdispmeas : Measurable fun q =>
      ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tdispatch M q) :=
    Measurable.lintegral_kernel_prod_right (κ := tdispatch M)
      (hmeas.comp measurable_snd)
  show ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂((tdispatch M ∘ₖ tsegStep M) p) = _
  rw [Kernel.lintegral_comp _ _ _ hmeas]
  show ∫⁻ q, (∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tdispatch M q))
      ∂((Kernel.deterministic clockUpd measurable_clockUpd ∘ₖ
        ((Kernel.deterministic Prod.fst measurable_fst).prod
          (M.seg.comap Prod.snd measurable_snd))) p) = _
  rw [Kernel.lintegral_comp _ _ _ hdispmeas,
    lintegral_congr fun r =>
      Kernel.lintegral_deterministic' measurable_clockUpd hdispmeas]
  have hprod :
      ((Kernel.deterministic (Prod.fst (α := ℝ≥0) (β := State)) measurable_fst).prod
        (M.seg.comap Prod.snd measurable_snd)) p
      = (Measure.dirac p.1).prod (M.seg p.2) := by
    rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply]
  rw [hprod, Measure.dirac_prod,
    lintegral_map
      (show Measurable fun r : ℝ≥0 × (ℝ≥0 × State × ExitKind) =>
          ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tdispatch M (clockUpd r)) from
        hdispmeas.comp measurable_clockUpd)
      measurable_prodMk_left]
  calc ∫⁻ o, ∫⁻ w, ENNReal.ofReal (tCert θ V w)
          ∂(tdispatch M (clockUpd (p.1, o))) ∂(M.seg p.2)
      = ∫⁻ o, expWeight θ p.1 * stepRead M θ V o ∂(M.seg p.2) :=
        lintegral_congr fun o => lintegral_tCert_tdispatch hV θ p.1 o
    _ = expWeight θ p.1 * ∫⁻ o, stepRead M θ V o ∂(M.seg p.2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem tskel_drift [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ : ℝ} (hV : Measurable V)
    (hSegD : SegmentDynkin M θ V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (q : TSkelState State) :
    ∫⁻ w, ENNReal.ofReal (tCert θ V w) ∂(tskel M q)
      ≤ ENNReal.ofReal (tCert θ V q) := by
  have hmeas : Measurable fun w => ENNReal.ofReal (tCert θ V w) :=
    ENNReal.measurable_ofReal.comp (measurable_tCert hV θ)
  rcases q with p | p | u
  · rw [tskel_alive, lintegral_tCert_tstepAlive hV θ p]
    calc expWeight θ p.1 * ∫⁻ o, stepRead M θ V o ∂(M.seg p.2)
        ≤ expWeight θ p.1 * ENNReal.ofReal (V p.2) := by
          gcongr
          exact iBridge M θ V hSegD hForce hNonneg p.2
      _ = ENNReal.ofReal (tCert θ V (TSkelState.alive p)) := by
          rw [tCert_alive, ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rfl
  · rw [tskel_halted, lintegral_dirac' _ hmeas]
  · rw [tskel_liveT, lintegral_dirac' _ hmeas]

def tbad (T : ℝ≥0) : Set (TSkelState State) :=
  fun q => Sum.elim (fun p : ℝ≥0 × State => T < p.1)
    (Sum.elim (fun p : ℝ≥0 × State => T < p.1) fun _ => False) q

omit [MeasurableSpace State] in
@[simp] lemma tbad_alive {T : ℝ≥0} (p : ℝ≥0 × State) :
    TSkelState.alive p ∈ tbad T ↔ T < p.1 := Iff.rfl

omit [MeasurableSpace State] in
@[simp] lemma tbad_halted {T : ℝ≥0} (p : ℝ≥0 × State) :
    TSkelState.halted p ∈ tbad T ↔ T < p.1 := Iff.rfl

omit [MeasurableSpace State] in
@[simp] lemma tbad_liveT {T : ℝ≥0} :
    TSkelState.liveT (State := State) ∉ tbad T := fun h => h

omit [MeasurableSpace State] in

lemma tbad_eq_clock (T : ℝ≥0) :
    tbad (State := State) T = {q | T < tclock q} := by
  ext q
  rcases q with p | p | u
  · exact Iff.rfl
  · exact Iff.rfl
  · refine ⟨fun h => h.elim, fun h => absurd h ?_⟩
    simp [tclock]

lemma measurableSet_tbad {T : ℝ≥0} :
    MeasurableSet (tbad (State := State) T) := by
  rw [measurableSet_sum_iff]
  constructor
  · have h : (Sum.inl ⁻¹' tbad (State := State) T : Set (ℝ≥0 × State))
        = {p | T < p.1} := rfl
    rw [h]
    exact measurable_fst measurableSet_Ioi
  · rw [measurableSet_sum_iff]
    constructor
    · have h : (Sum.inl ⁻¹' (Sum.inr ⁻¹' tbad (State := State) T)
          : Set (ℝ≥0 × State)) = {p | T < p.1} := rfl
      rw [h]
      exact measurable_fst measurableSet_Ioi
    · have h : (Sum.inr ⁻¹' (Sum.inr ⁻¹' tbad (State := State) T)
          : Set Unit) = ∅ := by
        ext u
        exact ⟨fun h => h, fun h => h.elim⟩
      rw [h]
      exact MeasurableSet.empty

def tbadIn (B : Set State) : Set (TSkelState State) :=
  fun q => Sum.elim (fun p : ℝ≥0 × State => p.2 ∈ B)
    (Sum.elim (fun p : ℝ≥0 × State => p.2 ∈ B) fun _ => False) q

omit [MeasurableSpace State] in
@[simp] lemma tbadIn_alive {B : Set State} (p : ℝ≥0 × State) :
    TSkelState.alive p ∈ tbadIn B ↔ p.2 ∈ B := Iff.rfl

omit [MeasurableSpace State] in
@[simp] lemma tbadIn_halted {B : Set State} (p : ℝ≥0 × State) :
    TSkelState.halted p ∈ tbadIn B ↔ p.2 ∈ B := Iff.rfl

omit [MeasurableSpace State] in
@[simp] lemma tbadIn_liveT {B : Set State} :
    TSkelState.liveT (State := State) ∉ tbadIn B := fun h => h

lemma measurableSet_tbadIn {B : Set State} (hB : MeasurableSet B) :
    MeasurableSet (tbadIn (State := State) B) := by
  rw [measurableSet_sum_iff]
  constructor
  · have h : (Sum.inl ⁻¹' tbadIn (State := State) B : Set (ℝ≥0 × State))
        = {p | p.2 ∈ B} := rfl
    rw [h]
    exact measurable_snd hB
  · rw [measurableSet_sum_iff]
    constructor
    · have h : (Sum.inl ⁻¹' (Sum.inr ⁻¹' tbadIn (State := State) B)
          : Set (ℝ≥0 × State)) = {p | p.2 ∈ B} := rfl
      rw [h]
      exact measurable_snd hB
    · have h : (Sum.inr ⁻¹' (Sum.inr ⁻¹' tbadIn (State := State) B)
          : Set Unit) = ∅ := by
        ext u
        exact ⟨fun h => h, fun h => h.elim⟩
      rw [h]
      exact MeasurableSet.empty

omit [MeasurableSpace State] in

lemma exceed_cases {T : ℝ≥0} {B : Set State} (q : TSkelState State)
    (hq : T < tclock q) :
    (q ∈ tbad T ∧ q ∉ tbadIn B) ∨ (q ∈ tbad T ∧ q ∈ tbadIn B) := by
  have hbad : q ∈ tbad T := by
    rw [tbad_eq_clock]
    exact hq
  by_cases hB : q ∈ tbadIn B
  · exact Or.inr ⟨hbad, hB⟩
  · exact Or.inl ⟨hbad, hB⟩

noncomputable def tCertCap (θ : ℝ) (T : ℝ≥0) (ε : ℝ) (V : State → ℝ)
    (q : TSkelState State) : ℝ :=
  min (tCert θ V q) (ε * Real.exp (θ * T)) / (ε * Real.exp (θ * T))

lemma measurable_tCertCap {V : State → ℝ} (hV : Measurable V) (θ : ℝ)
    (T : ℝ≥0) (ε : ℝ) : Measurable (tCertCap θ T ε V) :=
  ((measurable_tCert hV θ).min measurable_const).div_const _

omit [MeasurableSpace State] in
lemma tCertCap_nonneg {V : State → ℝ} (hNonneg : NonnegV V) {θ ε : ℝ}
    {T : ℝ≥0} (hε : 0 < ε) (q : TSkelState State) :
    0 ≤ tCertCap θ T ε V q := by
  have hKpos : 0 < ε * Real.exp (θ * T) := mul_pos hε (Real.exp_pos _)
  exact div_nonneg (le_min (tCert_nonneg hNonneg θ q) hKpos.le) hKpos.le

omit [MeasurableSpace State] in
lemma tCertCap_le_one {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0} (hε : 0 < ε)
    (q : TSkelState State) : tCertCap θ T ε V q ≤ 1 := by
  rw [tCertCap, div_le_one (mul_pos hε (Real.exp_pos _))]
  exact min_le_right _ _

omit [MeasurableSpace State] in

lemma tCertCap_floor {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0} (hθ : 0 ≤ θ)
    (hε : 0 < ε) (hFloor : ∀ y, ε ≤ V y) :
    ∀ q ∈ tbad (State := State) T, 1 ≤ tCertCap θ T ε V q := by
  have hKpos : 0 < ε * Real.exp (θ * T) := mul_pos hε (Real.exp_pos _)
  have key : ∀ (s : ℝ≥0) (y : State), T < s →
      ε * Real.exp (θ * T) ≤ Real.exp (θ * s) * V y := by
    intro s y hTs
    have hexp : Real.exp (θ * T) ≤ Real.exp (θ * s) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hTs.le) hθ)
    calc ε * Real.exp (θ * T) = Real.exp (θ * T) * ε := mul_comm _ _
      _ ≤ Real.exp (θ * s) * V y :=
          mul_le_mul hexp (hFloor y) hε.le (Real.exp_nonneg _)
  rintro (p | p | u) hq
  · have h := key p.1 p.2 hq
    show (1 : ℝ) ≤ tCertCap θ T ε V (TSkelState.alive p)
    rw [tCertCap, tCert_alive, min_eq_right h]
    exact le_of_eq (div_self hKpos.ne').symm
  · have h := key p.1 p.2 hq
    show (1 : ℝ) ≤ tCertCap θ T ε V (TSkelState.halted p)
    rw [tCertCap, tCert_halted, min_eq_right h]
    exact le_of_eq (div_self hKpos.ne').symm
  · exact hq.elim

lemma tskel_drift_capped [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0}
    (hV : Measurable V) (hSegD : SegmentDynkin M θ V)
    (hForce : ForcedNonexpansion M V) (hNonneg : NonnegV V) (hε : 0 < ε)
    (q : TSkelState State) :
    ∫ w, tCertCap θ T ε V w ∂(tskel M q) ≤ tCertCap θ T ε V q := by
  set K : ℝ := ε * Real.exp (θ * T) with hKdef
  have hKpos : 0 < K := mul_pos hε (Real.exp_pos _)
  have hminmeas : Measurable fun w : TSkelState State => min (tCert θ V w) K :=
    (measurable_tCert hV θ).min measurable_const
  have hminnonneg : ∀ w : TSkelState State, 0 ≤ min (tCert θ V w) K :=
    fun w => le_min (tCert_nonneg hNonneg θ w) hKpos.le

  have hlin : ∫⁻ w, ENNReal.ofReal (min (tCert θ V w) K) ∂(tskel M q)
      ≤ ENNReal.ofReal (min (tCert θ V q) K) := by
    have h1 : ∫⁻ w, ENNReal.ofReal (min (tCert θ V w) K) ∂(tskel M q)
        ≤ ENNReal.ofReal (tCert θ V q) :=
      le_trans (lintegral_mono fun w => ENNReal.ofReal_le_ofReal (min_le_left _ _))
        (tskel_drift hV hSegD hForce hNonneg q)
    have h2 : ∫⁻ w, ENNReal.ofReal (min (tCert θ V w) K) ∂(tskel M q)
        ≤ ENNReal.ofReal K := by
      calc ∫⁻ w, ENNReal.ofReal (min (tCert θ V w) K) ∂(tskel M q)
          ≤ ∫⁻ _, ENNReal.ofReal K ∂(tskel M q) :=
            lintegral_mono fun w => ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = ENNReal.ofReal K := by
            rw [lintegral_const, measure_univ, mul_one]
    have hofmin : ENNReal.ofReal (min (tCert θ V q) K)
        = min (ENNReal.ofReal (tCert θ V q)) (ENNReal.ofReal K) := by
      rcases le_total (tCert θ V q) K with h | h
      · rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
      · rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]
    rw [hofmin]
    exact le_min h1 h2

  have hboch : ∫ w, min (tCert θ V w) K ∂(tskel M q) ≤ min (tCert θ V q) K := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun w => hminnonneg w)
      hminmeas.aestronglyMeasurable]
    calc (∫⁻ w, ENNReal.ofReal (min (tCert θ V w) K) ∂(tskel M q)).toReal
        ≤ (ENNReal.ofReal (min (tCert θ V q) K)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = min (tCert θ V q) K := ENNReal.toReal_ofReal (hminnonneg q)
  calc ∫ w, tCertCap θ T ε V w ∂(tskel M q)
      = (∫ w, min (tCert θ V w) K ∂(tskel M q)) / K := by
        simp only [tCertCap, ← hKdef, div_eq_mul_inv]
        exact integral_mul_const _ _
    _ ≤ min (tCert θ V q) K / K := by gcongr
    _ = tCertCap θ T ε V q := rfl

theorem sound_GSHS_deadline [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0}
    (hV : Measurable V) (hθ : 0 ≤ θ)
    (hSegD : SegmentDynkin M θ V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (hε : 0 < ε) (hFloor : ∀ y, ε ≤ V y) (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, T < tclock (ω n)}
      ≤ ENNReal.ofReal (Real.exp (-(θ * T)) * V x / ε) := by
  have hKpos : 0 < ε * Real.exp (θ * T) := mul_pos hε (Real.exp_pos _)
  have hevent : {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n)}
      = {ω | ∃ n, ω n ∈ tbad T} := by
    ext ω
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [tbad_eq_clock]
      exact hn
    · rintro ⟨n, hn⟩
      rw [tbad_eq_clock] at hn
      exact ⟨n, hn⟩
  rw [hevent]
  have h := Battery.measure_reach_le (K := tskel M)
    measurableSet_tbad (measurable_tCertCap hV θ T ε)
    (tCertCap_nonneg hNonneg hε) (tCertCap_le_one hε)
    (tCertCap_floor hθ hε hFloor)
    (fun q _ => tskel_drift_capped hV hSegD hForce hNonneg hε q)
    (TSkelState.alive (0, x))
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hstart : tCertCap θ T ε V (TSkelState.alive (0, x))
      = min (V x) (ε * Real.exp (θ * T)) / (ε * Real.exp (θ * T)) := by
    rw [tCertCap, tCert_alive]
    norm_num
  rw [hstart]
  have hle : min (V x) (ε * Real.exp (θ * T)) / (ε * Real.exp (θ * T))
      ≤ V x / (ε * Real.exp (θ * T)) := by
    gcongr
    exact min_le_left _ _
  refine hle.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

theorem sound_GSHS_deadline_offTarget [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε : ℝ} {T : ℝ≥0} {B : Set State}
    (hV : Measurable V) (hθ : 0 ≤ θ) (hB : MeasurableSet B)
    (hSegD : SegmentDynkin M θ V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (hε : 0 < ε) (hFloorB : ∀ y ∉ B, ε ≤ V y)
    (x : State) :
    Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
        {ω | ∃ n, T < tclock (ω n) ∧ ω n ∉ tbadIn B}
      ≤ ENNReal.ofReal (Real.exp (-(θ * T)) * V x / ε) := by
  have hKpos : 0 < ε * Real.exp (θ * T) := mul_pos hε (Real.exp_pos _)
  have hevent : {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n) ∧ ω n ∉ tbadIn B}
      = {ω | ∃ n, ω n ∈ (tbad T \ tbadIn B : Set (TSkelState State))} := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnB⟩
      refine ⟨n, ?_, hnB⟩
      rw [tbad_eq_clock]
      exact hn
    · rintro ⟨n, hn, hnB⟩
      rw [tbad_eq_clock] at hn
      exact ⟨n, hn, hnB⟩
  rw [hevent]
  have hfloor : ∀ q ∈ (tbad (State := State) T \ tbadIn B),
      1 ≤ tCertCap θ T ε V q := by
    have key : ∀ (s : ℝ≥0) (y : State), T < s → y ∉ B →
        ε * Real.exp (θ * T) ≤ Real.exp (θ * s) * V y := by
      intro s y hTs hyB
      have hexp : Real.exp (θ * T) ≤ Real.exp (θ * s) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hTs.le) hθ)
      calc ε * Real.exp (θ * T) = Real.exp (θ * T) * ε := mul_comm _ _
        _ ≤ Real.exp (θ * s) * V y :=
            mul_le_mul hexp (hFloorB y hyB) hε.le (Real.exp_nonneg _)
    rintro (p | p | u) ⟨hq, hqB⟩
    · have hyB : p.2 ∉ B := fun hmem => hqB hmem
      have h := key p.1 p.2 hq hyB
      show (1 : ℝ) ≤ tCertCap θ T ε V (TSkelState.alive p)
      rw [tCertCap, tCert_alive, min_eq_right h]
      exact le_of_eq (div_self hKpos.ne').symm
    · have hyB : p.2 ∉ B := fun hmem => hqB hmem
      have h := key p.1 p.2 hq hyB
      show (1 : ℝ) ≤ tCertCap θ T ε V (TSkelState.halted p)
      rw [tCertCap, tCert_halted, min_eq_right h]
      exact le_of_eq (div_self hKpos.ne').symm
    · exact hq.elim
  have h := Battery.measure_reach_le (K := tskel M)
    (measurableSet_tbad.diff (measurableSet_tbadIn hB))
    (measurable_tCertCap hV θ T ε)
    (tCertCap_nonneg hNonneg hε) (tCertCap_le_one hε) hfloor
    (fun q _ => tskel_drift_capped hV hSegD hForce hNonneg hε q)
    (TSkelState.alive (0, x))
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hstart : tCertCap θ T ε V (TSkelState.alive (0, x))
      = min (V x) (ε * Real.exp (θ * T)) / (ε * Real.exp (θ * T)) := by
    rw [tCertCap, tCert_alive]
    norm_num
  rw [hstart]
  have hle : min (V x) (ε * Real.exp (θ * T)) / (ε * Real.exp (θ * T))
      ≤ V x / (ε * Real.exp (θ * T)) := by
    gcongr
    exact min_le_left _ _
  refine hle.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

theorem sound_GSHS_deadline_battery [IsMarkovKernel M.seg] [IsMarkovKernel M.jump]
    {V : State → ℝ} {θ ε p thr : ℝ} {T : ℝ≥0}
    (hV : Measurable V) (hθ : 0 ≤ θ)
    (hSegD : SegmentDynkin M θ V) (hForce : ForcedNonexpansion M V)
    (hNonneg : NonnegV V) (hε : 0 < ε) (hFloor : ∀ y, ε ≤ V y)
    (hΘ : p + Real.exp (-(θ * T)) * thr / ε ≤ 1) (x : State) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
      {ω | ∀ n, tclock (ω n) ≤ T} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]
    exact zero_le
  have hreach := sound_GSHS_deadline (T := T) hV hθ hSegD hForce hNonneg hε hFloor x
  have hthr0 : 0 ≤ thr := (hNonneg x).trans hthr
  have hmono : Real.exp (-(θ * T)) * V x / ε ≤ Real.exp (-(θ * T)) * thr / ε := by
    gcongr
  have h1 : Battery.pathMeasure (tskel M) (TSkelState.alive (0, x))
      {ω | ∃ n, T < tclock (ω n)}
      ≤ ENNReal.ofReal (Real.exp (-(θ * T)) * thr / ε) :=
    hreach.trans (ENNReal.ofReal_le_ofReal hmono)
  have hnever : {ω : ℕ → TSkelState State | ∀ n, tclock (ω n) ≤ T}
      = {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hreachMeas : MeasurableSet
      {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n)} := by
    have h : {ω : ℕ → TSkelState State | ∃ n, T < tclock (ω n)}
        = ⋃ n, (fun ω : ℕ → TSkelState State => ω n) ⁻¹' tbad T := by
      ext ω
      constructor
      · rintro ⟨n, hn⟩
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        rw [Set.mem_preimage, tbad_eq_clock]
        exact hn
      · intro hmem
        rcases Set.mem_iUnion.1 hmem with ⟨n, hn⟩
        rw [Set.mem_preimage, tbad_eq_clock] at hn
        exact ⟨n, hn⟩
    rw [h]
    exact MeasurableSet.iUnion fun n => (measurable_pi_apply n) measurableSet_tbad
  have hq0 : 0 ≤ Real.exp (-(θ * T)) * thr / ε :=
    div_nonneg (mul_nonneg (Real.exp_nonneg _) hthr0) hε.le
  rw [hnever, prob_compl_eq_one_sub hreachMeas]
  refine le_trans ?_ (tsub_le_tsub_left h1 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add hq0 hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Qtsl.LayerD
