import QtslAux.LayerD
import QtslAux.Battery

/-! # The outcome-step kernel and jump-time processes

This module lifts a segment model to a Markov chain on the outcome space
`ℝ≥0 × State × ExitKind` and provides the path-space infrastructure used by the
non-Zeno arguments.

* `outStep M`: the kernel that, from an outcome whose exit kind is `alarm` or
  `guard`, runs the reset followed by the next segment (`M.seg ∘ₖ M.jump`), and
  freezes terminal (`halt`/`live`) outcomes as Dirac points with zero dwell
  time; it is a Markov kernel whenever `M.seg` and `M.jump` are.
* `jumpTimes n ω`: the cumulative dwell time of the first `n + 1` outcomes
  along a path `ω`, monotone in `n` (`jumpTimes_monotone`) and adapted to the
  canonical filtration (`jumpTimes_adapted`).
* `outReach U`: the path event of ever visiting a non-`live` outcome whose
  state lies in `U`, with measurability lemma `measurableSet_outReach`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Qtsl.LayerD

variable {State : Type*} [MeasurableSpace State]

noncomputable def outStepFun (M : SegmentModel State) :
    ℝ≥0 × State × ExitKind → Measure (ℝ≥0 × State × ExitKind) := fun o =>
  if o.2.2 = ExitKind.alarm ∨ o.2.2 = ExitKind.guard then
    (M.seg ∘ₖ M.jump) (o.2.1, o.2.2)
  else Measure.dirac (0, o.2.1, o.2.2)

lemma measurable_outStepFun (M : SegmentModel State) :
    Measurable (outStepFun M) := by
  have hval : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.1 :=
    measurable_fst.comp measurable_snd
  have hkind : Measurable fun o : ℝ≥0 × State × ExitKind => o.2.2 :=
    measurable_snd.comp measurable_snd
  refine Measurable.ite ?_ ?_ ?_
  · exact ((hkind (measurableSet_singleton ExitKind.alarm)).union
      (hkind (measurableSet_singleton ExitKind.guard)))
  · exact (M.seg ∘ₖ M.jump).measurable.comp (hval.prodMk hkind)
  · exact Measure.measurable_dirac.comp
      ((measurable_const (a := (0 : ℝ≥0))).prodMk (hval.prodMk hkind))

noncomputable def outStep (M : SegmentModel State) :
    Kernel (ℝ≥0 × State × ExitKind) (ℝ≥0 × State × ExitKind) where
  toFun := outStepFun M
  measurable' := measurable_outStepFun M

instance (M : SegmentModel State) [IsMarkovKernel M.seg] [IsMarkovKernel M.jump] :
    IsMarkovKernel (outStep M) := by
  constructor
  intro o
  show IsProbabilityMeasure (outStepFun M o)
  unfold outStepFun
  split_ifs
  · infer_instance
  · exact Measure.dirac.isProbabilityMeasure

def jumpTimes (n : ℕ) (ω : ℕ → ℝ≥0 × State × ExitKind) : ℝ≥0 :=
  ∑ i ∈ range (n + 1), (ω i).1

omit [MeasurableSpace State] in

lemma jumpTimes_monotone (ω : ℕ → ℝ≥0 × State × ExitKind) :
    Monotone fun n => jumpTimes n ω := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset fun x hx =>
    Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hx) (Nat.succ_le_succ hab))

lemma jumpTimes_adapted (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE
      (X := fun _ : ℕ => ℝ≥0 × State × ExitKind) n] (jumpTimes (State := State) n) := by
  refine Finset.measurable_sum _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  exact measurable_fst.comp (Battery.measurable_coord_piLE hin)

def outReach (U : Set State) : Set (ℕ → ℝ≥0 × State × ExitKind) :=
  {ω | ∃ n, (ω n).2.1 ∈ U ∧ (ω n).2.2 ≠ ExitKind.live}

lemma measurableSet_outReach {U : Set State} (hU : MeasurableSet U) :
    MeasurableSet (outReach (State := State) U) := by
  have h : outReach (State := State) U
      = ⋃ n, (fun ω : ℕ → ℝ≥0 × State × ExitKind => ω n) ⁻¹'
          {o : ℝ≥0 × State × ExitKind | o.2.1 ∈ U ∧ o.2.2 ≠ ExitKind.live} := by
    ext ω
    simp [outReach]
  rw [h]
  refine MeasurableSet.iUnion fun n => (measurable_pi_apply n) ?_
  exact MeasurableSet.inter
    ((measurable_fst.comp measurable_snd) hU)
    (((measurable_snd.comp measurable_snd)
      (measurableSet_singleton ExitKind.live)).compl)

end Qtsl.LayerD
