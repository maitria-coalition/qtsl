import QtslAux.Sweep.Discrete

/-! # The `FaultyVaryingLastStep` benchmark row

Machine-generated theorem file internalizing a certified reachability bound for the
`FaultyVaryingLastStep` benchmark system as a Lean-checked consequence of its certificate.

The system is a Markov chain on `ℤ × ℤ` (counter, fault flag): while the flag is `0` and the
counter is below `10`, each step raises the fault flag with probability `1/1000` — except at
counter value `9`, the last active position, where the fault probability is `1/100` — and
otherwise either advances the counter or stays in place with equal probability; all other states
are absorbing. The certificate is the exact-rational table `tbl`, packaged as the supermartingale
witness `V`; its bounds, barrier, and drift conditions are verified by `norm_num`-level rational
arithmetic and discharged through `Sweep.reach_le_of_battery`.

* `sound`: starting from `(1, 0)`, the probability that the fault flag is ever raised is at most
  the certificate value at the initial state, stated as an exact rational;
* `sound_dec`: the same bound relaxed to the decimal bound `0.0353614`.
-/

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.FaultyVaryingLastStep

abbrev S : Type := ℤ × ℤ

noncomputable def tbl : ℤ → ℝ := fun i =>
  if i = 0 then 345471882992881537630409621537191 / 9264785863339884953421537191000000
  else if i = 1 then 327288091907714830296257346191 / 9255530333006878075346191000000
  else if i = 2 then 309104609927158050120155191 / 9246284048957920155191000000
  else if i = 3 then 290921418868020137964191 / 9237047001955964191000000
  else if i = 4 then 272738500547382773191 / 9227819182773191000000
  else if i = 5 then 254555836782582191 / 9218600582191000000
  else if i = 6 then 236373409391191 / 9209391191000000
  else if i = 7 then 218191200191 / 9200191000000
  else if i = 8 then 200009191 / 9191000000
  else if i = 9 then 2000101 / 101000000
  else if i = 10 then 1 / 1000000
  else 1

noncomputable def V : S → ℝ := fun s =>
  if s.2 ≠ 0 then 1
  else if 0 ≤ s.1 ∧ s.1 ≤ 10 then tbl s.1
  else 1

noncomputable def step : S → Measure S := fun s =>
  if s.1 < 10 ∧ s.2 = 0 then
    if s.1 < 9 then Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
    else Sweep.mix3 (1 / 100) (99 / 200) (99 / 200) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
  else Measure.dirac s

lemma step_active0 {i : ℤ} (hg : i < 10) (hr : i < 9) :
    step (i, 0) = Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (i, 1) (i + 1, 0) (i, 0) := by
  simp only [step]
  rw [if_pos (by exact ⟨hg, by trivial⟩)]
  rw [if_pos (by omega)]

lemma step_active1 {i : ℤ} (hg : i < 10) (hr : i ≥ 9) :
    step (i, 0) = Sweep.mix3 (1 / 100) (99 / 200) (99 / 200) (i, 1) (i + 1, 0) (i, 0) := by
  simp only [step]
  rw [if_pos (by exact ⟨hg, by trivial⟩)]
  rw [if_neg (by omega)]

lemma step_prob : ∀ s, IsProbabilityMeasure (step s) := by
  intro s
  unfold step
  split_ifs
  · exact Sweep.isProbabilityMeasure_mix3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _
  · exact Sweep.isProbabilityMeasure_mix3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _
  · infer_instance

instance : IsMarkovKernel (Sweep.ofFun step) := Sweep.isMarkovKernel_ofFun step_prob

lemma V_bounds : ∀ y : S, 0 ≤ V y ∧ V y ≤ 1 := by
  intro y
  obtain ⟨i, e⟩ := y
  by_cases he : e ≠ 0
  · norm_num [V, he]
  · by_cases hw : 0 ≤ i ∧ i ≤ 10
    · have he' : e = 0 := not_not.1 he
      subst he'
      obtain ⟨h1, h2⟩ := hw
      interval_cases i <;> norm_num [V, tbl]
    · norm_num [V, he, hw]

lemma V_nonneg : ∀ y : S, 0 ≤ V y := fun y => (V_bounds y).1

lemma V_le_one : ∀ y : S, V y ≤ 1 := fun y => (V_bounds y).2

lemma V_barrier : ∀ y ∈ {s : S | s.2 ≠ 0}, 1 ≤ V y := by
  intro y hy; simp only [Set.mem_setOf_eq] at hy; simp [V, hy]

lemma V_drift : ∀ y : S, y ∉ {s : S | s.2 ≠ 0} → ∫ z, V z ∂(step y) ≤ V y := by
  intro y hy
  obtain ⟨i, e⟩ := y
  simp only [Set.mem_setOf_eq, not_not] at hy
  subst hy
  by_cases hg : i < 10
  · by_cases hlo : 0 ≤ i
    · interval_cases i <;>
        (first
          | rw [step_active0 (by norm_num) (by omega),
              Sweep.integral_mix3 V (by norm_num) (by norm_num) (by norm_num)]
          | rw [step_active1 (by norm_num) (by omega),
              Sweep.integral_mix3 V (by norm_num) (by norm_num) (by norm_num)]
        ) <;> norm_num [V, tbl]
    · have : IsProbabilityMeasure (step (i, 0)) := step_prob _
      refine (Sweep.integral_le_of_le_const V_nonneg V_le_one).trans_eq ?_
      simp [V, hlo]
  · rw [show step (i, 0) = Measure.dirac (i, 0) by simp [step, hg],
      Sweep.integral_dirac_self]

theorem sound :
    Battery.pathMeasure (Sweep.ofFun step) ((1 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal (327288091907714830296257346191 / 9255530333006878075346191000000) := by
  have h := Sweep.reach_le_of_battery step {s : S | s.2 ≠ 0} V 1
    V_nonneg V_le_one V_barrier V_drift ((1 : ℤ), (0 : ℤ))
  have hV : V ((1 : ℤ), (0 : ℤ)) = 327288091907714830296257346191 / 9255530333006878075346191000000 := by norm_num [V, tbl]
  rw [hV] at h
  exact h

theorem sound_dec :
    Battery.pathMeasure (Sweep.ofFun step) ((1 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal 0.0353614 :=
  sound.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end Qtsl.Sweep.FaultyVaryingLastStep
