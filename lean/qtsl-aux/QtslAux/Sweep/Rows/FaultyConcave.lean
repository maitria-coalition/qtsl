import QtslAux.Sweep.Discrete

/-! # The `FaultyConcave` benchmark row

Machine-generated theorem file internalizing a certified reachability bound for the
`FaultyConcave` benchmark system as a Lean-checked consequence of its certificate.

The system is a Markov chain on `ℤ × ℤ` (counter, fault flag): while the flag is `0` and the
counter is below `10`, each step raises the fault flag with probability `1/1000` when the counter
is below `4` and `1/100` afterwards, and otherwise either advances the counter or stays in place
with equal probability; all other states are absorbing. The certificate is the exact-rational
table `tbl`, packaged as the supermartingale witness `V`; its bounds, barrier, and drift
conditions are verified by `norm_num`-level rational arithmetic and discharged through
`Sweep.reach_le_of_battery`.

* `sound`: starting from `(1, 0)`, the probability that the fault flag is ever raised is at most
  the certificate value at the initial state, stated as an exact rational;
* `sound_dec`: the same bound relaxed to the decimal bound `0.1183897`.
-/

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.FaultyConcave

abbrev S : Type := ℤ × ℤ

noncomputable def tbl : ℤ → ℝ := fun i =>
  if i = 0 then 8746246596867769377701561 / 72793702928177701561000000
  else if i = 1 then 94703552915782550546171 / 799930801408546171000000
  else if i = 2 then 1025183351109567126881 / 8790448367126881000000
  else if i = 3 then 11094914916515704691 / 96598333704691000000
  else if i = 4 then 120041062720150601 / 1061520150601000000
  else if i = 5 then 1000210512100501 / 10510100501000000
  else if i = 6 then 8000904060401 / 104060401000000
  else if i = 7 then 60003030301 / 1030301000000
  else if i = 8 then 400010201 / 10201000000
  else if i = 9 then 2000101 / 101000000
  else if i = 10 then 1 / 1000000
  else 1

noncomputable def V : S → ℝ := fun s =>
  if s.2 ≠ 0 then 1
  else if 0 ≤ s.1 ∧ s.1 ≤ 10 then tbl s.1
  else 1

noncomputable def step : S → Measure S := fun s =>
  if s.1 < 10 ∧ s.2 = 0 then
    if s.1 < 4 then Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
    else Sweep.mix3 (1 / 100) (99 / 200) (99 / 200) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
  else Measure.dirac s

lemma step_active0 {i : ℤ} (hg : i < 10) (hr : i < 4) :
    step (i, 0) = Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (i, 1) (i + 1, 0) (i, 0) := by
  simp only [step]
  rw [if_pos (by exact ⟨hg, by trivial⟩)]
  rw [if_pos (by omega)]

lemma step_active1 {i : ℤ} (hg : i < 10) (hr : i ≥ 4) :
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
      ≤ ENNReal.ofReal (94703552915782550546171 / 799930801408546171000000) := by
  have h := Sweep.reach_le_of_battery step {s : S | s.2 ≠ 0} V 1
    V_nonneg V_le_one V_barrier V_drift ((1 : ℤ), (0 : ℤ))
  have hV : V ((1 : ℤ), (0 : ℤ)) = 94703552915782550546171 / 799930801408546171000000 := by norm_num [V, tbl]
  rw [hV] at h
  exact h

theorem sound_dec :
    Battery.pathMeasure (Sweep.ofFun step) ((1 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal 0.1183897 :=
  sound.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end Qtsl.Sweep.FaultyConcave
