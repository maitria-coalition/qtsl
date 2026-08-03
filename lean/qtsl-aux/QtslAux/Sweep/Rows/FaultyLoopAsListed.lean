import QtslAux.Sweep.Discrete

/-! # The `FaultyLoopAsListed` benchmark row

Machine-generated theorem file internalizing a certified reachability bound for the
`FaultyLoopAsListed` benchmark system as a Lean-checked consequence of its certificate.

The system is a Markov chain on `ℤ × ℤ` (counter, fault flag): while the flag is `0` and the
counter is below `10`, each step raises the fault flag with probability `1/1000` and otherwise
either advances the counter or stays in place, with probability `999/2000` each; all other states
are absorbing. The dynamics agree with the `FaultyLoop` row; only the initial state differs. The
certificate is the exact-rational table `tbl`, packaged as the supermartingale witness `V`; its
bounds, barrier, and drift conditions are verified by `norm_num`-level rational arithmetic and
discharged through `Sweep.reach_le_of_battery`.

* `sound`: starting from `(0, 0)`, the probability that the fault flag is ever raised is at most
  the certificate value at the initial state, stated as an exact rational;
* `sound_dec`: the same bound relaxed to the decimal bound `0.0198024`.
-/

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.FaultyLoopAsListed

abbrev S : Type := ℤ × ℤ

noncomputable def tbl : ℤ → ℝ := fun i =>
  if i = 0 then 20001250045624210492210140045010001 / 1010045120210252210120045010001000000
  else if i = 1 then 18001177036336126198084038009001 / 1009036084126126084036009001000000
  else if i = 2 then 16001120028168070072028008001 / 1008028056070056028008001000000
  else if i = 3 then 14001077021077035023007001 / 1007021035035021007001000000
  else if i = 4 then 12001046015032015006001 / 1006015020015006001000000
  else if i = 5 then 10001025010012005001 / 1005010010005001000000
  else if i = 6 then 8001012006004001 / 1004006004001000000
  else if i = 7 then 6001005003001 / 1003003001000000
  else if i = 8 then 4001002001 / 1002001000000
  else if i = 9 then 2001001 / 1001000000
  else if i = 10 then 1 / 1000000
  else 1

noncomputable def V : S → ℝ := fun s =>
  if s.2 ≠ 0 then 1
  else if 0 ≤ s.1 ∧ s.1 ≤ 10 then tbl s.1
  else 1

noncomputable def step : S → Measure S := fun s =>
  if s.1 < 10 ∧ s.2 = 0 then
    Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
  else Measure.dirac s

lemma step_active0 {i : ℤ} (hg : i < 10) :
    step (i, 0) = Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (i, 1) (i + 1, 0) (i, 0) := by
  simp [step, hg]

lemma step_prob : ∀ s, IsProbabilityMeasure (step s) := by
  intro s
  unfold step
  split_ifs
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
        rw [step_active0 (by norm_num),
          Sweep.integral_mix3 V (by norm_num) (by norm_num) (by norm_num)] <;>
        norm_num [V, tbl]
    · have : IsProbabilityMeasure (step (i, 0)) := step_prob _
      refine (Sweep.integral_le_of_le_const V_nonneg V_le_one).trans_eq ?_
      simp [V, hlo]
  · rw [show step (i, 0) = Measure.dirac (i, 0) by simp [step, hg],
      Sweep.integral_dirac_self]

theorem sound :
    Battery.pathMeasure (Sweep.ofFun step) ((0 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal (20001250045624210492210140045010001 / 1010045120210252210120045010001000000) := by
  have h := Sweep.reach_le_of_battery step {s : S | s.2 ≠ 0} V 1
    V_nonneg V_le_one V_barrier V_drift ((0 : ℤ), (0 : ℤ))
  have hV : V ((0 : ℤ), (0 : ℤ)) = 20001250045624210492210140045010001 / 1010045120210252210120045010001000000 := by norm_num [V, tbl]
  rw [hV] at h
  exact h

theorem sound_dec :
    Battery.pathMeasure (Sweep.ofFun step) ((0 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal 0.0198024 :=
  sound.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end Qtsl.Sweep.FaultyLoopAsListed
