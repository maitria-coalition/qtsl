import QtslAux.Sweep.Discrete

/-! # The `FaultyNdecr` benchmark row

Machine-generated theorem file internalizing a certified reachability bound for the `FaultyNdecr`
benchmark system as a Lean-checked consequence of its certificate.

The system is a Markov chain on `ℤ × ℤ` (counter, fault flag): while the flag is `0` and the
counter is below `29`, each step raises the fault flag with probability `1/1000` and otherwise
either advances the counter or stays in place, with probability `999/2000` each; all other states
are absorbing. The certificate is the exact-rational table `tbl`, packaged as the supermartingale
witness `V`; its bounds, barrier, and drift conditions are verified by `norm_num`-level rational
arithmetic and discharged through `Sweep.reach_le_of_battery`.

* `sound`: starting from `(1, 0)`, the probability that the fault flag is ever raised is at most
  the certificate value at the initial state, stated as an exact rational;
* `sound_dec`: the same bound relaxed to the decimal bound `0.0544619`.
-/

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.FaultyNdecr

abbrev S : Type := ℤ × ℤ

noncomputable def tbl : ℤ → ℝ := fun i =>
  if i = 0 then 58008337647190991811615161374785387238994175178585905580914320248746302640779566654408029001 / 1029409677870231585082180069659253876551386675845552330029298706255138778754654406029001000000
  else if i = 1 then 56007580577858941751740997973479499034121677020977056112388089485976844852478332378028001 / 1028381296573657927155025044614639237314072603242310020009289416838300478276378028001000000
  else if i = 2 then 54006877515404407096273930846104456933706112569480776124637983361190748254925353027001 / 1027353942631026900254770274340298938375696906335974045963326090747552925351027001000000
  else if i = 3 then 52006226459176331617138480857210272043562591680576176713064590300994952652325026001 / 1026327615016010889365404869470828110265431474861112933030295794952600325026001000000
  else if i = 4 then 50005625408573664711667742536058623212042282833954411255902453143252300302025001 / 1025302312703307581783621248222605504760670804057055877153142652300300025001000000
  else if i = 5 then 48005072363043360849557853772760747141269115256447902246642562628072276024001 / 1024278034668638942840780467754850654106564239817238638514628024276024001000000
  else if i = 6 then 46004565322078379065827030836493707564203511882453275690658362771255023001 / 1023254779888750192648132335419431222883680559257980657856771253023001000000
  else if i = 7 then 44004102285215682497778705678932346919484827993286642421316584231022001 / 1022232547341408783864268067352079143739940618639341316540231022001000000
  else if i = 8 then 42003681252034237963968344489715475990242134346254355406330212021001 / 1021211336005403380483784283069010133606334284354986330210021001000000
  else if i = 9 then 40003300222153015583173566474065079126078566777788846180190020001 / 1020191144860542837646138144924086047558775508846140190020001000000
  else if i = 10 then 38002957195228988431367219825634507896422895632218969173019001 / 1019171972887655182463674470453632415143631876969171019001000000
  else if i = 11 then 36002650170955132234693107870311806978574203060852153018001 / 1018153819068586595867806663789842572571060816153018001000000
  else if i = 12 then 34002377149058425096444092359081465142190652680138017001 / 1017136682386200395472334329460382190380680136017001000000
  else if i = 13 then 32002136129297847256042332890184013489820592120016001 / 1016120561824376019452881448012369820560120016001000000
  else if i = 14 then 30001925111462380878021451442738004575455107015001 / 1015105456368008011441440008004365455105015001000000
  else if i = 15 then 28001742095369009869010439005731001392091014001 / 1014091365003005006435005003001364091014001000000
  else if i = 16 then 26001585080860719720719147287871286080013001 / 1013078286716288717717287715286078013001000000
  else if i = 17 then 24001452067804497376925232495244066012001 / 1012066220495792924792495220066012001000000
  else if i = 18 then 22001341056089331122462440165057011001 / 1011055165330462462330165055011001000000
  else if i = 19 then 20001250045624210492210140045010001 / 1010045120210252210120045010001000000
  else if i = 20 then 18001177036336126198084038009001 / 1009036084126126084036009001000000
  else if i = 21 then 16001120028168070072028008001 / 1008028056070056028008001000000
  else if i = 22 then 14001077021077035023007001 / 1007021035035021007001000000
  else if i = 23 then 12001046015032015006001 / 1006015020015006001000000
  else if i = 24 then 10001025010012005001 / 1005010010005001000000
  else if i = 25 then 8001012006004001 / 1004006004001000000
  else if i = 26 then 6001005003001 / 1003003001000000
  else if i = 27 then 4001002001 / 1002001000000
  else if i = 28 then 2001001 / 1001000000
  else if i = 29 then 1 / 1000000
  else 1

noncomputable def V : S → ℝ := fun s =>
  if s.2 ≠ 0 then 1
  else if 0 ≤ s.1 ∧ s.1 ≤ 29 then tbl s.1
  else 1

noncomputable def step : S → Measure S := fun s =>
  if s.1 < 29 ∧ s.2 = 0 then
    Sweep.mix3 (1 / 1000) (999 / 2000) (999 / 2000) (s.1, 1) (s.1 + 1, 0) (s.1, 0)
  else Measure.dirac s

lemma step_active0 {i : ℤ} (hg : i < 29) :
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
  · by_cases hw : 0 ≤ i ∧ i ≤ 29
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
  by_cases hg : i < 29
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
    Battery.pathMeasure (Sweep.ofFun step) ((1 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal (56007580577858941751740997973479499034121677020977056112388089485976844852478332378028001 / 1028381296573657927155025044614639237314072603242310020009289416838300478276378028001000000) := by
  have h := Sweep.reach_le_of_battery step {s : S | s.2 ≠ 0} V 1
    V_nonneg V_le_one V_barrier V_drift ((1 : ℤ), (0 : ℤ))
  have hV : V ((1 : ℤ), (0 : ℤ)) = 56007580577858941751740997973479499034121677020977056112388089485976844852478332378028001 / 1028381296573657927155025044614639237314072603242310020009289416838300478276378028001000000 := by norm_num [V, tbl]
  rw [hV] at h
  exact h

theorem sound_dec :
    Battery.pathMeasure (Sweep.ofFun step) ((1 : ℤ), (0 : ℤ)) {ω | ∃ n, (ω n).2 ≠ 0}
      ≤ ENNReal.ofReal 0.0544619 :=
  sound.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end Qtsl.Sweep.FaultyNdecr
