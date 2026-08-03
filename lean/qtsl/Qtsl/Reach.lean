import Qtsl.Tabular
import QtslAux.Excursions

/-! # Reachability certificates over measurable state spaces

Discrete-time reach/until events over a Markov kernel on a measurable
state space: the until event `untilEvent`, its bounded truncations, the
hitting sets `hitBy`, and their measurability; the table value `tableVal`
as the finite-horizon certificate object; and the envelope theorems
(`qLowerEnvUB_of_ge`, `qUpperEnvLB_subTable`, `qLowerEnvUB_reachAvoid`,
`qRegionSat_uniform`) that make a certified table an upper/lower envelope
for reach and reach-avoid probabilities under every Markov selection. -/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function Filter Topology

namespace Qtsl

namespace Reach

open Battery (mchain mchain_apply pathMeasure measurable_coord_piLE survive
  mem_survive survive_succ_subset survive_congr stopped stopped_zero
  stopped_succ_of_survive stopped_succ_of_not_survive stopped_pred
  stronglyAdapted_stopped measurableSet_survive_piLE supermartingale_stopped)

noncomputable section

variable {S : Type*} [MeasurableSpace S]

def untilEvent (A B : Set S) : Set (ℕ → S) :=
  {ω | ∃ k, ω k ∈ B ∧ ∀ j < k, ω j ∈ A}

theorem measurableSet_untilEvent {A B : Set S} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : MeasurableSet (untilEvent A B) := by
  have h : untilEvent A B = ⋃ k, ((fun ω : ℕ → S => ω k) ⁻¹' B
      ∩ ⋂ j, ⋂ (_ : j < k), (fun ω : ℕ → S => ω j) ⁻¹' A) := by
    ext ω; simp [untilEvent]
  rw [h]
  exact .iUnion fun k => ((measurable_pi_apply k) hB).inter
    (.iInter fun j => .iInter fun _ => (measurable_pi_apply j) hA)

theorem measurableSet_untilEventBdd {A B : Set S} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (T : ℕ) :
    MeasurableSet (Tabular.untilEventBdd A B T) := by
  have h : Tabular.untilEventBdd A B T = ⋃ k, ⋃ (_ : k ≤ T),
      ((fun ω : ℕ → S => ω k) ⁻¹' B
        ∩ ⋂ j, ⋂ (_ : j < k), (fun ω : ℕ → S => ω j) ⁻¹' A) := by
    ext ω
    simp only [Tabular.untilEventBdd, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
    tauto
  rw [h]
  exact .iUnion fun k => .iUnion fun _ => ((measurable_pi_apply k) hB).inter
    (.iInter fun j => .iInter fun _ => (measurable_pi_apply j) hA)

def hitBy (A B : Set S) (n : ℕ) : Set (ℕ → S) :=
  {ω | ∃ j ≤ n, ω j ∈ B ∧ ∀ i < j, ω i ∈ A \ B}

omit [MeasurableSpace S] in
theorem hitBy_mono {A B : Set S} {n m : ℕ} (h : n ≤ m) :
    hitBy A B n ⊆ hitBy A B m :=
  fun _ ⟨j, hj, hjB, hjA⟩ => ⟨j, hj.trans h, hjB, hjA⟩

omit [MeasurableSpace S] in
theorem hitBy_subset_untilEventBdd {A B : Set S} (n : ℕ) :
    hitBy A B n ⊆ Tabular.untilEventBdd A B n :=
  fun _ ⟨j, hj, hjB, hjA⟩ => ⟨j, hj, hjB, fun i hi => (hjA i hi).1⟩

theorem measurableSet_hitBy {A B : Set S} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (hitBy A B n) := by
  have h : hitBy A B n = ⋃ j, ⋃ (_ : j ≤ n),
      ((fun ω : ℕ → S => ω j) ⁻¹' B
        ∩ ⋂ i, ⋂ (_ : i < j), (fun ω : ℕ → S => ω i) ⁻¹' (A \ B)) := by
    ext ω
    simp only [hitBy, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_iInter, Set.mem_sdiff]
    tauto
  rw [h]
  exact .iUnion fun j => .iUnion fun _ => ((measurable_pi_apply j) hB).inter
    (.iInter fun i => .iInter fun _ => (measurable_pi_apply i) (hA.diff hB))

omit [MeasurableSpace S] in

theorem hitBy_congr {A B : Set S} {n : ℕ} {ω ω' : ℕ → S}
    (h : ∀ k ≤ n, ω k = ω' k) : ω ∈ hitBy A B n ↔ ω' ∈ hitBy A B n := by
  constructor
  · rintro ⟨j, hj, hjB, hjA⟩
    refine ⟨j, hj, by rw [← h j hj]; exact hjB, fun i hi => ?_⟩
    rw [← h i ((le_of_lt hi).trans hj)]
    exact hjA i hi
  · rintro ⟨j, hj, hjB, hjA⟩
    refine ⟨j, hj, by rw [h j hj]; exact hjB, fun i hi => ?_⟩
    rw [h i ((le_of_lt hi).trans hj)]
    exact hjA i hi

theorem measurableSet_survive {A' : Set S} (hA' : MeasurableSet A') (n : ℕ) :
    MeasurableSet (survive A' n) :=
  (Filtration.piLE (X := fun _ : ℕ => S)).le n _ (measurableSet_survive_piLE hA' n)

omit [MeasurableSpace S] in
lemma updateFinset_eq_of_le {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S}
    {k : ℕ} (hk : k ≤ n) : updateFinset y (Iic n) u k = u ⟨k, mem_Iic.2 hk⟩ := by
  simp [updateFinset, mem_Iic, hk]

omit [MeasurableSpace S] in
private lemma updateFinset_eq_succ {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S} :
    updateFinset y (Iic n) u (n + 1) = y (n + 1) := by
  simp [updateFinset, mem_Iic]

variable {K : Kernel S S} [IsMarkovKernel K]

private lemma integral_comp_coord_succ {g : S → ℝ} (hg : Measurable g) (n : ℕ)
    (u : Π _i : Iic n, S) :
    ∫ y, g (y (n + 1)) ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n u
      = ∫ z, g z ∂K (u ⟨n, mem_Iic.2 le_rfl⟩) := by
  have hmapK := DFunLike.congr_fun
    (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := mchain K) (a := n)) u
  rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
  rw [← mchain_apply, ← hmapK,
    integral_map_of_stronglyMeasurable (measurable_pi_apply _) hg.stronglyMeasurable]

lemma condExp_comp_coord_succ {g : S → ℝ} {C : ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) (hgC : ∀ y, g y ≤ C) (x : S) (n : ℕ) :
    (pathMeasure K x)[fun ω : ℕ → S => g (ω (n + 1)) |
        Filtration.piLE (X := fun _ : ℕ => S) n]
      =ᵐ[pathMeasure K x] fun ω => ∫ z, g z ∂K (ω n) := by
  have hint : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (pathMeasure K x) := by
    refine (integrable_const C).mono'
      ((hg.comp (measurable_pi_apply (n + 1))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
    exact hgC _
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.zero_le n) (x₀ := fun _ => x) hint
  exact hcond.trans (Filter.Eventually.of_forall fun ω =>
    integral_comp_coord_succ hg n (Preorder.frestrictLe n ω))

private lemma ae_coord_zero_mem {E : Set S} (hE : MeasurableSet E) {x : S}
    (hxE : x ∈ E) : ∀ᵐ ω ∂pathMeasure K x, ω 0 ∈ E := by
  rw [ae_iff]
  have hmeas : MeasurableSet {ω : ℕ → S | ¬ ω 0 ∈ E} := by
    have h : {ω : ℕ → S | ¬ ω 0 ∈ E} = (fun ω : ℕ → S => ω 0) ⁻¹' Eᶜ := rfl
    rw [h]; exact (measurable_pi_apply 0) hE.compl
  rw [← lintegral_indicator_one hmeas]
  rw [show pathMeasure K x
    = Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x) from rfl]
  rw [Kernel.lintegral_traj _ (measurable_one.indicator hmeas)]
  have hzero : ∀ y : ℕ → S,
      ({ω : ℕ → S | ¬ ω 0 ∈ E}).indicator (1 : (ℕ → S) → ℝ≥0∞)
        (updateFinset y (Iic 0) (fun _ : Iic 0 => x)) = 0 := fun y => by
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_setOf_eq, not_not]
    rw [updateFinset_eq_of_le le_rfl]
    exact hxE
  rw [lintegral_congr hzero, lintegral_zero]

private lemma measure_coord_zero_eq_one {E : Set S} (hE : MeasurableSet E)
    {x : S} (hxE : x ∈ E) :
    pathMeasure K x {ω : ℕ → S | ω 0 ∈ E} = 1 := by
  have h0 := ae_coord_zero_mem (K := K) hE hxE
  rw [ae_iff] at h0
  have hmeas : MeasurableSet {ω : ℕ → S | ω 0 ∈ E} :=
    (measurable_pi_apply 0) hE
  have hcompl : pathMeasure K x {ω : ℕ → S | ω 0 ∈ E}ᶜ = 0 := by
    have h : {ω : ℕ → S | ω 0 ∈ E}ᶜ = {ω : ℕ → S | ¬ ω 0 ∈ E} := rfl
    rw [h]; exact h0
  exact (prob_compl_eq_zero_iff hmeas).1 hcompl

def tableVal (g : ℕ → S → ℝ) (A B : Set S) (T n : ℕ) : (ℕ → S) → ℝ :=
  (hitBy A B n).piecewise (fun _ => 1)
    ((survive ((A \ B)ᶜ) n).piecewise (fun ω => g (T - n) (ω n)) fun _ => 0)

section TableVal

variable {g : ℕ → S → ℝ} {A B : Set S} {T : ℕ}

omit [MeasurableSpace S] in
lemma tableVal_of_hit {n : ℕ} {ω : ℕ → S} (h : ω ∈ hitBy A B n) :
    tableVal g A B T n ω = 1 :=
  Set.piecewise_eq_of_mem _ _ _ h

omit [MeasurableSpace S] in
lemma tableVal_of_alive {n : ℕ} {ω : ℕ → S} (h1 : ω ∉ hitBy A B n)
    (h2 : ω ∈ survive ((A \ B)ᶜ) n) :
    tableVal g A B T n ω = g (T - n) (ω n) := by
  rw [tableVal, Set.piecewise_eq_of_notMem _ _ _ h1,
    Set.piecewise_eq_of_mem _ _ _ h2]

omit [MeasurableSpace S] in
lemma tableVal_of_dead {n : ℕ} {ω : ℕ → S} (h1 : ω ∉ hitBy A B n)
    (h2 : ω ∉ survive ((A \ B)ᶜ) n) :
    tableVal g A B T n ω = 0 := by
  rw [tableVal, Set.piecewise_eq_of_notMem _ _ _ h1,
    Set.piecewise_eq_of_notMem _ _ _ h2]

lemma measurable_tableVal (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hgm : ∀ k, Measurable (g k)) (n : ℕ) :
    Measurable (tableVal g A B T n) :=
  Measurable.piecewise (measurableSet_hitBy hA hB n) measurable_const
    (Measurable.piecewise (measurableSet_survive (hA.diff hB).compl n)
      ((hgm (T - n)).comp (measurable_pi_apply n)) measurable_const)

omit [MeasurableSpace S] in
lemma abs_tableVal_le {C : ℝ} (hgb : ∀ k y, |g k y| ≤ C) (n : ℕ) (ω : ℕ → S) :
    |tableVal g A B T n ω| ≤ max 1 C := by
  by_cases hh : ω ∈ hitBy A B n
  · rw [tableVal_of_hit hh, abs_one]
    exact le_max_left _ _
  · by_cases hs : ω ∈ survive ((A \ B)ᶜ) n
    · rw [tableVal_of_alive hh hs]
      exact (hgb _ _).trans (le_max_right _ _)
    · rw [tableVal_of_dead hh hs, abs_zero]
      exact le_trans zero_le_one (le_max_left _ _)

end TableVal

section SubTable

variable {A B : Set S} {g : ℕ → S → ℝ} {T : ℕ} {C : ℝ}

omit [IsMarkovKernel K] in

private lemma row_le_one
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂K y else 0) :
    ∀ m ≤ T, ∀ z ∈ B, g m z ≤ 1 := by
  intro m hm z hz
  cases m with
  | zero =>
    have h := h0 z
    rwa [if_pos hz] at h
  | succ k =>
    have h := hstep k (Nat.lt_of_lt_of_le k.lt_succ_self hm) z
    rwa [if_pos hz] at h

omit [IsMarkovKernel K] in

private lemma row_nonpos
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂K y else 0) :
    ∀ m ≤ T, ∀ z, z ∉ B → z ∉ A → g m z ≤ 0 := by
  intro m hm z hzB hzA
  cases m with
  | zero =>
    have h := h0 z
    rwa [if_neg hzB] at h
  | succ k =>
    have h := hstep k (Nat.lt_of_lt_of_le k.lt_succ_self hm) z
    rwa [if_neg hzB, if_neg hzA] at h

private lemma tableVal_le_integral_succ
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hgm : ∀ k, Measurable (g k)) (hgb : ∀ k y, |g k y| ≤ C)
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂K y else 0)
    {n : ℕ} (hn : n < T) (ω : ℕ → S) :
    tableVal g A B T n ω ≤
      ∫ y, tableVal g A B T (n + 1) y
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n
          (Preorder.frestrictLe n ω) := by
  have hmeasN : AEStronglyMeasurable (tableVal g A B T (n + 1))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n
        (Preorder.frestrictLe n ω)) :=
    (measurable_tableVal hA hB hgm (n + 1)).aestronglyMeasurable
  rw [Kernel.integral_traj _ hmeasN]
  have hagree : ∀ y : ℕ → S, ∀ k ≤ n,
      updateFinset y (Iic n) (Preorder.frestrictLe n ω) k = ω k :=
    fun y k hk => by rw [updateFinset_eq_of_le hk]; rfl
  by_cases hhit : ω ∈ hitBy A B n
  ·
    have hpatch : ∀ y : ℕ → S, tableVal g A B T (n + 1)
        (updateFinset y (Iic n) (Preorder.frestrictLe n ω)) = 1 := fun y =>
      tableVal_of_hit (hitBy_mono n.le_succ ((hitBy_congr (hagree y)).2 hhit))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpatch), integral_const,
      tableVal_of_hit hhit]
    simp [measureReal_def]
  · by_cases hsur : ω ∈ survive ((A \ B)ᶜ) n
    ·
      have hsurQ : ∀ k ≤ n, ω k ∈ A \ B := fun k hk =>
        Set.notMem_compl_iff.1 (mem_survive.1 hsur k hk)
      have hmT : T - (n + 1) + 1 = T - n := by omega
      have hmle : T - (n + 1) ≤ T := by omega
      have hmlt : T - (n + 1) < T := by omega
      set φ : S → ℝ :=
        B.piecewise (fun _ => 1)
          ((A \ B).piecewise (g (T - (n + 1))) fun _ => 0) with hφ
      have hφm : Measurable φ :=
        Measurable.piecewise hB measurable_const
          (Measurable.piecewise (hA.diff hB) (hgm (T - (n + 1))) measurable_const)
      have hpatch : ∀ y : ℕ → S, tableVal g A B T (n + 1)
          (updateFinset y (Iic n) (Preorder.frestrictLe n ω)) = φ (y (n + 1)) := by
        intro y
        have hpn : updateFinset y (Iic n) (Preorder.frestrictLe n ω) (n + 1)
            = y (n + 1) := updateFinset_eq_succ
        have hphit : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
            ∉ hitBy A B n :=
          fun h => hhit ((hitBy_congr (hagree y)).1 h)
        by_cases hyB : y (n + 1) ∈ B
        · have hmem : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
              ∈ hitBy A B (n + 1) := by
            refine ⟨n + 1, le_rfl, by rwa [hpn], fun i hi => ?_⟩
            have hin : i ≤ n := Nat.lt_succ_iff.1 hi
            rw [hagree y i hin]
            exact hsurQ i hin
          rw [tableVal_of_hit hmem, hφ, Set.piecewise_eq_of_mem _ _ _ hyB]
        · have hphit' : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
              ∉ hitBy A B (n + 1) := by
            rintro ⟨j, hj, hjB, hjA⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hlt | rfl
            · exact hphit ⟨j, Nat.lt_succ_iff.1 hlt, hjB, hjA⟩
            · exact hyB (by rwa [hpn] at hjB)
          by_cases hyQ : y (n + 1) ∈ A \ B
          · have hsur' : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
                ∈ survive ((A \ B)ᶜ) (n + 1) := by
              refine mem_survive.2 fun k hk => ?_
              rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
              · have hkn : k ≤ n := Nat.lt_succ_iff.1 hlt
                rw [hagree y k hkn]
                exact Set.notMem_compl_iff.2 (hsurQ k hkn)
              · rw [hpn]
                exact Set.notMem_compl_iff.2 hyQ
            rw [tableVal_of_alive hphit' hsur', hpn, hφ,
              Set.piecewise_eq_of_notMem _ _ _ hyB,
              Set.piecewise_eq_of_mem _ _ _ hyQ]
          · have hsur' : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
                ∉ survive ((A \ B)ᶜ) (n + 1) := by
              intro hcon
              refine (mem_survive.1 hcon (n + 1) le_rfl) ?_
              rw [hpn]
              exact (Set.mem_compl_iff _ _).2 hyQ
            rw [tableVal_of_dead hphit' hsur', hφ,
              Set.piecewise_eq_of_notMem _ _ _ hyB,
              Set.piecewise_eq_of_notMem _ _ _ hyQ]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpatch),
        integral_comp_coord_succ hφm n _]
      have hωn : ω n ∈ A \ B := hsurQ n le_rfl
      rw [tableVal_of_alive hhit hsur]
      show g (T - n) (ω n) ≤ ∫ z, φ z ∂K (ω n)
      have hφb : ∀ z, |φ z| ≤ max 1 C := by
        intro z
        by_cases hzB : z ∈ B
        · rw [hφ, Set.piecewise_eq_of_mem _ _ _ hzB, abs_one]
          exact le_max_left _ _
        · by_cases hzQ : z ∈ A \ B
          · rw [hφ, Set.piecewise_eq_of_notMem _ _ _ hzB,
              Set.piecewise_eq_of_mem _ _ _ hzQ]
            exact (hgb (T - (n + 1)) z).trans (le_max_right _ _)
          · rw [hφ, Set.piecewise_eq_of_notMem _ _ _ hzB,
              Set.piecewise_eq_of_notMem _ _ _ hzQ, abs_zero]
            exact le_trans zero_le_one (le_max_left _ _)
      have hφint : Integrable φ (K (ω n)) :=
        (integrable_const (max 1 C)).mono' hφm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs]; exact hφb z)
      have hgint : Integrable (g (T - (n + 1))) (K (ω n)) :=
        (integrable_const C).mono' (hgm (T - (n + 1))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs]; exact hgb (T - (n + 1)) z)
      have hφge : ∀ z, g (T - (n + 1)) z ≤ φ z := by
        intro z
        by_cases hzB : z ∈ B
        · rw [hφ, Set.piecewise_eq_of_mem _ _ _ hzB]
          exact row_le_one h0 hstep (T - (n + 1)) hmle z hzB
        · by_cases hzQ : z ∈ A \ B
          · rw [hφ, Set.piecewise_eq_of_notMem _ _ _ hzB,
              Set.piecewise_eq_of_mem _ _ _ hzQ]
          · rw [hφ, Set.piecewise_eq_of_notMem _ _ _ hzB,
              Set.piecewise_eq_of_notMem _ _ _ hzQ]
            have hzA : z ∉ A := fun hzA => hzQ ⟨hzA, hzB⟩
            exact row_nonpos h0 hstep (T - (n + 1)) hmle z hzB hzA
      have hrow := hstep (T - (n + 1)) hmlt (ω n)
      rw [if_neg hωn.2, if_pos hωn.1, hmT] at hrow
      exact hrow.trans (integral_mono hgint hφint hφge)
    ·
      have hpatch : ∀ y : ℕ → S, tableVal g A B T (n + 1)
          (updateFinset y (Iic n) (Preorder.frestrictLe n ω)) = 0 := by
        intro y
        have hphit : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
            ∉ hitBy A B (n + 1) := by
          rintro ⟨j, hj, hjB, hjA⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hlt | rfl
          · exact hhit ((hitBy_congr (hagree y)).1
              ⟨j, Nat.lt_succ_iff.1 hlt, hjB, hjA⟩)
          · refine hsur (mem_survive.2 fun k hk => ?_)
            have hkQ := hjA k (Nat.lt_succ_of_le hk)
            rw [hagree y k hk] at hkQ
            exact Set.notMem_compl_iff.2 hkQ
        have hpsur : updateFinset y (Iic n) (Preorder.frestrictLe n ω)
            ∉ survive ((A \ B)ᶜ) (n + 1) := fun h =>
          hsur ((survive_congr (hagree y)).1 (survive_succ_subset h))
        exact tableVal_of_dead hphit hpsur
      rw [integral_congr_ae (Filter.Eventually.of_forall hpatch), integral_const,
        tableVal_of_dead hhit hsur]
      simp

private lemma integral_tableVal_mono
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hgm : ∀ k, Measurable (g k)) (hgb : ∀ k y, |g k y| ≤ C)
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂K y else 0)
    (x : S) {n : ℕ} (hn : n < T) :
    ∫ ω, tableVal g A B T n ω ∂pathMeasure K x
      ≤ ∫ ω, tableVal g A B T (n + 1) ω ∂pathMeasure K x := by
  have hint : ∀ p : ℕ, Integrable (tableVal g A B T p) (pathMeasure K x) := by
    intro p
    refine (integrable_const (max 1 C)).mono'
      ((measurable_tableVal hA hB hgm p).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_tableVal_le hgb p ω
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.zero_le n) (x₀ := fun _ => x) (hint (n + 1))
  have hR : Integrable (fun ω : ℕ → S => ∫ y, tableVal g A B T (n + 1) y
      ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n
        (Preorder.frestrictLe n ω)) (pathMeasure K x) :=
    integrable_condExp.congr hcond
  calc ∫ ω, tableVal g A B T n ω ∂pathMeasure K x
      ≤ ∫ ω : ℕ → S, (∫ y, tableVal g A B T (n + 1) y
          ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n
            (Preorder.frestrictLe n ω)) ∂pathMeasure K x :=
        integral_mono_ae (hint n) hR (Filter.Eventually.of_forall fun ω =>
          tableVal_le_integral_succ hA hB hgm hgb h0 hstep hn ω)
    _ = ∫ ω, ((pathMeasure K x)[tableVal g A B T (n + 1) |
          Filtration.piLE (X := fun _ : ℕ => S) n]) ω ∂pathMeasure K x :=
        (integral_congr_ae hcond).symm
    _ = ∫ ω, tableVal g A B T (n + 1) ω ∂pathMeasure K x :=
        integral_condExp ((Filtration.piLE (X := fun _ : ℕ => S)).le n)

theorem subTable_le
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hgm : ∀ k, Measurable (g k)) (hgb : ∀ k y, |g k y| ≤ C)
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂K y else 0)
    (x : S) :
    ENNReal.ofReal (g T x)
      ≤ pathMeasure K x (Tabular.untilEventBdd A B T) := by
  by_cases hxB : x ∈ B
  ·
    have h1 : pathMeasure K x {ω : ℕ → S | ω 0 ∈ B} = 1 :=
      measure_coord_zero_eq_one hB hxB
    have hsub : {ω : ℕ → S | ω 0 ∈ B} ⊆ Tabular.untilEventBdd A B T :=
      fun ω h => ⟨0, T.zero_le, h, fun j hj => absurd hj j.not_lt_zero⟩
    calc ENNReal.ofReal (g T x) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (row_le_one h0 hstep T le_rfl x hxB)
      _ = 1 := ENNReal.ofReal_one
      _ = pathMeasure K x {ω : ℕ → S | ω 0 ∈ B} := h1.symm
      _ ≤ pathMeasure K x (Tabular.untilEventBdd A B T) :=
          measure_mono hsub
  · have hint : ∀ p : ℕ, Integrable (tableVal g A B T p) (pathMeasure K x) := by
      intro p
      refine (integrable_const (max 1 C)).mono'
        ((measurable_tableVal hA hB hgm p).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact abs_tableVal_le hgb p ω

    have hval0 : ∀ ω : ℕ → S, tableVal g A B T 0 ω
        = B.piecewise (fun _ => 1) ((A \ B).piecewise (g T) fun _ => 0) (ω 0) := by
      intro ω
      by_cases h0B : ω 0 ∈ B
      · rw [tableVal_of_hit ⟨0, le_rfl, h0B, fun i hi => absurd hi i.not_lt_zero⟩,
          Set.piecewise_eq_of_mem _ _ _ h0B]
      · by_cases h0Q : ω 0 ∈ A \ B
        · have hhit : ω ∉ hitBy A B 0 := by
            rintro ⟨j, hj, hjB, -⟩
            obtain rfl : j = 0 := Nat.le_zero.1 hj
            exact h0B hjB
          have hsur : ω ∈ survive ((A \ B)ᶜ) 0 := by
            refine mem_survive.2 fun k hk => ?_
            obtain rfl : k = 0 := Nat.le_zero.1 hk
            exact Set.notMem_compl_iff.2 h0Q
          rw [tableVal_of_alive hhit hsur, Nat.sub_zero,
            Set.piecewise_eq_of_notMem _ _ _ h0B,
            Set.piecewise_eq_of_mem _ _ _ h0Q]
        · have hhit : ω ∉ hitBy A B 0 := by
            rintro ⟨j, hj, hjB, -⟩
            obtain rfl : j = 0 := Nat.le_zero.1 hj
            exact h0B hjB
          have hsur : ω ∉ survive ((A \ B)ᶜ) 0 := by
            intro hcon
            exact (mem_survive.1 hcon 0 le_rfl) ((Set.mem_compl_iff _ _).2 h0Q)
          rw [tableVal_of_dead hhit hsur,
            Set.piecewise_eq_of_notMem _ _ _ h0B,
            Set.piecewise_eq_of_notMem _ _ _ h0Q]
    have h0eq : ∫ ω, tableVal g A B T 0 ω ∂pathMeasure K x
        = B.piecewise (fun _ => 1) ((A \ B).piecewise (g T) fun _ => 0) x := by
      have hmeas : AEStronglyMeasurable (tableVal g A B T 0)
          (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
        (measurable_tableVal hA hB hgm 0).aestronglyMeasurable
      rw [show pathMeasure K x
        = Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x) from rfl]
      rw [Kernel.integral_traj _ hmeas]
      have hpt : ∀ y : ℕ → S,
          tableVal g A B T 0 (updateFinset y (Iic 0) (fun _ : Iic 0 => x))
            = B.piecewise (fun _ => 1) ((A \ B).piecewise (g T) fun _ => 0) x := by
        intro y
        rw [hval0]
        congr 1
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const]
      simp [measureReal_def]
    have hstart : g T x
        ≤ B.piecewise (fun _ => 1) ((A \ B).piecewise (g T) fun _ => 0) x := by
      by_cases hxQ : x ∈ A \ B
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxB, Set.piecewise_eq_of_mem _ _ _ hxQ]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxB,
          Set.piecewise_eq_of_notMem _ _ _ hxQ]
        have hxA : x ∉ A := fun hxA => hxQ ⟨hxA, hxB⟩
        exact row_nonpos h0 hstep T le_rfl x hxB hxA

    have hchain : ∀ n ≤ T, ∫ ω, tableVal g A B T 0 ω ∂pathMeasure K x
        ≤ ∫ ω, tableVal g A B T n ω ∂pathMeasure K x := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ k ih =>
        intro hk
        exact (ih (Nat.le_of_succ_le hk)).trans
          (integral_tableVal_mono hA hB hgm hgb h0 hstep x (Nat.lt_of_succ_le hk))

    have hend : ∫ ω, tableVal g A B T T ω ∂pathMeasure K x
        ≤ (pathMeasure K x).real (hitBy A B T) := by
      have hbound : ∀ ω, tableVal g A B T T ω
          ≤ (hitBy A B T).indicator 1 ω := by
        intro ω
        by_cases hh : ω ∈ hitBy A B T
        · rw [tableVal_of_hit hh, Set.indicator_of_mem hh, Pi.one_apply]
        · rw [Set.indicator_of_notMem hh]
          by_cases hs : ω ∈ survive ((A \ B)ᶜ) T
          · rw [tableVal_of_alive hh hs, Nat.sub_self]
            have hQ : ω T ∈ A \ B :=
              Set.notMem_compl_iff.1 (mem_survive.1 hs T le_rfl)
            have h := h0 (ω T)
            rwa [if_neg hQ.2] at h
          · rw [tableVal_of_dead hh hs]
      calc ∫ ω, tableVal g A B T T ω ∂pathMeasure K x
          ≤ ∫ ω, (hitBy A B T).indicator 1 ω ∂pathMeasure K x :=
            integral_mono (hint T)
              ((integrable_const 1).indicator (measurableSet_hitBy hA hB T))
              hbound
        _ = (pathMeasure K x).real (hitBy A B T) :=
            integral_indicator_one (measurableSet_hitBy hA hB T)
    have hreal : g T x ≤ (pathMeasure K x).real (Tabular.untilEventBdd A B T) := by
      calc g T x ≤ ∫ ω, tableVal g A B T 0 ω ∂pathMeasure K x :=
            hstart.trans_eq h0eq.symm
        _ ≤ ∫ ω, tableVal g A B T T ω ∂pathMeasure K x := hchain T le_rfl
        _ ≤ (pathMeasure K x).real (hitBy A B T) := hend
        _ ≤ (pathMeasure K x).real (Tabular.untilEventBdd A B T) :=
            measureReal_mono (hitBy_subset_untilEventBdd T)
    calc ENNReal.ofReal (g T x)
        ≤ ENNReal.ofReal ((pathMeasure K x).real (Tabular.untilEventBdd A B T)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = pathMeasure K x (Tabular.untilEventBdd A B T) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end SubTable

section ReachProgress

variable {A B : Set S}

omit [MeasurableSpace S] in

lemma stopped_const_sub (f : S → ℝ) (A' : Set S) (c : ℝ) :
    ∀ (n : ℕ) (ω : ℕ → S),
      stopped (fun y => c - f y) A' n ω = c - stopped f A' n ω := by
  intro n
  induction n with
  | zero => intro ω; rfl
  | succ n ih =>
    intro ω
    by_cases h : ω ∈ survive A' n
    · rw [stopped_succ_of_survive h, stopped_succ_of_survive h]
    · rw [stopped_succ_of_not_survive h, stopped_succ_of_not_survive h, ih]

omit [MeasurableSpace S] in

private lemma stopped_le_indicator_add {h : S → ℝ}
    (hle1 : ∀ y, h y ≤ 1)
    (hzero : ∀ y, y ∉ A \ B → y ∉ B → h y = 0) :
    ∀ (n : ℕ) (ω : ℕ → S),
      stopped h ((A \ B)ᶜ) n ω ≤
        (untilEvent A B).indicator 1 ω
          + (survive ((A \ B)ᶜ) n).indicator 1 ω := by
  have hnn : ∀ (s : Set (ℕ → S)) (ω : ℕ → S),
      (0 : ℝ) ≤ s.indicator 1 ω := fun s ω =>
    Set.indicator_apply_nonneg fun _ => zero_le_one
  intro n
  induction n with
  | zero =>
    intro ω
    rw [stopped_zero]
    by_cases h0Q : ω 0 ∈ A \ B
    · have hs : ω ∈ survive ((A \ B)ᶜ) 0 := by
        refine mem_survive.2 fun k hk => ?_
        obtain rfl : k = 0 := Nat.le_zero.1 hk
        exact Set.notMem_compl_iff.2 h0Q
      calc h (ω 0) ≤ 1 := hle1 _
        _ ≤ _ := by
            rw [Set.indicator_of_mem hs, Pi.one_apply]
            exact le_add_of_nonneg_left (hnn _ ω)
    · by_cases h0B : ω 0 ∈ B
      · have hu : ω ∈ untilEvent A B :=
          ⟨0, h0B, fun j hj => absurd hj j.not_lt_zero⟩
        calc h (ω 0) ≤ 1 := hle1 _
          _ ≤ _ := by
              rw [Set.indicator_of_mem hu, Pi.one_apply]
              exact le_add_of_nonneg_right (hnn _ ω)
      · rw [hzero _ h0Q h0B]
        exact add_nonneg (hnn _ ω) (hnn _ ω)
  | succ n ih =>
    intro ω
    by_cases hs : ω ∈ survive ((A \ B)ᶜ) n
    · rw [stopped_succ_of_survive hs]
      have hsQ : ∀ k ≤ n, ω k ∈ A \ B := fun k hk =>
        Set.notMem_compl_iff.1 (mem_survive.1 hs k hk)
      by_cases hQ : ω (n + 1) ∈ A \ B
      · have hs' : ω ∈ survive ((A \ B)ᶜ) (n + 1) := by
          refine mem_survive.2 fun k hk => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
          · exact Set.notMem_compl_iff.2 (hsQ k (Nat.lt_succ_iff.1 hlt))
          · exact Set.notMem_compl_iff.2 hQ
        calc h (ω (n + 1)) ≤ 1 := hle1 _
          _ ≤ _ := by
              rw [Set.indicator_of_mem hs', Pi.one_apply]
              exact le_add_of_nonneg_left (hnn _ ω)
      · by_cases hB' : ω (n + 1) ∈ B
        · have hu : ω ∈ untilEvent A B := by
            refine ⟨n + 1, hB', fun j hj => ?_⟩
            exact (hsQ j (Nat.lt_succ_iff.1 hj)).1
          calc h (ω (n + 1)) ≤ 1 := hle1 _
            _ ≤ _ := by
                rw [Set.indicator_of_mem hu, Pi.one_apply]
                exact le_add_of_nonneg_right (hnn _ ω)
        · rw [hzero _ hQ hB']
          exact add_nonneg (hnn _ ω) (hnn _ ω)
    · rw [stopped_succ_of_not_survive hs]
      refine (ih ω).trans ?_
      rw [Set.indicator_of_notMem hs]
      exact add_le_add le_rfl (hnn _ ω)

variable {K : Kernel S S} [IsMarkovKernel K]

set_option maxHeartbeats 1600000 in

theorem sound_reach_progress
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {g W : S → ℝ} {ε MW : ℝ}
    (hgm : Measurable g) (hWm : Measurable W)
    (hε : 0 < ε)
    (hg1 : ∀ y ∈ B, g y ≤ 1)
    (hg2 : ∀ y, y ∉ A → y ∉ B → g y ≤ 0)
    (hg30 : ∀ y ∈ A \ B, 0 ≤ g y)
    (hg31 : ∀ y ∈ A \ B, g y ≤ 1)
    (hgint : ∀ y ∈ A \ B, Integrable g (K y))
    (hg4 : ∀ y ∈ A \ B, g y ≤ ∫ z, g z ∂K y)
    (hW0 : ∀ y, 0 ≤ W y) (hWM : ∀ y, W y ≤ MW)
    (hW6 : ∀ y ∈ A \ B, ∫ z, W z ∂K y ≤ W y - ε)
    (x : S) :
    ENNReal.ofReal (g x) ≤ pathMeasure K x (untilEvent A B) := by
  by_cases hxB : x ∈ B
  ·
    have h1 : pathMeasure K x {ω : ℕ → S | ω 0 ∈ B} = 1 :=
      measure_coord_zero_eq_one hB hxB
    have hsub : {ω : ℕ → S | ω 0 ∈ B} ⊆ untilEvent A B :=
      fun ω h => ⟨0, h, fun j hj => absurd hj j.not_lt_zero⟩
    calc ENNReal.ofReal (g x) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (hg1 x hxB)
      _ = 1 := ENNReal.ofReal_one
      _ = pathMeasure K x {ω : ℕ → S | ω 0 ∈ B} := h1.symm
      _ ≤ pathMeasure K x (untilEvent A B) := measure_mono hsub
  by_cases hxA : x ∈ A
  swap
  ·
    rw [ENNReal.ofReal_eq_zero.2 (hg2 x hxA hxB)]
    exact zero_le
  have hxQ : x ∈ A \ B := ⟨hxA, hxB⟩
  have hQm : MeasurableSet (A \ B) := hA.diff hB

  set g' : S → ℝ := (A \ B).piecewise g (B.piecewise (fun _ => 1) fun _ => 0)
    with hg'def
  have hg'm : Measurable g' :=
    Measurable.piecewise hQm hgm
      (Measurable.piecewise hB measurable_const measurable_const)
  have hg'Q : ∀ y ∈ A \ B, g' y = g y := fun y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hg'B : ∀ y ∈ B, g' y = 1 := by
    intro y hy
    have hyQ : y ∉ A \ B := fun h => h.2 hy
    rw [hg'def, Set.piecewise_eq_of_notMem _ _ _ hyQ,
      Set.piecewise_eq_of_mem _ _ _ hy]
  have hg'zero : ∀ y, y ∉ A \ B → y ∉ B → g' y = 0 := by
    intro y hyQ hyB
    rw [hg'def, Set.piecewise_eq_of_notMem _ _ _ hyQ,
      Set.piecewise_eq_of_notMem _ _ _ hyB]
  have hg'0 : ∀ y, 0 ≤ g' y := by
    intro y
    by_cases hyQ : y ∈ A \ B
    · rw [hg'Q y hyQ]; exact hg30 y hyQ
    · by_cases hyB : y ∈ B
      · rw [hg'B y hyB]; exact zero_le_one
      · rw [hg'zero y hyQ hyB]
  have hg'1 : ∀ y, g' y ≤ 1 := by
    intro y
    by_cases hyQ : y ∈ A \ B
    · rw [hg'Q y hyQ]; exact hg31 y hyQ
    · by_cases hyB : y ∈ B
      · rw [hg'B y hyB]
      · rw [hg'zero y hyQ hyB]; exact zero_le_one
  have hg'ge : ∀ y, g y ≤ g' y := by
    intro y
    by_cases hyQ : y ∈ A \ B
    · rw [hg'Q y hyQ]
    · by_cases hyB : y ∈ B
      · rw [hg'B y hyB]; exact hg1 y hyB
      · rw [hg'zero y hyQ hyB]
        have hyA : y ∉ A := fun hyA => hyQ ⟨hyA, hyB⟩
        exact hg2 y hyA hyB
  have hg'int : ∀ y : S, Integrable g' (K y) := fun y =>
    (integrable_const (1 : ℝ)).mono' hg'm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg'0 z)]
        exact hg'1 z)

  have hVint : ∀ n : ℕ, Integrable (fun ω : ℕ → S => W (ω n)) (pathMeasure K x) := by
    intro n
    refine (integrable_const MW).mono'
      ((hWm.comp (measurable_pi_apply n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWM _
  have hexit : ∀ᵐ ω ∂pathMeasure K x, ∃ n, ω n ∈ (A \ B)ᶜ := by
    refine Excursions.ae_hits_of_ranking
      (𝒢 := Filtration.piLE (X := fun _ : ℕ => S))
      (X := fun n (ω : ℕ → S) => ω n) (B := (A \ B)ᶜ)
      (V := fun n (ω : ℕ → S) => W (ω n)) hε hVint
      (fun n ω => hW0 (ω n))
      (fun n => (measurable_coord_piLE le_rfl) hQm.compl) ?_
    intro n
    filter_upwards [condExp_comp_coord_succ (K := K) hWm hW0 hWM x n]
      with ω hω hmem
    have hωn : ω n ∈ A \ B := Set.notMem_compl_iff.1 hmem
    show ((pathMeasure K x)[fun ω : ℕ → S => W (ω (n + 1)) |
        Filtration.piLE (X := fun _ : ℕ => S) n]) ω ≤ W (ω n) - ε
    rw [hω]
    exact hW6 (ω n) hωn
  have hnever : pathMeasure K x {ω : ℕ → S | ∀ n, ω n ∈ A \ B} = 0 := by
    rw [ae_iff] at hexit
    refine measure_mono_null ?_ hexit
    intro ω hω
    simp only [Set.mem_setOf_eq, not_exists]
    exact fun n => Set.notMem_compl_iff.2 (hω n)

  have hdriftf : ∀ y, y ∉ (A \ B)ᶜ → ∫ z, (1 - g' z) ∂K y ≤ 1 - g' y := by
    intro y hy
    have hyQ : y ∈ A \ B := Set.notMem_compl_iff.1 hy
    have hsplit : ∫ z, (1 - g' z) ∂K y = 1 - ∫ z, g' z ∂K y := by
      rw [integral_sub (integrable_const 1) (hg'int y), integral_const]
      simp [measureReal_def]
    rw [hsplit]
    have hgle : g' y ≤ ∫ z, g' z ∂K y := by
      calc g' y = g y := hg'Q y hyQ
        _ ≤ ∫ z, g z ∂K y := hg4 y hyQ
        _ ≤ ∫ z, g' z ∂K y := integral_mono (hgint y hyQ) (hg'int y) hg'ge
    linarith
  have hsup := supermartingale_stopped (K := K) (A := (A \ B)ᶜ) (C := 1)
    hQm.compl (measurable_const.sub hg'm)
    (fun y => by show (0 : ℝ) ≤ 1 - g' y; have := hg'1 y; linarith)
    (fun y => by show (1 : ℝ) - g' y ≤ 1; have := hg'0 y; linarith)
    hdriftf x
  have hstopint : ∀ n : ℕ,
      Integrable (stopped g' ((A \ B)ᶜ) n) (pathMeasure K x) := by
    intro n
    refine (integrable_const (1 : ℝ)).mono'
      (((stronglyAdapted_stopped hQm.compl hg'm n).mono
        ((Filtration.piLE (X := fun _ : ℕ => S)).le n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (stopped_pred (fun r => 0 ≤ r) hg'0 n ω)]
    exact stopped_pred (fun r => r ≤ 1) hg'1 n ω
  have hstop0 : ∫ ω, stopped (fun y => 1 - g' y) ((A \ B)ᶜ) 0 ω ∂pathMeasure K x
      = 1 - g' x := by
    have hmeas : AEStronglyMeasurable (stopped (fun y => 1 - g' y) ((A \ B)ᶜ) 0)
        (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
      ((measurable_const.sub hg'm).comp (measurable_pi_apply 0)).aestronglyMeasurable
    rw [show pathMeasure K x
      = Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x) from rfl]
    rw [Kernel.integral_traj _ hmeas]
    have hpt : ∀ y : ℕ → S,
        stopped (fun y => 1 - g' y) ((A \ B)ᶜ) 0
          (updateFinset y (Iic 0) (fun _ : Iic 0 => x)) = 1 - g' x := fun y => by
      rw [stopped_zero, updateFinset_eq_of_le le_rfl]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const]
    simp [measureReal_def]
  have hexp : ∀ n : ℕ, g' x ≤ ∫ ω, stopped g' ((A \ B)ᶜ) n ω ∂pathMeasure K x := by
    intro n
    have h1 : ∫ ω, stopped (fun y => 1 - g' y) ((A \ B)ᶜ) n ω ∂pathMeasure K x
        ≤ 1 - g' x := by
      rw [← hstop0]
      have hle := hsup.setIntegral_le (Nat.zero_le n)
        (MeasurableSet.univ :
          MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) 0] _)
      simp only [setIntegral_univ] at hle
      exact hle
    have h2 : ∫ ω, stopped (fun y => 1 - g' y) ((A \ B)ᶜ) n ω ∂pathMeasure K x
        = 1 - ∫ ω, stopped g' ((A \ B)ᶜ) n ω ∂pathMeasure K x := by
      have hcongr : ∀ ω : ℕ → S, stopped (fun y => 1 - g' y) ((A \ B)ᶜ) n ω
          = 1 - stopped g' ((A \ B)ᶜ) n ω := fun ω => stopped_const_sub g' _ 1 n ω
      rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
        integral_sub (integrable_const 1) (hstopint n), integral_const]
      simp [measureReal_def]
    rw [h2] at h1
    linarith

  have huMeas : MeasurableSet (untilEvent A B) := measurableSet_untilEvent hA hB
  have hsMeas : ∀ n : ℕ, MeasurableSet (survive ((A \ B)ᶜ) n) := fun n =>
    measurableSet_survive hQm.compl n
  have hchain : ∀ n : ℕ, g' x ≤ (pathMeasure K x).real (untilEvent A B)
      + (pathMeasure K x).real (survive ((A \ B)ᶜ) n) := by
    intro n
    have hb := stopped_le_indicator_add (A := A) (B := B)
      hg'1 hg'zero n
    have hIu : Integrable ((untilEvent A B).indicator (1 : (ℕ → S) → ℝ))
        (pathMeasure K x) := (integrable_const 1).indicator huMeas
    have hIs : Integrable ((survive ((A \ B)ᶜ) n).indicator (1 : (ℕ → S) → ℝ))
        (pathMeasure K x) := (integrable_const 1).indicator (hsMeas n)
    calc g' x ≤ ∫ ω, stopped g' ((A \ B)ᶜ) n ω ∂pathMeasure K x := hexp n
      _ ≤ ∫ ω, (((untilEvent A B).indicator 1
            + (survive ((A \ B)ᶜ) n).indicator 1 : (ℕ → S) → ℝ)) ω ∂pathMeasure K x :=
          integral_mono_ae (hstopint n) (hIu.add hIs)
            (Filter.Eventually.of_forall fun ω => by
              simpa only [Pi.add_apply] using hb ω)
      _ = (pathMeasure K x).real (untilEvent A B)
            + (pathMeasure K x).real (survive ((A \ B)ᶜ) n) := by
          simp only [Pi.add_apply]
          rw [integral_add hIu hIs, integral_indicator_one huMeas,
            integral_indicator_one (hsMeas n)]

  have hIcap : ⋂ n, survive ((A \ B)ᶜ) n = {ω : ℕ → S | ∀ k, ω k ∈ A \ B} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h k
      exact Set.notMem_compl_iff.1 (mem_survive.1 (h k) k le_rfl)
    · intro h n k hk
      exact Set.notMem_compl_iff.2 (h k)
  have htend0 : Tendsto (fun n => pathMeasure K x (survive ((A \ B)ᶜ) n))
      atTop (𝓝 0) := by
    have hanti : Antitone fun n => survive ((A \ B)ᶜ) n :=
      antitone_nat_of_succ_le fun n => survive_succ_subset
    have h := tendsto_measure_iInter_atTop (μ := pathMeasure K x)
      (s := fun n => survive ((A \ B)ᶜ) n)
      (fun n => (hsMeas n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hIcap, hnever] at h
    exact h
  have htendR : Tendsto (fun n => (pathMeasure K x).real (survive ((A \ B)ᶜ) n))
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp htend0
    simpa [measureReal_def, Function.comp_def] using h
  have hfinal : g' x ≤ (pathMeasure K x).real (untilEvent A B) := by
    have hlim : Tendsto (fun n => (pathMeasure K x).real (untilEvent A B)
        + (pathMeasure K x).real (survive ((A \ B)ᶜ) n)) atTop
        (𝓝 ((pathMeasure K x).real (untilEvent A B) + 0)) :=
      tendsto_const_nhds.add htendR
    have h := ge_of_tendsto' hlim hchain
    simpa using h
  calc ENNReal.ofReal (g x) = ENNReal.ofReal (g' x) := by rw [hg'Q x hxQ]
    _ ≤ ENNReal.ofReal ((pathMeasure K x).real (untilEvent A B)) :=
        ENNReal.ofReal_le_ofReal hfinal
    _ = pathMeasure K x (untilEvent A B) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end ReachProgress

section Envelope

variable {C : S → Set (Measure S)}

def RectCompatible (C : S → Set (Measure S)) (K : Kernel S S) : Prop :=
  ∀ y, K y ∈ C y

theorem qSelRefines_of_pinRows {Ksel : Kernel S S}
    (hpin : ∀ y, Ksel y ∈ C y) : RectCompatible C Ksel :=
  hpin

noncomputable def upperEnvPath (C : S → Set (Measure S)) (x : S)
    (E : Set (ℕ → S)) : ℝ≥0∞ :=
  ⨆ (K : Kernel S S) (hK : IsMarkovKernel K) (_ : RectCompatible C K),
    @pathMeasure S _ K hK x E

noncomputable def lowerEnvPath (C : S → Set (Measure S)) (x : S)
    (E : Set (ℕ → S)) : ℝ≥0∞ :=
  ⨅ (K : Kernel S S) (hK : IsMarkovKernel K) (_ : RectCompatible C K),
    @pathMeasure S _ K hK x E

theorem qUpperEnvLB_of_le {Ksel : Kernel S S} [hKsel : IsMarkovKernel Ksel]
    (hmem : RectCompatible C Ksel) {x : S} {E : Set (ℕ → S)} {p : ℝ≥0∞}
    (hp : p ≤ pathMeasure Ksel x E) : p ≤ upperEnvPath C x E :=
  hp.trans (le_iSup_of_le Ksel (le_iSup_of_le hKsel (le_iSup_of_le hmem le_rfl)))

theorem qLowerEnvUB_of_ge {Ksel : Kernel S S} [hKsel : IsMarkovKernel Ksel]
    (hmem : RectCompatible C Ksel) {x : S} {E : Set (ℕ → S)} {p : ℝ≥0∞}
    (hp : pathMeasure Ksel x E ≤ p) : lowerEnvPath C x E ≤ p :=
  (iInf_le_of_le Ksel (iInf_le_of_le hKsel (iInf_le_of_le hmem le_rfl))).trans hp

theorem qRegionSat_uniform {x : S} {E : Set (ℕ → S)} {p : ℝ≥0∞}
    (h : ∀ (K : Kernel S S) (hK : IsMarkovKernel K),
      RectCompatible C K → p ≤ @pathMeasure S _ K hK x E) :
    p ≤ lowerEnvPath C x E :=
  le_iInf fun K => le_iInf fun hK => le_iInf fun hmem => h K hK hmem

theorem qUpperEnvLB_subTable {Ksel : Kernel S S} [IsMarkovKernel Ksel]
    (hmem : RectCompatible C Ksel) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {g : ℕ → S → ℝ} {T : ℕ} {Cb : ℝ}
    (hgm : ∀ k, Measurable (g k)) (hgb : ∀ k y, |g k y| ≤ Cb)
    (h0 : ∀ y, g 0 y ≤ if y ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ y, g (k + 1) y ≤
      if y ∈ B then 1 else if y ∈ A then ∫ z, g k z ∂Ksel y else 0)
    (x : S) :
    ENNReal.ofReal (g T x)
      ≤ upperEnvPath C x (Tabular.untilEventBdd A B T) :=
  qUpperEnvLB_of_le hmem (subTable_le hA hB hgm hgb h0 hstep x)

theorem qLowerEnvUB_reachAvoid {Ksel : Kernel S S} [IsMarkovKernel Ksel]
    (hmem : RectCompatible C Ksel) {Bad : Set S} {f : S → ℝ} {Cb : ℝ}
    (hBad : MeasurableSet Bad) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ Cb)
    (hf1 : ∀ y ∈ Bad, 1 ≤ f y)
    (hdrift : ∀ y, y ∉ Bad → ∫ z, f z ∂Ksel y ≤ f y)
    (x : S) :
    lowerEnvPath C x {ω : ℕ → S | ∃ n, ω n ∈ Bad} ≤ ENNReal.ofReal (f x) :=
  qLowerEnvUB_of_ge hmem
    (Battery.measure_reach_le hBad hf hf0 hfC hf1 hdrift x)

end Envelope

end

end Reach

end Qtsl

#print axioms Qtsl.Reach.subTable_le
#print axioms Qtsl.Reach.sound_reach_progress
#print axioms Qtsl.Reach.qSelRefines_of_pinRows
#print axioms Qtsl.Reach.qUpperEnvLB_of_le
#print axioms Qtsl.Reach.qLowerEnvUB_of_ge
#print axioms Qtsl.Reach.qRegionSat_uniform
#print axioms Qtsl.Reach.qUpperEnvLB_subTable
#print axioms Qtsl.Reach.qLowerEnvUB_reachAvoid
