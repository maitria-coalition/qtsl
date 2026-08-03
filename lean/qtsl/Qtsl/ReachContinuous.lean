import Qtsl.Reach
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Reachability certificates: continuous-state supermartingale side

The clamped exit function `clampExit` — the value-function surrogate a
continuous-state reach certificate carries — with the pointwise bounds and
measurability lemmas that let a one-step supermartingale inequality on the
transit region certify a bound on the reach probability. Companion to the
measurable-space reach module; the polynomial machinery discharges the
one-step inequality, and this module supplies the semantic bridge. -/

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

def clampExit (A B : Set S) (g : S → ℝ) : S → ℝ :=
  (A \ B).piecewise g (B.piecewise (fun _ => 1) fun _ => 0)

section ClampExit

variable {A B : Set S} {g : S → ℝ}

omit [MeasurableSpace S] in
lemma clampExit_of_transit {y : S} (hy : y ∈ A \ B) : clampExit A B g y = g y :=
  Set.piecewise_eq_of_mem _ _ _ hy

omit [MeasurableSpace S] in
lemma clampExit_of_target {y : S} (hy : y ∈ B) : clampExit A B g y = 1 := by
  have hyQ : y ∉ A \ B := fun h => h.2 hy
  rw [clampExit, Set.piecewise_eq_of_notMem _ _ _ hyQ, Set.piecewise_eq_of_mem _ _ _ hy]

omit [MeasurableSpace S] in
lemma clampExit_of_dead {y : S} (hyQ : y ∉ A \ B) (hyB : y ∉ B) :
    clampExit A B g y = 0 := by
  rw [clampExit, Set.piecewise_eq_of_notMem _ _ _ hyQ,
    Set.piecewise_eq_of_notMem _ _ _ hyB]

lemma measurable_clampExit (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hgm : Measurable g) : Measurable (clampExit A B g) :=
  Measurable.piecewise (hA.diff hB) hgm
    (Measurable.piecewise hB measurable_const measurable_const)

omit [MeasurableSpace S] in
lemma clampExit_nonneg (hg30 : ∀ y ∈ A \ B, 0 ≤ g y) (y : S) :
    0 ≤ clampExit A B g y := by
  by_cases hyQ : y ∈ A \ B
  · rw [clampExit_of_transit hyQ]; exact hg30 y hyQ
  · by_cases hyB : y ∈ B
    · rw [clampExit_of_target hyB]; exact zero_le_one
    · rw [clampExit_of_dead hyQ hyB]

omit [MeasurableSpace S] in
lemma clampExit_le_one (hg31 : ∀ y ∈ A \ B, g y ≤ 1) (y : S) :
    clampExit A B g y ≤ 1 := by
  by_cases hyQ : y ∈ A \ B
  · rw [clampExit_of_transit hyQ]; exact hg31 y hyQ
  · by_cases hyB : y ∈ B
    · rw [clampExit_of_target hyB]
    · rw [clampExit_of_dead hyQ hyB]; exact zero_le_one

omit [MeasurableSpace S] in

lemma le_clampExit (hg1 : ∀ y ∈ B, g y ≤ 1) (hg2 : ∀ y, y ∉ A → y ∉ B → g y ≤ 0)
    (y : S) : g y ≤ clampExit A B g y := by
  by_cases hyQ : y ∈ A \ B
  · rw [clampExit_of_transit hyQ]
  · by_cases hyB : y ∈ B
    · rw [clampExit_of_target hyB]; exact hg1 y hyB
    · rw [clampExit_of_dead hyQ hyB]
      have hyA : y ∉ A := fun hyA => hyQ ⟨hyA, hyB⟩
      exact hg2 y hyA hyB

end ClampExit

def stoppedState (A' : Set S) : ℕ → (ℕ → S) → S
  | 0 => fun ω => ω 0
  | n + 1 => (survive A' n).piecewise (fun ω => ω (n + 1)) (stoppedState A' n)

omit [MeasurableSpace S] in
lemma stoppedState_zero (A' : Set S) (ω : ℕ → S) : stoppedState A' 0 ω = ω 0 := rfl

omit [MeasurableSpace S] in
lemma stoppedState_succ_of_survive {A' : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∈ survive A' n) : stoppedState A' (n + 1) ω = ω (n + 1) :=
  Set.piecewise_eq_of_mem _ _ _ h

omit [MeasurableSpace S] in
lemma stoppedState_succ_of_not_survive {A' : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∉ survive A' n) : stoppedState A' (n + 1) ω = stoppedState A' n ω :=
  Set.piecewise_eq_of_notMem _ _ _ h

omit [MeasurableSpace S] in

lemma stopped_eq_stoppedState (f : S → ℝ) (A' : Set S) :
    ∀ (n : ℕ) (ω : ℕ → S), stopped f A' n ω = f (stoppedState A' n ω) := by
  intro n
  induction n with
  | zero => intro ω; rfl
  | succ n ih =>
    intro ω
    by_cases h : ω ∈ survive A' n
    · rw [stopped_succ_of_survive h, stoppedState_succ_of_survive h]
    · rw [stopped_succ_of_not_survive h, stoppedState_succ_of_not_survive h, ih]

omit [MeasurableSpace S] in

lemma stoppedState_of_survive {A' : Set S} : ∀ {n : ℕ} {ω : ℕ → S},
    ω ∈ survive A' n → stoppedState A' n ω = ω n
  | 0, _, _ => rfl
  | _ + 1, _, h => stoppedState_succ_of_survive (survive_succ_subset h)

omit [MeasurableSpace S] in

lemma exists_firstExit {A' : Set S} : ∀ {n : ℕ} {ω : ℕ → S}, ω ∉ survive A' n →
    ∃ j ≤ n, (∀ i < j, ω i ∉ A') ∧ ω j ∈ A' ∧ stoppedState A' n ω = ω j := by
  intro n
  induction n with
  | zero =>
    intro ω h
    have h0 : ω 0 ∈ A' := by
      by_contra h0
      exact h fun k hk => by
        obtain rfl : k = 0 := Nat.le_zero.1 hk
        exact h0
    exact ⟨0, le_rfl, fun i hi => absurd hi i.not_lt_zero, h0, rfl⟩
  | succ n ih =>
    intro ω h
    by_cases hs : ω ∈ survive A' n
    · have hlast : ω (n + 1) ∈ A' := by
        by_contra hlast
        refine h (mem_survive.2 fun k hk => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
        · exact mem_survive.1 hs k (Nat.lt_succ_iff.1 hlt)
        · exact hlast
      exact ⟨n + 1, le_rfl,
        fun i hi => mem_survive.1 hs i (Nat.lt_succ_iff.1 hi), hlast,
        stoppedState_succ_of_survive hs⟩
    · obtain ⟨j, hj, hpre, hjA, heq⟩ := ih hs
      exact ⟨j, hj.trans n.le_succ, hpre, hjA,
        (stoppedState_succ_of_not_survive hs).trans heq⟩

structure SpaceTimeReachInterface (A B : Set S) (T : ℝ) (g : ℝ → S → ℝ) (x : S) where

  Ω : Type*

  [mΩ : MeasurableSpace Ω]

  P : Measure Ω

  τ : Ω → ℝ
  hτ0 : ∀ ω, 0 ≤ τ ω
  hτT : ∀ ω, τ ω ≤ T

  ξ : Ω → S

  hstill : ∀ ω, ξ ω ∈ A \ B → τ ω = T

  hreachMeas : MeasurableSet {ω | ξ ω ∈ B}

  hsampled : ENNReal.ofReal (g 0 x) ≤ ∫⁻ ω, ENNReal.ofReal (g (τ ω) (ξ ω)) ∂P

attribute [instance] SpaceTimeReachInterface.mΩ

namespace SpaceTimeReachInterface

variable {A B : Set S} {T : ℝ} {g : ℝ → S → ℝ} {x : S}

omit [MeasurableSpace S] in

theorem reach_floor (D : SpaceTimeReachInterface A B T g x)
    (hgB : ∀ t, 0 ≤ t → t ≤ T → ∀ y ∈ B, g t y ≤ 1)
    (hgD : ∀ t, 0 ≤ t → t ≤ T → ∀ y, y ∉ A → y ∉ B → g t y ≤ 0)
    (hgT : ∀ y ∈ A \ B, g T y ≤ 0) :
    ENNReal.ofReal (g 0 x) ≤ D.P {ω | D.ξ ω ∈ B} := by
  refine D.hsampled.trans ?_
  calc ∫⁻ ω, ENNReal.ofReal (g (D.τ ω) (D.ξ ω)) ∂D.P
      ≤ ∫⁻ ω, ({ω | D.ξ ω ∈ B}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂D.P := by
        refine lintegral_mono fun ω => ?_
        by_cases hB : D.ξ ω ∈ B
        · have hmem : ω ∈ {ω' | D.ξ ω' ∈ B} := hB
          rw [Set.indicator_of_mem hmem]
          calc ENNReal.ofReal (g (D.τ ω) (D.ξ ω))
              ≤ ENNReal.ofReal 1 :=
                ENNReal.ofReal_le_ofReal (hgB _ (D.hτ0 ω) (D.hτT ω) _ hB)
            _ = 1 := ENNReal.ofReal_one
        · have hmem : ω ∉ {ω' | D.ξ ω' ∈ B} := hB
          rw [Set.indicator_of_notMem hmem]
          refine le_of_eq (ENNReal.ofReal_eq_zero.2 ?_)
          by_cases hQ : D.ξ ω ∈ A \ B
          · rw [D.hstill ω hQ]
            exact hgT _ hQ
          · have hA : D.ξ ω ∉ A := fun hA => hQ ⟨hA, hB⟩
            exact hgD _ (D.hτ0 ω) (D.hτT ω) _ hA hB
    _ = D.P {ω | D.ξ ω ∈ B} := by
        rw [lintegral_indicator D.hreachMeas]
        simp

def ofExitPoint (t₀ : ℝ) (y₀ : S) (h0 : 0 ≤ t₀) (hT : t₀ ≤ T)
    (hstill : y₀ ∈ A \ B → t₀ = T) (hmono : g 0 x ≤ g t₀ y₀) :
    SpaceTimeReachInterface A B T g x where
  Ω := Unit
  mΩ := inferInstance
  P := Measure.dirac ()
  τ _ := t₀
  hτ0 _ := h0
  hτT _ := hT
  ξ _ := y₀
  hstill _ h := hstill h
  hreachMeas := by
    by_cases h : y₀ ∈ B
    · simp [h]
    · simp [h]
  hsampled := by
    rw [lintegral_dirac' _ measurable_const]
    exact ENNReal.ofReal_le_ofReal hmono

end SpaceTimeReachInterface

structure ProgressReachInterface (A B : Set S) (g : S → ℝ) (x : S) where

  Ω : Type*

  [mΩ : MeasurableSpace Ω]

  P : Measure Ω

  X : ℝ → Ω → S

  reach : Set Ω
  hreachMeas : MeasurableSet reach

  transit : ℝ → Set Ω
  htransitMeas : ∀ t : ℝ, MeasurableSet (transit t)

  hhit : ∀ (t : ℝ) ω, 0 ≤ t → X t ω ∈ B → ω ∈ reach

  hstill : ∀ (t : ℝ) ω, 0 ≤ t → X t ω ∈ A \ B → ω ∈ transit t

  hsampled : ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal (g x) ≤ ∫⁻ ω, ENNReal.ofReal (g (X t ω)) ∂P

  hvanish : Tendsto (fun n : ℕ => P (transit n)) atTop (𝓝 0)

attribute [instance] ProgressReachInterface.mΩ

theorem vanish_of_time_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s : ℕ → Set Ω} {Eτ : ℝ≥0∞} (hEτ : Eτ ≠ ∞)
    (h : ∀ n : ℕ, (n : ℝ≥0∞) * P (s n) ≤ Eτ) :
    Tendsto (fun n : ℕ => P (s n)) atTop (𝓝 0) := by
  refine ENNReal.tendsto_atTop_zero.2 fun ε hε => ?_
  rcases eq_top_or_lt_top ε with rfl | hεtop
  · exact ⟨0, fun n _ => le_top⟩
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hEτ hε.ne').ne
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 N) hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.1 hn1
  have hP : P (s n) ≤ Eτ / (n : ℝ≥0∞) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hn0)
      (Or.inl (ENNReal.natCast_ne_top n))).2 (by rw [mul_comm]; exact h n)
  refine hP.trans ?_
  rw [ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n)]
  calc Eτ = Eτ / ε * ε := (ENNReal.div_mul_cancel hε.ne' hεtop.ne).symm
    _ ≤ (n : ℝ≥0∞) * ε :=
        mul_le_mul' (hN.le.trans (Nat.cast_le.2 (le_trans (Nat.le_succ N) hn)))
          le_rfl
    _ = ε * (n : ℝ≥0∞) := mul_comm _ _

namespace ProgressReachInterface

variable {A B : Set S} {g : S → ℝ} {x : S}

omit [MeasurableSpace S] in

theorem reach_floor (D : ProgressReachInterface A B g x)
    (hg1 : ∀ y ∈ B, g y ≤ 1) (hg2 : ∀ y, y ∉ A → y ∉ B → g y ≤ 0)
    (hg31 : ∀ y ∈ A \ B, g y ≤ 1) :
    ENNReal.ofReal (g x) ≤ D.P D.reach := by
  have hstep : ∀ n : ℕ, ENNReal.ofReal (g x) ≤ D.P D.reach + D.P (D.transit n) := by
    intro n
    refine (D.hsampled n (Nat.cast_nonneg n)).trans ?_
    calc ∫⁻ ω, ENNReal.ofReal (g (D.X n ω)) ∂D.P
        ≤ ∫⁻ ω, (D.reach.indicator (fun _ => (1 : ℝ≥0∞)) ω
            + (D.transit n).indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂D.P := by
          refine lintegral_mono fun ω => ?_
          by_cases hB : D.X (n : ℝ) ω ∈ B
          · have hr : ω ∈ D.reach := D.hhit n ω (Nat.cast_nonneg n) hB
            calc ENNReal.ofReal (g (D.X (n : ℝ) ω))
                ≤ 1 := by
                  rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (hg1 _ hB)
              _ ≤ _ := by
                  rw [Set.indicator_of_mem hr]
                  exact le_add_of_nonneg_right zero_le
          · by_cases hQ : D.X (n : ℝ) ω ∈ A \ B
            · have ht : ω ∈ D.transit n := D.hstill n ω (Nat.cast_nonneg n) hQ
              calc ENNReal.ofReal (g (D.X (n : ℝ) ω))
                  ≤ 1 := by
                    rw [← ENNReal.ofReal_one]
                    exact ENNReal.ofReal_le_ofReal (hg31 _ hQ)
                _ ≤ _ := by
                    rw [Set.indicator_of_mem ht]
                    exact le_add_of_nonneg_left zero_le
            · have hA : D.X (n : ℝ) ω ∉ A := fun hA => hQ ⟨hA, hB⟩
              rw [ENNReal.ofReal_eq_zero.2 (hg2 _ hA hB)]
              exact zero_le
      _ = D.P D.reach + D.P (D.transit n) := by
          rw [lintegral_add_left (measurable_const.indicator D.hreachMeas),
            lintegral_indicator D.hreachMeas,
            lintegral_indicator (D.htransitMeas n)]
          simp
  have hlim : Tendsto (fun n : ℕ => D.P D.reach + D.P (D.transit n)) atTop
      (𝓝 (D.P D.reach)) := by
    simpa using tendsto_const_nhds.add D.hvanish
  exact ge_of_tendsto' hlim hstep

end ProgressReachInterface

section HullWrapper

variable {K : Kernel S S} [IsMarkovKernel K] {A B : Set S}

set_option maxHeartbeats 800000 in

theorem sound_reach_progress_hull
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {g W : S → ℝ} {ε MW : ℝ} {H : Set S} (hH : MeasurableSet H)
    (hgm : Measurable g) (hWm : Measurable W)
    (hε : 0 < ε)
    (hg1 : ∀ y ∈ B, g y ≤ 1)
    (hg2 : ∀ y, y ∉ A → y ∉ B → g y ≤ 0)
    (hg30 : ∀ y ∈ A \ B, 0 ≤ g y)
    (hg31 : ∀ y ∈ A \ B, g y ≤ 1)
    (hgint : ∀ y ∈ A \ B, Integrable g (K y))
    (hg4 : ∀ y ∈ A \ B, g y ≤ ∫ z, g z ∂K y)
    (hQH : A \ B ⊆ H)
    (hconf : ∀ y ∈ A \ B, K y Hᶜ = 0)
    (hW0 : ∀ y ∈ H, 0 ≤ W y) (hWM : ∀ y ∈ H, W y ≤ MW)
    (hW6 : ∀ y ∈ A \ B, ∫ z, W z ∂K y ≤ W y - ε)
    (x : S) :
    ENNReal.ofReal (g x) ≤ pathMeasure K x (untilEvent A B) := by
  set W' : S → ℝ := H.piecewise W (fun _ => 0) with hW'def
  have hW'm : Measurable W' := Measurable.piecewise hH hWm measurable_const
  have hW'H : ∀ y ∈ H, W' y = W y := fun y hy => Set.piecewise_eq_of_mem _ _ _ hy
  have hW'0 : ∀ y, 0 ≤ W' y := by
    intro y
    by_cases hy : y ∈ H
    · rw [hW'H y hy]; exact hW0 y hy
    · rw [hW'def, Set.piecewise_eq_of_notMem _ _ _ hy]
  have hW'M : ∀ y, W' y ≤ max MW 0 := by
    intro y
    by_cases hy : y ∈ H
    · rw [hW'H y hy]; exact (hWM y hy).trans (le_max_left _ _)
    · rw [hW'def, Set.piecewise_eq_of_notMem _ _ _ hy]
      exact le_max_right _ _
  have hW'6 : ∀ y ∈ A \ B, ∫ z, W' z ∂K y ≤ W' y - ε := by
    intro y hy
    have hae : W' =ᵐ[K y] W := by
      refine measure_mono_null (fun z hz => ?_) (hconf y hy)
      by_contra hzH
      exact hz (hW'H z (Set.notMem_compl_iff.1 hzH))
    rw [integral_congr_ae hae, hW'H y (hQH hy)]
    exact hW6 y hy
  exact sound_reach_progress hA hB hgm hW'm hε hg1 hg2 hg30 hg31 hgint hg4
    hW'0 hW'M hW'6 x

end HullWrapper

section OfChain

variable {K : Kernel S S} [IsMarkovKernel K] {A B : Set S}

set_option maxHeartbeats 1600000 in

def ProgressReachInterface.ofChain
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
    ProgressReachInterface A B (clampExit A B g) x where
  Ω := ℕ → S
  mΩ := inferInstance
  P := pathMeasure K x
  X t ω := stoppedState ((A \ B)ᶜ) ⌊t⌋₊ ω
  reach := untilEvent A B
  hreachMeas := measurableSet_untilEvent hA hB
  transit t := survive ((A \ B)ᶜ) ⌊t⌋₊
  htransitMeas t := measurableSet_survive (hA.diff hB).compl _
  hhit := by
    intro t ω _ hXB
    by_cases hs : ω ∈ survive ((A \ B)ᶜ) ⌊t⌋₊
    · rw [stoppedState_of_survive hs] at hXB
      have hQ : ω ⌊t⌋₊ ∈ A \ B :=
        Set.notMem_compl_iff.1 (mem_survive.1 hs _ le_rfl)
      exact absurd hXB hQ.2
    · obtain ⟨j, _, hpre, _, heq⟩ := exists_firstExit hs
      rw [heq] at hXB
      exact ⟨j, hXB, fun i hi => (Set.notMem_compl_iff.1 (hpre i hi)).1⟩
  hstill := by
    intro t ω _ hXQ
    by_contra hs
    obtain ⟨j, _, _, hjA, heq⟩ := exists_firstExit hs
    rw [heq] at hXQ
    exact hjA hXQ
  hsampled := by
    intro t _
    set n : ℕ := ⌊t⌋₊
    set g' : S → ℝ := clampExit A B g
    have hg'm : Measurable g' := measurable_clampExit hA hB hgm
    have hg'0 : ∀ y, 0 ≤ g' y := clampExit_nonneg hg30
    have hg'1 : ∀ y, g' y ≤ 1 := clampExit_le_one hg31
    have hg'int : ∀ y : S, Integrable g' (K y) := fun y =>
      (integrable_const (1 : ℝ)).mono' hg'm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg'0 z)]
          exact hg'1 z)

    have hdriftf : ∀ y, y ∉ (A \ B)ᶜ → ∫ z, (1 - g' z) ∂K y ≤ 1 - g' y := by
      intro y hy
      have hyQ : y ∈ A \ B := Set.notMem_compl_iff.1 hy
      have hsplit : ∫ z, (1 - g' z) ∂K y = 1 - ∫ z, g' z ∂K y := by
        rw [integral_sub (integrable_const 1) (hg'int y), integral_const]
        simp [measureReal_def]
      rw [hsplit]
      have hgle : g' y ≤ ∫ z, g' z ∂K y := by
        calc g' y = g y := clampExit_of_transit hyQ
          _ ≤ ∫ z, g z ∂K y := hg4 y hyQ
          _ ≤ ∫ z, g' z ∂K y :=
              integral_mono (hgint y hyQ) (hg'int y) (le_clampExit hg1 hg2)
      linarith
    have hsup := supermartingale_stopped (K := K) (A := (A \ B)ᶜ) (C := 1)
      (hA.diff hB).compl (measurable_const.sub hg'm)
      (fun y => by show (0 : ℝ) ≤ 1 - g' y; have := hg'1 y; linarith)
      (fun y => by show (1 : ℝ) - g' y ≤ 1; have := hg'0 y; linarith)
      hdriftf x
    have hstopint : ∀ m : ℕ,
        Integrable (stopped g' ((A \ B)ᶜ) m) (pathMeasure K x) := by
      intro m
      refine (integrable_const (1 : ℝ)).mono'
        (((stronglyAdapted_stopped (hA.diff hB).compl hg'm m).mono
          ((Filtration.piLE (X := fun _ : ℕ => S)).le m)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (stopped_pred (fun r => 0 ≤ r) hg'0 m ω)]
      exact stopped_pred (fun r => r ≤ 1) hg'1 m ω
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
    have hexp : g' x ≤ ∫ ω, stopped g' ((A \ B)ᶜ) n ω ∂pathMeasure K x := by
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
            = 1 - stopped g' ((A \ B)ᶜ) n ω := fun ω =>
          stopped_const_sub g' _ 1 n ω
        rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
          integral_sub (integrable_const 1) (hstopint n), integral_const]
        simp [measureReal_def]
      rw [h2] at h1
      linarith

    calc ENNReal.ofReal (g' x)
        ≤ ENNReal.ofReal (∫ ω, stopped g' ((A \ B)ᶜ) n ω ∂pathMeasure K x) :=
          ENNReal.ofReal_le_ofReal hexp
      _ ≤ ∫⁻ ω, ENNReal.ofReal (stopped g' ((A \ B)ᶜ) n ω) ∂pathMeasure K x :=
          le_of_eq (ofReal_integral_eq_lintegral_ofReal (hstopint n)
            (Filter.Eventually.of_forall fun ω =>
              stopped_pred (fun r => 0 ≤ r) hg'0 n ω))
      _ = ∫⁻ ω, ENNReal.ofReal (g' (stoppedState ((A \ B)ᶜ) n ω))
            ∂pathMeasure K x := by
          refine lintegral_congr fun ω => ?_
          rw [stopped_eq_stoppedState]
  hvanish := by
    have hVint : ∀ m : ℕ,
        Integrable (fun ω : ℕ → S => W (ω m)) (pathMeasure K x) := by
      intro m
      refine (integrable_const MW).mono'
        ((hWm.comp (measurable_pi_apply m)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
      exact hWM _
    have hexit : ∀ᵐ ω ∂pathMeasure K x, ∃ m, ω m ∈ (A \ B)ᶜ := by
      refine Excursions.ae_hits_of_ranking
        (𝒢 := Filtration.piLE (X := fun _ : ℕ => S))
        (X := fun m (ω : ℕ → S) => ω m) (B := (A \ B)ᶜ)
        (V := fun m (ω : ℕ → S) => W (ω m)) hε hVint
        (fun m ω => hW0 (ω m))
        (fun m => (measurable_coord_piLE le_rfl) (hA.diff hB).compl) ?_
      intro m
      filter_upwards [condExp_comp_coord_succ (K := K) hWm hW0 hWM x m]
        with ω hω hmem
      have hωm : ω m ∈ A \ B := Set.notMem_compl_iff.1 hmem
      show ((pathMeasure K x)[fun ω : ℕ → S => W (ω (m + 1)) |
          Filtration.piLE (X := fun _ : ℕ => S) m]) ω ≤ W (ω m) - ε
      rw [hω]
      exact hW6 (ω m) hωm
    have hnever : pathMeasure K x {ω : ℕ → S | ∀ m, ω m ∈ A \ B} = 0 := by
      rw [ae_iff] at hexit
      refine measure_mono_null ?_ hexit
      intro ω hω
      simp only [Set.mem_setOf_eq, not_exists]
      exact fun m => Set.notMem_compl_iff.2 (hω m)
    have hIcap : ⋂ m : ℕ, survive ((A \ B)ᶜ) m
        = {ω : ℕ → S | ∀ k, ω k ∈ A \ B} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h k
        exact Set.notMem_compl_iff.1 (mem_survive.1 (h k) k le_rfl)
      · intro h m k hk
        exact Set.notMem_compl_iff.2 (h k)
    have htend0 : Tendsto (fun m : ℕ => pathMeasure K x (survive ((A \ B)ᶜ) m))
        atTop (𝓝 0) := by
      have hanti : Antitone fun m : ℕ => survive ((A \ B)ᶜ) m :=
        antitone_nat_of_succ_le fun m => survive_succ_subset
      have h := tendsto_measure_iInter_atTop (μ := pathMeasure K x)
        (s := fun m : ℕ => survive ((A \ B)ᶜ) m)
        (fun m => (measurableSet_survive (hA.diff hB).compl m).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [hIcap, hnever] at h
      exact h
    have heq : (fun m : ℕ =>
        pathMeasure K x (survive ((A \ B)ᶜ) ⌊(m : ℝ)⌋₊))
        = fun m : ℕ => pathMeasure K x (survive ((A \ B)ᶜ) m) := by
      funext m
      rw [Nat.floor_natCast]
    rw [heq]
    exact htend0

set_option maxHeartbeats 800000 in

theorem reach_floor_ofChain
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
  have hD := (ProgressReachInterface.ofChain hA hB hgm hWm hε hg1 hg2 hg30 hg31
    hgint hg4 hW0 hWM hW6 x).reach_floor
    (fun y hy => by rw [clampExit_of_target hy])
    (fun y hyA hyB => by
      have hyQ : y ∉ A \ B := fun h => hyA h.1
      rw [clampExit_of_dead hyQ hyB])
    (fun y hy => by rw [clampExit_of_transit hy]; exact hg31 y hy)
  exact (ENNReal.ofReal_le_ofReal (le_clampExit hg1 hg2 x)).trans hD

end OfChain

section OU

theorem integral_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ z, z ^ 2 ∂gaussianReal m v = (v : ℝ) + m ^ 2 := by
  have h2 : MemLp (fun z : ℝ => z) 2 (gaussianReal m v) := by
    simpa [Function.id_def] using
      memLp_id_gaussianReal (μ := m) (v := v) 2
  have hvar := variance_fun_id_gaussianReal (μ := m) (v := v)
  rw [variance_eq_sub h2] at hvar
  simp only [Pi.pow_apply] at hvar
  have hmean : ∫ z, z ∂gaussianReal m v = m := integral_id_gaussianReal
  rw [hmean] at hvar
  linarith

def ouKernel (a : ℝ) (v : ℝ≥0) : Kernel ℝ ℝ where
  toFun y := gaussianReal (a * y) v
  measurable' := measurable_gaussianReal.comp
    ((measurable_id.const_mul a).prodMk measurable_const)

lemma ouKernel_apply (a : ℝ) (v : ℝ≥0) (y : ℝ) :
    ouKernel a v y = gaussianReal (a * y) v := rfl

instance (a : ℝ) (v : ℝ≥0) : IsMarkovKernel (ouKernel a v) :=
  ⟨fun y => by rw [ouKernel_apply]; infer_instance⟩

set_option maxHeartbeats 1600000 in

theorem ou_reach_floor (x : ℝ) :
    ENNReal.ofReal (1 - x ^ 2 / 100)
      ≤ pathMeasure (ouKernel (1/2) 1) x
          (untilEvent (Set.Ioo (-10 : ℝ) 10) (Set.Icc (-2 : ℝ) 2)) := by

  have hQmem : ∀ y : ℝ, y ∈ Set.Ioo (-10 : ℝ) 10 \ Set.Icc (-2 : ℝ) 2 →
      4 < y ^ 2 ∧ y ^ 2 < 100 := by
    rintro y ⟨⟨hlo, hhi⟩, hnB⟩
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnB
    constructor
    · rcases hnB with h | h <;> nlinarith
    · nlinarith

  have hsq : ∀ y : ℝ, ∫ z, z ^ 2 ∂(ouKernel (1/2) 1 y) = 1 + (y / 2) ^ 2 := by
    intro y
    rw [ouKernel_apply, integral_sq_gaussianReal]
    norm_num
    ring
  have hsqint : ∀ y : ℝ, Integrable (fun z : ℝ => z ^ 2) (ouKernel (1/2) 1 y) := by
    intro y
    rw [ouKernel_apply]
    simpa [Function.id_def] using
      (memLp_id_gaussianReal (μ := (1/2 : ℝ) * y) (v := 1) 2).integrable_sq
  refine reach_floor_ofChain (K := ouKernel (1/2) 1)
    measurableSet_Ioo measurableSet_Icc
    (g := fun y => 1 - y ^ 2 / 100) (W := fun y => min (y ^ 2) 100)
    (ε := 2) (MW := 100)
    (by fun_prop) (by fun_prop) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x
  ·
    intro y _
    nlinarith [sq_nonneg y]
  ·
    intro y hyA _
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hyA
    rcases hyA with h | h <;> nlinarith
  ·
    intro y hy
    have := (hQmem y hy).2
    nlinarith
  ·
    intro y hy
    nlinarith [sq_nonneg y]
  ·
    intro y _
    exact (integrable_const (1 : ℝ)).sub ((hsqint y).div_const 100)
  ·
    intro y hy
    have h4 := (hQmem y hy).1
    have hval : ∫ z, (1 - z ^ 2 / 100) ∂(ouKernel (1/2) 1 y)
        = 1 - (1 + (y / 2) ^ 2) / 100 := by
      rw [integral_sub (integrable_const 1) ((hsqint y).div_const 100),
        integral_const, integral_div, hsq y]
      simp [measureReal_def]
    rw [hval]
    nlinarith
  ·
    intro y
    exact le_min (sq_nonneg y) (by norm_num)
  ·
    intro y
    exact min_le_right _ _
  ·
    intro y hy
    obtain ⟨h4, h100⟩ := hQmem y hy
    have hWint : Integrable (fun z : ℝ => min (z ^ 2) 100) (ouKernel (1/2) 1 y) := by
      refine (integrable_const (100 : ℝ)).mono' ?_
        (Filter.Eventually.of_forall fun z => ?_)
      · exact ((measurable_id.pow_const 2).min measurable_const).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg z) (by norm_num))]
        exact min_le_right _ _
    have hle : ∫ z, min (z ^ 2) 100 ∂(ouKernel (1/2) 1 y)
        ≤ ∫ z, z ^ 2 ∂(ouKernel (1/2) 1 y) :=
      integral_mono hWint (hsqint y) fun z => min_le_left _ _
    rw [hsq y] at hle
    have hWy : min (y ^ 2) 100 = y ^ 2 := min_eq_left h100.le
    rw [hWy]
    nlinarith

theorem ou_reach_floor_at_five :
    ENNReal.ofReal (3 / 4)
      ≤ pathMeasure (ouKernel (1/2) 1) 5
          (untilEvent (Set.Ioo (-10 : ℝ) 10) (Set.Icc (-2 : ℝ) 2)) := by
  have h := ou_reach_floor 5
  norm_num at h ⊢
  exact h

end OU

end

end Reach

end Qtsl

#print axioms Qtsl.Reach.SpaceTimeReachInterface.reach_floor
#print axioms Qtsl.Reach.SpaceTimeReachInterface.ofExitPoint
#print axioms Qtsl.Reach.ProgressReachInterface.reach_floor
#print axioms Qtsl.Reach.vanish_of_time_bound
#print axioms Qtsl.Reach.sound_reach_progress_hull
#print axioms Qtsl.Reach.ProgressReachInterface.ofChain
#print axioms Qtsl.Reach.reach_floor_ofChain
#print axioms Qtsl.Reach.integral_sq_gaussianReal
#print axioms Qtsl.Reach.ou_reach_floor
#print axioms Qtsl.Reach.ou_reach_floor_at_five
