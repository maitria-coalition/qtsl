import QtslAux.Ville
import QtslAux.Deadline
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # Soundness of safety-battery and deadline certificates over Markov chains

This module constructs the path measure of a time-homogeneous Markov chain
from a Markov kernel `K : Kernel S S` via the Ionescu-Tulcea trajectory
kernel, and proves the soundness of two families of QTSL proof rules whose
side conditions are stated pointwise on the kernel: safety batteries
(invariance with probability at least `p`) and deadlines (hitting a target
within `T` steps with probability at least `p`).

The certificate data in both cases is a barrier/Lyapunov function
`V : S → ℝ` satisfying nonnegativity, a drift (respectively geometric decay)
condition off the unsafe (respectively target) set, a unit floor on the
unsafe set, and kernel-support conditions keeping the chain inside the
certified region. The proofs stop the process at the first entry into the
distinguished set, show the stopped process is a supermartingale for the path
measure, and conclude with Ville's inequality (safety) or the geometric
deadline tail bound (deadlines).

Main definitions:

* `pathMeasure K x`: the law on `ℕ → S` of the chain started at `x`.
* `survive A n`: paths avoiding `A` up to time `n`.
* `stopped f A`: the process `f` frozen at the first entry into `A`.

Main results:

* `supermartingale_stopped`: the stopped process of a bounded measurable
  `f` with nonpositive drift off `A` is a supermartingale.
* `measure_reach_le`: the probability of ever reaching `A` is at most `f x`.
* `sound_QSafetyBattery_failClosed`, `sound_QSafetyBattery`: soundness of the
  safety-battery rule — the chain remains in the safe region forever with
  probability at least `p`.
* `sound_QDeadline_hit`, `sound_QDeadline`: soundness of the deadline rule —
  the chain reaches `B` within `T` steps with probability at least `p`.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function

namespace Qtsl.Battery

variable {S : Type*}

section Chain

variable [MeasurableSpace S]

/-- The time-homogeneous kernel `K` reindexed for the Ionescu-Tulcea
construction: the transition out of a finite history `u : Π i : Iic n, S`
depends only on the current state `u n`. -/
noncomputable def mchain (K : Kernel S S) (n : ℕ) : Kernel (Π _i : Iic n, S) S :=
  K.comap (fun u => u ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) : IsMarkovKernel (mchain K n) := by
  unfold mchain; infer_instance

lemma mchain_apply (K : Kernel S S) (n : ℕ) (u : Π _i : Iic n, S) :
    mchain K n u = K (u ⟨n, mem_Iic.2 le_rfl⟩) :=
  Kernel.comap_apply _ _ _

/-- The law of the Markov chain with transition kernel `K` started at `x`,
as a probability measure on the path space `ℕ → S`, obtained from the
Ionescu-Tulcea trajectory kernel. -/
noncomputable def pathMeasure (K : Kernel S S) [IsMarkovKernel K] (x : S) :
    Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S) (κ := mchain K) 0 (fun _ => x)

instance (K : Kernel S S) [IsMarkovKernel K] (x : S) :
    IsProbabilityMeasure (pathMeasure K x) := by
  unfold pathMeasure; infer_instance

lemma measurable_coord_piLE {k n : ℕ} (hk : k ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] (fun ω : ℕ → S => ω k) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h₁ : Measurable[MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => S) n)
      inferInstance] (Preorder.frestrictLe (π := fun _ : ℕ => S) n) :=
    measurable_iff_comap_le.2 le_rfl
  exact (measurable_pi_apply (⟨k, mem_Iic.2 hk⟩ : Iic n)).comp h₁

end Chain

/-- The event that a path avoids the set `A` at every time up to `n`. -/
def survive (A : Set S) (n : ℕ) : Set (ℕ → S) := {ω | ∀ k ≤ n, ω k ∉ A}

lemma mem_survive {A : Set S} {n : ℕ} {ω : ℕ → S} :
    ω ∈ survive A n ↔ ∀ k ≤ n, ω k ∉ A := Iff.rfl

lemma survive_succ_subset {A : Set S} {n : ℕ} : survive A (n + 1) ⊆ survive A n :=
  fun _ h k hk => h k (hk.trans n.le_succ)

lemma survive_congr {A : Set S} {n : ℕ} {ω ω' : ℕ → S} (h : ∀ k ≤ n, ω k = ω' k) :
    ω ∈ survive A n ↔ ω' ∈ survive A n := by
  constructor <;> intro hs k hk <;> [rw [← h k hk]; rw [h k hk]] <;> exact hs k hk

/-- The process `n ↦ f (ω n)` stopped at the first entry of the path `ω` into
`A`: while the path has avoided `A` strictly before time `n + 1`, the value is
`f (ω (n + 1))`; afterwards the value is frozen. -/
noncomputable def stopped (f : S → ℝ) (A : Set S) : ℕ → (ℕ → S) → ℝ
  | 0 => fun ω => f (ω 0)
  | n + 1 => (survive A n).piecewise (fun ω => f (ω (n + 1))) (stopped f A n)

lemma stopped_zero (f : S → ℝ) (A : Set S) (ω : ℕ → S) : stopped f A 0 ω = f (ω 0) := rfl

lemma stopped_succ_of_survive {f : S → ℝ} {A : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∈ survive A n) : stopped f A (n + 1) ω = f (ω (n + 1)) :=
  Set.piecewise_eq_of_mem _ _ _ h

lemma stopped_succ_of_not_survive {f : S → ℝ} {A : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∉ survive A n) : stopped f A (n + 1) ω = stopped f A n ω :=
  Set.piecewise_eq_of_notMem _ _ _ h

lemma stopped_of_survive {f : S → ℝ} {A : Set S} : ∀ {n : ℕ} {ω : ℕ → S},
    ω ∈ survive A n → stopped f A n ω = f (ω n)
  | 0, _, _ => rfl
  | _ + 1, _, h => stopped_succ_of_survive (survive_succ_subset h)

lemma stopped_pred {f : S → ℝ} {A : Set S} (P : ℝ → Prop) (hf : ∀ y, P (f y)) :
    ∀ (n : ℕ) (ω : ℕ → S), P (stopped f A n ω) := by
  intro n
  induction n with
  | zero => exact fun ω => hf _
  | succ n ih =>
    intro ω
    by_cases h : ω ∈ survive A n
    · rw [stopped_succ_of_survive h]; exact hf _
    · rw [stopped_succ_of_not_survive h]; exact ih ω

lemma one_le_stopped {f : S → ℝ} {A : Set S} (hf1 : ∀ y ∈ A, 1 ≤ f y) :
    ∀ (n : ℕ) (ω : ℕ → S), (∃ k ≤ n, ω k ∈ A) → 1 ≤ stopped f A n ω := by
  intro n
  induction n with
  | zero =>
    rintro ω ⟨k, hk, hkA⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact hf1 _ hkA
  | succ n ih =>
    rintro ω ⟨k, hk, hkA⟩
    by_cases h : ω ∈ survive A n
    · rw [stopped_succ_of_survive h]
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
      · exact absurd hkA (h k (Nat.lt_succ_iff.1 hlt))
      · exact hf1 _ hkA
    · rw [stopped_succ_of_not_survive h]
      rw [mem_survive] at h
      push Not at h
      obtain ⟨j, hjn, hjA⟩ := h
      exact ih ω ⟨j, hjn, hjA⟩

lemma stopped_congr {f : S → ℝ} {A : Set S} : ∀ {n : ℕ} {ω ω' : ℕ → S},
    (∀ k ≤ n, ω k = ω' k) → stopped f A n ω = stopped f A n ω' := by
  intro n
  induction n with
  | zero => intro ω ω' h; simp only [stopped_zero, h 0 le_rfl]
  | succ n ih =>
    intro ω ω' h
    have hh : ∀ k ≤ n, ω k = ω' k := fun k hk => h k (hk.trans n.le_succ)
    by_cases hs : ω ∈ survive A n
    · rw [stopped_succ_of_survive hs, stopped_succ_of_survive ((survive_congr hh).1 hs),
        h (n + 1) le_rfl]
    · rw [stopped_succ_of_not_survive hs,
        stopped_succ_of_not_survive (fun hs' => hs ((survive_congr hh).2 hs')), ih hh]

private lemma updateFinset_eq_of_le {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S} {k : ℕ}
    (hk : k ≤ n) : updateFinset y (Iic n) u k = u ⟨k, mem_Iic.2 hk⟩ := by
  simp [updateFinset, mem_Iic, hk]

private lemma updateFinset_eq_succ {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S} :
    updateFinset y (Iic n) u (n + 1) = y (n + 1) := by
  simp [updateFinset, mem_Iic]

section WithMeasurable

variable [MeasurableSpace S]

lemma measurableSet_survive_piLE {A : Set S} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (survive A n) := by
  have h : survive A n = ⋂ k, ⋂ (_ : k ≤ n), (fun ω : ℕ → S => ω k) ⁻¹' Aᶜ := by
    ext ω; simp [survive]
  rw [h]
  exact .iInter fun k => .iInter fun hk => (measurable_coord_piLE hk) hA.compl

lemma stronglyAdapted_stopped {f : S → ℝ} {A : Set S} (hA : MeasurableSet A)
    (hf : Measurable f) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => S)) (stopped f A) := by
  intro n
  induction n with
  | zero => exact (hf.comp (measurable_coord_piLE le_rfl)).stronglyMeasurable
  | succ n ih =>
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.piecewise
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono n.le_succ _
        (measurableSet_survive_piLE hA n))
      (hf.comp (measurable_coord_piLE le_rfl))
      ((ih.mono ((Filtration.piLE (X := fun _ : ℕ => S)).mono n.le_succ)).measurable)

variable {K : Kernel S S} [IsMarkovKernel K]

private lemma integrable_stopped_pathMeasure {f : S → ℝ} {A : Set S} {C : ℝ}
    (hA : MeasurableSet A) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (x : S) (n : ℕ) : Integrable (stopped f A n) (pathMeasure K x) := by
  refine (integrable_const C).mono'
    (((stronglyAdapted_stopped hA hf n).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).le n)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (stopped_pred (fun r => 0 ≤ r) hf0 n ω)]
  exact stopped_pred (fun r => r ≤ C) hfC n ω

private lemma integral_stopped_succ_le {f : S → ℝ} {A : Set S}
    (hA : MeasurableSet A) (hf : Measurable f)
    (hdrift : ∀ y, y ∉ A → ∫ z, f z ∂K y ≤ f y) (n : ℕ) (ω : ℕ → S) :
    ∫ y, stopped f A (n + 1) y
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)
      ≤ stopped f A n ω := by
  have hmeas : AEStronglyMeasurable (stopped f A (n + 1))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)) :=
    (((stronglyAdapted_stopped hA hf (n + 1)).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).le (n + 1)))).aestronglyMeasurable
  rw [Kernel.integral_traj _ hmeas]

  have hagree : ∀ y : ℕ → S, ∀ k ≤ n,
      updateFinset y (Iic n) (Preorder.frestrictLe n ω) k = ω k := fun y k hk => by
    rw [updateFinset_eq_of_le hk]; rfl
  by_cases hs : ω ∈ survive A n
  ·
    have hpatch : ∀ y : ℕ → S,
        stopped f A (n + 1) (updateFinset y (Iic n) (Preorder.frestrictLe n ω))
          = f (y (n + 1)) := fun y => by
      rw [stopped_succ_of_survive ((survive_congr (hagree y)).2 hs), updateFinset_eq_succ]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpatch y)]
    have hstep : ∫ y : ℕ → S, f (y (n + 1))
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)
        = ∫ z, f z ∂K (ω n) := by
      have hmapK := DFunLike.congr_fun
        (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := mchain K) (a := n))
        (Preorder.frestrictLe n ω)
      rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
      have hcoord : (mchain K n) (Preorder.frestrictLe n ω) = K (ω n) := by
        rw [mchain_apply]; rfl
      rw [← hcoord, ← hmapK,
        integral_map_of_stronglyMeasurable (measurable_pi_apply _) hf.stronglyMeasurable]
    rw [hstep, stopped_of_survive hs]
    exact hdrift (ω n) (hs n le_rfl)
  ·
    have hpatch : ∀ y : ℕ → S,
        stopped f A (n + 1) (updateFinset y (Iic n) (Preorder.frestrictLe n ω))
          = stopped f A n ω := fun y => by
      rw [stopped_succ_of_not_survive (fun h => hs ((survive_congr (hagree y)).1 h)),
        stopped_congr (fun k hk => hagree y k hk)]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpatch y),
      integral_const]
    simp [measureReal_def]

/-- If `f` is measurable, nonnegative, bounded by `C`, and has nonpositive
one-step drift under `K` outside `A` (`∫ z, f z ∂(K y) ≤ f y` for `y ∉ A`),
then the process `stopped f A` is a supermartingale with respect to the
canonical filtration of the path measure started at any `x`. -/
theorem supermartingale_stopped {f : S → ℝ} {A : Set S} {C : ℝ}
    (hA : MeasurableSet A) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hdrift : ∀ y, y ∉ A → ∫ z, f z ∂K y ≤ f y) (x : S) :
    Supermartingale (stopped f A) (Filtration.piLE (X := fun _ : ℕ => S))
      (pathMeasure K x) := by
  have hint : ∀ n, Integrable (stopped f A n) (pathMeasure K x) := fun n =>
    integrable_stopped_pathMeasure hA hf hf0 hfC x n
  refine supermartingale_nat (stronglyAdapted_stopped hA hf) hint (fun n => ?_)
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.zero_le n) (x₀ := fun _ => x) (hint (n + 1))
  exact hcond.trans_le
    (Filter.Eventually.of_forall fun ω => integral_stopped_succ_le hA hf hdrift n ω)

/-- Reachability bound: if additionally `1 ≤ f` on `A`, the probability that
the chain started at `x` ever visits `A` is at most `f x`. This is Ville's
inequality applied to the stopped supermartingale. -/
theorem measure_reach_le {f : S → ℝ} {A : Set S} {C : ℝ}
    (hA : MeasurableSet A) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hf1 : ∀ y ∈ A, 1 ≤ f y) (hdrift : ∀ y, y ∉ A → ∫ z, f z ∂K y ≤ f y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ A} ≤ ENNReal.ofReal (f x) := by
  have hbound := Qtsl.Ville.reach_avoid (X := fun n (ω : ℕ → S) => ω n) (B := A)
    (supermartingale_stopped hA hf hf0 hfC hdrift x)
    (fun n ω => stopped_pred (fun r => 0 ≤ r) hf0 n ω)
    (a := 1) (fun n ω hn => one_le_stopped hf1 n ω ⟨n, le_rfl, hn⟩)
  rw [ENNReal.ofReal_one, one_mul] at hbound
  refine hbound.trans (le_of_eq (congrArg ENNReal.ofReal ?_))

  have hmeas : AEStronglyMeasurable (stopped f A 0)
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
  unfold pathMeasure
  rw [Kernel.integral_traj _ hmeas]
  have hval : ∀ y : ℕ → S,
      stopped f A 0 (updateFinset y (Iic 0) (fun _ => x)) = f x := fun y => by
    rw [stopped_zero, updateFinset_eq_of_le le_rfl]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hval y), integral_const]
  simp [measureReal_def]

section Battery

variable {D Dbar U : Set S} {V : S → ℝ} {p thr : ℝ} {x : S}

/-- Soundness of the safety-battery certificate, fail-closed form: under the
side conditions — `p + thr ≤ 1`; the kernel keeps `D \ U` inside `Dbar` and
inside `D ∪ U`; `V` is integrable with nonpositive drift on `D \ U`, at least
`1` on the failure set `U ∩ Dbar`, nonnegative on `Dbar`; and the initial
state satisfies `x ∈ D` with `V x ≤ thr` — the chain started at `x` stays in
`D \ U` forever with probability at least `p`. -/
theorem sound_QSafetyBattery_failClosed
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV : Measurable V)
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hB12int : ∀ y ∈ D, y ∉ U → Integrable V (K y))
    (hB12 : ∀ y ∈ D, y ∉ U → ∫ z, V z ∂K y ≤ V y)
    (hB3 : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V y)
    (hB4 : ∀ y ∈ Dbar, 0 ≤ V y)
    (hx : x ∈ D) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∀ n, ω n ∈ D \ U} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]; exact zero_le

  set C : ℝ := max thr 1 with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  set A : Set S := U ∪ Dᶜ with hAdef
  have hAmeas : MeasurableSet A := hU.union hD.compl
  set g : S → ℝ := fun y => min (D.piecewise (fun z => max (V z) 0) (fun z => max (V z) 1) y) C
    with hg
  have hgmeas : Measurable g :=
    (Measurable.piecewise hD (hV.max measurable_const) (hV.max measurable_const)).min
      measurable_const
  have hg0 : ∀ y, 0 ≤ g y := by
    intro y
    refine le_min ?_ (le_trans zero_le_one hC1)
    by_cases hyD : y ∈ D
    · rw [Set.piecewise_eq_of_mem _ _ _ hyD]; exact le_max_right _ _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hyD]
      exact le_trans zero_le_one (le_max_right _ _)
  have hgC : ∀ y, g y ≤ C := fun y => min_le_right _ _
  have hg1 : ∀ y ∈ A, 1 ≤ g y := by
    intro y hy
    refine le_min ?_ hC1
    by_cases hyD : y ∈ D
    · have hyU : y ∈ U := hy.resolve_right (fun h => h hyD)
      rw [Set.piecewise_eq_of_mem _ _ _ hyD]
      exact le_trans (hB3 y hyU (hDsub hyD)) (le_max_left _ _)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hyD]; exact le_max_right _ _

  have hclamp : ∀ z ∈ Dbar ∩ (D ∪ U), g z = min (V z) C := by
    rintro z ⟨hzbar, hzDU⟩
    rcases hzDU with hzD | hzU
    · rw [hg]; dsimp only
      rw [Set.piecewise_eq_of_mem _ _ _ hzD, max_eq_left (hB4 z (hDsub hzD))]
    · by_cases hzD : z ∈ D
      · rw [hg]; dsimp only
        rw [Set.piecewise_eq_of_mem _ _ _ hzD, max_eq_left (hB4 z hzbar)]
      · rw [hg]; dsimp only
        rw [Set.piecewise_eq_of_notMem _ _ _ hzD, max_eq_left (hB3 z hzU hzbar)]

  have hgdrift : ∀ y, y ∉ A → ∫ z, g z ∂K y ≤ g y := by
    intro y hy
    have hyD : y ∈ D := not_not.1 fun h => hy (Or.inr h)
    have hyU : y ∉ U := fun h => hy (Or.inl h)
    have hae : ∀ᵐ z ∂K y, z ∈ Dbar ∩ (D ∪ U) := by
      have h1 : K y Dbarᶜ = 0 := by
        rw [prob_compl_eq_one_sub hDbar, hR3 y hyD hyU, tsub_self]
      have h2 : K y (D ∪ U)ᶜ = 0 := by
        rw [prob_compl_eq_one_sub (hD.union hU), hR4 y hyD hyU, tsub_self]
      have h3 : K y ((Dbar ∩ (D ∪ U))ᶜ) = 0 := by
        refine le_antisymm ?_ zero_le
        rw [Set.compl_inter]
        exact le_trans (measure_union_le _ _) (by rw [h1, h2, add_zero])
      rw [ae_iff]
      exact h3
    have hVint : Integrable V (K y) := hB12int y hyD hyU
    have hminint : Integrable (fun z => min (V z) C) (K y) := by
      refine (hVint.norm.add (integrable_const |C|)).mono'
        ((hV.min measurable_const).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rcases le_total (V z) C with h | h
      · rw [min_eq_left h]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [min_eq_right h]; exact le_add_of_nonneg_left (abs_nonneg _)
    have hgint : ∫ z, g z ∂K y = ∫ z, min (V z) C ∂K y :=
      integral_congr_ae (hae.mono fun z hz => hclamp z hz)
    have hgy : g y = min (V y) C := hclamp y ⟨hDsub hyD, Or.inl hyD⟩
    rw [hgint, hgy]
    refine le_min ?_ ?_
    · exact le_trans
        (integral_mono hminint hVint (fun z => min_le_left _ _))
        (hB12 y hyD hyU)
    · calc ∫ z, min (V z) C ∂K y ≤ ∫ _z, C ∂K y :=
            integral_mono hminint (integrable_const C) (fun z => min_le_right _ _)
        _ = C := by simp [measureReal_def]

  have hgx : g x = V x := by
    rw [hclamp x ⟨hDsub hx, Or.inl hx⟩, min_eq_left (hthr.trans (le_max_left _ _))]

  have hreach := measure_reach_le (K := K) hAmeas hgmeas hg0 hgC hg1 hgdrift x
  rw [hgx] at hreach
  have hthr0 : 0 ≤ thr := le_trans (hB4 x (hDsub hx)) hthr
  have hnever : {ω : ℕ → S | ∀ n, ω n ∈ D \ U} = {ω : ℕ → S | ∃ n, ω n ∈ A}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, hAdef]
    constructor
    · intro h n hn
      rcases hn with hn | hn
      · exact (h n).2 hn
      · exact hn (h n).1
    · intro h n
      exact ⟨not_not.1 fun hD' => h n (Or.inr hD'), fun hU' => h n (Or.inl hU')⟩
  have hreachMeas : MeasurableSet {ω : ℕ → S | ∃ n, ω n ∈ A} := by
    have h : {ω : ℕ → S | ∃ n, ω n ∈ A} = ⋃ n, (fun ω : ℕ → S => ω n) ⁻¹' A := by
      ext ω; simp
    rw [h]
    exact MeasurableSet.iUnion fun n => (measurable_pi_apply n) hAmeas
  rw [hnever, prob_compl_eq_one_sub hreachMeas]
  have h1 : pathMeasure K x {ω : ℕ → S | ∃ n, ω n ∈ A} ≤ ENNReal.ofReal thr :=
    hreach.trans (ENNReal.ofReal_le_ofReal hthr)
  refine le_trans ?_ (tsub_le_tsub_left h1 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add hthr0 hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Soundness of the safety-battery certificate against an abstract state
predicate `sat`: if every non-satisfying state lies in the failure set `U`,
the conclusion of `sound_QSafetyBattery_failClosed` strengthens to
"`sat` holds at every time with probability at least `p`". -/
theorem sound_QSafetyBattery {sat : S → Prop}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV : Measurable V)
    (hF : ∀ y, ¬ sat y → y ∈ U)
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hB12int : ∀ y ∈ D, y ∉ U → Integrable V (K y))
    (hB12 : ∀ y ∈ D, y ∉ U → ∫ z, V z ∂K y ≤ V y)
    (hB3 : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V y)
    (hB4 : ∀ y ∈ Dbar, 0 ≤ V y)
    (hx : x ∈ D) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∀ n, sat (ω n)} := by
  refine (sound_QSafetyBattery_failClosed hD hDbar hU hV hΘ hDsub hR3 hR4 hB12int hB12
    hB3 hB4 hx hthr).trans (measure_mono fun ω hω n => ?_)
  by_contra hns
  exact (hω n).2 (hF _ hns)

end Battery

section QDeadline

variable {D Dbar B : Set S} {V : S → ℝ} {β p thr : ℝ} {x : S}

private lemma integral_comp_coord_succ {g : S → ℝ} (hg : Measurable g) (n : ℕ)
    (u : Π _i : Iic n, S) :
    ∫ y, g (y (n + 1)) ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n u
      = ∫ z, g z ∂K (u ⟨n, mem_Iic.2 le_rfl⟩) := by
  have hmapK := DFunLike.congr_fun
    (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := mchain K) (a := n)) u
  rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
  rw [← mchain_apply, ← hmapK,
    integral_map_of_stronglyMeasurable (measurable_pi_apply _) hg.stronglyMeasurable]

private lemma condExp_comp_coord_succ {g : S → ℝ} {C : ℝ} (hg : Measurable g)
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

private lemma ae_coord_zero_mem {E : Set S} (hE : MeasurableSet E) (hxE : x ∈ E) :
    ∀ᵐ ω ∂pathMeasure K x, ω 0 ∈ E := by
  rw [ae_iff]
  have hmeas : MeasurableSet {ω : ℕ → S | ¬ ω 0 ∈ E} := by
    have h : {ω : ℕ → S | ¬ ω 0 ∈ E} = (fun ω : ℕ → S => ω 0) ⁻¹' Eᶜ := rfl
    rw [h]; exact (measurable_pi_apply 0) hE.compl
  rw [← lintegral_indicator_one hmeas]
  unfold pathMeasure
  rw [Kernel.lintegral_traj _ (measurable_one.indicator hmeas)]
  have hzero : ∀ y : ℕ → S,
      ({ω : ℕ → S | ¬ ω 0 ∈ E}).indicator (1 : (ℕ → S) → ℝ≥0∞)
        (updateFinset y (Iic 0) (fun _ : Iic 0 => x)) = 0 := fun y => by
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_setOf_eq, not_not]
    rw [updateFinset_eq_of_le le_rfl]
    exact hxE
  rw [lintegral_congr hzero, lintegral_zero]

private lemma ae_no_escape (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hR4 : ∀ y ∈ D, y ∉ B → K y (D ∪ B) = 1) (hx : x ∈ D) :
    pathMeasure K x (⋃ n, {ω : ℕ → S | (∀ k ≤ n, ω k ∉ B) ∧ ω n ∉ D}) = 0 := by
  refine measure_iUnion_null fun n => ?_
  induction n with
  | zero =>
    have h0 := ae_coord_zero_mem (K := K) hD hx
    rw [ae_iff] at h0
    exact measure_mono_null (fun ω hω => hω.2) h0
  | succ n ih =>
    have hsub : {ω : ℕ → S | (∀ k ≤ n + 1, ω k ∉ B) ∧ ω (n + 1) ∉ D}
        ⊆ {ω : ℕ → S | (∀ k ≤ n, ω k ∉ B) ∧ ω n ∉ D}
          ∪ {ω : ℕ → S | (∀ i : Iic n, ω i ∉ B) ∧ ω n ∈ D ∧ ω (n + 1) ∉ D ∪ B} := by
      rintro ω ⟨hmiss, hesc⟩
      by_cases hn : ω n ∈ D
      · refine Or.inr ⟨fun i => hmiss i ((mem_Iic.1 i.2).trans n.le_succ), hn, ?_⟩
        rintro (h | h)
        · exact hesc h
        · exact hmiss (n + 1) le_rfl h
      · exact Or.inl ⟨fun k hk => hmiss k (hk.trans n.le_succ), hn⟩
    refine measure_mono_null hsub (measure_union_null ih ?_)

    have hpair : Measurable (fun ω : ℕ → S => (Preorder.frestrictLe n ω, ω (n + 1))) :=
      (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
    set Cn : Set (Π _i : Iic n, S) :=
      {u | (∀ i : Iic n, u i ∉ B) ∧ u ⟨n, mem_Iic.2 le_rfl⟩ ∈ D} with hCn
    have hCnMeas : MeasurableSet Cn := by
      have h : Cn = (⋂ i : Iic n, (fun u : Π _i : Iic n, S => u i) ⁻¹' Bᶜ)
          ∩ (fun u : Π _i : Iic n, S => u ⟨n, mem_Iic.2 le_rfl⟩) ⁻¹' D := by
        ext u; simp [hCn, Set.mem_iInter]
      rw [h]
      exact (MeasurableSet.iInter fun i => (measurable_pi_apply i) hB.compl).inter
        ((measurable_pi_apply _) hD)
    have hset : {ω : ℕ → S | (∀ i : Iic n, ω i ∉ B) ∧ ω n ∈ D ∧ ω (n + 1) ∉ D ∪ B}
        = (fun ω : ℕ → S => (Preorder.frestrictLe n ω, ω (n + 1)))
            ⁻¹' (Cn ×ˢ (D ∪ B)ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, hCn,
        Set.mem_compl_iff]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
    have hmap := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ : ℕ => S)
      (κ := mchain K) (Nat.zero_le n) (x₀ := fun _ => x)
    rw [hset,
      show pathMeasure K x
        = Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x) from rfl,
      ← Measure.map_apply hpair (hCnMeas.prod (hD.union hB).compl), ← hmap,
      Measure.compProd_apply (hCnMeas.prod (hD.union hB).compl)]
    refine le_antisymm
      (le_trans (le_of_eq (lintegral_congr fun u => ?_)) lintegral_zero.le) zero_le
    by_cases hu : u ∈ Cn
    · have hsec : Prod.mk u ⁻¹' (Cn ×ˢ (D ∪ B)ᶜ) = (D ∪ B)ᶜ := by
        ext z; simp [hu]
      rw [hsec, mchain_apply, prob_compl_eq_one_sub (hD.union hB),
        hR4 _ hu.2 (hu.1 ⟨n, mem_Iic.2 le_rfl⟩), tsub_self]
    · have hsec : Prod.mk u ⁻¹' (Cn ×ˢ (D ∪ B)ᶜ) = ∅ := by
        ext z; simp [hu]
      rw [hsec]
      exact measure_empty

/-- Soundness of the deadline certificate, hitting form: if `V` decays
geometrically with rate `β` under the kernel on `D \ B`, is at least `1` on
`Dbar \ B`, is bounded by `M` on `Dbar`, the kernel keeps `D \ B` inside
`Dbar` and inside `D ∪ B`, and `β ^ T * thr ≤ 1 - p` with `V x ≤ thr`, then
the chain started at `x ∈ D` visits `B` within `T` steps with probability at
least `p`. The proof combines the geometric deadline tail bound with the
almost-sure impossibility of escaping `D` before reaching `B`. -/
theorem sound_QDeadline_hit {T : ℕ} {M : ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hB : MeasurableSet B)
    (hV : Measurable V)
    (hβ : 0 ≤ β)
    (hΘF : β ^ T * thr ≤ 1 - p)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ B → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ B → K y (D ∪ B) = 1)
    (hint : ∀ y ∈ D, y ∉ B → Integrable V (K y))
    (hdecay : ∀ y ∈ D, y ∉ B → ∫ z, V z ∂K y ≤ β * V y)
    (hfloor : ∀ y ∈ Dbar, y ∉ B → 1 ≤ V y)
    (hnonneg : ∀ y ∈ Dbar, 0 ≤ V y)
    (hM : ∀ y ∈ Dbar, V y ≤ M)
    (hx : x ∈ D) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∃ k ≤ T, ω k ∈ B} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]; exact zero_le
  have hthr0 : 0 ≤ thr := le_trans (hnonneg x (hDsub hx)) hthr
  have h1p : 0 ≤ 1 - p := le_trans (mul_nonneg (pow_nonneg hβ T) hthr0) hΘF
  by_cases hxB : x ∈ B
  ·
    have h0 := ae_coord_zero_mem (K := K) hB hxB
    have hnull : pathMeasure K x {ω : ℕ → S | ¬ ω 0 ∈ B} = 0 := by
      rw [ae_iff] at h0; exact h0
    have hsub : {ω : ℕ → S | ω 0 ∈ B} ⊆ {ω : ℕ → S | ∃ k ≤ T, ω k ∈ B} :=
      fun ω h => ⟨0, T.zero_le, h⟩
    refine le_trans ?_ (measure_mono hsub)
    have hcompl : {ω : ℕ → S | ω 0 ∈ B} = {ω : ℕ → S | ¬ ω 0 ∈ B}ᶜ := by ext; simp
    have hset0 : MeasurableSet {ω : ℕ → S | ¬ ω 0 ∈ B} := by
      have h : {ω : ℕ → S | ¬ ω 0 ∈ B} = (fun ω : ℕ → S => ω 0) ⁻¹' Bᶜ := rfl
      rw [h]; exact (measurable_pi_apply 0) hB.compl
    rw [hcompl, prob_compl_eq_one_sub hset0, hnull,
      tsub_zero]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith))
      (le_of_eq ENNReal.ofReal_one)

  set C : ℝ := max M 1 with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  set B' : Set S := B ∪ Dᶜ with hB'def
  have hB'meas : MeasurableSet B' := hB.union hD.compl
  set g : S → ℝ :=
    fun y => min ((D \ B).piecewise (fun z => max (V z) 1) (fun z => max (V z) 0) y) C
    with hg
  have hgmeas : Measurable g :=
    (Measurable.piecewise (hD.diff hB) (hV.max measurable_const)
      (hV.max measurable_const)).min measurable_const
  have hg0 : ∀ y, 0 ≤ g y := by
    intro y
    refine le_min ?_ (le_trans zero_le_one hC1)
    by_cases hy : y ∈ D \ B
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      exact le_trans zero_le_one (le_max_right _ _)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]; exact le_max_right _ _
  have hgC : ∀ y, g y ≤ C := fun y => min_le_right _ _
  have hg1 : ∀ y, y ∉ B' → 1 ≤ g y := by
    intro y hy
    have hyDB : y ∈ D \ B :=
      ⟨not_not.1 fun h => hy (Or.inr h), fun h => hy (Or.inl h)⟩
    refine le_min ?_ hC1
    rw [Set.piecewise_eq_of_mem _ _ _ hyDB]; exact le_max_right _ _

  have hclamp : ∀ z ∈ Dbar ∩ (D ∪ B), g z = min (V z) C := by
    rintro z ⟨hzbar, hzDB⟩
    by_cases hz : z ∈ D \ B
    · rw [hg]; dsimp only
      rw [Set.piecewise_eq_of_mem _ _ _ hz, max_eq_left (hfloor z hzbar hz.2)]
    · have hzB : z ∈ B := by
        rcases hzDB with hzD | hzB
        · exact not_not.1 fun hzB => hz ⟨hzD, hzB⟩
        · exact hzB
      rw [hg]; dsimp only
      rw [Set.piecewise_eq_of_notMem _ _ _ hz, max_eq_left (hnonneg z hzbar)]
  have hgV : ∀ y ∈ D, y ∉ B → g y = V y := by
    intro y hyD hyB
    rw [hclamp y ⟨hDsub hyD, Or.inl hyD⟩,
      min_eq_left (le_trans (hM y (hDsub hyD)) (le_max_left _ _))]

  have hgdecay : ∀ y, y ∉ B' → ∫ z, g z ∂K y ≤ β * g y := by
    intro y hy
    have hyD : y ∈ D := not_not.1 fun h => hy (Or.inr h)
    have hyB : y ∉ B := fun h => hy (Or.inl h)
    have hae : ∀ᵐ z ∂K y, z ∈ Dbar ∩ (D ∪ B) := by
      have h1 : K y Dbarᶜ = 0 := by
        rw [prob_compl_eq_one_sub hDbar, hR3 y hyD hyB, tsub_self]
      have h2 : K y (D ∪ B)ᶜ = 0 := by
        rw [prob_compl_eq_one_sub (hD.union hB), hR4 y hyD hyB, tsub_self]
      have h3 : K y ((Dbar ∩ (D ∪ B))ᶜ) = 0 := by
        refine le_antisymm ?_ zero_le
        rw [Set.compl_inter]
        exact le_trans (measure_union_le _ _) (by rw [h1, h2, add_zero])
      rw [ae_iff]
      exact h3
    have hVint : Integrable V (K y) := hint y hyD hyB
    have hminint : Integrable (fun z => min (V z) C) (K y) := by
      refine (hVint.norm.add (integrable_const |C|)).mono'
        ((hV.min measurable_const).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rcases le_total (V z) C with h | h
      · rw [min_eq_left h]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [min_eq_right h]; exact le_add_of_nonneg_left (abs_nonneg _)
    rw [integral_congr_ae (hae.mono fun z hz => hclamp z hz), hgV y hyD hyB]
    exact le_trans (integral_mono hminint hVint fun z => min_le_left _ _)
      (hdecay y hyD hyB)

  have hmB' : ∀ n, MeasurableSet[(Filtration.piLE (X := fun _ : ℕ => S)) n]
      {ω : ℕ → S | ω n ∈ B'} := fun n => (measurable_coord_piLE le_rfl) hB'meas
  have hVint' : ∀ n, Integrable (fun ω : ℕ → S => g (ω n)) (pathMeasure K x) := by
    intro n
    refine (integrable_const C).mono'
      ((hgmeas.comp (measurable_pi_apply n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
    exact hgC _
  have hdrift' : ∀ n, ∀ᵐ ω ∂pathMeasure K x, ω n ∉ B' →
      ((pathMeasure K x)[fun ω : ℕ → S => g (ω (n + 1)) |
        Filtration.piLE (X := fun _ : ℕ => S) n]) ω ≤ β * g (ω n) := by
    intro n
    filter_upwards [condExp_comp_coord_succ (K := K) hgmeas hg0 hgC x n] with ω hω hmem
    rw [hω]
    exact hgdecay (ω n) hmem
  have htail := Qtsl.Deadline.deadline_tail (μ := pathMeasure K x)
    (𝒢 := Filtration.piLE (X := fun _ : ℕ => S)) (X := fun n (ω : ℕ → S) => ω n)
    (B := B') (V := fun n (ω : ℕ → S) => g (ω n)) (a := 1)
    hβ hVint' (fun n ω => hg0 _) hmB' hdrift' (fun n ω hω => hg1 _ hω) T

  have hinit : ∫ ω, g (ω 0) ∂pathMeasure K x = g x := by
    have hmeas0 : AEStronglyMeasurable (fun ω : ℕ → S => g (ω 0))
        (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
      (hgmeas.comp (measurable_pi_apply 0)).aestronglyMeasurable
    unfold pathMeasure
    rw [Kernel.integral_traj _ hmeas0]
    have hval : ∀ y : ℕ → S,
        g ((updateFinset y (Iic 0) (fun _ : Iic 0 => x)) 0) = g x := fun y => by
      rw [updateFinset_eq_of_le le_rfl]
    rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const]
    simp [measureReal_def]
  rw [ENNReal.ofReal_one, one_mul, hinit, hgV x hx hxB] at htail

  have hescape := ae_no_escape (K := K) hD hB hR4 hx
  have hmiss_sub : {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
      ⊆ {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B'}
        ∪ (⋃ n, {ω : ℕ → S | (∀ k ≤ n, ω k ∉ B) ∧ ω n ∉ D}) := by
    intro ω hω
    by_cases hin : ∀ k ≤ T, ω k ∈ D
    · refine Or.inl fun k hk => ?_
      rintro (h | h)
      · exact hω k hk h
      · exact h (hin k hk)
    · push Not at hin
      obtain ⟨k, hkT, hkD⟩ := hin
      exact Or.inr (Set.mem_iUnion.2 ⟨k, fun j hj => hω j (hj.trans hkT), hkD⟩)
  have hmiss : pathMeasure K x {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
      ≤ ENNReal.ofReal (β ^ T * V x) := by
    refine le_trans (measure_mono hmiss_sub)
      (le_trans (measure_union_le _ _) ?_)
    rw [hescape, add_zero]
    exact htail

  have hmissMeas : MeasurableSet {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B} := by
    have h : {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
        = ⋂ k, ⋂ (_ : k ≤ T), (fun ω : ℕ → S => ω k) ⁻¹' Bᶜ := by
      ext ω; simp
    rw [h]
    exact .iInter fun k => .iInter fun hk => (measurable_pi_apply k) hB.compl
  have hcompl : {ω : ℕ → S | ∃ k ≤ T, ω k ∈ B}
      = {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}ᶜ := by
    ext ω; simp
  rw [hcompl, prob_compl_eq_one_sub hmissMeas]
  have hchain : pathMeasure K x {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
      ≤ ENNReal.ofReal (1 - p) :=
    hmiss.trans (ENNReal.ofReal_le_ofReal
      (le_trans (mul_le_mul_of_nonneg_left hthr (pow_nonneg hβ T)) hΘF))
  refine le_trans ?_ (tsub_le_tsub_left hchain 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add h1p hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Soundness of the deadline certificate against an abstract state predicate
`sat`: if every state of `B` satisfies `sat`, the chain started at `x`
reaches a satisfying state within `T` steps with probability at least `p`. -/
theorem sound_QDeadline {T : ℕ} {M : ℝ} {sat : S → Prop}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hB : MeasurableSet B)
    (hV : Measurable V)
    (hF : ∀ y ∈ B, sat y)
    (hβ : 0 ≤ β)
    (hΘF : β ^ T * thr ≤ 1 - p)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ B → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ B → K y (D ∪ B) = 1)
    (hint : ∀ y ∈ D, y ∉ B → Integrable V (K y))
    (hdecay : ∀ y ∈ D, y ∉ B → ∫ z, V z ∂K y ≤ β * V y)
    (hfloor : ∀ y ∈ Dbar, y ∉ B → 1 ≤ V y)
    (hnonneg : ∀ y ∈ Dbar, 0 ≤ V y)
    (hM : ∀ y ∈ Dbar, V y ≤ M)
    (hx : x ∈ D) (hthr : V x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∃ k ≤ T, sat (ω k)} := by
  refine (sound_QDeadline_hit hD hDbar hB hV hβ hΘF hDsub hR3 hR4 hint hdecay hfloor
    hnonneg hM hx hthr).trans (measure_mono ?_)
  rintro ω ⟨k, hk, hkB⟩
  exact ⟨k, hk, hF _ hkB⟩

end QDeadline

end WithMeasurable

end Qtsl.Battery
