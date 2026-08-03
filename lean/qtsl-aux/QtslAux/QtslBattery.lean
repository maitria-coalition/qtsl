import QtslAux.Battery

/-! # Composite soundness theorems for bounded-horizon temporal operators

This module assembles the base supermartingale bounds into composite
("battery") soundness theorems for until- and deadline-shaped temporal
properties of a Markov kernel `K`, evaluated on the path measure from an
initial state.

Principal declarations:

* `sound_QUnionBound`, `sound_QUnionBound_ofReal`: the union bound
  `μ F ≤ a + b` for `F ⊆ E₁ ∪ E₂`.
* `compl_firstExit_subset`: the failure event of a bounded-horizon first-exit
  property is covered by "first exit lands outside the target" and "no exit by
  the deadline".
* `measure_firstBad_le`: a Ville-type first-passage bound — a bounded
  nonnegative function `f` with supermartingale drift off a stopping set,
  and `f ≥ 1` on the bad set, bounds by `f x` the probability of reaching
  the bad set before the stopping set.
* `measure_missTarget_le`: a geometric deadline bound — a `β`-decaying
  certificate `V` bounds by `β ^ T * V x` the probability of avoiding the
  target set `B` for `T` steps while confined.
* `sound_QUntilBattery_firstHit` and `sound_QUntilBattery`: soundness of the
  until battery. An avoidance supermartingale `Va` (barring the avoid set
  `A`) and a `β`-decaying deadline certificate `Vd` (forcing arrival in
  `A ∪ R`) combine, via the union bound over `compl_firstExit_subset`, into
  the lower bound `p ≤ P(reach R within T steps, avoiding A before that)`
  whenever `Va x + c * Vd x ≤ 1 - p` with `β ^ T ≤ c`.
* `sound_QDeadlineBattery`: the deadline battery with the exponential
  threshold discharged arithmetically: from `β ≤ exp (-θ)` and a rational
  Taylor lower bound `q ≤ ∑ (θT)ᵏ/k!` one gets `β ^ T * q ≤ 1`, so
  `V x ≤ (1 - p) * q` suffices for `p ≤ P(hit within T)`.
* `sound_QSafetyBattery_staged`: the safety battery for staged (multi-mode)
  systems on `Md × X`. Each step of the kernel is a mixture of a within-mode
  flow and finitely many guarded jumps `g j` between modes
  (`mixture_integrable`, `mixture_drift`); a per-mode certificate family
  `V m` that drifts down along flows and does not increase across enabled
  jumps yields `p ≤ P(always sat)` from `V m z ≤ thr` at the initial point.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function

namespace Qtsl.Battery

/-- Union bound: if `F ⊆ E₁ ∪ E₂` with `μ E₁ ≤ a` and `μ E₂ ≤ b`, then
`μ F ≤ a + b`. -/
theorem sound_QUnionBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E₁ E₂ F : Set Ω} {a b : ℝ≥0∞}
    (h₁ : μ E₁ ≤ a) (h₂ : μ E₂ ≤ b) (hsub : F ⊆ E₁ ∪ E₂) :
    μ F ≤ a + b :=
  (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h₁ h₂))

/-- The union bound with real-valued budgets: nonnegative real bounds `a, b`
combine to the bound `ENNReal.ofReal (a + b)`. -/
theorem sound_QUnionBound_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E₁ E₂ F : Set Ω} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a) (h₂ : μ E₂ ≤ ENNReal.ofReal b)
    (hsub : F ⊆ E₁ ∪ E₂) :
    μ F ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact sound_QUnionBound μ h₁ h₂ hsub

/-- Failure-event cover for bounded-horizon first exit: a path that does not
reach `Good` by time `T` before touching `Stop` either makes its first entry
into `Stop` outside `Good`, or avoids `Stop` entirely through time `T`. This
is the case split fed to the union bound in the until battery. -/
theorem compl_firstExit_subset {S : Type*} (Stop Good : Set S) (T : ℕ) :
    {ω : ℕ → S | ∃ n ≤ T, ω n ∈ Good ∧ ∀ j < n, ω j ∉ Stop}ᶜ ⊆
      {ω : ℕ → S | ∃ n, ω n ∈ Stop \ Good ∧ ∀ j < n, ω j ∉ Stop} ∪
        {ω : ℕ → S | ∀ k ≤ T, ω k ∉ Stop} := by
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and] at hω
  by_cases hmiss : ∀ k ≤ T, ω k ∉ Stop
  · exact Or.inr hmiss
  · push Not at hmiss
    obtain ⟨k, hkT, hk⟩ := hmiss
    have hex : ∃ n, ω n ∈ Stop := ⟨k, hk⟩
    refine Or.inl ⟨Nat.find hex, ⟨Nat.find_spec hex, fun hgood => ?_⟩,
      fun j hj => Nat.find_min hex hj⟩
    exact hω (Nat.find hex) (le_trans (Nat.find_min' hex hk) hkT) hgood
      fun j hj => Nat.find_min hex hj

private lemma updateFinset_zero {S : Type*} {y : ℕ → S} {x : S} :
    updateFinset y (Iic 0) (fun _ : Iic 0 => x) 0 = x := by
  simp [updateFinset, mem_Iic]

variable {S : Type*} [MeasurableSpace S]

private lemma integral_stopped_zero {K : Kernel S S} [IsMarkovKernel K]
    {f : S → ℝ} {A : Set S} (hf : Measurable f) (x : S) :
    ∫ ω, stopped f A 0 ω ∂pathMeasure K x = f x := by
  have hmeas : AEStronglyMeasurable (stopped f A 0)
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) 0 (fun _ => x)) :=
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
  unfold pathMeasure
  rw [Kernel.integral_traj _ hmeas]
  have hval : ∀ y : ℕ → S,
      stopped f A 0 (updateFinset y (Iic 0) (fun _ : Iic 0 => x)) = f x := fun y => by
    rw [stopped_zero, updateFinset_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const]
  simp [measureReal_def]

/-- First-passage bound: for a bounded nonnegative `f` with supermartingale
drift off the stopping set `Stop` and `f ≥ 1` on `Bad`, the probability of
visiting `Bad` before ever touching `Stop` is at most `ENNReal.ofReal (f x)`.
Proved by Ville's maximal inequality for the `Stop`-stopped supermartingale. -/
theorem measure_firstBad_le {K : Kernel S S} [IsMarkovKernel K]
    {f : S → ℝ} {Stop Bad : Set S} {C : ℝ}
    (hStop : MeasurableSet Stop) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hf1 : ∀ y ∈ Bad, 1 ≤ f y)
    (hdrift : ∀ y, y ∉ Stop → ∫ z, f z ∂K y ≤ f y) (x : S) :
    pathMeasure K x {ω | ∃ n, ω n ∈ Bad ∧ ∀ j < n, ω j ∉ Stop}
      ≤ ENNReal.ofReal (f x) := by
  have hsub : {ω : ℕ → S | ∃ n, ω n ∈ Bad ∧ ∀ j < n, ω j ∉ Stop}
      ⊆ {ω : ℕ → S | ∃ n, (((1 : ℝ≥0) : ℝ)) ≤ stopped f Stop n ω} := by
    rintro ω ⟨n, hnB, hmin⟩
    refine ⟨n, ?_⟩
    have h1 : 1 ≤ stopped f Stop n ω := by
      cases n with
      | zero => rw [stopped_zero]; exact hf1 _ hnB
      | succ m =>
        have hsurv : ω ∈ survive Stop m := fun k hk => hmin k (Nat.lt_succ_of_le hk)
        rw [stopped_succ_of_survive hsurv]
        exact hf1 _ hnB
    simpa using h1
  have hsup := supermartingale_stopped (K := K) hStop hf hf0 hfC hdrift x
  have hville := hsup.ville_ineq
    (fun n ω => stopped_pred (fun r => 0 ≤ r) hf0 n ω) 1
  rw [ENNReal.coe_one, one_mul] at hville
  refine (measure_mono hsub).trans
    (hville.trans (le_of_eq (congrArg ENNReal.ofReal ?_)))
  exact integral_stopped_zero hf x

/-- Deadline-miss bound: for a confined chain (`D`, `Dbar`, boundary
conditions `hR3`/`hR4`) and a certificate `V` with geometric decay
`∫ V dK y ≤ β * V y` off the target set `B` and floor `1` off `B`, the
probability of avoiding `B` through time `T` is at most
`ENNReal.ofReal (β ^ T * V x)` — the complement of the deadline-hit bound. -/
theorem measure_missTarget_le {K : Kernel S S} [IsMarkovKernel K]
    {D Dbar B : Set S} {V : S → ℝ} {β : ℝ} {x : S} {T : ℕ} {M : ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hB : MeasurableSet B)
    (hV : Measurable V) (hβ : 0 ≤ β)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ B → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ B → K y (D ∪ B) = 1)
    (hint : ∀ y ∈ D, y ∉ B → Integrable V (K y))
    (hdecay : ∀ y ∈ D, y ∉ B → ∫ z, V z ∂K y ≤ β * V y)
    (hfloor : ∀ y ∈ Dbar, y ∉ B → 1 ≤ V y)
    (hnonneg : ∀ y ∈ Dbar, 0 ≤ V y)
    (hM : ∀ y ∈ Dbar, V y ≤ M)
    (hx : x ∈ D) :
    pathMeasure K x {ω | ∀ k ≤ T, ω k ∉ B} ≤ ENNReal.ofReal (β ^ T * V x) := by
  set c : ℝ := β ^ T * V x with hc
  have hc0 : 0 ≤ c := mul_nonneg (pow_nonneg hβ T) (hnonneg x (hDsub hx))
  have hhit := sound_QDeadline_hit (K := K) (p := 1 - c) (thr := V x) (T := T) (M := M)
    hD hDbar hB hV hβ (le_of_eq (by rw [hc]; ring)) hDsub hR3 hR4 hint hdecay
    hfloor hnonneg hM hx le_rfl
  have hmissMeas : MeasurableSet {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B} := by
    have h : {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
        = ⋂ k, ⋂ (_ : k ≤ T), (fun ω : ℕ → S => ω k) ⁻¹' Bᶜ := by
      ext ω; simp
    rw [h]
    exact .iInter fun k => .iInter fun _ => (measurable_pi_apply k) hB.compl
  have hcompl : {ω : ℕ → S | ∃ k ≤ T, ω k ∈ B}
      = {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}ᶜ := by
    ext ω; simp
  rw [hcompl, prob_compl_eq_one_sub hmissMeas] at hhit
  rcases le_total c 1 with hcase | hcase
  ·
    have hadd : ENNReal.ofReal (1 - c) + pathMeasure K x {ω : ℕ → S | ∀ k ≤ T, ω k ∉ B}
        ≤ 1 :=
      le_trans (add_le_add hhit le_rfl)
        (le_of_eq (tsub_add_cancel_of_le prob_le_one))
    have h1c : ENNReal.ofReal c = 1 - ENNReal.ofReal (1 - c) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 1 - c)]
      congr 1
      ring
    rw [h1c]
    exact ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hadd
  ·
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hcase

section QUntil

variable {K : Kernel S S} [IsMarkovKernel K]
  {D Dbar A R : Set S} {Va Vd : S → ℝ} {β p c M : ℝ} {x : S} {T : ℕ}

/-- The until battery, first-hit form. Two certificates combine: an avoidance
supermartingale `Va` (nonnegative on `Dbar`, floor `1` on the avoid set `A`,
drift down off `A ∪ R`) and a deadline certificate `Vd` (geometric decay
factor `β`, floor `1` while neither `A` nor `R` is reached, cap `M`). If
`β ^ T ≤ c` and `Va x + c * Vd x ≤ 1 - p`, then with probability at least
`p` the chain reaches the target `R` within `T` steps with its first exit
from confinement, having touched neither `A` nor `R` nor left `D` before.
The failure event is covered by `compl_firstExit_subset` and priced by
`measure_firstBad_le` (exit lands badly: ≤ `Va x`) plus `measure_missTarget_le`
(no exit by `T`: ≤ `β ^ T * Vd x ≤ c * Vd x`), via the union bound. The
technical clamp `ga` extends `Va` off the confined region without disturbing
either bound. -/
theorem sound_QUntilBattery_firstHit
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar)
    (hA : MeasurableSet A) (hR : MeasurableSet R)
    (hVa : Measurable Va) (hVd : Measurable Vd)
    (hβ : 0 ≤ β) (hc : β ^ T ≤ c)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ A ∪ R → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ A ∪ R → K y (D ∪ (A ∪ R)) = 1)
    (hVaint : ∀ y ∈ D, y ∉ A ∪ R → Integrable Va (K y))
    (hVadrift : ∀ y ∈ D, y ∉ A ∪ R → ∫ z, Va z ∂K y ≤ Va y)
    (hVafloor : ∀ y ∈ A, y ∈ Dbar → 1 ≤ Va y)
    (hVanonneg : ∀ y ∈ Dbar, 0 ≤ Va y)
    (hVdint : ∀ y ∈ D, y ∉ A ∪ R → Integrable Vd (K y))
    (hVddecay : ∀ y ∈ D, y ∉ A ∪ R → ∫ z, Vd z ∂K y ≤ β * Vd y)
    (hVdfloor : ∀ y ∈ Dbar, y ∉ A ∪ R → 1 ≤ Vd y)
    (hVdnonneg : ∀ y ∈ Dbar, 0 ≤ Vd y)
    (hVdM : ∀ y ∈ Dbar, Vd y ≤ M)
    (hx : x ∈ D) (hthr : Va x + c * Vd x ≤ 1 - p) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ (A ∪ R) ∪ Dᶜ} := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp]; exact zero_le
  have hVax0 : 0 ≤ Va x := hVanonneg x (hDsub hx)
  have hVdx0 : 0 ≤ Vd x := hVdnonneg x (hDsub hx)
  have hc0 : 0 ≤ c := le_trans (pow_nonneg hβ T) hc
  have h1p : 0 ≤ 1 - p :=
    le_trans (add_nonneg hVax0 (mul_nonneg hc0 hVdx0)) hthr
  set Stp : Set S := (A ∪ R) ∪ Dᶜ with hStp
  have hStpMeas : MeasurableSet Stp := (hA.union hR).union hD.compl

  set Ca : ℝ := max (1 - p) 1 with hCa
  have hCa1 : (1 : ℝ) ≤ Ca := le_max_right _ _
  set ga : S → ℝ := fun y =>
    min ((D ∪ R).piecewise (fun z => max (Va z) 0) (fun z => max (Va z) 1) y) Ca
    with hga
  have hgaMeas : Measurable ga :=
    (Measurable.piecewise (hD.union hR) (hVa.max measurable_const)
      (hVa.max measurable_const)).min measurable_const
  have hga0 : ∀ y, 0 ≤ ga y := by
    intro y
    refine le_min ?_ (le_trans zero_le_one hCa1)
    by_cases hy : y ∈ D ∪ R
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]; exact le_max_right _ _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      exact le_trans zero_le_one (le_max_right _ _)
  have hgaC : ∀ y, ga y ≤ Ca := fun y => min_le_right _ _

  have hga1 : ∀ y ∈ Stp \ R, 1 ≤ ga y := by
    rintro y ⟨hyStp, hyR⟩
    refine le_min ?_ hCa1
    by_cases hyD : y ∈ D
    · have hyA : y ∈ A := by
        rcases hyStp with h | h
        · exact h.resolve_right fun h' => hyR h'
        · exact absurd hyD h
      rw [Set.piecewise_eq_of_mem _ _ _ (Set.mem_union_left R hyD)]
      exact le_trans (hVafloor y hyA (hDsub hyD)) (le_max_left _ _)
    · rw [Set.piecewise_eq_of_notMem _ _ _
        (fun h => h.elim (fun h' => hyD h') fun h' => hyR h')]
      exact le_max_right _ _

  have hclamp : ∀ z ∈ Dbar ∩ (D ∪ (A ∪ R)), ga z = min (Va z) Ca := by
    rintro z ⟨hzbar, hzDU⟩
    by_cases hzDR : z ∈ D ∪ R
    · rw [hga]; dsimp only
      rw [Set.piecewise_eq_of_mem _ _ _ hzDR, max_eq_left (hVanonneg z hzbar)]
    · have hzA : z ∈ A := by
        rcases hzDU with h | h
        · exact absurd (Or.inl h) hzDR
        · exact h.resolve_right fun h' => hzDR (Or.inr h')
      rw [hga]; dsimp only
      rw [Set.piecewise_eq_of_notMem _ _ _ hzDR,
        max_eq_left (hVafloor z hzA hzbar)]

  have hgadrift : ∀ y, y ∉ Stp → ∫ z, ga z ∂K y ≤ ga y := by
    intro y hy
    have hyD : y ∈ D := not_not.1 fun h => hy (Or.inr h)
    have hyAR : y ∉ A ∪ R := fun h => hy (Or.inl h)
    have hae : ∀ᵐ z ∂K y, z ∈ Dbar ∩ (D ∪ (A ∪ R)) := by
      have h1 : K y Dbarᶜ = 0 := by
        rw [prob_compl_eq_one_sub hDbar, hR3 y hyD hyAR, tsub_self]
      have h2 : K y (D ∪ (A ∪ R))ᶜ = 0 := by
        rw [prob_compl_eq_one_sub (hD.union (hA.union hR)), hR4 y hyD hyAR,
          tsub_self]
      have h3 : K y ((Dbar ∩ (D ∪ (A ∪ R)))ᶜ) = 0 := by
        refine le_antisymm ?_ zero_le
        rw [Set.compl_inter]
        exact le_trans (measure_union_le _ _) (by rw [h1, h2, add_zero])
      rw [ae_iff]
      exact h3
    have hVint : Integrable Va (K y) := hVaint y hyD hyAR
    have hminint : Integrable (fun z => min (Va z) Ca) (K y) := by
      refine (hVint.norm.add (integrable_const |Ca|)).mono'
        ((hVa.min measurable_const).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rcases le_total (Va z) Ca with h | h
      · rw [min_eq_left h]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [min_eq_right h]; exact le_add_of_nonneg_left (abs_nonneg _)
    have hgy : ga y = min (Va y) Ca := hclamp y ⟨hDsub hyD, Or.inl hyD⟩
    rw [integral_congr_ae (hae.mono fun z hz => hclamp z hz), hgy]
    refine le_min ?_ ?_
    · exact le_trans
        (integral_mono hminint hVint fun z => min_le_left _ _)
        (hVadrift y hyD hyAR)
    · calc ∫ z, min (Va z) Ca ∂K y ≤ ∫ _z, Ca ∂K y :=
            integral_mono hminint (integrable_const Ca) fun z => min_le_right _ _
        _ = Ca := by simp [measureReal_def]

  have hgax : ga x = Va x := by
    rw [hclamp x ⟨hDsub hx, Or.inl hx⟩]
    exact min_eq_left (le_trans
      (le_trans (le_add_of_nonneg_right (mul_nonneg hc0 hVdx0)) hthr)
      (le_max_left _ _))

  have hE1 := measure_firstBad_le (K := K) hStpMeas hgaMeas hga0 hgaC hga1 hgadrift x
  rw [hgax] at hE1

  have hE2' := measure_missTarget_le (K := K) (B := A ∪ R) (T := T) (M := M)
    hD hDbar (hA.union hR) hVd hβ hDsub hR3 hR4 hVdint hVddecay hVdfloor
    hVdnonneg hVdM hx
  have hE2 : pathMeasure K x {ω : ℕ → S | ∀ k ≤ T, ω k ∉ Stp}
      ≤ ENNReal.ofReal (β ^ T * Vd x) :=
    le_trans (measure_mono fun ω hω k hk h => hω k hk (Or.inl h)) hE2'

  have hUB := sound_QUnionBound_ofReal (pathMeasure K x) hVax0
    (mul_nonneg (pow_nonneg hβ T) hVdx0) hE1 hE2
    (compl_firstExit_subset Stp R T)
  have hbound : pathMeasure K x
      ({ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp}ᶜ)
      ≤ ENNReal.ofReal (1 - p) := by
    refine hUB.trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_right hc hVdx0
    linarith

  have hSuccMeas : MeasurableSet
      {ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp} := by
    have h : {ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp}
        = ⋃ n, ⋃ (_ : n ≤ T), ((fun ω : ℕ → S => ω n) ⁻¹' R
            ∩ ⋂ j, ⋂ (_ : j < n), (fun ω : ℕ → S => ω j) ⁻¹' Stpᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_iInter, Set.mem_compl_iff, exists_prop]
    rw [h]
    exact .iUnion fun n => .iUnion fun _ =>
      ((measurable_pi_apply n) hR).inter
        (.iInter fun j => .iInter fun _ => (measurable_pi_apply j) hStpMeas.compl)
  have hcc : pathMeasure K x {ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp}
      = 1 - pathMeasure K x
          ({ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp}ᶜ) := by
    conv_lhs => rw [← compl_compl
      {ω : ℕ → S | ∃ n ≤ T, ω n ∈ R ∧ ∀ j < n, ω j ∉ Stp}]
    exact prob_compl_eq_one_sub hSuccMeas.compl
  rw [hcc]
  refine le_trans ?_ (tsub_le_tsub_left hbound 1)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add h1p hp.le, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The until battery in predicate form: if every state violating the
side condition `sat_s` lies in the avoid set `A` and every state of `R`
satisfies the target predicate `sat`, then the first-hit bound of
`sound_QUntilBattery_firstHit` yields
`p ≤ P(∃ n ≤ T, sat (ω n) ∧ ∀ j < n, sat_s (ω j))` — the bounded until
`sat_s U≤T sat`. -/
theorem sound_QUntilBattery {sat_s sat : S → Prop}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar)
    (hA : MeasurableSet A) (hR : MeasurableSet R)
    (hVa : Measurable Va) (hVd : Measurable Vd)
    (hFs : ∀ y, ¬ sat_s y → y ∈ A) (hFt : ∀ y ∈ R, sat y)
    (hβ : 0 ≤ β) (hc : β ^ T ≤ c)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ A ∪ R → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ A ∪ R → K y (D ∪ (A ∪ R)) = 1)
    (hVaint : ∀ y ∈ D, y ∉ A ∪ R → Integrable Va (K y))
    (hVadrift : ∀ y ∈ D, y ∉ A ∪ R → ∫ z, Va z ∂K y ≤ Va y)
    (hVafloor : ∀ y ∈ A, y ∈ Dbar → 1 ≤ Va y)
    (hVanonneg : ∀ y ∈ Dbar, 0 ≤ Va y)
    (hVdint : ∀ y ∈ D, y ∉ A ∪ R → Integrable Vd (K y))
    (hVddecay : ∀ y ∈ D, y ∉ A ∪ R → ∫ z, Vd z ∂K y ≤ β * Vd y)
    (hVdfloor : ∀ y ∈ Dbar, y ∉ A ∪ R → 1 ≤ Vd y)
    (hVdnonneg : ∀ y ∈ Dbar, 0 ≤ Vd y)
    (hVdM : ∀ y ∈ Dbar, Vd y ≤ M)
    (hx : x ∈ D) (hthr : Va x + c * Vd x ≤ 1 - p) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∃ n ≤ T, sat (ω n) ∧ ∀ j < n, sat_s (ω j)} := by
  refine (sound_QUntilBattery_firstHit hD hDbar hA hR hVa hVd hβ hc hDsub hR3 hR4
    hVaint hVadrift hVafloor hVanonneg hVdint hVddecay hVdfloor hVdnonneg hVdM
    hx hthr).trans (measure_mono ?_)
  rintro ω ⟨n, hnT, hnR, hmin⟩
  exact ⟨n, hnT, hFt _ hnR, fun j hj =>
    not_not.1 fun hns => hmin j hj (Or.inl (Or.inl (hFs _ hns)))⟩

end QUntil

section QDeadlineBattery

variable {K : Kernel S S} [IsMarkovKernel K]
  {D Dbar B : Set S} {V : S → ℝ} {β p θ q : ℝ} {x : S} {T : ℕ} {M : ℝ}

/-- The deadline battery with an arithmetic discharge of the exponential
threshold: from `β ≤ exp (-θ)`, `θ ≥ 0`, and a nonnegative `q` below the
degree-`n` Taylor sum of `exp (θ * T)`, one gets `β ^ T * q ≤ 1`, so the
hypothesis `V x ≤ (1 - p) * q` implies the deadline-hit bound
`p ≤ P(∃ k ≤ T, sat (ω k))` for a `β`-decaying certificate `V` whose zero
set forces `B ⊆ {sat}`. All transcendental reasoning is confined to the
inequality `q ≤ exp (θ * T)`, checkable from rational Taylor data. -/
theorem sound_QDeadlineBattery {n : ℕ} {sat : S → Prop}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hB : MeasurableSet B)
    (hV : Measurable V)
    (hF : ∀ y ∈ B, sat y)
    (hβ : 0 ≤ β) (hβθ : β ≤ Real.exp (-θ)) (hθ : 0 ≤ θ)
    (hq0 : 0 ≤ q)
    (hq : q ≤ ∑ k ∈ range (n + 1), (θ * T) ^ k / (Nat.factorial k : ℝ))
    (hp : p ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ B → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ B → K y (D ∪ B) = 1)
    (hint : ∀ y ∈ D, y ∉ B → Integrable V (K y))
    (hdecay : ∀ y ∈ D, y ∉ B → ∫ z, V z ∂K y ≤ β * V y)
    (hfloor : ∀ y ∈ Dbar, y ∉ B → 1 ≤ V y)
    (hnonneg : ∀ y ∈ Dbar, 0 ≤ V y)
    (hM : ∀ y ∈ Dbar, V y ≤ M)
    (hx : x ∈ D) (hthr : V x ≤ (1 - p) * q) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∃ k ≤ T, sat (ω k)} := by
  have hβT : β ^ T ≤ Real.exp (-θ) ^ T := pow_le_pow_left₀ hβ hβθ T
  have hqexp : q ≤ Real.exp (θ * T) :=
    hq.trans (Real.sum_le_exp_of_nonneg (mul_nonneg hθ (Nat.cast_nonneg T)) _)
  have hkey : β ^ T * q ≤ 1 := by
    have h1 : β ^ T * q ≤ Real.exp (-θ) ^ T * Real.exp (θ * T) :=
      mul_le_mul hβT hqexp hq0 (pow_nonneg (Real.exp_pos _).le T)
    have h2 : Real.exp (-θ) ^ T * Real.exp (θ * T) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show (T : ℝ) * -θ + θ * T = 0 by ring, Real.exp_zero]
    linarith
  have hΘF : β ^ T * ((1 - p) * q) ≤ 1 - p := by
    rw [show β ^ T * ((1 - p) * q) = (1 - p) * (β ^ T * q) by ring]
    calc (1 - p) * (β ^ T * q) ≤ (1 - p) * 1 :=
          mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = 1 - p := mul_one _
  exact sound_QDeadline hD hDbar hB hV hF hβ hΘF hDsub hR3 hR4 hint hdecay
    hfloor hnonneg hM hx hthr

end QDeadlineBattery

section Staged

variable {Md X : Type*} [MeasurableSpace Md] [Countable Md]
  [MeasurableSingletonClass Md] [MeasurableSpace X]

lemma measurableSet_modeSet {Dm : Md → Set X} (h : ∀ m, MeasurableSet (Dm m)) :
    MeasurableSet {y : Md × X | y.2 ∈ Dm y.1} := by
  have hset : {y : Md × X | y.2 ∈ Dm y.1} = ⋃ m, {m} ×ˢ Dm m := by
    ext ⟨m, z⟩
    simp [Set.mem_iUnion]
  rw [hset]
  exact .iUnion fun m => (measurableSet_singleton m).prod (h m)

variable {J : Type*} [Fintype J]
  {flow : Md → Kernel X X} {src dst : J → Md} {G : J → Set X} {g : J → X → X}
  {V : Md → X → ℝ}

lemma mixture_integrable {m : Md} {z : X} {κ : Measure (Md × X)}
    {w₀ : ℝ≥0} {w : J → ℝ≥0}
    (hVmeas : ∀ m', Measurable (V m'))
    (hκ : κ = (w₀ : ℝ≥0∞) • ((flow m) z).map (Prod.mk m)
      + ∑ j, (w j : ℝ≥0∞) • Measure.dirac (dst j, g j z))
    (hflowint : Integrable (fun ζ => V m ζ) ((flow m) z)) :
    Integrable (fun y : Md × X => V y.1 y.2) κ := by
  have hVfun : Measurable fun y : Md × X => V y.1 y.2 :=
    measurable_from_prod_countable_right fun m' => hVmeas m'
  rw [hκ]
  refine Integrable.add_measure ?_ ?_
  · refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
    refine (integrable_map_measure hVfun.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 ?_
    exact hflowint
  · rw [integrable_finsetSum_measure]
    intro j _
    refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
    exact integrable_dirac' hVfun.stronglyMeasurable enorm_lt_top

lemma mixture_drift {m : Md} {z : X} {κ : Measure (Md × X)}
    {w₀ : ℝ≥0} {w : J → ℝ≥0}
    (hVmeas : ∀ m', Measurable (V m'))
    (hκ : κ = (w₀ : ℝ≥0∞) • ((flow m) z).map (Prod.mk m)
      + ∑ j, (w j : ℝ≥0∞) • Measure.dirac (dst j, g j z))
    (hsum : w₀ + ∑ j, w j = 1)
    (hguard : ∀ j, w j ≠ 0 → V (dst j) (g j z) ≤ V m z)
    (hflowint : Integrable (fun ζ => V m ζ) ((flow m) z))
    (hflowdrift : ∫ ζ, V m ζ ∂(flow m) z ≤ V m z) :
    ∫ y, V y.1 y.2 ∂κ ≤ V m z := by
  have hVfun : Measurable fun y : Md × X => V y.1 y.2 :=
    measurable_from_prod_countable_right fun m' => hVmeas m'
  have hint₁ : Integrable (fun y : Md × X => V y.1 y.2)
      ((w₀ : ℝ≥0∞) • ((flow m) z).map (Prod.mk m)) :=
    Integrable.smul_measure
      ((integrable_map_measure hVfun.aestronglyMeasurable
        measurable_prodMk_left.aemeasurable).2 hflowint) ENNReal.coe_ne_top
  have hdint : ∀ j : J, Integrable (fun y : Md × X => V y.1 y.2)
      (Measure.dirac (dst j, g j z)) := fun j =>
    integrable_dirac' hVfun.stronglyMeasurable enorm_lt_top
  have hint₂ : Integrable (fun y : Md × X => V y.1 y.2)
      (∑ j, (w j : ℝ≥0∞) • Measure.dirac (dst j, g j z)) := by
    rw [integrable_finsetSum_measure]
    exact fun j _ => Integrable.smul_measure (hdint j) ENNReal.coe_ne_top
  have hmap : ∫ y, V y.1 y.2 ∂(((flow m) z).map (Prod.mk m))
      = ∫ ζ, V m ζ ∂(flow m) z :=
    integral_map_of_stronglyMeasurable measurable_prodMk_left
      hVfun.stronglyMeasurable
  have hsumint : ∫ y, V y.1 y.2 ∂(∑ j, (w j : ℝ≥0∞) • Measure.dirac (dst j, g j z))
      = ∑ j, (w j : ℝ) * V (dst j) (g j z) := by
    rw [integral_finsetSum_measure fun j _ =>
      Integrable.smul_measure (hdint j) ENNReal.coe_ne_top]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac' _ _ hVfun.stronglyMeasurable]
    simp [smul_eq_mul, ENNReal.coe_toReal]
  calc ∫ y, V y.1 y.2 ∂κ
      = (w₀ : ℝ) * ∫ ζ, V m ζ ∂(flow m) z
        + ∑ j, (w j : ℝ) * V (dst j) (g j z) := by
        rw [hκ, integral_add_measure hint₁ hint₂, integral_smul_measure, hmap,
          hsumint]
        simp [smul_eq_mul, ENNReal.coe_toReal]
    _ ≤ (w₀ : ℝ) * V m z + ∑ j, (w j : ℝ) * V m z := by
        refine add_le_add
          (mul_le_mul_of_nonneg_left hflowdrift w₀.coe_nonneg)
          (Finset.sum_le_sum fun j _ => ?_)
        by_cases hj : w j = 0
        · simp [hj]
        · exact mul_le_mul_of_nonneg_left (hguard j hj) (w j).coe_nonneg
    _ = ((w₀ : ℝ) + ∑ j, (w j : ℝ)) * V m z := by
        rw [add_mul, Finset.sum_mul]
    _ = V m z := by
        have : ((w₀ : ℝ) + ∑ j, (w j : ℝ)) = 1 := by
          have := congrArg (fun t : ℝ≥0 => (t : ℝ)) hsum
          push_cast at this
          simpa using this
        rw [this, one_mul]

/-- The staged safety battery for multi-mode systems on `Md × X` (countably
many modes). Each kernel step from a confined state `(m, z)` is required to
be a convex mixture (`hmix`) of the within-mode flow `flow m` (weight `w₀`)
and finitely many guarded jumps `j` to `(dst j, g j z)`, enabled only when
`src j = m` and `z ∈ G j`. Given a per-mode certificate family `V m` that
drifts down along each flow (`hB1`), does not increase across any enabled
jump (`hB2`), has floor `1` on the per-mode unsafe sets (`hB3`), and is
nonnegative (`hB4`), the mixture drift lemma assembles a single certificate
`(m, z) ↦ V m z` for the joint chain, and the base safety battery yields:
from any confined start with `V m z ≤ thr` and `p + thr ≤ 1`, the probability
that the path satisfies `sat` forever is at least `p`. -/
theorem sound_QSafetyBattery_staged
    {K : Kernel (Md × X) (Md × X)} [IsMarkovKernel K]
    {Dm Dbarm Um : Md → Set X} {p thr : ℚ} {sat : Md × X → Prop}
    (hDm : ∀ m, MeasurableSet (Dm m)) (hDbarm : ∀ m, MeasurableSet (Dbarm m))
    (hUm : ∀ m, MeasurableSet (Um m)) (hVmeas : ∀ m, Measurable (V m))
    (hF : ∀ m z, ¬ sat (m, z) → z ∈ Um m)
    (hΘ : p + thr ≤ 1)
    (hDsub : ∀ m, Dm m ⊆ Dbarm m)
    (hR3 : ∀ m z, z ∈ Dm m → z ∉ Um m → K (m, z) {y | y.2 ∈ Dbarm y.1} = 1)
    (hR4 : ∀ m z, z ∈ Dm m → z ∉ Um m →
      K (m, z) ({y | y.2 ∈ Dm y.1} ∪ {y | y.2 ∈ Um y.1}) = 1)
    (hint : ∀ m z, z ∈ Dm m → z ∉ Um m → Integrable (V m) ((flow m) z))
    (hB1 : ∀ m z, z ∈ Dm m → z ∉ Um m → ∫ ζ, V m ζ ∂(flow m) z ≤ V m z)
    (hB2 : ∀ j, ∀ z ∈ G j, V (dst j) (g j z) ≤ V (src j) z)
    (hB3 : ∀ m z, z ∈ Um m → z ∈ Dbarm m → 1 ≤ V m z)
    (hB4 : ∀ m z, z ∈ Dbarm m → 0 ≤ V m z)
    (hmix : ∀ m z, z ∈ Dm m → z ∉ Um m →
      ∃ (w₀ : ℝ≥0) (w : J → ℝ≥0), w₀ + ∑ j, w j = 1 ∧
        (∀ j, w j ≠ 0 → src j = m ∧ z ∈ G j) ∧
        K (m, z) = (w₀ : ℝ≥0∞) • ((flow m) z).map (Prod.mk m)
          + ∑ j, (w j : ℝ≥0∞) • Measure.dirac (dst j, g j z)) :
    ∀ m z, z ∈ Dm m → V m z ≤ (thr : ℝ) →
      ENNReal.ofReal (p : ℝ)
        ≤ pathMeasure K (m, z) {ω | ∀ n, sat (ω n)} := by
  intro m z hz hthrz
  have hguards : ∀ (m' : Md) (z' : X), z' ∈ Dm m' → z' ∉ Um m' →
      ∀ (w₀ : ℝ≥0) (w : J → ℝ≥0),
        (∀ j, w j ≠ 0 → src j = m' ∧ z' ∈ G j) →
        ∀ j, w j ≠ 0 → V (dst j) (g j z') ≤ V m' z' := by
    intro m' z' _ _ _w₀ w hsupp j hj
    obtain ⟨hsrc, hG⟩ := hsupp j hj
    have := hB2 j z' hG
    rwa [hsrc] at this
  refine sound_QSafetyBattery (K := K)
    (D := {y : Md × X | y.2 ∈ Dm y.1}) (Dbar := {y : Md × X | y.2 ∈ Dbarm y.1})
    (U := {y : Md × X | y.2 ∈ Um y.1}) (V := fun y => V y.1 y.2)
    (sat := sat) (p := (p : ℝ)) (thr := (thr : ℝ)) (x := (m, z))
    (measurableSet_modeSet hDm) (measurableSet_modeSet hDbarm)
    (measurableSet_modeSet hUm)
    (measurable_from_prod_countable_right fun m' => hVmeas m')
    (fun y hy => hF y.1 y.2 hy)
    (by exact_mod_cast hΘ)
    (fun y hy => hDsub y.1 hy)
    (fun y hy hyU => hR3 y.1 y.2 hy hyU)
    (fun y hy hyU => hR4 y.1 y.2 hy hyU)
    (fun y hy hyU => by
      obtain ⟨w₀, w, hsum, hsupp, hκ⟩ := hmix y.1 y.2 hy hyU
      exact mixture_integrable hVmeas hκ (hint y.1 y.2 hy hyU))
    (fun y hy hyU => by
      obtain ⟨w₀, w, hsum, hsupp, hκ⟩ := hmix y.1 y.2 hy hyU
      exact mixture_drift hVmeas hκ hsum
        (hguards y.1 y.2 hy hyU w₀ w hsupp)
        (hint y.1 y.2 hy hyU) (hB1 y.1 y.2 hy hyU))
    (fun y hyU hybar => hB3 y.1 y.2 hyU hybar)
    (fun y hybar => hB4 y.1 y.2 hybar)
    hz hthrz

end Staged

end Qtsl.Battery
