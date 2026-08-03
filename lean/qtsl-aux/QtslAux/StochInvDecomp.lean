import QtslAux.Battery

/-! # The stochastic-invariant decomposition schema

The Abate–Giacobbe–Roy decomposition as a reusable lemma-schema over the
`Battery` substrate: a quantitative claim `P ≥ p [ψ]` factors as ONE safety
supermartingale (the stochastic invariant, consumed by Ville's inequality via
`measure_reach_le`) plus an almost-sure obligation conditional on confinement
— stated per start state as a null hypothesis on the original chain. No
absorbing modification of the chain is constructed: this is the same pattern
the Streett-bundle soundness proof uses for its per-pair dichotomies,
factored out once.

Main results:

* `sound_QStochInvDecomp`: confinement certificate + conditional-a.s.
  property ⟹ quantitative lower bound on the property. The property `ψ`
  needs no measurability hypothesis (outer-measure monotonicity carries the
  two steps that touch it).
* `confinement_of_stochInv`: the schema instantiated at the confinement
  event itself (the conditional premise is trivially null), recovering the
  bare Ville-style confinement conclusion — the instantiability smoke test.

The rule-form's shift-invariance hypothesis is deliberately absent here: it
is what makes the conditional-a.s. premise *dischargeable* upstream (every
shift-invariant a.s. property of the confined chain yields the null
hypothesis), not something this lemma consumes. The bound `C` on `V` mirrors
the battery genre (`sound_QSafetyBattery` clamps its own certificate at
`max thr 1` before entering the stopped-supermartingale machinery; callers
may do the same).
-/

open scoped ENNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Qtsl.Battery

namespace Qtsl.StochInvDecomp

variable {S : Type*} [MeasurableSpace S] {K : Kernel S S} [IsMarkovKernel K]

/-- The stochastic-invariant decomposition: if `V` is a bounded nonnegative
supermartingale certificate for confinement to `I` (unit floor off `I`,
nonpositive drift on `I`), and the chain started at `x` almost surely
satisfies `ψ` conditional on confinement (the confined-but-not-`ψ` paths are
null), then `ψ` holds with probability at least `p` whenever
`p + V x ≤ 1`. -/
theorem sound_QStochInvDecomp
    {I : Set S} {ψ : Set (ℕ → S)} {V : S → ℝ} {C p : ℝ} {x : S}
    (hI : MeasurableSet I)
    (hV : Measurable V) (hV0 : ∀ y, 0 ≤ V y) (hVC : ∀ y, V y ≤ C)
    (hV1 : ∀ y, y ∉ I → 1 ≤ V y)
    (hdrift : ∀ y, y ∈ I → ∫ z, V z ∂K y ≤ V y)
    (hcond : pathMeasure K x ({ω | ∀ n, ω n ∈ I} \ ψ) = 0)
    (hpV : p + V x ≤ 1) :
    ENNReal.ofReal p ≤ pathMeasure K x ψ := by
  -- the escape event is measurable (countable union of coordinate preimages)
  have hreachMeas : MeasurableSet {ω : ℕ → S | ∃ n, ω n ∈ Iᶜ} := by
    have hEq : {ω : ℕ → S | ∃ n, ω n ∈ Iᶜ}
        = ⋃ n, (fun ω : ℕ → S => ω n) ⁻¹' Iᶜ := by
      ext ω; simp [Set.mem_iUnion]
    rw [hEq]
    exact MeasurableSet.iUnion fun n => measurable_pi_apply n hI.compl
  -- Ville: escaping `I` has probability at most `V x`
  have hreach : pathMeasure K x {ω | ∃ n, ω n ∈ Iᶜ} ≤ ENNReal.ofReal (V x) :=
    measure_reach_le hI.compl hV hV0 hVC (fun y hy => hV1 y hy)
      (fun y hy => hdrift y (by simpa using hy)) x
  -- confinement is the complement of escape
  have hconfine : {ω : ℕ → S | ∀ n, ω n ∈ I}
      = {ω : ℕ → S | ∃ n, ω n ∈ Iᶜ}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_not]
  have hμconf : 1 - ENNReal.ofReal (V x)
      ≤ pathMeasure K x {ω | ∀ n, ω n ∈ I} := by
    rw [hconfine, prob_compl_eq_one_sub hreachMeas]
    exact tsub_le_tsub_left hreach 1
  -- conditional-a.s.: confinement mass all sits inside `ψ`
  have hsplit : pathMeasure K x {ω | ∀ n, ω n ∈ I} ≤ pathMeasure K x ψ :=
    calc pathMeasure K x {ω | ∀ n, ω n ∈ I}
        = pathMeasure K x
            (({ω | ∀ n, ω n ∈ I} ∩ ψ) ∪ ({ω | ∀ n, ω n ∈ I} \ ψ)) := by
          rw [Set.inter_union_sdiff]
      _ ≤ pathMeasure K x ({ω | ∀ n, ω n ∈ I} ∩ ψ)
            + pathMeasure K x ({ω | ∀ n, ω n ∈ I} \ ψ) :=
          measure_union_le _ _
      _ = pathMeasure K x ({ω | ∀ n, ω n ∈ I} ∩ ψ) := by
          rw [hcond, add_zero]
      _ ≤ pathMeasure K x ψ := measure_mono Set.inter_subset_right
  -- threshold arithmetic in `ℝ≥0∞`
  have hp1 : ENNReal.ofReal p ≤ 1 - ENNReal.ofReal (V x) := by
    have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (V x) = ENNReal.ofReal (1 - V x) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (hV0 x)]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (le_sub_iff_add_le.mpr hpV)
  exact hp1.trans (hμconf.trans hsplit)

/-- The schema instantiated at the confinement event itself: the conditional
premise is trivially null, and the conclusion is the bare confinement bound.
This is the instantiability smoke test for the schema. -/
theorem confinement_of_stochInv
    {I : Set S} {V : S → ℝ} {C p : ℝ} {x : S}
    (hI : MeasurableSet I)
    (hV : Measurable V) (hV0 : ∀ y, 0 ≤ V y) (hVC : ∀ y, V y ≤ C)
    (hV1 : ∀ y, y ∉ I → 1 ≤ V y)
    (hdrift : ∀ y, y ∈ I → ∫ z, V z ∂K y ≤ V y)
    (hpV : p + V x ≤ 1) :
    ENNReal.ofReal p ≤ pathMeasure K x {ω | ∀ n, ω n ∈ I} :=
  sound_QStochInvDecomp hI hV hV0 hVC hV1 hdrift (by simp) hpV

end Qtsl.StochInvDecomp
