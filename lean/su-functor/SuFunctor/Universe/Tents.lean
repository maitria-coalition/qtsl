import SuFunctor.Universe.Closure

/-! # The tents theorem: quadratic gambles see the whole universe

Every lsc penalty on the (compact, finite-dimensional) carrier is the
pointwise supremum of its **tent** minorants — downward parabolas
`μ ↦ L − M·‖μ − μ₀‖²`, which are degree-2 polynomial gambles in the
distribution coordinates.

Read against the convex chart (`SuFunctor.Universe.ConvexChart`):
degree-1 (affine) gambles see exactly the biconjugate — the convex
shadow — and the witnesses module shows how much that shadow forgets.
This module shows the loss is repaired one degree up: **with arbitrary
menus, nothing in the universe is invisible to quadratic gambles.**
The degree axis of the certification ladder prices certificate size,
never ontology; its strictness above degree 2 is entirely a
finite-presentation phenomenon.

The proof is the classical tent construction: below any level `L` of
`σ` at `μ₀`, lower semicontinuity yields a ball on which `σ` stays
above `L`; a parabola of curvature `L/δ²` capped at `L` fits under `σ`
inside the ball (where `σ > L`) and under `0` outside it (penalties
are nonnegative — the codomain anchors the tent for free), while
touching height `L` at the apex.  Compactness is not consumed; only
the metric and nonnegativity are. -/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-- The squared distance between two distributions, coordinatewise. -/
def sqDist (μ₀ μ : BelState V) : ℝ :=
  ∑ v, ((μ : V → ℝ) v - (μ₀ : V → ℝ) v) ^ 2

theorem sqDist_nonneg (μ₀ μ : BelState V) : 0 ≤ sqDist μ₀ μ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem sqDist_self (μ₀ : BelState V) : sqDist μ₀ μ₀ = 0 := by
  simp [sqDist]

/-- A tent: the degree-2 polynomial gamble `L − M·‖μ − μ₀‖²`, read as a
penalty (negative values clamp to `0`). -/
noncomputable def tent (μ₀ : BelState V) (L M : ℝ) : Penalty V :=
  fun μ => ENNReal.ofReal (L - M * sqDist μ₀ μ)

theorem continuous_sqDist (μ₀ : BelState V) :
    Continuous fun μ : BelState V => sqDist μ₀ μ := by
  refine continuous_finsetSum _ fun v _ => ?_
  have h : Continuous fun μ : BelState V => (μ : V → ℝ) v :=
    (continuous_apply v).comp continuous_subtype_val
  exact (h.sub continuous_const).pow 2

/-- Tents are continuous, hence citizens of the universe. -/
theorem continuous_tent (μ₀ : BelState V) (L M : ℝ) :
    Continuous (tent μ₀ L M) :=
  ENNReal.continuous_ofReal.comp
    (continuous_const.sub (continuous_const.mul (continuous_sqDist μ₀)))

theorem lowerSemicontinuous_tent (μ₀ : BelState V) (L M : ℝ) :
    LowerSemicontinuous (tent μ₀ L M) :=
  (continuous_tent μ₀ L M).lowerSemicontinuous

/-- The apex value of a tent. -/
theorem tent_apex (μ₀ : BelState V) (L M : ℝ) :
    tent μ₀ L M μ₀ = ENNReal.ofReal L := by
  simp [tent]

/-- **The tents theorem.**  Every lsc penalty is the pointwise
supremum of its tent minorants: with arbitrary menus of degree-2
gambles, nothing in the universe is invisible.  (Compare
`biconj_le`/`biconj_eq_self`: at degree 1 the recoverable part is
exactly the convex shadow; one degree up, the shadow is the
territory.) -/
theorem iSup_tents_eq_self {σ : Penalty V} (hσ : LowerSemicontinuous σ) :
    ⨆ (μ₀ : BelState V) (L : ℝ) (M : ℝ)
        (_ : ∀ ν, tent μ₀ L M ν ≤ σ ν), tent μ₀ L M = σ := by
  apply le_antisymm
  · -- every tent in the supremum is a minorant
    refine iSup_le fun μ₀ => iSup_le fun L => iSup_le fun M => iSup_le fun hmin => ?_
    intro ν
    exact hmin ν
  · -- σ is dominated by its tents, pointwise
    intro μstar
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨L, hL0, h1, h2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt'
    -- h1 : (⨆ …) μstar < ofReal L ; h2 : ofReal L < σ μstar
    -- lower semicontinuity gives a ball on which σ stays above L
    have hev : ∀ᶠ ν in nhds μstar, ENNReal.ofReal L < σ ν := hσ μstar _ h2
    obtain ⟨δ, hδ0, hball⟩ := Metric.eventually_nhds_iff.mp hev
    -- the tent of curvature L/δ² at μstar is a minorant of σ
    set M : ℝ := L / δ ^ 2 with hM_def
    have hM0 : 0 ≤ M := div_nonneg hL0 (by positivity)
    have hmin : ∀ ν, tent μstar L M ν ≤ σ ν := by
      intro ν
      rcases lt_or_ge (sqDist μstar ν) (δ ^ 2) with hin | hout
      · -- inside the ball: the tent is below L, and σ is above L
        have hdist : dist ν μstar < δ := by
          rw [Subtype.dist_eq, dist_pi_lt_iff hδ0]
          intro v
          rw [Real.dist_eq]
          have hcoord : ((ν : V → ℝ) v - (μstar : V → ℝ) v) ^ 2 < δ ^ 2 := by
            calc ((ν : V → ℝ) v - (μstar : V → ℝ) v) ^ 2
                ≤ sqDist μstar ν :=
                  Finset.single_le_sum (f := fun w =>
                    ((ν : V → ℝ) w - (μstar : V → ℝ) w) ^ 2)
                    (fun w _ => sq_nonneg _) (Finset.mem_univ v)
              _ < δ ^ 2 := hin
          exact abs_lt_of_sq_lt_sq hcoord hδ0.le
        have hσν : ENNReal.ofReal L < σ ν := hball hdist
        calc tent μstar L M ν
            ≤ ENNReal.ofReal L := by
              unfold tent
              exact ENNReal.ofReal_le_ofReal
                (by nlinarith [sqDist_nonneg μstar ν])
          _ ≤ σ ν := hσν.le
      · -- outside the ball: the tent is below zero
        have hnp : L - M * sqDist μstar ν ≤ 0 := by
          have hMδ : M * δ ^ 2 = L := by
            rw [hM_def]
            field_simp
          nlinarith
        unfold tent
        rw [ENNReal.ofReal_eq_zero.mpr hnp]
        exact zero_le
    -- but the tent's apex beats L at μstar, contradicting h1
    have happex : ENNReal.ofReal L
        ≤ (⨆ (μ₀ : BelState V) (L' : ℝ) (M' : ℝ)
            (_ : ∀ ν, tent μ₀ L' M' ν ≤ σ ν), tent μ₀ L' M') μstar := by
      have hle : tent μstar L M
          ≤ ⨆ (μ₀ : BelState V) (L' : ℝ) (M' : ℝ)
              (_ : ∀ ν, tent μ₀ L' M' ν ≤ σ ν), tent μ₀ L' M' := by
        refine le_iSup_of_le μstar ?_
        refine le_iSup_of_le L ?_
        refine le_iSup_of_le M ?_
        exact le_iSup_of_le hmin le_rfl
      calc ENNReal.ofReal L = tent μstar L M μstar := (tent_apex μstar L M).symm
        _ ≤ _ := hle μstar
    exact absurd (lt_of_le_of_lt happex h1) (lt_irrefl _)

end SuFunctor.Universe
