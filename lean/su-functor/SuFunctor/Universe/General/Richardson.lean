import SuFunctor.Universe.General.CredalPoset
import Mathlib.Analysis.MeanInequalities

/-! # Richardson's universe at the general carrier

Bodies compiled from penalty functionals both **convex** and **lower
semicontinuous**, at the general carrier.  Provenance, stated
carefully: the probabilistic-dependency-graph programme never
axiomatizes a codomain class — convexity of its inconsistency measure
is proved there as a lemma, and semicontinuity is never mentioned — so
this class pins the programme's *working reading*, both properties
assumed of its penalty functionals (its conditional-relative-entropy
family satisfies both; the finite-stratum
`exists_penaltyConvex_compile_not_richardson` shows the lsc conjunct
is not implied by convexity).  Convexity of the penalty is
sufficient, not necessary, for convexity of the body: the exact
criterion is the grade-convexity (`e^f` convex) of
`SuFunctor.Universe.General.CredalPoset`, and this module supplies the
sufficiency leg —

* `grade_coe_smul`: the grade of a scaled height is the real power of
  the grade (`e^{-s·a} = (e^{-a})^s`), the multiplicative face of the
  additive scale;
* `gradeConvex_of_penaltyConvex`: an additively convex penalty is
  grade-convex — the two-point weighted AM–GM inequality, in the
  cross-multiplied harmonic form the atlas uses;
* `IsRichardsonBody.isConvexCredalBody`: Richardson bodies are convex
  credal bodies.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

namespace CredalPoset

/-- Convexity of a penalty functional on the direction carrier,
quantified over strictly interior mixture weights (the endpoint cases
are degenerate identities).  `ℝ≥0∞` arithmetic: with `s, t > 0` no
`0 * ⊤` corner arises on the right-hand side. -/
def PenaltyConvex (f : Penalty X) : Prop :=
  ∀ (μ ν : ProbabilityMeasure X) (s t : ℝ≥0) (hst : s + t = 1),
    0 < s → 0 < t →
    f (pmix s t hst μ ν) ≤ (s : ℝ≥0∞) * f μ + (t : ℝ≥0∞) * f ν

/-- Richardson bodies: radial compiles of penalty functionals both
*convex* and *lower semicontinuous* — the programme's working reading
(neither property is axiomatized in its sources; see the module
docstring). -/
def IsRichardsonBody (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∃ f : Penalty X,
    PenaltyConvex f ∧ LowerSemicontinuous f ∧ S = compile f

/-- The grade of a scaled finite height is the real power of the
grade: the multiplicative face of the additive penalty scale. -/
theorem grade_coe_smul (s : ℝ≥0) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    grade ((s : ℝ≥0∞) * a) = grade a ^ (s : ℝ) := by
  have hmul : (s : ℝ≥0∞) * a ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ha
  rw [grade_of_ne_top hmul, grade_of_ne_top ha,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  congr 1
  ring

/-- The `ℝ≥0` face of `grade_coe_smul`. -/
theorem gradeN_coe_smul (s : ℝ≥0) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    gradeN ((s : ℝ≥0∞) * a) = gradeN a ^ (s : ℝ) := by
  ext
  rw [coe_gradeN, NNReal.coe_rpow, coe_gradeN]
  exact grade_coe_smul s ha

/-- Grades split additive heights multiplicatively, `ℝ≥0` face. -/
theorem gradeN_add (a b : ℝ≥0∞) :
    gradeN (a + b) = gradeN a * gradeN b := by
  ext
  rw [coe_gradeN, NNReal.coe_mul, coe_gradeN, coe_gradeN]
  exact grade_add a b

/-- **Additively convex penalties are grade-convex**: the two-point
weighted AM–GM inequality, arranged in the cross-multiplied harmonic
form.  This is the sufficiency direction of the chapter's "convexity
of the penalty is sufficient, not necessary" sentence, at the general
carrier. -/
theorem gradeConvex_of_penaltyConvex {f : Penalty X}
    (hf : PenaltyConvex f) : GradeConvex f := by
  intro μ ν s t hst
  -- degenerate weights first: the mixture is one of the endpoints
  rcases eq_or_ne s 0 with rfl | hs0
  · have ht1 : t = 1 := by rwa [zero_add] at hst
    subst ht1
    rw [pmix_zero_left hst μ ν, zero_mul, zero_add, one_mul, mul_comm]
  · rcases eq_or_ne t 0 with rfl | ht0
    · have hs1 : s = 1 := by rwa [add_zero] at hst
      subst hs1
      rw [pmix_zero_right hst μ ν, zero_mul, add_zero, one_mul]
    · -- interior weights
      rcases eq_or_ne (f μ) ⊤ with hfμ | hfμ
      · rw [hfμ, gradeN_top, zero_mul]
        exact zero_le
      · rcases eq_or_ne (f ν) ⊤ with hfν | hfν
        · rw [hfν, gradeN_top, mul_zero]
          exact zero_le
        · -- both heights finite: AM–GM does the work
          have hs : 0 < s := pos_iff_ne_zero.mpr hs0
          have ht : 0 < t := pos_iff_ne_zero.mpr ht0
          have hkey := hf μ ν s t hst hs ht
          have hgπ : gradeN (f μ) ^ (s : ℝ) * gradeN (f ν) ^ (t : ℝ)
              ≤ gradeN (f (pmix s t hst μ ν)) := by
            calc gradeN (f μ) ^ (s : ℝ) * gradeN (f ν) ^ (t : ℝ)
                = gradeN ((s : ℝ≥0∞) * f μ + (t : ℝ≥0∞) * f ν) := by
                  rw [gradeN_add, gradeN_coe_smul s hfμ,
                    gradeN_coe_smul t hfν]
              _ ≤ gradeN (f (pmix s t hst μ ν)) := gradeN_anti hkey
          -- the AM–GM bound on the weight term
          have hamgm : gradeN (f ν) ^ (s : ℝ) * gradeN (f μ) ^ (t : ℝ)
              ≤ s * gradeN (f ν) + t * gradeN (f μ) :=
            NNReal.geom_mean_le_arith_mean2_weighted
              (w₁ := s) (w₂ := t) (p₁ := gradeN (f ν))
              (p₂ := gradeN (f μ)) hst
          -- positive grades let the powers recombine
          have hgμ : (0 : ℝ≥0) < gradeN (f μ) := gradeN_pos hfμ
          have hgν : (0 : ℝ≥0) < gradeN (f ν) := gradeN_pos hfν
          have hsum : (s : ℝ) + (t : ℝ) = 1 := by exact_mod_cast hst
          have hx : gradeN (f μ)
              = gradeN (f μ) ^ (s : ℝ) * gradeN (f μ) ^ (t : ℝ) := by
            rw [← NNReal.rpow_add hgμ.ne', hsum, NNReal.rpow_one]
          have hy : gradeN (f ν)
              = gradeN (f ν) ^ (s : ℝ) * gradeN (f ν) ^ (t : ℝ) := by
            rw [← NNReal.rpow_add hgν.ne', hsum, NNReal.rpow_one]
          calc gradeN (f μ) * gradeN (f ν)
              = (gradeN (f μ) ^ (s : ℝ) * gradeN (f μ) ^ (t : ℝ))
                * (gradeN (f ν) ^ (s : ℝ) * gradeN (f ν) ^ (t : ℝ)) := by
                rw [← hx, ← hy]
            _ = (gradeN (f μ) ^ (s : ℝ) * gradeN (f ν) ^ (t : ℝ))
                * (gradeN (f ν) ^ (s : ℝ) * gradeN (f μ) ^ (t : ℝ)) := by
                ring
            _ ≤ gradeN (f (pmix s t hst μ ν))
                * (s * gradeN (f ν) + t * gradeN (f μ)) :=
                mul_le_mul hgπ hamgm zero_le zero_le

/-- **Richardson bodies are convex credal bodies** at the general
carrier: closedness from the dictionary (`isClosed_compile`),
convexity from grade-convexity through the harmonic-mean leg. -/
theorem IsRichardsonBody.isConvexCredalBody [Nonempty X]
    {S : Set (SubProbabilityMeasure X)} (h : IsRichardsonBody S) :
    IsConvexCredalBody S := by
  obtain ⟨f, hconv, hlsc, rfl⟩ := h
  exact ⟨⟨⟨_, zero_mem_compile f⟩, isClosed_compile hlsc,
    isRadial_compile f⟩,
    convexBody_compile_of_gradeConvex (gradeConvex_of_penaltyConvex hconv)⟩

end CredalPoset

end SuFunctor.Universe.General
