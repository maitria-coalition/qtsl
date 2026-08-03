import QtslAux.Battery

/-! # Discrete-state infrastructure for the benchmark sweep

Helper definitions and lemmas for internalizing certified reachability bounds for Markov chains on
discrete measurable state spaces.

Main declarations:

* `Qtsl.Sweep.ofFun`: packages a function `S → Measure S` as a `Kernel S S`
  (measurability is automatic on a discrete measurable space), together with
  `isMarkovKernel_ofFun`;
* `mix2`, `mix3`, `mix4`: finite convex mixtures of Dirac measures, with
  `isProbabilityMeasure_mix2`/`_mix3`/`_mix4` and the evaluation lemmas
  `integral_mix2`/`_mix3`/`_mix4`, which reduce an integral against a mixture to a finite rational
  combination of function values;
* `integral_le_of_le_const` and `integral_dirac_self`: the remaining integral bounds needed for
  drift checks;
* `reach_le_of_battery`: the specialization of `Battery.measure_reach_le` to such kernels:
  if `V : S → ℝ` is nonnegative, bounded, at least `1` on the target set `A`, and superharmonic
  for `step` outside `A`, then the probability that the chain started at `x` ever visits `A` is
  at most `V x`.

Each generated benchmark-row file instantiates `reach_le_of_battery` with an exact-rational
certificate table.
-/

open MeasureTheory ProbabilityTheory

namespace Qtsl.Sweep

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]

def ofFun (f : S → Measure S) : Kernel S S := ⟨f, Measurable.of_discrete⟩

@[simp] lemma ofFun_apply (f : S → Measure S) (x : S) : ofFun f x = f x := rfl

lemma isMarkovKernel_ofFun {f : S → Measure S} (h : ∀ x, IsProbabilityMeasure (f x)) :
    IsMarkovKernel (ofFun f) := ⟨fun x => h x⟩

lemma integrable_dirac' (f : S → ℝ) (a : S) : Integrable f (Measure.dirac a) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_dirac' _ Measurable.of_discrete.enorm]
  exact enorm_lt_top

lemma integrable_smul_dirac (f : S → ℝ) (p : ℝ) (a : S) :
    Integrable f (ENNReal.ofReal p • Measure.dirac a) :=
  (integrable_dirac' f a).smul_measure ENNReal.ofReal_ne_top

lemma integral_smul_dirac (f : S → ℝ) {p : ℝ} (hp : 0 ≤ p) (a : S) :
    ∫ z, f z ∂(ENNReal.ofReal p • Measure.dirac a) = p * f a := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp, smul_eq_mul]

noncomputable def mix2 (p₁ p₂ : ℝ) (t₁ t₂ : S) : Measure S :=
  ENNReal.ofReal p₁ • Measure.dirac t₁ + ENNReal.ofReal p₂ • Measure.dirac t₂

noncomputable def mix3 (p₁ p₂ p₃ : ℝ) (t₁ t₂ t₃ : S) : Measure S :=
  ENNReal.ofReal p₁ • Measure.dirac t₁ + ENNReal.ofReal p₂ • Measure.dirac t₂
    + ENNReal.ofReal p₃ • Measure.dirac t₃

noncomputable def mix4 (p₁ p₂ p₃ p₄ : ℝ) (t₁ t₂ t₃ t₄ : S) : Measure S :=
  ENNReal.ofReal p₁ • Measure.dirac t₁ + ENNReal.ofReal p₂ • Measure.dirac t₂
    + ENNReal.ofReal p₃ • Measure.dirac t₃ + ENNReal.ofReal p₄ • Measure.dirac t₄

omit [DiscreteMeasurableSpace S] in
lemma isProbabilityMeasure_mix2 {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂)
    (hsum : p₁ + p₂ = 1) (t₁ t₂ : S) : IsProbabilityMeasure (mix2 p₁ p₂ t₁ t₂) := by
  constructor
  simp only [mix2, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h₁ h₂, hsum, ENNReal.ofReal_one]

omit [DiscreteMeasurableSpace S] in
lemma isProbabilityMeasure_mix3 {p₁ p₂ p₃ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (t₁ t₂ t₃ : S) :
    IsProbabilityMeasure (mix3 p₁ p₂ p₃ t₁ t₂ t₃) := by
  constructor
  simp only [mix3, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_add (by linarith) h₃, hsum,
    ENNReal.ofReal_one]

omit [DiscreteMeasurableSpace S] in
lemma isProbabilityMeasure_mix4 {p₁ p₂ p₃ p₄ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂)
    (h₃ : 0 ≤ p₃) (h₄ : 0 ≤ p₄) (hsum : p₁ + p₂ + p₃ + p₄ = 1) (t₁ t₂ t₃ t₄ : S) :
    IsProbabilityMeasure (mix4 p₁ p₂ p₃ p₄ t₁ t₂ t₃ t₄) := by
  constructor
  simp only [mix4, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_add (by linarith) h₃,
    ← ENNReal.ofReal_add (by linarith) h₄, hsum, ENNReal.ofReal_one]

lemma integral_mix2 (f : S → ℝ) {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (t₁ t₂ : S) :
    ∫ z, f z ∂(mix2 p₁ p₂ t₁ t₂) = p₁ * f t₁ + p₂ * f t₂ := by
  rw [mix2, integral_add_measure (integrable_smul_dirac f p₁ t₁)
    (integrable_smul_dirac f p₂ t₂), integral_smul_dirac f h₁, integral_smul_dirac f h₂]

lemma integral_mix3 (f : S → ℝ) {p₁ p₂ p₃ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃)
    (t₁ t₂ t₃ : S) :
    ∫ z, f z ∂(mix3 p₁ p₂ p₃ t₁ t₂ t₃) = p₁ * f t₁ + p₂ * f t₂ + p₃ * f t₃ := by
  rw [mix3, integral_add_measure
    ((integrable_smul_dirac f p₁ t₁).add_measure (integrable_smul_dirac f p₂ t₂))
    (integrable_smul_dirac f p₃ t₃),
    integral_add_measure (integrable_smul_dirac f p₁ t₁) (integrable_smul_dirac f p₂ t₂),
    integral_smul_dirac f h₁, integral_smul_dirac f h₂, integral_smul_dirac f h₃]

lemma integral_mix4 (f : S → ℝ) {p₁ p₂ p₃ p₄ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂)
    (h₃ : 0 ≤ p₃) (h₄ : 0 ≤ p₄) (t₁ t₂ t₃ t₄ : S) :
    ∫ z, f z ∂(mix4 p₁ p₂ p₃ p₄ t₁ t₂ t₃ t₄)
      = p₁ * f t₁ + p₂ * f t₂ + p₃ * f t₃ + p₄ * f t₄ := by
  rw [mix4, integral_add_measure
    (((integrable_smul_dirac f p₁ t₁).add_measure (integrable_smul_dirac f p₂ t₂)).add_measure
      (integrable_smul_dirac f p₃ t₃))
    (integrable_smul_dirac f p₄ t₄),
    integral_add_measure
      ((integrable_smul_dirac f p₁ t₁).add_measure (integrable_smul_dirac f p₂ t₂))
      (integrable_smul_dirac f p₃ t₃),
    integral_add_measure (integrable_smul_dirac f p₁ t₁) (integrable_smul_dirac f p₂ t₂),
    integral_smul_dirac f h₁, integral_smul_dirac f h₂, integral_smul_dirac f h₃,
    integral_smul_dirac f h₄]

omit [DiscreteMeasurableSpace S] in

lemma integral_le_of_le_const {μ : Measure S} [IsProbabilityMeasure μ] {V : S → ℝ}
    {C : ℝ} (h0 : ∀ y, 0 ≤ V y) (hC : ∀ y, V y ≤ C) : ∫ z, V z ∂μ ≤ C := by
  calc ∫ z, V z ∂μ ≤ ∫ _z, C ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall h0)
          (integrable_const C) (Filter.Eventually.of_forall hC)
      _ = C := by simp

lemma integral_dirac_self (V : S → ℝ) (y : S) : ∫ z, V z ∂(Measure.dirac y) = V y :=
  integral_dirac V y

theorem reach_le_of_battery (step : S → Measure S) [IsMarkovKernel (ofFun step)]
    (A : Set S) (V : S → ℝ) (C : ℝ)
    (h0 : ∀ y, 0 ≤ V y) (hC : ∀ y, V y ≤ C)
    (h1 : ∀ y ∈ A, 1 ≤ V y)
    (hdrift : ∀ y, y ∉ A → ∫ z, V z ∂(step y) ≤ V y)
    (x : S) :
    Battery.pathMeasure (ofFun step) x {ω | ∃ n, ω n ∈ A} ≤ ENNReal.ofReal (V x) :=
  Battery.measure_reach_le (K := ofFun step) MeasurableSet.of_discrete
    Measurable.of_discrete h0 hC h1 (fun y hy => by rw [ofFun_apply]; exact hdrift y hy) x

end Qtsl.Sweep
