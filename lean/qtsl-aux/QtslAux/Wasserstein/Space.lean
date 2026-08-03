import QtslAux.Wasserstein.Glue

/-! # The Wasserstein-2 space `P2 X`

The type `P2 X` of probability measures with finite second moment on a metric space `X`, metrized
by the Wasserstein-2 distance.

Main declarations:

* `P2 X`: a bundled measure together with `IsProbabilityMeasure` and finiteness of the second
  moment about every base point; `P2.mk'` constructs it from finiteness at a single base point,
  and `P2.dirac` is the point mass;
* the `EDist` instance given by `W2edist` on the underlying measures (`P2.edist_def`), with
  `P2.edist_le_cost` and finiteness `P2.edist_ne_top`;
* for `X` complete, second countable, and Borel: the `EMetricSpace` and `MetricSpace` instances on
  `P2 X` — symmetry, the triangle inequality, and identity of indiscernibles are inherited from
  the `W2edist` development — with `P2.dist_def` expressing `dist` as `(W2edist …).toReal`.
-/

namespace Qtsl

namespace Wasserstein

open MeasureTheory Set Metric
open scoped ENNReal NNReal

variable (X : Type*) [MetricSpace X] [MeasurableSpace X]

structure P2 where

  toMeasure : Measure X

  protected prob : IsProbabilityMeasure toMeasure

  protected m2_ne_top' : ∀ x₀ : X, m2 toMeasure x₀ ≠ ∞

variable {X}

namespace P2

instance (μ : P2 X) : IsProbabilityMeasure μ.toMeasure := μ.prob

theorem m2_ne_top (μ : P2 X) (x₀ : X) : m2 μ.toMeasure x₀ ≠ ∞ := μ.m2_ne_top' x₀

noncomputable def mk' [OpensMeasurableSpace X] (μ : Measure X)
    (hp : IsProbabilityMeasure μ) (h : ∃ x₀ : X, m2 μ x₀ ≠ ∞) : P2 X := by
  refine ⟨μ, hp, fun x₁ => ?_⟩
  haveI := hp
  obtain ⟨x₀, h₀⟩ := h
  exact m2_ne_top_of_ne_top h₀ x₁

@[simp] theorem mk'_toMeasure [OpensMeasurableSpace X] (μ : Measure X)
    (hp : IsProbabilityMeasure μ) (h : ∃ x₀ : X, m2 μ x₀ ≠ ∞) :
    (mk' μ hp h).toMeasure = μ := rfl

@[ext] theorem ext {μ ν : P2 X} (h : μ.toMeasure = ν.toMeasure) : μ = ν := by
  cases μ
  cases ν
  simpa using h

noncomputable def dirac [OpensMeasurableSpace X] (x : X) : P2 X := by
  refine mk' (Measure.dirac x) inferInstance ⟨x, ?_⟩
  rw [m2, lintegral_dirac' x (measurable_edist_rpow_left x), edist_self,
    ENNReal.zero_rpow_of_pos (by norm_num)]
  exact ENNReal.zero_ne_top

instance [OpensMeasurableSpace X] [Nonempty X] : Nonempty (P2 X) :=
  ⟨dirac (Classical.arbitrary X)⟩

noncomputable instance : EDist (P2 X) :=
  ⟨fun μ ν => W2edist μ.toMeasure ν.toMeasure⟩

theorem edist_def (μ ν : P2 X) : edist μ ν = W2edist μ.toMeasure ν.toMeasure :=
  rfl

theorem edist_le_cost {μ ν : P2 X} {π : Measure (X × X)}
    (h : IsCoupling π μ.toMeasure ν.toMeasure) :
    edist μ ν ≤ cost2 π ^ (1 / 2 : ℝ) :=
  W2edist_le_cost h

theorem edist_ne_top [BorelSpace X] (μ ν : P2 X) : edist μ ν ≠ ∞ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact absurd (nonempty_of_isProbabilityMeasure μ.toMeasure) (not_nonempty_iff.mpr hX)
  · obtain ⟨x₀⟩ := hX
    exact W2edist_ne_top (μ.m2_ne_top x₀) (ν.m2_ne_top x₀)

end P2

section Instances

variable [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]

noncomputable instance : EMetricSpace (P2 X) where
  edist_self μ := W2edist_self μ.toMeasure
  edist_comm μ ν := W2edist_comm μ.toMeasure ν.toMeasure
  edist_triangle μ ν ξ := W2edist_triangle
  eq_of_edist_eq_zero {μ ν} h := P2.ext (measure_eq_of_W2edist_eq_zero h)

noncomputable instance : MetricSpace (P2 X) :=
  EMetricSpace.toMetricSpace P2.edist_ne_top

theorem P2.dist_def (μ ν : P2 X) :
    dist μ ν = (W2edist μ.toMeasure ν.toMeasure).toReal := rfl

end Instances

end Wasserstein

end Qtsl
