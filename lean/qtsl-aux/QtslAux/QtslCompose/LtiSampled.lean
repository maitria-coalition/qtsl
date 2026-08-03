import QtslAux.QtslCompose.Presentation

/-! # A sampled-data LTI system

This module presents a small worked example of the presentation layer: a
sampled-data linear time-invariant control loop consisting of a continuous
plant chart (drift field only, hence profile `ode`) and a digital
controller chart (counter-time jumps only, hence profile `discrete`).

* `ltiPlantShape`, `ltiDigitalShape`: the two chart shapes and their profile
  computations.
* `ltiSampled`: the two-chart `System` with trivial wiring.
* `ltiSampled_heterogeneous`: the system genuinely mixes profiles — its two
  charts have distinct profiles.
* `ltiSampled_tier`: nevertheless the system sits in the `admissible` tier
  of assume-guarantee composition, since both profiles (`ode` and
  `discrete`) admit certificate construction.
-/

namespace Qtsl.QtslCompose

/-- The continuous plant chart: a drift field and nothing else, so its
profile is `ode`. -/
def ltiPlantShape : ChartShape := ⟨true, false, false, false⟩

/-- The digital controller chart: counter-time jumps only (the sampling
events), so its profile is `discrete`. -/
def ltiDigitalShape : ChartShape := ⟨false, false, true, true⟩

@[simp] theorem ltiPlantShape_profile : ltiPlantShape.profile = .ode := rfl

@[simp] theorem ltiDigitalShape_profile :
    ltiDigitalShape.profile = .discrete := rfl

/-- The sampled-data LTI system: two charts (plant and digital controller)
with no upstream dependencies. -/
def ltiSampled : System 2 where
  charts := fun i => match i with
    | ⟨0, _⟩ => ltiPlantShape
    | ⟨1, _⟩ => ltiDigitalShape
    | ⟨n + 2, h⟩ => absurd h (by omega)
  upstream := fun _ => ∅
  rank := fun _ => 0
  causality := by intro j i hi; simp at hi

theorem ltiSampled_charts_zero : ltiSampled.charts 0 = ltiPlantShape := rfl

theorem ltiSampled_charts_one : ltiSampled.charts 1 = ltiDigitalShape := rfl

/-- The system mixes dynamical species: its plant chart has profile `ode`
while its controller chart has profile `discrete`. -/
theorem ltiSampled_heterogeneous :
    (ltiSampled.charts 0).profile ≠ (ltiSampled.charts 1).profile := by
  rw [ltiSampled_charts_zero, ltiSampled_charts_one,
      ltiPlantShape_profile, ltiDigitalShape_profile]
  exact fun h => Profile.noConfusion h

/-- Despite its heterogeneity, the sampled-data system lies in the
`admissible` assume-guarantee tier: every chart's profile is `ode` or
`discrete`, so certificates are directly constructible. -/
theorem ltiSampled_tier : ltiSampled.qagTier = .admissible := by
  rw [System.qagTier_admissible_iff]
  intro i
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl
  | ⟨n + 2, h⟩ => exact absurd h (by omega)

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.ltiSampled_heterogeneous
#print axioms Qtsl.QtslCompose.ltiSampled_tier
