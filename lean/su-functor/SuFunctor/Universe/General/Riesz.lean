import SuFunctor.Universe.General.Carrier
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-! # States are Radon functionals: the general tie

The finite-stratum Riesz module (`SuFunctor.Universe.Riesz`) pins the
equivalence between mass coordinates and expectation functionals on a
finite outcome space, and remarks that the functional presentation is
the one that survives past the finite stratum.  This module makes that
sentence a theorem at the stratum where it lives: on a locally compact
Hausdorff Borel carrier, the states of the general subprobability
carrier embed **faithfully** into the positive linear functionals on
compactly supported continuous observations, and the Riesz–Markov–
Kakutani representation inverts the embedding on regular states —
states *are* Radon functionals, kernel-checked.

The regularity hypothesis is carried explicitly: Riesz–Markov speaks
about regular measures, and the general carrier does not impose
regularity (on Polish carriers every finite Borel measure is regular,
and the hypothesis discharges by instance search there).
-/

namespace SuFunctor.Universe.General

open MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

namespace SubProbabilityMeasure

/-- The Radon-functional presentation of a state: integration of
compactly supported continuous observations. -/
noncomputable def toRadon (ν : SubProbabilityMeasure X) :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
  integralLinearMap (ν.toFiniteMeasure : Measure X)

/-- **States are Radon functionals, faithfully**: on regular states the
functional presentation forgets nothing.  (Regularity enters as an
explicit hypothesis: Riesz–Markov speaks about regular measures.) -/
theorem toRadon_injective {ν ρ : SubProbabilityMeasure X}
    (hν : (ν.toFiniteMeasure : Measure X).Regular)
    (hρ : (ρ.toFiniteMeasure : Measure X).Regular)
    (h : ν.toRadon = ρ.toRadon) : ν = ρ := by
  have hm : (ν.toFiniteMeasure : Measure X)
      = (ρ.toFiniteMeasure : Measure X) := by
    haveI := hν
    haveI := hρ
    exact NNRealRMK.integralLinearMap_inj.mp h
  exact ext (Subtype.ext hm)

/-- **States are Radon functionals, and Riesz–Markov reads them back**:
the Riesz measure of a regular state's functional is the state's
measure. -/
theorem rieszMeasure_toRadon (ν : SubProbabilityMeasure X)
    (hν : (ν.toFiniteMeasure : Measure X).Regular) :
    NNRealRMK.rieszMeasure ν.toRadon = (ν.toFiniteMeasure : Measure X) := by
  haveI := hν
  exact NNRealRMK.rieszMeasure_integralLinearMap

end SubProbabilityMeasure

end SuFunctor.Universe.General
