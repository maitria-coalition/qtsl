import Pointfree.Valuation.Bridge
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! # The classical subprobability carrier

Finite Borel measures of total mass at most one, carrying the subspace
topology of the weak topology on finite measures.  This is the
classical face of the point-free subprobability carrier `SubProb`:
restriction to opens (`toSubProb`) sends it into `SubProb (Opens X)`,
and the bridge-continuity module proves that map continuous into the
narrow topology.  The measure-level dagger chart (`DaggerChart`)
exhibits this carrier as `ProbabilityMeasure (X ⊕ Unit)`.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

variable (X) in
/-- The **classical subprobability carrier**: finite measures of total
mass at most one.  Mass strictly below one is meaningful — a model
licensed to lose mass — so the carrier is the lower closure of the
probability face, exactly as for its point-free image `SubProb`. -/
def SubProbabilityMeasure : Type _ :=
  {μ : FiniteMeasure X // μ.mass ≤ 1}

namespace SubProbabilityMeasure

/-- The underlying finite measure. -/
def toFiniteMeasure (μ : SubProbabilityMeasure X) : FiniteMeasure X := μ.1

instance : Coe (SubProbabilityMeasure X) (FiniteMeasure X) := ⟨toFiniteMeasure⟩

@[simp] theorem coe_toFiniteMeasure (μ : SubProbabilityMeasure X) :
    (μ : FiniteMeasure X) = μ.1 := rfl

theorem mass_le_one (μ : SubProbabilityMeasure X) : μ.1.mass ≤ 1 := μ.2

theorem measure_univ_le_one (μ : SubProbabilityMeasure X) :
    (μ.1 : Measure X) Set.univ ≤ 1 := by
  rw [← FiniteMeasure.ennreal_mass]
  exact_mod_cast μ.2

section WeakTopology

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The subspace topology of the weak topology on finite measures. -/
instance : TopologicalSpace (SubProbabilityMeasure X) :=
  inferInstanceAs (TopologicalSpace {μ : FiniteMeasure X // μ.mass ≤ 1})

theorem continuous_toFiniteMeasure :
    Continuous (toFiniteMeasure : SubProbabilityMeasure X → FiniteMeasure X) :=
  continuous_subtype_val

/-- Restriction to opens: the classical subprobability carrier lands in
the point-free one.  Bridge-continuity (`BridgeContinuity`) proves this
map continuous from the weak topology into the narrow topology. -/
noncomputable def toSubProb (μ : SubProbabilityMeasure X) : SubProb (Opens X) :=
  (μ.1 : Measure X).toSubProb μ.measure_univ_le_one

@[simp] theorem toSubProb_apply (μ : SubProbabilityMeasure X)
    (U : Opens X) : μ.toSubProb U = (μ.1 : Measure X) (U : Set X) := rfl

end WeakTopology

end SubProbabilityMeasure

end Pointfree
