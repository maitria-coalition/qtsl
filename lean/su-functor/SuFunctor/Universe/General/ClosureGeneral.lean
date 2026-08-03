import SuFunctor.Universe.General.Dictionary
import SuFunctor.Universe.General.CheckerAnchor

/-! # The closure table at the general carrier

The operations the calculus owns, as citizenship-closure theorems over
the general carrier — the finite storey's `SuFunctor.Universe.Closure`
with the finiteness fence retired.  The lattice/addition rows never
read the carrier at all, so they are stated once over an arbitrary
topological carrier `Y` and instantiate to penalties on the general
subprobability carrier (`StatePenalty X`) and on probability directions
(`Penalty X`) alike:

| operation                  | closure theorem     | hypotheses |
| -------------------------- | ------------------- | ---------- |
| `σ + τ`                    | `lsc_add`           | none beyond lsc |
| `σ ⊔ τ` (pointwise max)    | `lsc_sup`           | none beyond lsc |
| `σ ⊓ τ` (pointwise min)    | `lsc_inf`           | none beyond lsc |
| `⨆ i, f i` (arbitrary sup) | `lsc_iSup`          | none beyond lsc |
| `σ ∘ r`, `r` continuous    | `lsc_comp`          | continuity of `r` |
| `tilt g` and `σ + tilt g`  | `continuous_tilt`, `lsc_add` | `g` bounded continuous |
| `wall C`, `C` closed       | `lowerSemicontinuous_wall_iff` (in `General.Faces`) | closedness |

`lsc_comp` is the pullback half of mechanism composition (pull each
component's penalty to the common carrier along a continuous map, then
add by `lsc_add`) — the row the finite table narrates in its
composition comment but never states.

**The tilt delta, documented.**  The finite storey's tilt is the
coordinate-affine expectation `μ ↦ Σ_v c v · μ v` of a score
`c : V → ℝ≥0` — over a finite discrete outcome type *every* score is
automatically bounded and continuous.  At the general carrier the
honest form of the same object is the expectation of a **bounded
continuous** nonnegative score, `ν ↦ ν.testAgainstNN g` for
`g : X →ᵇ ℝ≥0`: bounded continuity is now a real hypothesis, carried by
the bundled type, and it is exactly what narrow continuity of the
expectation consumes (the weak topology is *defined* by these reads).
An unbounded or discontinuous score need not define a narrowly
continuous tilt, so the general row prices what the finite row got for
free.  Both polarities of the carrier get their tilt: `tilt` on
subprobability states, `tiltDir` on probability directions.

The honest boundary is unchanged from the finite storey: arbitrary
pointwise *infima* of citizens need not be citizens; finite minima are
free.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

/-! ## The carrier-free rows -/

section AnyCarrier

variable {Y : Type*} [TopologicalSpace Y]

/-- Composition row, addition half: the sum of two citizens is a
citizen — over any carrier. -/
theorem lsc_add {σ τ : Y → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ + τ) :=
  hσ.add hτ

/-- Conjunction row: the pointwise maximum of two citizens is a
citizen — over any carrier. -/
theorem lsc_sup {σ τ : Y → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ ⊔ τ) :=
  hσ.sup hτ

/-- Disjunction row: the pointwise minimum of two citizens is a citizen
— exactly, with no envelope, over any carrier.  This is the operation
every convexity-flavored citizenship class refuses; the universe's
coproduct is plain `⊓` (see `General.Faces.entails_inf_iff`). -/
theorem lsc_inf {σ τ : Y → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ ⊓ τ) :=
  hσ.inf hτ

/-- Arbitrary suprema of citizens are citizens (sublevels intersect) —
over any carrier; countable suprema are the special case the chapter
names. -/
theorem lsc_iSup {ι : Sort*} {f : ι → Y → ℝ≥0∞}
    (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (⨆ i, f i) := by
  have heq : (⨆ i, f i) = fun ν => ⨆ i, f i ν := funext fun ν => iSup_apply
  rw [heq]
  exact lowerSemicontinuous_iSup h

/-- Composition row, pullback half: the pullback of a citizen along a
continuous map of carriers is a citizen.  Mechanism composition pulls
each component's penalty to the glued carrier along this row and adds
by `lsc_add`. -/
theorem lsc_comp {Z : Type*} [TopologicalSpace Z]
    {σ : Y → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    {r : Z → Y} (hr : Continuous r) : LowerSemicontinuous (σ ∘ r) :=
  hσ.comp hr

end AnyCarrier

/-! ## The tilt rows -/

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- The tilt by a bounded continuous nonnegative score `g`: the
expected score `ν ↦ ∫ g dν`, as a penalty functional on the general
subprobability carrier. -/
noncomputable def tilt (g : X →ᵇ ℝ≥0) : StatePenalty X :=
  fun ν => ((ν : FiniteMeasure X).testAgainstNN g : ℝ≥0∞)

/-- Tilts are narrowly continuous: expectation against a bounded
continuous score is a defining read of the weak topology. -/
theorem continuous_tilt (g : X →ᵇ ℝ≥0) : Continuous (tilt (X := X) g) :=
  ENNReal.continuous_coe.comp
    ((FiniteMeasure.continuous_testAgainstNN_eval g).comp
      SubProbabilityMeasure.continuous_toFiniteMeasure)

/-- Tilt row: tilts are citizens, and tilting a citizen (`σ + tilt g`)
stays a citizen by the composition row `lsc_add`. -/
theorem lsc_tilt (g : X →ᵇ ℝ≥0) : LowerSemicontinuous (tilt (X := X) g) :=
  (continuous_tilt g).lowerSemicontinuous

/-- The tilt on probability directions: the same expectation read on
the spec-side carrier of the radial dictionary. -/
noncomputable def tiltDir (g : X →ᵇ ℝ≥0) : Penalty X :=
  fun μ => ((μ.toFiniteMeasure.testAgainstNN g : ℝ≥0) : ℝ≥0∞)

theorem continuous_tiltDir (g : X →ᵇ ℝ≥0) :
    Continuous (tiltDir (X := X) g) :=
  ENNReal.continuous_coe.comp
    (ProbabilityMeasure.continuous_testAgainstNN_eval g)

theorem lsc_tiltDir (g : X →ᵇ ℝ≥0) :
    LowerSemicontinuous (tiltDir (X := X) g) :=
  (continuous_tiltDir g).lowerSemicontinuous

end SuFunctor.Universe.General
