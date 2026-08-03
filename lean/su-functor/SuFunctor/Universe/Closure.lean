import SuFunctor.Universe.Carrier

/-! # The closure table: the universe is closed under the calculus's operations

The operations the calculus owns, as citizenship-closure theorems.  Each
theorem is one row of the operations table; the point of the table is
that **lower semicontinuity survives every operation the semantics
needs, including the two that no convexity-flavored class survives
together** (addition and pointwise minimum):

| operation                     | closure theorem            | role |
| ----------------------------- | -------------------------- | ---- |
| `σ + τ`                       | `lsc_add`                  | mechanism composition (pull to a common carrier, add) |
| `σ ⊔ τ` (pointwise max)       | `lsc_sup`                  | conjunction — the categorical product in the entailment order |
| `σ ⊓ τ` (pointwise min)       | `lsc_inf`                  | disjunction — the categorical coproduct, **exact**: no envelope, no hull (see `SuFunctor.Universe.Judgment`) |
| `⨆ i, f i` (arbitrary sup)    | `lsc_iSup`                 | arbitrary conjunction; also the closure that builds envelopes |
| `tilt c` and `σ + tilt c`     | `continuous_tilt`, `lsc_add` | pricing/reward tilts: expectations of nonnegative scores are continuous, hence citizens; tilting is addition of a continuous penalty |
| `wall C`, `C` closed          | `lowerSemicontinuous_wall_iff` (in `Carrier`) | crisp claims, convexity *not* required |

The honest boundary: arbitrary pointwise *infima* of citizens need not
be citizens (a decreasing sequence of walls on shrinking closed sets can
converge to the wall of a non-closed set); finite minima — the
disjunctions the calculus asks for — are free.  On the finite-`V`
stratum no compactness side conditions appear anywhere in this table.
-/

namespace SuFunctor.Universe

open scoped ENNReal NNReal

variable {V : Type*} [Fintype V]

/-- Composition row: the sum of two citizens is a citizen.  (Mechanism
composition pulls each component's penalty to the glued carrier and
adds; the pullback of a citizen along a continuous map is a citizen, and
this is the addition half.) -/
theorem lsc_add {σ τ : Penalty V} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ + τ) :=
  hσ.add hτ

/-- Conjunction row: the pointwise maximum of two citizens is a citizen.
This is the categorical product in the entailment order (see
`sat_sup_iff`). -/
theorem lsc_sup {σ τ : Penalty V} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ ⊔ τ) :=
  hσ.sup hτ

/-- Disjunction row: the pointwise minimum of two citizens is a citizen —
**exactly**, with no envelope.  A sublevel of the minimum is the union of
the two sublevels, a finite union of closed sets; this is the operation
every convexity-flavored citizenship class refuses, and the reason the
universe's coproduct is plain `⊓` (see `entails_inf_iff`). -/
theorem lsc_inf {σ τ : Penalty V} (hσ : LowerSemicontinuous σ)
    (hτ : LowerSemicontinuous τ) : LowerSemicontinuous (σ ⊓ τ) :=
  hσ.inf hτ

/-- Arbitrary suprema of citizens are citizens (sublevels intersect). -/
theorem lsc_iSup {ι : Sort*} {f : ι → Penalty V}
    (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (⨆ i, f i) := by
  have heq : (⨆ i, f i) = fun μ => ⨆ i, f i μ := funext fun μ => iSup_apply
  rw [heq]
  exact lowerSemicontinuous_iSup h

/-- The tilt by a nonnegative score `c`: the expected score
`μ ↦ Σ_v c v · μ v`, as a penalty functional. -/
noncomputable def tilt (c : V → ℝ≥0) : Penalty V :=
  fun μ => ∑ v, (c v : ℝ≥0∞) * ENNReal.ofReal ((μ : V → ℝ) v)

/-- Tilts are continuous (finite sums of continuous coordinate reads). -/
theorem continuous_tilt (c : V → ℝ≥0) : Continuous (tilt (V := V) c) := by
  refine continuous_finsetSum _ fun v _ => ?_
  have h1 : Continuous fun μ : BelState V => (μ : V → ℝ) v :=
    (continuous_apply v).comp continuous_subtype_val
  have h2 : Continuous fun μ : BelState V => ENNReal.ofReal ((μ : V → ℝ) v) :=
    ENNReal.continuous_ofReal.comp h1
  exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp h2

/-- Tilt row: tilts are citizens, and tilting a citizen (`σ + tilt c`)
stays a citizen by the composition row. -/
theorem lsc_tilt (c : V → ℝ≥0) : LowerSemicontinuous (tilt (V := V) c) :=
  (continuous_tilt c).lowerSemicontinuous

/-! ## Wall algebra

On walls, conjunction is intersection and disjunction is union —
**verbatim**, with no hull: the crisp fragment of the universe is closed
under both lattice operations, and the union wall is the exact
disjunction (compare the rational stratum's
`SuFunctor.specPenaltyConj_le_iff`, where conjunction-as-join is the
same fact for finite conjunctions of judgment walls). -/

theorem wall_sup_wall (C D : Set (BelState V)) :
    wall C ⊔ wall D = wall (C ∩ D) := by
  funext μ
  by_cases hC : μ ∈ C <;> by_cases hD : μ ∈ D <;>
    simp [Pi.sup_apply, wall, hC, hD]

theorem wall_inf_wall (C D : Set (BelState V)) :
    wall C ⊓ wall D = wall (C ∪ D) := by
  funext μ
  by_cases hC : μ ∈ C <;> by_cases hD : μ ∈ D <;>
    simp [Pi.inf_apply, wall, hC, hD]

end SuFunctor.Universe
