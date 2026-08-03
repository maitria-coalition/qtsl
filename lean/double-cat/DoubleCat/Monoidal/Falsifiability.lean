import DoubleCat.Monoidal.GradedModel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# The falsifiability table for the coherence mixins

Every coherence mixin of `DoubleCat.Monoidal` is refutable: for each of
`M1`–`M11` this file exhibits a braided (indeed symmetric-base) monoidal
double category satisfying all the *data-level* laws
(`MonoidalDoubleCategory`, `BraidedDoubleCategory` — these hold in every
graded model, by `DoubleCat.Monoidal.GradedModel`) in which that mixin
fails.  A mixin that were derivable from the data-level laws would have
no such model; a mixin definition that were accidentally vacuous would be
refuted by nothing.  All witnesses are graded models, so each row is a
weight record together with `decide`- or `ring`-checked arithmetic
through the linearization lemmas (`m1Pentagon_iff` …).

The rows come in two tiers.

* **Independence rows** (`M2`, `M4`, `M6`; `M9` is the standalone witness
  of `DoubleCat.Monoidal.GradedCounterexample`): the failing mixin is
  refuted while *every other* mixin is satisfied, so the mixin is not
  derivable from the data-level laws together with all the other mixins.
  The `M4` row: the interchanger weight `δc` in the *tensor* pairing
  (`c(x, y) = x²y²`) satisfies everything — including the
  associator–interchanger axiom `M9` — except interchanger associativity.
  It is the exact mirror of the `M9` witness (`δc` in the *composition*
  pairing), and the two failures are numerically mirror images.

* **Falsifiability rows** (`M1`, `M3`, `M5`, `M7`, `M10`, `M11a`,
  `M11b`): the mixin is refuted relative to the data-level laws only;
  co-failures among the other mixins occur.  One-vs-rest witnesses for
  these families cannot exist among graded models: in the linearized
  functional-equation system each of them lies in the span of the
  remaining families (exact linear algebra over the finite configurations
  `G = ZMod 2, ZMod 3` with weights in `𝔽₂, 𝔽₃, 𝔽₅`), so any graded
  one-vs-rest candidate is excluded — a genuinely nonlinear model would
  be required.  For `M3` the three component equations are refuted
  separately: each of the two hexagons and involutivity has content of
  its own (the involutivity row satisfies both hexagons and fails
  involutivity alone).
-/

namespace CategoryTheory

namespace MonoidalDoubleCategory

namespace Graded

open PseudoDoubleCategoryStruct MonoidalDoubleCategoryStruct

/-- The all-zero weight record: the strict graded model. -/
def Weights.zero (G A : Type) [AddCommGroup G] [AddCommGroup A] :
    Weights G A where
  chi _ _ _ _ := 0
  mu := 0
  assoc _ _ _ := 0
  lunit _ := 0
  runit _ := 0
  braid _ _ := 0

/-- The coboundary of `c(x, y) = x²y²` in the *tensor* pairing — the mirror
of the composition-pairing coboundary of
`DoubleCat.Monoidal.GradedCounterexample`. -/
def gWTensor (s t s' t' : ℤ) : ℤ :=
  s ^ 2 * t ^ 2 + s' ^ 2 * t' ^ 2 - (s + s') ^ 2 * (t + t') ^ 2

/-- The `M4` independence row: interchanger weight `gWTensor`, all else zero. -/
def tensorCoboundary : Weights ℤ ℤ :=
  { Weights.zero ℤ ℤ with chi := gWTensor }

instance : M1Pentagon (WPt tensorCoboundary) :=
  (m1Pentagon_iff _).mpr (by intros; simp [tensorCoboundary, Weights.zero])

instance : M2Triangle (WPt tensorCoboundary) :=
  (m2Triangle_iff _).mpr (by intros; simp [tensorCoboundary, Weights.zero])

instance : M3Hexagons (WPt tensorCoboundary) :=
  (m3Hexagons_iff _).mpr
    ⟨by intros; simp [tensorCoboundary, Weights.zero],
     by intros; simp [tensorCoboundary, Weights.zero],
     by intros; simp [tensorCoboundary, Weights.zero]⟩

instance : M5InterchangerUnit (WPt tensorCoboundary) :=
  (m5InterchangerUnit_iff _).mpr
    ⟨by intros; simp [tensorCoboundary, Weights.zero, gWTensor],
     by intros; simp [tensorCoboundary, Weights.zero, gWTensor]⟩

instance : M6BraidingInterchanger (WPt tensorCoboundary) :=
  (m6BraidingInterchanger_iff _).mpr
    (by intros; simp [tensorCoboundary, Weights.zero, gWTensor]; ring)

instance : M7UnitorUnit (WPt tensorCoboundary) :=
  (m7UnitorUnit_iff _).mpr
    ⟨by simp [tensorCoboundary, Weights.zero],
     by simp [tensorCoboundary, Weights.zero]⟩

instance : M9AssociatorInterchanger (WPt tensorCoboundary) :=
  (m9AssociatorInterchanger_iff _).mpr
    (by intros; simp [tensorCoboundary, Weights.zero, gWTensor]; ring)

instance : M10UnitorInterchanger (WPt tensorCoboundary) :=
  (m10UnitorInterchanger_iff _).mpr
    ⟨by intros; simp [tensorCoboundary, Weights.zero, gWTensor],
     by intros; simp [tensorCoboundary, Weights.zero, gWTensor]⟩

instance : M11aAssociatorUnit (WPt tensorCoboundary) :=
  (m11aAssociatorUnit_iff _).mpr (by simp [tensorCoboundary, Weights.zero])

instance : M11bBraidingUnit (WPt tensorCoboundary) :=
  (m11bBraidingUnit_iff _).mpr (by simp [tensorCoboundary, Weights.zero])

/-- `M4` fails in the `tensorCoboundary` model while every other mixin holds:
interchanger associativity is independent of the rest. -/
theorem not_m4InterchangerAssoc :
    ¬ M4InterchangerAssoc (WPt tensorCoboundary) := by
  intro h
  have e := (m4InterchangerAssoc_iff tensorCoboundary).mp h 1 1 2 1 1 2
  norm_num [tensorCoboundary, Weights.zero, gWTensor] at e

/-- The `M2` independence row. -/
def triangleBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with assoc := fun m _ p => m + p }

instance : M1Pentagon (WPt triangleBreaker) :=
  (m1Pentagon_iff _).mpr (by decide)

instance : M3Hexagons (WPt triangleBreaker) :=
  (m3Hexagons_iff _).mpr (by refine ⟨?_, ?_, ?_⟩ <;> decide)

instance : M4InterchangerAssoc (WPt triangleBreaker) :=
  (m4InterchangerAssoc_iff _).mpr (by decide)

instance : M5InterchangerUnit (WPt triangleBreaker) :=
  (m5InterchangerUnit_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M6BraidingInterchanger (WPt triangleBreaker) :=
  (m6BraidingInterchanger_iff _).mpr (by decide)

instance : M7UnitorUnit (WPt triangleBreaker) :=
  (m7UnitorUnit_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M9AssociatorInterchanger (WPt triangleBreaker) :=
  (m9AssociatorInterchanger_iff _).mpr (by decide)

instance : M10UnitorInterchanger (WPt triangleBreaker) :=
  (m10UnitorInterchanger_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M11aAssociatorUnit (WPt triangleBreaker) :=
  (m11aAssociatorUnit_iff _).mpr (by decide)

instance : M11bBraidingUnit (WPt triangleBreaker) :=
  (m11bBraidingUnit_iff _).mpr (by decide)

/-- `M2` fails in the `triangleBreaker` model while every other mixin holds. -/
theorem not_m2Triangle : ¬ M2Triangle (WPt triangleBreaker) :=
  fun h => absurd ((m2Triangle_iff _).mp h) (by decide)

/-- The `M6` independence row. -/
def braidingBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with braid := fun m n => m * n }

instance : M1Pentagon (WPt braidingBreaker) :=
  (m1Pentagon_iff _).mpr (by decide)

instance : M2Triangle (WPt braidingBreaker) :=
  (m2Triangle_iff _).mpr (by decide)

instance : M3Hexagons (WPt braidingBreaker) :=
  (m3Hexagons_iff _).mpr (by refine ⟨?_, ?_, ?_⟩ <;> decide)

instance : M4InterchangerAssoc (WPt braidingBreaker) :=
  (m4InterchangerAssoc_iff _).mpr (by decide)

instance : M5InterchangerUnit (WPt braidingBreaker) :=
  (m5InterchangerUnit_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M7UnitorUnit (WPt braidingBreaker) :=
  (m7UnitorUnit_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M9AssociatorInterchanger (WPt braidingBreaker) :=
  (m9AssociatorInterchanger_iff _).mpr (by decide)

instance : M10UnitorInterchanger (WPt braidingBreaker) :=
  (m10UnitorInterchanger_iff _).mpr (by refine ⟨?_, ?_⟩ <;> decide)

instance : M11aAssociatorUnit (WPt braidingBreaker) :=
  (m11aAssociatorUnit_iff _).mpr (by decide)

instance : M11bBraidingUnit (WPt braidingBreaker) :=
  (m11bBraidingUnit_iff _).mpr (by decide)

/-- `M6` fails in the `braidingBreaker` model while every other mixin holds. -/
theorem not_m6BraidingInterchanger :
    ¬ M6BraidingInterchanger (WPt braidingBreaker) :=
  fun h => absurd ((m6BraidingInterchanger_iff _).mp h) (by decide)

/-- The `M1` falsifiability row. -/
def pentagonBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with assoc := fun m n _ => m * n }

/-- `M1` fails in the `pentagonBreaker` model. -/
theorem not_m1Pentagon : ¬ M1Pentagon (WPt pentagonBreaker) :=
  fun h => absurd ((m1Pentagon_iff _).mp h) (by decide)

/-- Falsifiability row for the forward hexagon of `M3`. -/
def hexagonForwardBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with braid := fun m _ => m }

/-- The forward hexagon of `M3` fails in the `hexagonForwardBreaker` model. -/
theorem not_m3_hexagonForward : ¬ M3Hexagons (WPt hexagonForwardBreaker) :=
  fun h => absurd ((m3Hexagons_iff _).mp h).1 (by decide)

/-- Falsifiability row for the reverse hexagon of `M3`. -/
def hexagonReverseBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with braid := fun _ n => n }

/-- The reverse hexagon of `M3` fails in the `hexagonReverseBreaker` model. -/
theorem not_m3_hexagonReverse : ¬ M3Hexagons (WPt hexagonReverseBreaker) :=
  fun h => absurd ((m3Hexagons_iff _).mp h).2.1 (by decide)

/-- Falsifiability row for the involutivity clause of `M3`: this model
satisfies both hexagons and fails involutivity alone. -/
def involutivityBreaker : Weights (ZMod 3) (ZMod 3) :=
  { Weights.zero (ZMod 3) (ZMod 3) with braid := fun m n => m * n }

/-- Involutivity fails in the `involutivityBreaker` model. -/
theorem not_m3_involutive : ¬ M3Hexagons (WPt involutivityBreaker) :=
  fun h => absurd ((m3Hexagons_iff _).mp h).2.2 (by decide)

/-- Falsifiability row for `M5` and `M7` (a nonzero `mu` weight). -/
def muBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with mu := 1 }

/-- `M5` fails in the `muBreaker` model. -/
theorem not_m5InterchangerUnit : ¬ M5InterchangerUnit (WPt muBreaker) :=
  fun h => absurd ((m5InterchangerUnit_iff _).mp h).1 (by decide)

/-- `M7` fails in the `muBreaker` model. -/
theorem not_m7UnitorUnit : ¬ M7UnitorUnit (WPt muBreaker) :=
  fun h => absurd ((m7UnitorUnit_iff _).mp h).1 (by decide)

/-- Falsifiability row for `M10` (a constant nonzero `chi` weight). -/
def chiConstBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with chi := fun _ _ _ _ => 1 }

/-- `M10` fails in the `chiConstBreaker` model. -/
theorem not_m10UnitorInterchanger :
    ¬ M10UnitorInterchanger (WPt chiConstBreaker) :=
  fun h => absurd ((m10UnitorInterchanger_iff _).mp h).1 (by decide)

/-- Falsifiability row for `M11a`. -/
def assocUnitBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with
      assoc := fun m n p => (m + 1) * (n + 1) * (p + 1) }

/-- `M11a` fails in the `assocUnitBreaker` model. -/
theorem not_m11aAssociatorUnit :
    ¬ M11aAssociatorUnit (WPt assocUnitBreaker) :=
  fun h => absurd ((m11aAssociatorUnit_iff _).mp h) (by decide)

/-- Falsifiability row for `M11b`. -/
def braidUnitBreaker : Weights (ZMod 2) (ZMod 2) :=
  { Weights.zero (ZMod 2) (ZMod 2) with braid := fun _ _ => 1 }

/-- `M11b` fails in the `braidUnitBreaker` model. -/
theorem not_m11bBraidingUnit :
    ¬ M11bBraidingUnit (WPt braidUnitBreaker) :=
  fun h => absurd ((m11bBraidingUnit_iff _).mp h) (by decide)

end Graded

end MonoidalDoubleCategory

end CategoryTheory
