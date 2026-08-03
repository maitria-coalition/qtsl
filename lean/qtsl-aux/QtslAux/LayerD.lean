import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Kernel.Basic

/-! # Segment models for general stochastic hybrid systems

This module sets up the segment-level interface for reasoning about general
stochastic hybrid systems (GSHS) one inter-jump segment at a time.

* `ExitKind`: how a segment ends — `alarm` (spontaneous jump), `guard` (forced
  jump at a guard), `halt` (terminal), or `live` (the flow never exits).
* `SegmentModel State`: a kernel `seg` sending a start state to a distribution
  over `(dwell time, exit state, ExitKind)` triples, together with a `jump`
  kernel giving the post-exit reset distribution.
* `expWeight θ t = ENNReal.ofReal (exp (θ * t))`, the clock weight, and two
  readouts of a certificate `V` on segment outcomes: `outcomeRead` integrates
  the jump kernel on `alarm` exits but reads `V` at the exit state (before the
  reset) on `guard` and `halt` exits, while `stepRead` integrates the jump
  kernel on both `alarm` and `guard` exits; `live` outcomes read `0` in both.
* `SegmentDynkin M θ V`: the segment-level Dynkin inequality — the
  `expWeight θ`-weighted `outcomeRead` of `V` integrates below `V` at every
  start state. `ForcedNonexpansion M V` asks that resets at guards do not
  increase `V`, and `NonnegV V` is pointwise nonnegativity.
* `iBridge`: the bridge theorem (statement `IBridgeStatement`) —
  `SegmentDynkin` together with `ForcedNonexpansion` yields `D1Conclusion`,
  the same inequality with `stepRead` in place of `outcomeRead`, which is the
  form consumed by the skeleton constructions downstream.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Qtsl.LayerD

inductive ExitKind : Type
  | alarm : ExitKind
  | guard : ExitKind
  | halt : ExitKind
  | live : ExitKind
  deriving DecidableEq

instance : MeasurableSpace ExitKind := ⊤

instance : MeasurableSingletonClass ExitKind := ⟨fun _ => trivial⟩

variable (State : Type*) [MeasurableSpace State]

structure SegmentModel where

  seg : Kernel State (ℝ≥0 × State × ExitKind)

  jump : Kernel (State × ExitKind) State

variable {State}

noncomputable def expWeight (θ : ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * t))

@[simp] lemma expWeight_zero (t : ℝ≥0) : expWeight 0 t = 1 := by
  simp [expWeight]

noncomputable def outcomeRead (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) :
    ℝ≥0 × State × ExitKind → ℝ≥0∞
  | (t, y, ExitKind.alarm) =>
      expWeight θ t * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, ExitKind.alarm))
  | (t, y, ExitKind.guard) => expWeight θ t * ENNReal.ofReal (V y)
  | (t, y, ExitKind.halt) => expWeight θ t * ENNReal.ofReal (V y)
  | (_, _, ExitKind.live) => 0

def SegmentDynkin (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) : Prop :=
  ∀ x : State, ∫⁻ o, outcomeRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x)

def ForcedNonexpansion (M : SegmentModel State) (V : State → ℝ) : Prop :=
  ∀ y : State,
    ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, ExitKind.guard)) ≤ ENNReal.ofReal (V y)

def NonnegV (V : State → ℝ) : Prop :=
  ∀ x : State, 0 ≤ V x

noncomputable def stepRead (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) :
    ℝ≥0 × State × ExitKind → ℝ≥0∞
  | (t, y, k) =>
      match k with
      | ExitKind.halt => expWeight θ t * ENNReal.ofReal (V y)
      | ExitKind.live => 0
      | _ => expWeight θ t * ∫⁻ z, ENNReal.ofReal (V z) ∂(M.jump (y, k))

def D1Conclusion (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) : Prop :=
  ∀ x : State, ∫⁻ o, stepRead M θ V o ∂(M.seg x) ≤ ENNReal.ofReal (V x)

def IBridgeStatement (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) : Prop :=
  SegmentDynkin M θ V → ForcedNonexpansion M V → NonnegV V → D1Conclusion M θ V

theorem iBridge (M : SegmentModel State) (θ : ℝ) (V : State → ℝ) :
    IBridgeStatement M θ V := by
  intro hSegD hForce _hNonneg x
  refine le_trans (lintegral_mono fun o => ?_) (hSegD x)
  rcases o with ⟨t, y, k⟩
  cases k with
  | alarm => exact le_rfl
  | halt => exact le_rfl
  | live => exact le_rfl
  | guard =>
      exact mul_le_mul_right (hForce y) _

end Qtsl.LayerD
