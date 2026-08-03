import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finsupp.Basic
import DoubleCat.WireSpan

/-! # Penalty functionals on subprobability joints, exact stratum

The scalar stock of the spec-class decoration tier: finitely supported
subprobability joints over an arbitrary carrier, their pushforward along
carrier maps, and penalty functionals — maps from joints to `ℝ≥0∞` — with
their contravariant transport.  This is the exact, measure-free stratum
of the semantic-universe chapter's penalty calculus: partiality (mass
loss) is native, everything is a finite sum, and no topology enters; the
Fell/hyperspace presentation of penalty functionals is a separate layer
(`SuFunctor.Universe`) that this stratum feeds.

Design notes:

* `Joint X` is total in `X` (no finiteness of the carrier): finite
  support does the work, so the decoration tier can be indexed by a base
  whose objects are arbitrary wire sets.
* `Pen.pull` is the *whole* transport story: a penalty pulls back along
  pushforward of joints.  Wire-map covariance of penalty transport (the
  chapter's `h_• f = f ∘ h_♯`) is `pull` along the backward state map;
  cell covariance is `pull` along the backward apex-state map.  Both
  functorialities reduce to `Finsupp.mapDomain`'s.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open scoped NNReal ENNReal

universe u

/-- A finitely supported subprobability joint: nonnegative weights (in
`ℝ≥0`) of total mass at most one.  Mass strictly below one is meaningful
(a joint licensed to lose mass), matching the partiality-native reading
of the denotation tier. -/
structure Joint (X : Type u) : Type u where
  /-- The weight function, finitely supported. -/
  wt : X →₀ ℝ≥0
  /-- Total mass is at most one. -/
  mass_le_one : wt.sum (fun _ v => v) ≤ 1

namespace Joint

variable {X Y Z : Type u}

@[ext] theorem ext {μ ν : Joint X} (h : μ.wt = ν.wt) : μ = ν := by
  cases μ; cases ν; cases h; rfl

/-- The zero joint: all mass lost.  Its existence at every carrier is
what makes several refutation pins below carrier-uniform. -/
def zero (X : Type u) : Joint X :=
  ⟨0, by simp⟩

@[simp] theorem zero_wt (X : Type u) : (zero X).wt = 0 := rfl

/-- Pushforward of a joint along a carrier map: image weights.  Mass is
preserved on the nose (a finite sum reindexed), so subprobability is
preserved. -/
def push (h : X → Y) (μ : Joint X) : Joint Y where
  wt := μ.wt.mapDomain h
  mass_le_one := by
    classical
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact μ.mass_le_one

@[simp] theorem push_wt (h : X → Y) (μ : Joint X) :
    (μ.push h).wt = μ.wt.mapDomain h := rfl

@[simp] theorem push_id (μ : Joint X) : μ.push id = μ :=
  ext Finsupp.mapDomain_id

/-- Pushforward is functorial: the two-step image is the image along the
composite. -/
theorem push_push (h₁ : X → Y) (h₂ : Y → Z) (μ : Joint X) :
    (μ.push h₁).push h₂ = μ.push (h₂ ∘ h₁) :=
  ext Finsupp.mapDomain_comp.symm

end Joint

/-- A penalty functional on joints over a carrier: graded prohibition,
valued in `ℝ≥0∞` — `0` is permitted outright, `⊤` forbidden outright,
intermediate values price partial incompatibility. -/
abbrev Pen (X : Type u) : Type u := Joint X → ℝ≥0∞

namespace Pen

variable {X Y Z : Type u}

/-- Transport of a penalty along a carrier map, contravariantly: evaluate
on the pushforward of the joint.  (Along a *backward* state map this is
the chapter's covariant penalty pushforward along a wire map; along a
backward apex-state map it is the covariant cell transport.) -/
def pull (h : X → Y) (f : Pen Y) : Pen X :=
  fun μ => f (μ.push h)

@[simp] theorem pull_apply (h : X → Y) (f : Pen Y) (μ : Joint X) :
    pull h f μ = f (μ.push h) := rfl

@[simp] theorem pull_id (f : Pen X) : pull id f = f :=
  funext fun μ => congrArg f (Joint.push_id μ)

/-- Contravariant functoriality of penalty transport. -/
theorem pull_pull (h₂ : Y → Z) (h₁ : X → Y) (f : Pen Z) :
    pull h₁ (pull h₂ f) = pull (h₂ ∘ h₁) f :=
  funext fun μ => congrArg f (Joint.push_push h₁ h₂ μ)

@[simp] theorem pull_const (h : X → Y) (c : ℝ≥0∞) :
    pull h (fun _ => c) = fun _ => c := rfl

end Pen

end

end Plain

end SuFunctor
