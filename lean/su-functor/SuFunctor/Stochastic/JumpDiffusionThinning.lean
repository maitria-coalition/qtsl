import SuFunctor.Stochastic.JumpMeasure
import QtslAux.JumpDiffusion

/-! # The jump-diffusion jump structure in tagged normal form

The landed multi-leg jump-diffusion generator
(`Qtsl.JumpDiffusion.generator`) carries its jump structure in a
legacy encoding: per-leg rates with *sub-stochastic* reset mixtures —
the deficit read as killing by convention (`transferSum_sub_self`,
Davis's convention) — plus a separate standalone killing field.  Two
renderings of one semantic object.

This module recovers that entire content in the **tagged normal
form**: mixtures into the one-step alphabet
`Step X = next X | stay | cemetery`
(`SuFunctor.Stochastic.Step`), where killing is an explicit cemetery
*outcome* and every mixture has weight sum exactly one.

* `stepMixGenerator` — the generator contribution of a weighted
  mixture of tagged one-step maps: next legs pair increments, a
  cemetery leg pays the killing term, stay legs are invisible.
* `deficitToCemetery` — **the deficit-is-killing thinning move**: keep
  each reset map as a next leg, add one cemetery leg carrying the
  deficit.  Its weight sum is exactly one, *unconditionally*
  (`weightSum_deficitToCemetery`); under the landed per-leg validity
  rows (weights nonnegative, sum at most one) the rewritten mixture is
  a genuine probability mixture (`deficitToCemetery_weights_nonneg`).
* `stepMixGenerator_deficitToCemetery` — **the move is sound**: the
  tagged generator of the rewrite equals the legacy transfer increment
  `T_μ V - V`.  The landed `transferSum_sub_self` is consumed as
  exactly this soundness fact.
* `generator_eq_stepMix` — **the recovery**: the full multi-leg
  generator equals its drift/diffusion part plus rate-weighted tagged
  generators of mass-one mixtures — the per-leg rewrites for the jump
  legs, one pure-cemetery mixture for the killing field.  Nothing
  sub-stochastic remains; the legacy encoding's semantic content is
  exactly the tagged normal form's.
-/

namespace SuFunctor.Stochastic

open Qtsl.JumpDiffusion

variable {X : Type*}

/-! ## Tagged one-step mixtures and their generator -/

/-- A finite weighted mixture of tagged one-step maps. -/
abbrev StepMixture (X : Type*) := List (ℝ × (X → Step X))

/-- The generator increment of one tagged outcome: a next state pairs
the observable increment, stay is invisible, the cemetery pays the
observable itself. -/
noncomputable def stepIncrement (f : X → ℝ) (x : X) : Step X → ℝ
  | .next y => f y - f x
  | .stay => 0
  | .cemetery => -(f x)

@[simp] theorem stepIncrement_next (f : X → ℝ) (x y : X) :
    stepIncrement f x (.next y) = f y - f x := rfl
@[simp] theorem stepIncrement_stay (f : X → ℝ) (x : X) :
    stepIncrement f x .stay = 0 := rfl
@[simp] theorem stepIncrement_cemetery (f : X → ℝ) (x : X) :
    stepIncrement f x .cemetery = -(f x) := rfl

/-- The generator contribution of a tagged mixture: the weighted sum
of tagged increments. -/
noncomputable def stepMixGenerator (κ : StepMixture X) (f : X → ℝ)
    (x : X) : ℝ :=
  (κ.map fun wg => wg.1 * stepIncrement f x (wg.2 x)).sum

@[simp] theorem stepMixGenerator_nil (f : X → ℝ) (x : X) :
    stepMixGenerator ([] : StepMixture X) f x = 0 := rfl

@[simp] theorem stepMixGenerator_cons (wg : ℝ × (X → Step X))
    (κ : StepMixture X) (f : X → ℝ) (x : X) :
    stepMixGenerator (wg :: κ) f x
      = wg.1 * stepIncrement f x (wg.2 x) + stepMixGenerator κ f x := by
  simp [stepMixGenerator]

theorem stepMixGenerator_append (κ₁ κ₂ : StepMixture X) (f : X → ℝ)
    (x : X) :
    stepMixGenerator (κ₁ ++ κ₂) f x
      = stepMixGenerator κ₁ f x + stepMixGenerator κ₂ f x := by
  simp [stepMixGenerator]

/-- The weight sum of a weighted list. -/
noncomputable def weightSum {α : Type*} (μ : List (ℝ × α)) : ℝ :=
  (μ.map fun wg => wg.1).sum

@[simp] theorem weightSum_nil {α : Type*} :
    weightSum ([] : List (ℝ × α)) = 0 := rfl

@[simp] theorem weightSum_cons {α : Type*} (wg : ℝ × α)
    (μ : List (ℝ × α)) :
    weightSum (wg :: μ) = wg.1 + weightSum μ := by
  simp [weightSum]

theorem weightSum_append {α : Type*} (μ₁ μ₂ : List (ℝ × α)) :
    weightSum (μ₁ ++ μ₂) = weightSum μ₁ + weightSum μ₂ := by
  simp [weightSum]

/-! ## The deficit-is-killing thinning move -/

variable {n m : ℕ}

open Qtsl.SdeGenerator (State)

/-- The deficit→cemetery rewrite of a reset mixture: each reset map
becomes a next leg; one cemetery leg carries the deficit. -/
noncomputable def deficitToCemetery (μ : MixtureR n) :
    StepMixture (State n) :=
  (μ.map fun wg => (wg.1, fun z => Step.next (wg.2 z)))
    ++ [(1 - weightSum μ, fun _ => Step.cemetery)]

/-- The rewritten mixture has weight sum exactly one,
*unconditionally*: mass bookkeeping is explicit by construction. -/
theorem weightSum_deficitToCemetery (μ : MixtureR n) :
    weightSum (deficitToCemetery μ) = 1 := by
  unfold deficitToCemetery
  rw [weightSum_append]
  have hmap : weightSum (μ.map fun wg => (wg.1, fun z => Step.next (wg.2 z)))
      = weightSum μ := by
    simp [weightSum, List.map_map, Function.comp_def]
  rw [hmap]
  simp

/-- Under the landed per-leg validity rows — weights nonnegative, sum
at most one — the rewritten mixture is a genuine probability mixture:
every weight, including the cemetery leg's deficit, is nonnegative. -/
theorem deficitToCemetery_weights_nonneg (μ : MixtureR n)
    (hw : ∀ wg ∈ μ, 0 ≤ wg.1) (hs : weightSum μ ≤ 1) :
    ∀ wg ∈ deficitToCemetery μ, 0 ≤ wg.1 := by
  intro wg hwg
  rcases List.mem_append.mp hwg with hmem | hmem
  · obtain ⟨wg', hwg', rfl⟩ := List.mem_map.mp hmem
    exact hw wg' hwg'
  · rw [List.mem_singleton.mp hmem]
    simpa using sub_nonneg.mpr hs

/-- **The thinning move is sound**: the tagged generator of the
deficit→cemetery rewrite is the legacy transfer increment.  The
landed decomposition `transferSum_sub_self` — a sub-stochastic
mixture's increment is Dirac increments minus the deficit spent as
killing — is consumed as exactly this fact: Davis's convention,
re-derived as the soundness of one rewrite. -/
theorem stepMixGenerator_deficitToCemetery (μ : MixtureR n)
    (f : State n → ℝ) (z : State n) :
    stepMixGenerator (deficitToCemetery μ) f z
      = transferSum μ f z - f z := by
  rw [transferSum_sub_self]
  unfold deficitToCemetery
  rw [stepMixGenerator_append]
  have hlegs : stepMixGenerator
      (μ.map fun wg => (wg.1, fun z => Step.next (wg.2 z))) f z
      = (μ.map fun wg => wg.1 * (f (wg.2 z) - f z)).sum := by
    simp [stepMixGenerator, List.map_map, Function.comp_def]
  have hcem : stepMixGenerator
      ([(1 - weightSum μ, fun _ => Step.cemetery)] : StepMixture (State n))
      f z = -((1 - weightSum μ) * f z) := by
    simp [stepMixGenerator]
  rw [hlegs, hcem]
  unfold weightSum
  ring

/-- The killing field as a tagged mixture: one cemetery leg of weight
one — a mass-one mixture, trivially. -/
noncomputable def killMixture (n : ℕ) : StepMixture (State n) :=
  [(1, fun _ => Step.cemetery)]

@[simp] theorem weightSum_killMixture :
    weightSum (killMixture n) = 1 := by
  simp [killMixture]

theorem stepMixGenerator_killMixture (f : State n → ℝ) (z : State n) :
    stepMixGenerator (killMixture n) f z = -(f z) := by
  simp [killMixture, stepMixGenerator]

/-! ## The recovery: the legacy encoding's content, in tagged form -/

/-- **The multi-leg generator, recovered over the tagged alphabet**:
drift and diffusion unchanged, and the entire jump structure — the
sub-stochastic reset legs *and* the standalone killing field — as
rate-weighted tagged generators of weight-sum-one mixtures.  The
legacy encoding stores nothing the tagged normal form does not
express; killing is an outcome, deficits do not exist. -/
theorem generator_eq_stepMix (P : JdProfile n m) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) :
    Qtsl.JumpDiffusion.generator P V gradV hessV z
      = (∑ i, gradV z i * P.f z i)
        + (1 / 2) * (∑ i, ∑ j, P.gram z i j * hessV z i j)
        + P.kill z * stepMixGenerator (killMixture n) V z
        + (P.legs.map fun lm =>
            lm.1 z * stepMixGenerator (deficitToCemetery lm.2) V z).sum := by
  unfold Qtsl.JumpDiffusion.generator
  rw [stepMixGenerator_killMixture]
  have hlegs : (P.legs.map fun lm =>
        lm.1 z * stepMixGenerator (deficitToCemetery lm.2) V z).sum
      = (P.legs.map fun lm =>
          lm.1 z * (transferSum lm.2 V z - V z)).sum := by
    refine congrArg List.sum (List.map_congr_left fun lm _ => ?_)
    rw [stepMixGenerator_deficitToCemetery]
  rw [hlegs]
  ring

end SuFunctor.Stochastic

#print axioms SuFunctor.Stochastic.weightSum_deficitToCemetery
#print axioms SuFunctor.Stochastic.deficitToCemetery_weights_nonneg
#print axioms SuFunctor.Stochastic.stepMixGenerator_deficitToCemetery
#print axioms SuFunctor.Stochastic.generator_eq_stepMix
