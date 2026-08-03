import QtslAux.QtslAliases
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Class-stratum alias fixtures, path-sugar family

Four alias rows of the QTSL stratum — `QNegFAlias` (T15) and the sugar
trio `QAvoid` / `QStreettGF` / `QStreettFG` (the former QSugarBatch,
factored 2026-07-26) — in the alias-derivation fixture pattern
(`AliasSmallGain` is the exemplar), at the class stratum's current
state: the elaboration lands on the base rule's **in-repo warrant**
(`QtslAux.QtslAliases`) with computed arguments; the cell plumbing
arrives with the class-stratum presentation.  Per fixture: the alias
structure (premise bound as a proof field), the one-line elaboration
producing the concluded event, the generic gate from the structure's
fields alone, and a concrete instance on `Bool`-valued paths under a
Dirac path measure — computable end to end, with constants that a
polarity or negation mutant cannot survive.

Scope notes carried from the catalogue rows, deliberately:

* `QStreettGF` is **the chart-consuming member**: its identity
  (`sugarGF_denot`) consumes $\mathrm{Fin}(S) = \emptyset$, hard-coded
  here by the total path type `ℕ → S` — exact on total-path (and
  $\dagger$-inside-$V$) charts only; the rewrite direction would be
  unsound on killed-process classes with the cemetery outside the
  region vocabulary.  The hypothesis rides the TYPE in this file;
  wherever the alias is cited over a completed space, it must ride
  explicitly.
* `QStreettFG`'s honest scope is the polarized form
  $\mathsf{FG}\,\neg\beta$ — general $\mathsf{FG}\,\varphi$ is not
  this rule.
* `QAvoid` targets `QSafetyBattery` at the avoid set; its identity is
  `rfl`-grade.
-/

namespace SuFunctor

namespace QtslSem

open MeasureTheory Filter
open Qtsl.Aliases

/-!
## QNegFAlias — $\neg\mathsf{F}_{\le T}\varphi$ from the unbounded
safety kernel

Catalogue T15: child claims the unbounded never-event; concludes the
bounded-horizon never-event at a producer-chosen horizon $T$ — the
computed argument.  Choice-free, no side conditions.  Base lemma:
`Qtsl.Aliases.sound_NegFAlias` (one explicit hypothesis: the child
bound).
-/

/-- A neg-F alias step: the state predicate, the producer-chosen
horizon, the transported bound, the path measure; the proof field
carries the child claim (the unbounded never-event bound). -/
structure NegFAliasStep (S : Type*) [MeasurableSpace S] where
  sat : S → Prop
  T : ℕ
  b : ENNReal
  μ : Measure (ℕ → S)
  premise : b ≤ μ {ω | ∀ n, ¬ sat (ω n)}

/-- The elaboration: the concluded event at the computed horizon —
$\neg\mathsf{F}_{\le T}\varphi$. -/
def NegFAliasStep.negFEvent {S : Type*} [MeasurableSpace S]
    (st : NegFAliasStep S) : Set (ℕ → S) :=
  {ω | ¬ ∃ k ≤ st.T, st.sat (ω k)}

/-- **The generic gate**: the bound transports to the elaborated event,
discharged entirely from the structure's fields (`sound_NegFAlias`
takes one explicit hypothesis; the step form takes none). -/
theorem negFAlias_gate {S : Type*} [MeasurableSpace S]
    (st : NegFAliasStep S) : st.b ≤ st.μ st.negFEvent :=
  sound_NegFAlias st.μ st.premise

namespace NegFDemo

/-- The concrete step: `Bool` states, the all-`false` path under its
Dirac measure, horizon `7`, full mass. -/
noncomputable def step : NegFAliasStep Bool where
  sat s := s = true
  T := 7
  b := 1
  μ := Measure.dirac (fun _ => false)
  premise := by
    refine (Measure.dirac_apply_of_mem ?_).ge
    simp only [Set.mem_setOf_eq]
    intro n
    simp

/-- The concrete face: full mass on the bounded never-event, from the
gate alone. -/
theorem face :
    1 ≤ step.μ {ω | ¬ ∃ k ≤ 7, ω k = true} :=
  negFAlias_gate step

end NegFDemo

/-!
## QAvoid — $\mathsf{avoid}\,\beta := \mathsf{G}\,\neg\beta$

Exact, `rfl`-grade (`sugarAvoid_denot`); target: `QSafetyBattery` at
the avoid set.
-/

/-- An avoid-sugar step: the avoid set, the transported bound, the path
measure; the proof field carries the base claim (the
$\mathsf{G}(\cdot \in B^\complement)$ bound the safety battery
concludes). -/
structure AvoidStep (S : Type*) [MeasurableSpace S] where
  B : Set S
  b : ENNReal
  μ : Measure (ℕ → S)
  premise : b ≤ μ {ω | ∀ n, ω n ∈ Bᶜ}

/-- The elaboration: the sugar's event, $\mathsf{avoid}\,B$. -/
def AvoidStep.avoidEvent {S : Type*} [MeasurableSpace S]
    (st : AvoidStep S) : Set (ℕ → S) :=
  {ω | ∀ n, ω n ∉ st.B}

/-- **The generic gate**: the bound transports across the definitional
identity `sugarAvoid_denot`. -/
theorem avoid_gate {S : Type*} [MeasurableSpace S] (st : AvoidStep S) :
    st.b ≤ st.μ st.avoidEvent := by
  show st.b ≤ st.μ {ω | ∀ n, ω n ∉ st.B}
  rw [sugarAvoid_denot]
  exact st.premise

namespace AvoidDemo

/-- The concrete step: avoid `{true}` along the all-`false` path. -/
noncomputable def step : AvoidStep Bool where
  B := {true}
  b := 1
  μ := Measure.dirac (fun _ => false)
  premise := by
    refine (Measure.dirac_apply_of_mem ?_).ge
    simp only [Set.mem_setOf_eq]
    intro n
    simp

/-- The concrete face: full mass on the avoid event. -/
theorem face : 1 ≤ step.μ {ω | ∀ n, ω n ∉ ({true} : Set Bool)} :=
  avoid_gate step

end AvoidDemo

/-!
## QStreettGF — $\mathsf{GF}\,\varphi := \mathsf{Streett}((\top, \varphi))$

The chart-consuming member (see the module docstring): exact here
because the path type is total.  Target: `QStreettDegenerate`'s bound
statement, without adjustment.
-/

/-- A GF-sugar step: the response set, the transported bound, the path
measure; the proof field carries the degenerate-Streett-pair claim —
the $(\top, G)$ pair's event. -/
structure StreettGFStep (S : Type*) [MeasurableSpace S] where
  G : Set S
  b : ENNReal
  μ : Measure (ℕ → S)
  premise : b ≤ μ {ω | (∃ᶠ n in atTop, ω n ∈ (Set.univ : Set S)) →
    ∃ᶠ n in atTop, ω n ∈ G}

/-- The elaboration: the sugar's event, $\mathsf{GF}\,G$ —
unconditional recurrence. -/
def StreettGFStep.gfEvent {S : Type*} [MeasurableSpace S]
    (st : StreettGFStep S) : Set (ℕ → S) :=
  {ω | ∃ᶠ n in atTop, ω n ∈ st.G}

/-- **The generic gate**: the bound transports across `sugarGF_denot`
(the trivial-request collapse — the $\mathrm{Fin}(S) = \emptyset$
consumption rides the total path type). -/
theorem streettGF_gate {S : Type*} [MeasurableSpace S]
    (st : StreettGFStep S) : st.b ≤ st.μ st.gfEvent := by
  have h : {ω : ℕ → S | (∃ᶠ n in atTop, ω n ∈ (Set.univ : Set S)) →
      ∃ᶠ n in atTop, ω n ∈ st.G} = st.gfEvent :=
    Set.ext fun ω => sugarGF_denot st.G ω
  exact h ▸ st.premise

namespace GFDemo

/-- The concrete step: recur in `{false}` along the all-`false`
path. -/
noncomputable def step : StreettGFStep Bool where
  G := {false}
  b := 1
  μ := Measure.dirac (fun _ => false)
  premise := by
    refine (Measure.dirac_apply_of_mem ?_).ge
    simp only [Set.mem_setOf_eq]
    intro _
    exact (Eventually.of_forall (fun n => by simp)).frequently

/-- The concrete face: full mass on the recurrence event. -/
theorem face :
    1 ≤ step.μ {ω | ∃ᶠ n in atTop, ω n ∈ ({false} : Set Bool)} :=
  streettGF_gate step

end GFDemo

/-!
## QStreettFG — $\mathsf{FG}\,\neg\beta := \mathsf{Streett}((\beta, \bot))$

Pure per-path logic (no conservativity, no chart); honest scope = the
polarized form.  Target: `QStreettBattery` at $(\beta, \bot)$.
-/

/-- An FG-sugar step: the visit set, the transported bound, the path
measure; the proof field carries the $(\beta, \bot)$ Streett-pair
claim — the empty-response event. -/
structure StreettFGStep (S : Type*) [MeasurableSpace S] where
  B : Set S
  b : ENNReal
  μ : Measure (ℕ → S)
  premise : b ≤ μ {ω | (∃ᶠ n in atTop, ω n ∈ B) →
    ∃ᶠ n in atTop, ω n ∈ (∅ : Set S)}

/-- The elaboration: the sugar's event, $\mathsf{FG}(\cdot \notin B)$ —
eventual permanent avoidance. -/
def StreettFGStep.fgEvent {S : Type*} [MeasurableSpace S]
    (st : StreettFGStep S) : Set (ℕ → S) :=
  {ω | ∀ᶠ n in atTop, ω n ∉ st.B}

/-- **The generic gate**: the bound transports across
`sugarFG_denot`. -/
theorem streettFG_gate {S : Type*} [MeasurableSpace S]
    (st : StreettFGStep S) : st.b ≤ st.μ st.fgEvent := by
  have h : {ω : ℕ → S | (∃ᶠ n in atTop, ω n ∈ st.B) →
      ∃ᶠ n in atTop, ω n ∈ (∅ : Set S)} = st.fgEvent :=
    Set.ext fun ω => sugarFG_denot st.B ω
  exact h ▸ st.premise

namespace FGDemo

/-- The concrete step: eventually always outside `{true}`, along the
all-`false` path. -/
noncomputable def step : StreettFGStep Bool where
  B := {true}
  b := 1
  μ := Measure.dirac (fun _ => false)
  premise := by
    refine (Measure.dirac_apply_of_mem ?_).ge
    simp only [Set.mem_setOf_eq]
    intro hfreq
    exact absurd hfreq.exists (by simp)

/-- The concrete face: full mass on the eventual-avoidance event. -/
theorem face :
    1 ≤ step.μ {ω | ∀ᶠ n in atTop, ω n ∉ ({true} : Set Bool)} :=
  streettFG_gate step

end FGDemo

end QtslSem

end SuFunctor
