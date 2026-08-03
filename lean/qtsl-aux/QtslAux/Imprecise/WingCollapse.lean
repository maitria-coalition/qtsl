import QtslAux.Imprecise.PenaltyKernelCompose

/-! # The wing collapse: durations are imprecise kernels like everything else

A timed transition's dwell is a one-dimensional kernel into a duration
carrier — so the classical clock taxonomy (forced delay, demonic window,
stochastic race, carved window) is not a family of primitive constructors
but **four presentations of one penalty-kernel discipline applied to the
duration coordinate**.  This module states the collapse at the finite
stratum (any finite linear order as time grid; the continuous-time meter-law
adequacy is deliberately out of scope here and named as the owed proof in
the design record):

* `PrevEq` — prevision equivalence of presentations: same upper prevision on
  every gamble (`PrevEq.lower`: the lower face follows by conjugacy).
  Presentations are data; `PrevEq` is the semantic quotient at which the
  taxonomy dissolves.
* The four wings as penalty families: `wingForced` (Dirac point),
  `wingDemonic` (vacuous over the up-set), `wingRace` (an arbitrary precise
  law — the stochastic face; a particular quantile shape is a modelling
  choice one level up), `wingCarved` (vacuous over a window), and
  `wingCarvedGraded` (a *soft* window: costs on the window family — "firing
  early is expensive" costs no new machinery, it is a cost vector).
* **Collapse theorems**: `wingForced_eq_wingRace_dirac` (definitional);
  `wingCarved_point_prevEq_forced` (degenerate window = forced);
  `wingCarved_full_prevEq_demonic` (unbounded window = demonic).  The carved
  window is thereby *regenerated as a named degenerate* of the kernel
  discipline rather than carved as a separate former.
* **Polarity**: `wingDemonic_penUpperE`/`wingDemonic_penLowerE` — the
  angelic (∃ over the window) and demonic (∀ over the window) liveness faces
  read the same wing at the two envelopes; one datum, two quantifiers.

Composition of dwell with the marking kernel is `Imprecise.
PenaltyKernelCompose`: per-consultation freshness (penalties integrating
along the record) is the composition's definition, and the once-drawn
crystal is its named, strictly different sibling.
-/

namespace Qtsl.Imprecise

open Finset

section PrevEqDef

variable {X : Type*} [Fintype X]

/-- Prevision equivalence of penalty presentations: the same upper prevision
on every gamble.  The semantic quotient of presentation space. -/
def PrevEq {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (M : ι → FinPMF X) (c : ι → ℚ) (N : κ → FinPMF X) (e : κ → ℚ) : Prop :=
  ∀ f : X → ℚ, penUpperE M c f = penUpperE N e f

/-- Upper-prevision equivalence carries the lower face with it, by
conjugacy: one quotient, both envelopes. -/
theorem PrevEq.lower {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    {M : ι → FinPMF X} {c : ι → ℚ} {N : κ → FinPMF X} {e : κ → ℚ}
    (h : PrevEq M c N e) (f : X → ℚ) :
    penLowerE M c f = penLowerE N e f := by
  have h1 := h fun x => -f x
  rw [penUpperE_eq_neg_penLowerE_neg M c, penUpperE_eq_neg_penLowerE_neg N e]
    at h1
  have hM : penLowerE M c (fun x => - -f x) = penLowerE M c f :=
    penLowerE_congr fun x => neg_neg (f x)
  have hN : penLowerE N e (fun x => - -f x) = penLowerE N e f :=
    penLowerE_congr fun x => neg_neg (f x)
  rw [hM, hN] at h1
  linarith

end PrevEqDef

section Wings

variable {T : Type*} [Fintype T] [LinearOrder T]

/-- The stochastic face: a precise dwell law (one-member family).  Which
law — exponential quantile, discretized hazard — is a modelling choice one
level up; the wing is just precision. -/
def wingRace (μ : FinPMF T) : Unit → FinPMF T := fun _ => μ

/-- The forced delay: the Dirac point law. -/
def wingForced (d : T) : Unit → FinPMF T := fun _ => FinPMF.dirac d

/-- The demonic window: vacuous (zero-cost) over the up-set `d ≤ t` —
any dwell law supported there, presented by its Dirac extreme points. -/
def wingDemonic (d : T) : {t : T // d ≤ t} → FinPMF T :=
  fun t => FinPMF.dirac t.val

/-- The carved window: vacuous over `lo ≤ t ≤ hi`. -/
def wingCarved (lo hi : T) : {t : T // lo ≤ t ∧ t ≤ hi} → FinPMF T :=
  fun t => FinPMF.dirac t.val

instance instNonemptyUpSet (d : T) : Nonempty {t : T // d ≤ t} :=
  ⟨⟨d, le_rfl⟩⟩

omit [Fintype T] in
/-- A window with attainable ends is inhabited. -/
theorem carvedNonempty {lo hi : T} (h : lo ≤ hi) :
    Nonempty {t : T // lo ≤ t ∧ t ≤ hi} :=
  ⟨⟨lo, le_rfl, h⟩⟩

omit [LinearOrder T] in
/-- The race wing prices by its one law: precision, at the prevision level. -/
theorem wingRace_penUpperE (μ : FinPMF T) (f : T → ℚ) :
    penUpperE (wingRace μ) 0 f = μ.exp f := by
  rw [penUpperE_unique]
  simp [wingRace]

/-- The forced wing prices at the point. -/
theorem wingForced_penUpperE (d : T) (f : T → ℚ) :
    penUpperE (wingForced d) 0 f = f d := by
  rw [penUpperE_unique]
  simp [wingForced]

/-- The **angelic face** of the demonic window: the upper envelope is the
max over the up-set (∃ a dwell in the window achieving the gamble). -/
theorem wingDemonic_penUpperE (d : T) (f : T → ℚ) :
    penUpperE (wingDemonic d) 0 f
      = univ.sup' univ_nonempty fun t : {t : T // d ≤ t} => f t.val := by
  unfold penUpperE wingDemonic
  exact Finset.sup'_congr _ rfl fun t _ => by simp

/-- The **demonic face** of the same window: the lower envelope is the min
over the up-set (∀ dwells in the window).  One datum, two quantifiers —
the two liveness polarities read one wing at the two envelopes. -/
theorem wingDemonic_penLowerE (d : T) (f : T → ℚ) :
    penLowerE (wingDemonic d) 0 f
      = univ.inf' univ_nonempty fun t : {t : T // d ≤ t} => f t.val := by
  unfold penLowerE wingDemonic
  exact Finset.inf'_congr _ rfl fun t _ => by simp

/-- The soft window: graded costs on the window family — "firing early is
expensive" is a cost vector, not new machinery. -/
theorem wingCarvedGraded_penUpperE (lo hi : T)
    [Nonempty {t : T // lo ≤ t ∧ t ≤ hi}]
    (w : {t : T // lo ≤ t ∧ t ≤ hi} → ℚ) (f : T → ℚ) :
    penUpperE (wingCarved lo hi) w f
      = univ.sup' univ_nonempty
          fun t : {t : T // lo ≤ t ∧ t ≤ hi} => f t.val - w t := by
  unfold penUpperE wingCarved
  exact Finset.sup'_congr _ rfl fun t _ => by simp

/-- **Collapse, definitional face**: forced is the race at the Dirac. -/
theorem wingForced_eq_wingRace_dirac (d : T) :
    wingForced d = wingRace (FinPMF.dirac d) := rfl

/-- **Collapse, degenerate window**: the one-point window is the forced
delay, at the prevision level. -/
theorem wingCarved_point_prevEq_forced (d : T)
    [Nonempty {t : T // d ≤ t ∧ t ≤ d}] :
    PrevEq (wingCarved d d) 0 (wingForced d) 0 := by
  intro f
  rw [wingForced_penUpperE]
  apply le_antisymm
  · refine penUpperE_le fun t => ?_
    have hv : t.val = d := le_antisymm t.2.2 t.2.1
    simp [wingCarved, hv]
  · have hb := exp_sub_le_penUpperE (wingCarved d d) 0 f ⟨d, le_rfl, le_rfl⟩
    simpa [wingCarved] using hb

/-- **Collapse, unbounded window**: a window whose ceiling is above the
whole carrier is the demonic wing, at the prevision level.  The carved
window is a degenerate of the kernel discipline, not a separate former. -/
theorem wingCarved_full_prevEq_demonic (lo hi : T) (hhi : ∀ t : T, t ≤ hi)
    [Nonempty {t : T // lo ≤ t ∧ t ≤ hi}] :
    PrevEq (wingCarved lo hi) 0 (wingDemonic lo) 0 := by
  intro f
  apply le_antisymm
  · refine penUpperE_le fun t => ?_
    have hb := exp_sub_le_penUpperE (wingDemonic lo) 0 f ⟨t.val, t.2.1⟩
    simpa [wingCarved, wingDemonic] using hb
  · refine penUpperE_le fun t => ?_
    have hb := exp_sub_le_penUpperE (wingCarved lo hi) 0 f
      ⟨t.val, t.2, hhi t.val⟩
    simpa [wingCarved, wingDemonic] using hb

end Wings

end Qtsl.Imprecise
