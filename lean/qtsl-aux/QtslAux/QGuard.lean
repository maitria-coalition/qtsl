import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import QtslAux.QtslAliases

/-! # Guarded satisfaction: soundness core for the guarded spec-former

A *guarded specification* `Guard(R, s)` conditions a body specification `s`
on an initial-region antecedent `R`: satisfaction demands the body's
guarantee only from initial states inside `R`, and promises nothing
off-region. The former internalizes, into specification structure, the
initial-membership side condition that region-warranted satisfaction
otherwise discharges at the ground seam — the introduction rule concludes a
guarded claim from a region warrant alone (implication introduction: the
membership hypothesis is discharged into the former), and the elimination
rule is where the membership evaluation re-enters.

This module is the rules' soundness core, stated over the existing
satisfaction semantics with the guard explicit (the former's constructor
lands with a future theory revision; these lemmas re-key to it then):

* `GuardSat` — the guarded denotation, pointwise over a demonic initial
  set: every admitted initial point inside the guard region meets the
  body's demand. `GuardSatBlanket` is the strictly weaker whole-set
  conditional, recorded for the semantics adjudication
  (`exists_blanket_not_guardSat` is the strictness witness; the pointwise
  reading is the adopted one).
* `sound_QGuardIntro` / `sound_QGuardElim` — soundness of introduction
  (warrant in, guarded claim out, no membership premise, any initial set)
  and elimination (guarded claim plus initial containment yields the
  unguarded claim); `qsatFromRegion_derived` recovers the region-warranted
  record route as their composite, and `guardSat_singleton_iff` ties the
  denotation to the point-shaped consumption of
  `Qtsl.Aliases.sound_QSatFromRegion`.
* Monotonicity in all three arguments (`GuardSat.mono_region` — a smaller
  guard region is a weaker claim — `GuardSat.mono_init`,
  `GuardSat.mono_sat`) and honest vacuity (`guardSat_of_disjoint`).
* The rational sublevel specialization (`sound_QGuardIntro_sublevel`,
  `guard_eval_sublevel` — the evaluation leaf, via the cast identities of
  `Qtsl.Aliases`) and the kernel-form probability corollary
  (`sound_QGuardIntro_prob`).
* Countermodels keeping the rules honest: `exists_blanket_not_guardSat`
  (dropping the membership evaluation from elimination is unsound) and
  `exists_not_guardSat_wrong_region` (a warrant licenses a guard on its
  own region only).
-/

open MeasureTheory

namespace Qtsl.Guard

variable {X : Type*}

/-- The guarded-satisfaction denotation, pointwise (demonic-initial-set)
form: every admitted initial point inside the guard region meets the body's
demand; initial points outside the region are unconstrained. -/
def GuardSat (init R : Set X) (sat : X → Prop) : Prop :=
  ∀ x₀ ∈ init, x₀ ∈ R → sat x₀

/-- The blanket (whole-set conditional) reading, recorded for the semantics
comparison: if the entire initial set lies inside the guard region, the
body's demand holds from every initial point. Strictly weaker than
`GuardSat` (`GuardSat.toBlanket`, `exists_blanket_not_guardSat`): an
initial set straddling the region gets nothing from a blanket guard, while
the pointwise guard still constrains every in-region initial point. -/
def GuardSatBlanket (init R : Set X) (sat : X → Prop) : Prop :=
  init ⊆ R → ∀ x₀ ∈ init, sat x₀

/-- Soundness of the introduction rule: a region warrant — the body's
demand holds from every state of `R` — yields the guarded claim with no
initial-membership premise, for any initial set. The membership hypothesis
that region-warranted satisfaction discharges at the ground seam is here
discharged into the former (implication introduction). -/
theorem sound_QGuardIntro {init R : Set X} {sat : X → Prop}
    (hchild : ∀ x ∈ R, sat x) : GuardSat init R sat :=
  fun x₀ _ hR => hchild x₀ hR

/-- Soundness of the elimination rule: the initial-membership evaluation
re-enters exactly here — a guarded claim together with containment of the
initial set in the guard region yields the unguarded claim. -/
theorem sound_QGuardElim {init R : Set X} {sat : X → Prop}
    (hg : GuardSat init R sat) (heval : init ⊆ R) : ∀ x₀ ∈ init, sat x₀ :=
  fun x₀ hx => hg x₀ hx (heval hx)

/-- Coherence: introduction followed by elimination recovers the
region-warranted record route (warrant plus initial containment yields
satisfaction from every initial point). -/
theorem qsatFromRegion_derived {init R : Set X} {sat : X → Prop}
    (hchild : ∀ x ∈ R, sat x) (heval : init ⊆ R) : ∀ x₀ ∈ init, sat x₀ :=
  sound_QGuardElim (sound_QGuardIntro hchild) heval

/-- At a singleton initial set the guarded denotation is the pointwise
conditional — the shape `Qtsl.Aliases.sound_QSatFromRegion` consumes. -/
theorem guardSat_singleton_iff {R : Set X} {sat : X → Prop} {x₀ : X} :
    GuardSat {x₀} R sat ↔ (x₀ ∈ R → sat x₀) := by
  simp [GuardSat]

/-- A smaller guard region is a weaker guarded claim (fewer initial states
constrained): guarding covaries with the region. -/
theorem GuardSat.mono_region {init R R' : Set X} {sat : X → Prop}
    (hRR : R' ⊆ R) (hg : GuardSat init R sat) : GuardSat init R' sat :=
  fun x₀ hx hR' => hg x₀ hx (hRR hR')

/-- Refining the initial set preserves the guarded claim. -/
theorem GuardSat.mono_init {init init' R : Set X} {sat : X → Prop}
    (hII : init' ⊆ init) (hg : GuardSat init R sat) : GuardSat init' R sat :=
  fun x₀ hx hR => hg x₀ (hII hx) hR

/-- Weakening the body's demand preserves the guarded claim. -/
theorem GuardSat.mono_sat {init R : Set X} {sat sat' : X → Prop}
    (hss : ∀ x, sat x → sat' x) (hg : GuardSat init R sat) :
    GuardSat init R sat' :=
  fun x₀ hx hR => hss x₀ (hg x₀ hx hR)

/-- Vacuity, stated honestly: a guard region disjoint from the initial set
is satisfied trivially. The former promises nothing off-region — that is
the price of discharging the membership evaluation, paid exactly where the
absent evaluation would have been. -/
theorem guardSat_of_disjoint {init R : Set X} {sat : X → Prop}
    (h : Disjoint init R) : GuardSat init R sat :=
  fun _ hx hR => (Set.disjoint_left.mp h hx hR).elim

/-- The pointwise reading implies the blanket reading (elimination in
disguise: containment turns the pointwise guard into the unguarded claim). -/
theorem GuardSat.toBlanket {init R : Set X} {sat : X → Prop}
    (hg : GuardSat init R sat) : GuardSatBlanket init R sat :=
  fun heval => sound_QGuardElim hg heval

/-- Strictness witness for the semantics adjudication, and the permanent
twin of the dropped-membership mutant: the blanket reading does not imply
the pointwise one. On `Bool` with the full initial set, guard region
`{true}`, and an everywhere-false demand, the blanket conditional holds
vacuously (the initial set is not contained in the region) while the
pointwise guard is refuted at `true`. A blanket semantics would license
claims the pointwise semantics rejects; the former adopts the pointwise
reading. -/
theorem exists_blanket_not_guardSat :
    ∃ (init R : Set Bool) (sat : Bool → Prop),
      GuardSatBlanket init R sat ∧ ¬ GuardSat init R sat := by
  refine ⟨Set.univ, {true}, fun _ => False, fun hsub _ _ => ?_, fun hg => ?_⟩
  · exact absurd (hsub (Set.mem_univ false)) (by simp)
  · exact hg true (Set.mem_univ true) rfl

/-- The permanent twin of the dropped-membership mutant, stated directly:
elimination WITHOUT its containment premise is false — a guarded claim
does not yield the unguarded one. On `Bool` with the full initial set and
guard region `{true}`, the demand "the state is `true`" is guarded-satisfied
(vacuously off-region, directly on it) yet fails from the initial point
`false`. -/
theorem exists_guardSat_not_unguarded :
    ∃ (init R : Set Bool) (sat : Bool → Prop),
      GuardSat init R sat ∧ ¬ ∀ x₀ ∈ init, sat x₀ := by
  refine ⟨Set.univ, {true}, fun x => x = true, fun x _ hx => hx, fun h => ?_⟩
  exact absurd (h false (Set.mem_univ false)) (by simp)

/-- Wrong-region countermodel (the permanent twin of the region-substitution
mutant): a warrant on one region does not license a guard on an unrelated
one — an everywhere-false demand is vacuously warranted on the empty
region, and the guard on the full region is refuted. -/
theorem exists_not_guardSat_wrong_region :
    ∃ (init R R' : Set Bool) (sat : Bool → Prop),
      (∀ x ∈ R, sat x) ∧ ¬ GuardSat init R' sat := by
  refine ⟨Set.univ, ∅, Set.univ, fun _ => False, fun x hx => ?_, fun hg => ?_⟩
  · exact hx.elim
  · exact hg true (Set.mem_univ true) (Set.mem_univ true)

/-- The rational-sublevel guard (a certificate family's sublevel set at an
exact-rational threshold, single-piece form): a warrant on the real
sublevel set of the coefficient-cast polynomial yields the guarded claim
with that sublevel set in the guard slot, for any initial set. -/
theorem sound_QGuardIntro_sublevel {σ : Type*} {init : Set (σ → ℝ)}
    {sat : (σ → ℝ) → Prop} {P : MvPolynomial σ ℚ} {thr : ℚ}
    (hchild : ∀ x ∈ {x : σ → ℝ |
        MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P) ≤ (thr : ℝ)},
      sat x) :
    GuardSat init
      {x : σ → ℝ |
        MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P) ≤ (thr : ℝ)}
      sat :=
  sound_QGuardIntro hchild

/-- The elimination-side evaluation leaf (exact-rational form): a rational
point evaluating below the threshold lies in the sublevel guard region,
via the cast identity `Qtsl.Aliases.rootEval_sublevel_iff`. -/
theorem guard_eval_sublevel {σ : Type*} {P : MvPolynomial σ ℚ} {thr : ℚ}
    {xq : σ → ℚ} (heval : MvPolynomial.eval xq P ≤ thr) :
    (fun i => (xq i : ℝ)) ∈ {x : σ → ℝ |
      MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P) ≤ (thr : ℝ)} :=
  (Qtsl.Aliases.rootEval_sublevel_iff P xq thr).1 heval

/-- Kernel-form corollary in the battery idiom: a per-initial-state
probability floor warranted on the region yields the guarded floor. -/
theorem sound_QGuardIntro_prob [MeasurableSpace X] {init R : Set X}
    {μ : X → Measure (ℕ → X)} {p : ENNReal} {A : Set (ℕ → X)}
    (hchild : ∀ x ∈ R, p ≤ μ x A) :
    GuardSat init R fun x => p ≤ μ x A :=
  sound_QGuardIntro hchild

end Qtsl.Guard
