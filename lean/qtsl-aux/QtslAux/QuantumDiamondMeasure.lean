/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumCoarseGraining

/-! # The diamond-indexed measure toy: transport and pushforward
together on a real site

The transport module fenced its own gap: "No concrete diamond-indexed
quantum measure witness exists in-tree and none is manufactured here."
This module manufactures it — the first specimen whose index is
genuinely ORDER-EVENTS from the spacetime vocabulary (`Diamond X`,
`Diamond.map`, `Diamond.congr`) rather than an abstract `Fin n` — and
exercises the two variance faces TOGETHER, with all three landed mixed
composites (`pushforward_equiv`, `map_pushforward`, `pushforward_map`)
instantiated concrete.

* **The order-event index**: `Diamond (Fin 2)` has exactly three
  elements — two degenerate diamonds `[0,0]`, `[1,1]` (instantaneous
  events) and the thick span `[0,1]` (the extended event) — enumerated
  by `diamondEquiv : Fin 3 ≃ Diamond (Fin 2)`. The landed
  strictly-quantum `mergeMeasure` transports onto the site:
  `diamondMeasure := mergeMeasure.map diamondEquiv` — the missing
  witness, manufactured BY the transport being witnessed. The toy
  re-proves nothing: the one new arithmetic item is the
  `(pointLo, span)` Gram entry `= 3/5` (an instantaneous event
  interfering with the extended event); everything else is consumed
  through the landed calculus (`map_isDiagonal_iff`, `map_probRow`,
  `mapDiamond_*`, the merge toys).

* **The atom merge is definable in the site's own vocabulary**:
  `degeneracy : Diamond X → Bool` — "was the event instantaneous or
  extended?" — generic in the carrier, plus the `DecidableEq
  (Diamond X)` instance without which pushforward on diamond indices
  is not even stateable (the `Fintype (Diamond X)` instance's missing
  sibling). Merging along it, **decoherence by temporal
  coarse-graining lands on the site**: the fine diamond-indexed
  measure interferes (`diamondMeasure_not_isDiagonal`), its degeneracy
  pushforward is exactly diagonal
  (`diamondMeasure_pushforward_isDiagonal`) with Born row
  P(point) = 16/25, P(extended) = 9/25, and is (equal to) a classical
  measure — asking only "instantaneous or extended?" erases the
  interference.

* **Covariance and merge compose** — the crown, generic over carriers:
  degeneracy is invariant under any order isomorphism
  (`degeneracy_map`; injectivity is the load-bearing half), hence
  **the degeneracy coarse-graining is covariance-equivariant**
  (`mapDiamond_pushforward_degeneracy`): coarse-grain-then-relabel
  needs no relabeling at all, because the classifier never looked at
  the labels. Instantiated on the toy along `Fin 2 ≃o Bool`
  (`diamondMeasure_covariant_coarse`), where the transported measure
  keeps its interference at the relabeled order events.

Scope fences inherited from the record tier: finite indices, matrix
grade, pure states, toy grade — never operator-algebra generality; the
physical readings (point-event vs extended-event, temporal
coarse-graining) are interpretation, not new claims; continuum sites
out of scope. -/

namespace Qtsl

namespace QuantumDiamondMeasure

open Matrix DiamondSite QuantumRecords QuantumDForm QuantumTransport
  QuantumCoarseGraining
open scoped ComplexOrder

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

/-! ## Site bookkeeping: decidable equality and the degeneracy
classifier, generic in the carrier -/

/-- A diamond is determined by its endpoints (re-proved locally; the
transport module's copy is private there by design). -/
private theorem diamond_ext {D E : Diamond X} (hlo : D.lo = E.lo)
    (hhi : D.hi = E.hi) : D = E := by
  cases D
  cases E
  subst hlo
  subst hhi
  rfl

/-- Decidable equality of diamonds from decidable equality of
endpoints — the `Fintype (Diamond X)` instance's missing sibling:
pushforward on diamond indices is not even stateable without it. -/
instance [DecidableEq X] : DecidableEq (Diamond X) := fun D E =>
  decidable_of_iff (D.lo = E.lo ∧ D.hi = E.hi)
    ⟨fun h => diamond_ext h.1 h.2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- **The degeneracy classifier**: was the event instantaneous
(`true`) or extended (`false`)? Stated in the site's own order
vocabulary — no reference to any enumeration. -/
def degeneracy [DecidableEq X] (D : Diamond X) : Bool :=
  decide (D.lo = D.hi)

/-- Degeneracy is invariant under any order isomorphism of carriers —
injectivity is the load-bearing half (a merely monotone map can
collapse a thick diamond to a degenerate one). -/
theorem degeneracy_map [DecidableEq X] [DecidableEq Y] (f : X ≃o Y)
    (D : Diamond X) : degeneracy (D.map f) = degeneracy D := by
  simp only [degeneracy, Diamond.map_lo, Diamond.map_hi]
  exact decide_eq_decide.mpr f.injective.eq_iff

/-- **The degeneracy coarse-graining is covariance-equivariant**:
transporting along the covariance bridge and then merging by
degeneracy is the same as merging by degeneracy — coarse-grain-then-
relabel needs no relabeling at all, because the classifier never
looked at the labels. Generic over finite carriers; the proof consumes
only `map_pushforward` and `degeneracy_map`. -/
theorem mapDiamond_pushforward_degeneracy [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X ≃o Y)
    (Q : QuantumMeasure (Diamond X)) :
    (Q.mapDiamond f).pushforward degeneracy
      = Q.pushforward degeneracy := by
  show (Q.map (Diamond.congr f).toEquiv).pushforward degeneracy = _
  rw [map_pushforward]
  have hfun : degeneracy ∘ ⇑(Diamond.congr f).toEquiv
      = (degeneracy : Diamond X → Bool) :=
    funext fun D => degeneracy_map f D
  rw [hfun]

/-! ## The concrete site: three order events on `Fin 2` -/

/-- The instantaneous event at the early endpoint. -/
def pointLo : Diamond (Fin 2) := ⟨0, 0, le_rfl⟩

/-- The instantaneous event at the late endpoint. -/
def pointHi : Diamond (Fin 2) := ⟨1, 1, le_rfl⟩

/-- The extended event: the thick span `[0, 1]`. -/
def span : Diamond (Fin 2) := ⟨0, 1, by decide⟩

/-- The diamond poset of `Fin 2` has exactly the three order events. -/
theorem diamond_cases (D : Diamond (Fin 2)) :
    D = pointLo ∨ D = pointHi ∨ D = span := by
  obtain ⟨lo, hi, le⟩ := D
  fin_cases lo <;> fin_cases hi
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact absurd le (by decide)
  · exact Or.inr (Or.inl rfl)

/-- The enumeration of the order events. -/
def diamondEquiv : Fin 3 ≃ Diamond (Fin 2) where
  toFun := ![pointLo, pointHi, span]
  invFun D := if D.lo = D.hi then (if D.lo = 0 then 0 else 1) else 2
  left_inv i := by fin_cases i <;> rfl
  right_inv D := by
    rcases diamond_cases D with rfl | rfl | rfl <;> rfl

@[simp] theorem diamondEquiv_symm_pointLo :
    diamondEquiv.symm pointLo = 0 := by
  rw [show pointLo = diamondEquiv 0 from rfl, Equiv.symm_apply_apply]

@[simp] theorem diamondEquiv_symm_pointHi :
    diamondEquiv.symm pointHi = 1 := by
  rw [show pointHi = diamondEquiv 1 from rfl, Equiv.symm_apply_apply]

@[simp] theorem diamondEquiv_symm_span :
    diamondEquiv.symm span = 2 := by
  rw [show span = diamondEquiv 2 from rfl, Equiv.symm_apply_apply]

/-- The relabeling of carriers: `Fin 2 ≃o Bool`. -/
def finBoolIso : Fin 2 ≃o Bool where
  toFun := ![false, true]
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl
  map_rel_iff' {a b} := by fin_cases a <;> fin_cases b <;> decide

/-- The relabeled instantaneous event at the early endpoint. -/
def bPointLo : Diamond Bool := ⟨false, false, le_rfl⟩

/-- The relabeled extended event. -/
def bSpan : Diamond Bool := ⟨false, true, by decide⟩

/-- The coarse-index bookkeeping: the landed `mergeCoarse` put the
merged pair at index `0`; degeneracy calls that fiber `true`. -/
def coarseEquiv : Fin 2 ≃ Bool where
  toFun := ![true, false]
  invFun b := if b then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-! ## The witness: the landed strictly-quantum measure, living on
order events -/

/-- **The diamond-indexed quantum measure** — the transport module's
declared missing witness, manufactured BY the transport being
witnessed: the landed strictly-quantum `mergeMeasure` (branch vectors
`(1,0)`, `(−1,4/5)`, `(3/5,0)` at the state `(1,0)`), transported onto
the order events of the `Fin 2` site. -/
noncomputable def diamondMeasure : QuantumMeasure (Diamond (Fin 2)) :=
  mergeMeasure.map diamondEquiv

/-- The instantaneous event at `0` interferes with the extended event:
the `(pointLo, span)` overlap is `3/5` — the module's one new
arithmetic computation (`star(v₂) ⬝ᵥ v₀ = 3/5`). -/
theorem diamondMeasure_gram_pointLo_span :
    diamondMeasure.gram pointLo span = 3/5 := by
  rw [diamondMeasure, map_gram, diamondEquiv_symm_pointLo,
    diamondEquiv_symm_span]
  show decoherenceFunctional mergeFamily mergeState 0 2 = 3/5
  norm_num [decoherenceFunctional, mergeFamily, mergeState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

/-- The diamond-indexed measure genuinely interferes at order events —
inherited through the transport, no arithmetic re-done. -/
theorem diamondMeasure_not_isDiagonal : ¬ diamondMeasure.IsDiagonal :=
  fun h => mergeMeasure_not_isDiagonal
    ((map_isDiagonal_iff diamondEquiv mergeMeasure).mp h)

/-! ## The merge: degeneracy pushforward = the landed merge, up to
coarse-index bookkeeping -/

/-- **The bridge**: pushing the diamond-indexed measure forward along
the degeneracy classifier IS the landed merge, up to the coarse-index
bookkeeping equiv — `map_pushforward` and `pushforward_map` exercised
concrete on the site, in one statement. -/
theorem diamondMeasure_pushforward_eq :
    diamondMeasure.pushforward degeneracy
      = (mergeMeasure.pushforward mergeCoarse).map coarseEquiv := by
  rw [pushforward_map]
  show (mergeMeasure.map diamondEquiv).pushforward degeneracy = _
  rw [map_pushforward]
  have hfun : degeneracy ∘ ⇑diamondEquiv = ⇑coarseEquiv ∘ mergeCoarse :=
    funext fun a => by fin_cases a <;> rfl
  rw [hfun]

/-- **Decoherence by temporal coarse-graining, on the site**: asking
only "instantaneous or extended?" erases the interference — the coarse
measure is exactly diagonal, though the fine one is not. -/
theorem diamondMeasure_pushforward_isDiagonal :
    (diamondMeasure.pushforward degeneracy).IsDiagonal := by
  rw [diamondMeasure_pushforward_eq]
  exact (map_isDiagonal_iff coarseEquiv _).mpr
    mergeMeasure_pushforward_isDiagonal

/-- The coarse Born weight of "instantaneous": `16/25` — the merged
point events' fiber weight, interference between them included. -/
theorem diamondMeasure_pushforward_probRow_point :
    (diamondMeasure.pushforward degeneracy).probRow true = 16/25 := by
  rw [diamondMeasure_pushforward_eq, map_probRow]
  exact congrFun mergeMeasure_pushforward_probRow 0

/-- The coarse Born weight of "extended": `9/25`. -/
theorem diamondMeasure_pushforward_probRow_extended :
    (diamondMeasure.pushforward degeneracy).probRow false = 9/25 := by
  rw [diamondMeasure_pushforward_eq, map_probRow]
  exact congrFun mergeMeasure_pushforward_probRow 1

/-- The degeneracy-merged measure is (equal to) a classical measure:
conservativity at the coarse index, on the site. -/
theorem diamondMeasure_pushforward_classical :
    ∃ (p : Bool → ℝ) (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1),
      diamondMeasure.pushforward degeneracy
        = QuantumMeasure.classical p hp hs :=
  ⟨_, _, _, (diamondMeasure.pushforward degeneracy).isDiagonal_eq_classical
    diamondMeasure_pushforward_isDiagonal⟩

/-! ## The covariance leg: the same measure on the relabeled carrier -/

/-- The transported measure keeps its interference at the relabeled
order events — `mapDiamond_gram` consuming the fine value, no
arithmetic re-done. -/
theorem diamondMeasure_mapDiamond_gram :
    (diamondMeasure.mapDiamond finBoolIso).gram bPointLo bSpan = 3/5 := by
  rw [mapDiamond_gram]
  exact diamondMeasure_gram_pointLo_span

/-- The transported measure is still genuinely quantum — diagonality
is invariant under the covariance bridge. -/
theorem diamondMeasure_mapDiamond_not_isDiagonal :
    ¬ (diamondMeasure.mapDiamond finBoolIso).IsDiagonal :=
  fun h => diamondMeasure_not_isDiagonal
    ((mapDiamond_isDiagonal_iff finBoolIso diamondMeasure).mp h)

/-- **The crown, instantiated**: relabeling the carrier `Fin 2 → Bool`
and then merging by degeneracy is the same as merging by degeneracy. -/
theorem diamondMeasure_covariant_coarse :
    (diamondMeasure.mapDiamond finBoolIso).pushforward degeneracy
      = diamondMeasure.pushforward degeneracy :=
  mapDiamond_pushforward_degeneracy finBoolIso diamondMeasure

/-! ## The third mixed composite, instantiated on the site -/

/-- Transport recovered as the pushforward's core restriction, at the
diamond index: `pushforward_equiv` concrete on the site. -/
theorem pushforward_diamondEquiv :
    mergeMeasure.pushforward ⇑diamondEquiv = diamondMeasure :=
  pushforward_equiv diamondEquiv mergeMeasure

end QuantumDiamondMeasure

end Qtsl

-- Axiom receipts (expected: exactly [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumDiamondMeasure.degeneracy_map
#print axioms Qtsl.QuantumDiamondMeasure.mapDiamond_pushforward_degeneracy
#print axioms Qtsl.QuantumDiamondMeasure.diamond_cases
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_pointLo
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_pointHi
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_span
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_gram_pointLo_span
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_not_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_eq
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_probRow_point
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_probRow_extended
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_classical
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_mapDiamond_gram
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_mapDiamond_not_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_covariant_coarse
#print axioms Qtsl.QuantumDiamondMeasure.pushforward_diamondEquiv
