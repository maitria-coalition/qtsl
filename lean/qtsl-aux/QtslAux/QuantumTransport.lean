/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumDForm
import QtslAux.QuantumCovariance

/-! # (ℰ, D)-transport: the quantum measure rides the covariance
machinery

The base-compatibility design clause: along order-isomorphisms
the decoherence data transports **by precomposition**. This module is
that clause at Lean grade, and the covariance story
(`QtslAux.QuantumCovariance`: nets, covers, separation moving along
`Diamond.map`/`Diamond.congr`) reaching the D-form storey.

* **The transport** (`QuantumMeasure.map`): a quantum measure on a
  finite index moves along any equivalence of indices — the Gram data
  is reindexed by `e.symm` in both slots (`Matrix.submatrix`:
  precomposition exactly), positivity by `PosSemidef.submatrix`, unit
  total weight by sum reindexing. Functorial: `map_refl`,
  `map_trans`, `map_symm_map`/`map_map_symm`.

* **Equivariance of the whole D-form story**: the event form, Sorkin
  measure, and grade-2 interference transport along `Finset.map`
  (`map_eventForm`, `map_sorkinMeasure`, `map_interference`);
  diagonality and the probability row transport (`map_isDiagonal_iff`,
  `map_probRow`); **the classical embedding is natural**
  (`classical_map`), so **conservativity commutes with transport**:
  classicalize-then-transport equals transport-then-classicalize
  (`classicalization_map_comm`, `map_isDiagonal_eq_classical`), and a
  transported recorded presentation is classical
  (`records_conservativity_map`, through `ofPresentation_map`:
  presentations transport by precomposition of the family — the state
  does not move; only the index bookkeeping does).

* **The covariance bridge** (`QuantumMeasure.mapDiamond`): for finite
  event carriers the diamond poset is a `Fintype`, so an order
  isomorphism `f : X ≃o Y` — the same morphism that transports
  chronology kits, derived covers, observable nets, and
  separation-grade descent in `QtslAux.QuantumCovariance` — also
  transports a quantum measure on the diamond index, through
  `(Diamond.congr f).toEquiv`. Diagonality (hence
  record-forcedness) is invariant (`mapDiamond_isDiagonal_iff`).

* **Toys re-prove nothing**: the transported coherent switch keeps its
  grade-2 interference `2/5` at the swapped order events
  (`switchMeasure_map_interference` — the landed value consumed
  through the transport lemma, no matrix arithmetic re-done); the
  transported controlled measure stays diagonal
  (`controlledMeasure_map_isDiagonal`); the transported recorded
  z-measure stays classical (`zMeasure_map_conservative`).

Scope fences, honestly: finite indices throughout (the transport is
along `Equiv`s of Fintypes; `Diamond X` is finite exactly when `X`
is). No concrete diamond-indexed quantum measure witness exists
in-tree and none is manufactured here — the order-index toys carry the
witnesses, and the diamond face ships as the typed bridge with its
inherited lemmas. Coarse-graining (bi-additive pushforward along
non-injective maps, the clause's other half) is out of leg scope. -/

namespace Qtsl

namespace QuantumTransport

open Matrix QuantumRecords DiamondSite QuantumDForm
open scoped ComplexOrder

variable {ι κ μ' : Type*} [Fintype ι] [Fintype κ] [Fintype μ']

private theorem sum_sum_equiv (e : ι ≃ κ) (f : ι → ι → ℂ) :
    ∑ α, ∑ β, f (e.symm α) (e.symm β) = ∑ a, ∑ b, f a b := by
  rw [← Equiv.sum_comp e.symm fun a => ∑ b, f a b]
  exact Finset.sum_congr rfl fun α _ =>
    Equiv.sum_comp e.symm fun b => f (e.symm α) b

/-! ## The transport, and its functoriality -/

/-- Transport of a quantum measure along an equivalence of indices:
the Gram data is reindexed by precomposition with `e.symm` in both
slots — the base-compatibility clause, verbatim. -/
noncomputable def _root_.Qtsl.QuantumDForm.QuantumMeasure.map (e : ι ≃ κ)
    (Q : QuantumMeasure ι) : QuantumMeasure κ where
  gram := Q.gram.submatrix e.symm e.symm
  posSemidef := Q.posSemidef.submatrix e.symm
  normalized := by
    show ∑ α, ∑ β, Q.gram (e.symm α) (e.symm β) = 1
    rw [sum_sum_equiv e fun a b => Q.gram a b]
    exact Q.normalized

@[simp] theorem map_gram (e : ι ≃ κ) (Q : QuantumMeasure ι) (α β : κ) :
    (Q.map e).gram α β = Q.gram (e.symm α) (e.symm β) := rfl

theorem map_refl (Q : QuantumMeasure ι) : Q.map (Equiv.refl ι) = Q :=
  QuantumMeasure.ext rfl

theorem map_symm_map (e : ι ≃ κ) (Q : QuantumMeasure ι) :
    (Q.map e).map e.symm = Q :=
  QuantumMeasure.ext (by ext α β; simp)

theorem map_map_symm (e : ι ≃ κ) (Q : QuantumMeasure κ) :
    (Q.map e.symm).map e = Q :=
  QuantumMeasure.ext (by ext α β; simp)

theorem map_trans (e : ι ≃ κ) (f : κ ≃ μ') (Q : QuantumMeasure ι) :
    Q.map (e.trans f) = (Q.map e).map f :=
  QuantumMeasure.ext rfl

/-! ## Equivariance of the event algebra -/

theorem map_eventForm (e : ι ≃ κ) (Q : QuantumMeasure ι)
    (A B : Finset ι) :
    (Q.map e).eventForm (A.map e.toEmbedding) (B.map e.toEmbedding)
      = Q.eventForm A B := by
  simp only [QuantumMeasure.eventForm, Finset.sum_map,
    Equiv.coe_toEmbedding, map_gram, Equiv.symm_apply_apply]

theorem map_sorkinMeasure (e : ι ≃ κ) (Q : QuantumMeasure ι)
    (A : Finset ι) :
    (Q.map e).sorkinMeasure (A.map e.toEmbedding) = Q.sorkinMeasure A :=
  map_eventForm e Q A A

theorem map_interference [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (Q : QuantumMeasure ι) (A B : Finset ι) :
    (Q.map e).interference (A.map e.toEmbedding) (B.map e.toEmbedding)
      = Q.interference A B := by
  simp only [QuantumMeasure.interference, ← Finset.map_union,
    map_sorkinMeasure]

/-! ## Equivariance of classicalization: conservativity commutes -/

theorem map_isDiagonal_iff (e : ι ≃ κ) (Q : QuantumMeasure ι) :
    (Q.map e).IsDiagonal ↔ Q.IsDiagonal := by
  constructor
  · intro hd α β hαβ
    have h := hd (e.injective.ne hαβ)
    simpa using h
  · intro hd α β hαβ
    exact hd (e.symm.injective.ne hαβ)

theorem map_probRow (e : ι ≃ κ) (Q : QuantumMeasure ι) (α : κ) :
    (Q.map e).probRow α = Q.probRow (e.symm α) := rfl

/-- **Naturality of the classical embedding**: transporting the
classical measure of a probability row is the classical measure of the
reindexed row. -/
theorem classical_map [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (p : ι → ℝ) (hp : ∀ α, 0 ≤ p α) (hsum : ∑ α, p α = 1) :
    (QuantumMeasure.classical p hp hsum).map e
      = QuantumMeasure.classical (fun b => p (e.symm b)) (fun _ => hp _)
          ((Equiv.sum_comp e.symm p).trans hsum) := by
  refine QuantumMeasure.ext ?_
  show (Matrix.diagonal fun α => (p α : ℂ)).submatrix e.symm e.symm = _
  rw [Matrix.submatrix_diagonal _ _ e.symm.injective]
  rfl

/-- A transported diagonal measure is the classical embedding of its
reindexed probability row. -/
theorem map_isDiagonal_eq_classical [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) :
    Q.map e = QuantumMeasure.classical (fun b => Q.probRow (e.symm b))
      (fun _ => Q.probRow_nonneg _)
      ((Equiv.sum_comp e.symm Q.probRow).trans (Q.probRow_sum hd)) :=
  (Q.map e).isDiagonal_eq_classical ((map_isDiagonal_iff e Q).mpr hd)

/-- **Conservativity commutes with transport**:
classicalize-then-transport equals transport-then-classicalize — the
naturality square of `isDiagonal_eq_classical` along `e`. -/
theorem classicalization_map_comm [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) :
    (QuantumMeasure.classical Q.probRow Q.probRow_nonneg
        (Q.probRow_sum hd)).map e
      = QuantumMeasure.classical ((Q.map e).probRow)
          ((Q.map e).probRow_nonneg)
          ((Q.map e).probRow_sum ((map_isDiagonal_iff e Q).mpr hd)) :=
  (congrArg (QuantumMeasure.map e) (Q.isDiagonal_eq_classical hd)).symm.trans
    ((Q.map e).isDiagonal_eq_classical ((map_isDiagonal_iff e Q).mpr hd))

/-! ## Presentations and records transport -/

/-- Presentations transport by precomposition of the family: the state
does not move, only the index bookkeeping does. -/
theorem ofPresentation_map {d : Type*} [Fintype d] (e : ι ≃ κ)
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hnorm : ∑ α, ∑ β, decoherenceFunctional C ψ α β = 1) :
    (QuantumMeasure.ofPresentation C ψ hnorm).map e
      = QuantumMeasure.ofPresentation (fun b => C (e.symm b)) ψ
          ((sum_sum_equiv e fun a b =>
            decoherenceFunctional C ψ a b).trans hnorm) :=
  QuantumMeasure.ext (by ext α β; rfl)

/-- **The conservativity theorem commutes with transport**: a recorded
presentation's quantum measure, transported along any index
equivalence, is still (equal to) a classical measure — the record
triple transports by precomposition, and `records_conservativity`
fires on the far side. -/
theorem records_conservativity_map {d : Type*} [Fintype d]
    [DecidableEq κ] (e : ι ≃ κ)
    (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hnorm : ∑ α, ∑ β, decoherenceFunctional C ψ α β = 1)
    (hherm : ∀ α, (R α).IsHermitian)
    (horth : ∀ α β, α ≠ β → R α * R β = 0)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :
    ∃ (p : κ → ℝ) (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1),
      (QuantumMeasure.ofPresentation C ψ hnorm).map e
        = QuantumMeasure.classical p hp hs := by
  rw [ofPresentation_map]
  exact QuantumMeasure.records_conservativity
    (R := fun b => R (e.symm b)) _
    (fun b => hherm _)
    (fun b b' hbb' => horth _ _ (e.symm.injective.ne hbb'))
    (fun b => hrec _)

/-! ## The covariance bridge: diamond indices -/

private theorem diamond_ext {X : Type*} [PartialOrder X]
    {D E : Diamond X} (hlo : D.lo = E.lo) (hhi : D.hi = E.hi) : D = E := by
  cases D
  cases E
  subst hlo
  subst hhi
  rfl

/-- For a finite event carrier, the diamond poset is finite (a diamond
is determined by its endpoints). -/
noncomputable instance {X : Type*} [PartialOrder X] [Fintype X] :
    Fintype (Diamond X) :=
  Fintype.ofInjective (fun D => (D.lo, D.hi)) fun _ _ h =>
    diamond_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **The covariance bridge**: the same order isomorphism that
transports chronology kits, derived covers, observable nets, and
separation (`QtslAux.QuantumCovariance`) transports a quantum measure
on the diamond index — the D-form storey riding `Diamond.congr`. -/
noncomputable def _root_.Qtsl.QuantumDForm.QuantumMeasure.mapDiamond
    {X Y : Type*} [PartialOrder X] [PartialOrder Y] [Fintype X]
    [Fintype Y] (f : X ≃o Y) (Q : QuantumMeasure (Diamond X)) :
    QuantumMeasure (Diamond Y) :=
  Q.map (Diamond.congr f).toEquiv

theorem mapDiamond_gram {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    [Fintype X] [Fintype Y] (f : X ≃o Y) (Q : QuantumMeasure (Diamond X))
    (D E : Diamond Y) :
    (Q.mapDiamond f).gram D E = Q.gram (D.map f.symm) (E.map f.symm) :=
  rfl

/-- Diagonality — record-forcedness at measure grade — is invariant
under the covariance transport. -/
theorem mapDiamond_isDiagonal_iff {X Y : Type*} [PartialOrder X]
    [PartialOrder Y] [Fintype X] [Fintype Y] (f : X ≃o Y)
    (Q : QuantumMeasure (Diamond X)) :
    (Q.mapDiamond f).IsDiagonal ↔ Q.IsDiagonal :=
  map_isDiagonal_iff _ _

/-! ## Toys: landed values consumed through the transport, nothing
re-proven -/

open QuantumOuterStorey

/-- The nontrivial automorphism of the order index: swap the two
temporal orders. -/
def orderSwap : SwitchOrder ≃ SwitchOrder where
  toFun x := match x with
    | .zThenX => .xThenZ
    | .xThenZ => .zThenX
  invFun x := match x with
    | .zThenX => .xThenZ
    | .xThenZ => .zThenX
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- The transported coherent switch keeps its grade-2 interference
`2/5` at the swapped order events — the landed value, consumed through
`map_interference`; no matrix arithmetic re-done. -/
theorem switchMeasure_map_interference :
    (switchMeasure.map orderSwap).interference
      {SwitchOrder.xThenZ} {SwitchOrder.zThenX} = 2/5 := by
  have h := map_interference orderSwap switchMeasure
    {SwitchOrder.zThenX} {SwitchOrder.xThenZ}
  rw [Finset.map_singleton, Finset.map_singleton] at h
  exact h.trans switchMeasure_interference

/-- The transported controlled measure stays diagonal: the pointer's
classicalization is transport-invariant. -/
theorem controlledMeasure_map_isDiagonal :
    (controlledMeasure.map orderSwap).IsDiagonal :=
  (map_isDiagonal_iff orderSwap controlledMeasure).mpr
    controlledMeasure_isDiagonal

/-- The transported recorded z-measure is still classical:
`records_conservativity_map` exercised end-to-end on the D-form
module's recorded presentation. -/
theorem zMeasure_map_conservative :
    ∃ (p : Fin 2 → ℝ) (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1),
      zMeasure.map (Equiv.swap (0 : Fin 2) 1)
        = QuantumMeasure.classical p hp hs := by
  refine records_conservativity_map (Equiv.swap (0 : Fin 2) 1)
    ![Pz0, Pz1] ![Pz0, Pz1] ![(3/5 : ℂ), 4/5] _ ?_ ?_ ?_
  · intro α
    fin_cases α
    · exact Pz0_isHermitian
    · exact Pz1_isHermitian
  · intro α β h
    fin_cases α <;> fin_cases β <;>
      first
        | exact absurd rfl h
        | exact Pz0_mul_Pz1
        | exact Pz1_mul_Pz0
  · intro α
    rfl

end QuantumTransport

end Qtsl

-- Axiom receipts (expected: exactly [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumTransport.map_gram
#print axioms Qtsl.QuantumTransport.map_refl
#print axioms Qtsl.QuantumTransport.map_symm_map
#print axioms Qtsl.QuantumTransport.map_map_symm
#print axioms Qtsl.QuantumTransport.map_trans
#print axioms Qtsl.QuantumTransport.map_eventForm
#print axioms Qtsl.QuantumTransport.map_sorkinMeasure
#print axioms Qtsl.QuantumTransport.map_interference
#print axioms Qtsl.QuantumTransport.map_isDiagonal_iff
#print axioms Qtsl.QuantumTransport.map_probRow
#print axioms Qtsl.QuantumTransport.classical_map
#print axioms Qtsl.QuantumTransport.map_isDiagonal_eq_classical
#print axioms Qtsl.QuantumTransport.classicalization_map_comm
#print axioms Qtsl.QuantumTransport.ofPresentation_map
#print axioms Qtsl.QuantumTransport.records_conservativity_map
#print axioms Qtsl.QuantumTransport.mapDiamond_gram
#print axioms Qtsl.QuantumTransport.mapDiamond_isDiagonal_iff
#print axioms Qtsl.QuantumTransport.switchMeasure_map_interference
#print axioms Qtsl.QuantumTransport.controlledMeasure_map_isDiagonal
#print axioms Qtsl.QuantumTransport.zMeasure_map_conservative
