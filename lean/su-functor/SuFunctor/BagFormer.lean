import SuFunctor.WiringModes
import DoubleCat.BagMonad
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin

/-! # The bag former against the semantic universe: statics, exchange, and
the multiset denotation

The token-population former: `Bag(S)` is the countably-indexed
switched-mode system whose mode `n` holds `n` interchangeable copies of
`S`, quotiented by exchange.  This file gives the former's denotational
semantics at the stratum where the wiring modes live — the untyped
wiring base and the DNF spec tier — in the form that is *true* at this
stratum (the discipline of `SuFunctor.WiringModes`: statics here,
dynamics one stratum down):

* **The bag interface is the mode-switching composite over the power
  roster — definitionally.**  `bagObj A` is one count wire plus the
  countable roster of token powers, and at universe zero
  `bagObj_eq_switchObj` holds by `rfl`: the bag former's static
  interface consumes the switch pattern's statics on the nose (the kin
  of `SetRows.pat_eq_share`, one pattern over).  At higher universes
  the same fact holds up to `ULift` on the mode index; nothing below
  depends on it.

* **The exchange quotient enters as a group action by wire renames.**
  `bagPerm` acts per mode, fixes the count wire
  (`bagPerm_countIncl`), permutes the token inclusions
  (`bagPerm_tokenIncl` — the action's content: which token goes
  where), and commutes with component renames (`bagPerm_bagMap`).
  Exchange-invariance of a DNF presentation (`ExchangeInvariant`) is
  the spec-tier face of "tokens within a place are exchangeable":
  count-wire specs are invariant (`exchangeInvariant_count`) and the
  invariant class is closed under component-rename transport
  (`exchangeInvariant_map`) — the aggregate-observable interface is
  forced by the quotient, as a theorem.

* **The multiset denotation is a complete invariant.**  `powBag` reads
  the token multiset out of a mode-`n` state; it is exchange-invariant
  (`powBag_perm`) and complete (`powBag_eq_iff`): two states have equal
  multisets iff an exchange rename relates them.  Together these
  identify mode-`n` states modulo exchange with `Sym^n` of the
  component state space — the quotient identification at the interface
  stratum, with no order on states demanded (the group-action face of
  `BagMonad.bagEquiv`, whose canonical-representative face needs a
  linear order).  The underlying combinatorial fact is
  `map_univ_val_eq_iff`: two tuples enumerate equal multisets iff a
  permutation of indices relates them.

* **The monad structure's static shadows.**  The unit's shadow: a
  mode-1 bag is the singleton of its token readout (`toBag_one`, the
  interface shadow of `BagMonad.toMultiset_bagEta`).  The
  multiplication's shadow: the per-shape flatten rename
  (`flattenWires`) denotes multiset bind (`powBag_flatten`, the
  interface shadow of `BagMonad.toMultiset_bagMu`).  The monad *laws*
  live one stratum down in `DoubleCat.BagMonad` (value stratum,
  proved); dynamics preservation for `η`/`μ` is a process-stratum
  obligation, enumerated there, deliberately absent here.

Deliberately *not* stated, per the switch precedent: any
spec-class-level composition law for token creation/destruction
species (delay rates, guard forcing, cascade closure of immediate
firings) — those compose behaviors in time, not interfaces in space,
and their semantics is generator-stratum content.  The arc-level
compile statements the reconstruction of stochastic Petri frames
consumes (token removal/production, read arcs, count guards) live in
`SuFunctor.TokenArcs`.
-/

namespace SuFunctor

namespace BagFormer

noncomputable section

open CategoryTheory CategoryTheory.WireSpan
open SuFunctor.Plain SuFunctor.Universe

universe u

variable {El : Type u}

/-! ## The power and bag interfaces -/

/-- The `n`-fold token power of an interface: `n` copies of its wires
(its state space is the space of `n`-tuples of component states). -/
def powObj (A : WireSpan El) (n : ℕ) : WireSpan El :=
  ⟨Fin n × A.wires⟩

/-- Token `i`'s copy of the component inside the power. -/
def tokenRes (A : WireSpan El) (n : ℕ) (i : Fin n) : A ⟶ powObj A n :=
  fun w => (i, w)

/-- The bag interface: one **count wire** (`none`) plus the countable
mode roster (`some ⟨n, token wires⟩`).  Mode `n` is the `n`-token
variant; the count wire's value encodes the active mode, and the
untyped stratum deliberately does not fix the encoding (it is the
switch composite's location wire). -/
def bagObj (A : WireSpan El) : WireSpan El :=
  ⟨Option ((n : ℕ) × (Fin n × A.wires))⟩

/-- The static inclusion of the mode-`n` power into the bag. -/
def modeIncl (A : WireSpan El) (n : ℕ) : powObj A n ⟶ bagObj A :=
  fun p => some ⟨n, p⟩

/-- The static inclusion of token `i` of mode `n`. -/
def tokenIncl (A : WireSpan El) (n : ℕ) (i : Fin n) : A ⟶ bagObj A :=
  tokenRes A n i ≫ modeIncl A n

/-- The one-wire interface of the count observable. -/
def countObj : WireSpan El :=
  ⟨PUnit⟩

/-- The count wire's inclusion: the bag's supervisory location wire. -/
def countIncl (A : WireSpan El) : countObj ⟶ bagObj A :=
  fun _ => none

/-- The token inclusion factors through the mode inclusion. -/
theorem tokenIncl_factor (A : WireSpan El) (n : ℕ) (i : Fin n) :
    tokenIncl A n i = tokenRes A n i ≫ modeIncl A n := rfl

/-! ### The switch subsumption

At universe zero the bag interface **is** the mode-switching composite
over the power roster, definitionally — the bag former consumes the
switch pattern's statics rather than duplicating them.  (At higher
universes the switch composite's index type must live in the wire
universe, so the same fact holds up to `ULift ℕ` on the index; nothing
in this file depends on the identification.) -/

/-- The bag interface is the switch composite of the power roster, by
`rfl`: the count wire is the location wire, the mode roster is the
component roster. -/
theorem bagObj_eq_switchObj {El : Type} (A : WireSpan El) :
    bagObj A = WiringModes.switchObj (fun n : ℕ => powObj A n) := rfl

/-- The mode inclusion is the switch composite's component inclusion,
by `rfl`. -/
theorem modeIncl_eq_switchIncl {El : Type} (A : WireSpan El) (n : ℕ) :
    modeIncl A n = WiringModes.switchIncl (fun n : ℕ => powObj A n) n := rfl

/-! ## Functoriality: component renames -/

/-- The power's action on component renames: per token. -/
def powMap {A B : WireSpan El} (ρ : A ⟶ B) (n : ℕ) :
    powObj A n ⟶ powObj B n :=
  fun p => (p.1, ρ p.2)

/-- The bag's action on component renames: per token, count wire
fixed. -/
def bagMap {A B : WireSpan El} (ρ : A ⟶ B) : bagObj A ⟶ bagObj B :=
  Option.map fun p => ⟨p.1, p.2.1, ρ p.2.2⟩

theorem bagMap_id (A : WireSpan El) : bagMap (𝟙 A) = 𝟙 (bagObj A) :=
  funext fun w => by cases w <;> rfl

theorem bagMap_comp {A B C : WireSpan El} (ρ : A ⟶ B) (τ : B ⟶ C) :
    bagMap (ρ ≫ τ) = bagMap ρ ≫ bagMap τ :=
  funext fun w => by cases w <;> rfl

/-- **The token inclusions are natural in component renames.** -/
theorem tokenIncl_natural {A B : WireSpan El} (ρ : A ⟶ B) (n : ℕ)
    (i : Fin n) :
    tokenIncl A n i ≫ bagMap ρ = ρ ≫ tokenIncl B n i := rfl

/-- The count wire is natural in component renames (it never reads the
component). -/
theorem countIncl_natural {A B : WireSpan El} (ρ : A ⟶ B) :
    countIncl A ≫ bagMap ρ = countIncl B := rfl

/-- The mode inclusions are natural in component renames. -/
theorem modeIncl_natural {A B : WireSpan El} (ρ : A ⟶ B) (n : ℕ) :
    modeIncl A n ≫ bagMap ρ = powMap ρ n ≫ modeIncl B n := rfl

/-- Per-token spec transport into the bag composite is natural in
component renames (the kin of `dnfPull_switch_natural`). -/
theorem dnfPull_token_natural {A B : WireSpan El} (ρ : A ⟶ B) (n : ℕ)
    (i : Fin n) (D : DnfSpec A) :
    dnfPull (res (bagMap ρ)) (dnfPull (res (tokenIncl A n i)) D)
      = dnfPull (res (tokenIncl B n i)) (dnfPull (res ρ) D) := by
  rw [dnfPull_dnfPull, dnfPull_dnfPull]
  rfl

/-! ## The exchange action -/

/-- The exchange action on the power: permute token indices. -/
def powPerm {A : WireSpan El} {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    powObj A n ⟶ powObj A n :=
  fun p => (σ p.1, p.2)

/-- The exchange action on the bag: permute token indices per mode,
count wire fixed. -/
def bagPerm (A : WireSpan El) (σ : ∀ n, Equiv.Perm (Fin n)) :
    bagObj A ⟶ bagObj A :=
  Option.map fun p => ⟨p.1, σ p.1 p.2.1, p.2.2⟩

theorem bagPerm_one (A : WireSpan El) :
    bagPerm A (fun _ => 1) = 𝟙 (bagObj A) :=
  funext fun w => by cases w <;> rfl

theorem bagPerm_comp (A : WireSpan El) (σ τ : ∀ n, Equiv.Perm (Fin n)) :
    bagPerm A σ ≫ bagPerm A τ = bagPerm A (fun n => τ n * σ n) :=
  funext fun w => by cases w <;> rfl

/-- Permutations fix the count wire. -/
theorem bagPerm_countIncl (A : WireSpan El) (σ : ∀ n, Equiv.Perm (Fin n)) :
    countIncl A ≫ bagPerm A σ = countIncl A := rfl

/-- **The action's content**: composing a token inclusion with an
exchange rename is the inclusion of the permuted token. -/
theorem bagPerm_tokenIncl (A : WireSpan El) (σ : ∀ n, Equiv.Perm (Fin n))
    (n : ℕ) (i : Fin n) :
    tokenIncl A n i ≫ bagPerm A σ = tokenIncl A n (σ n i) := rfl

/-- The exchange action restricted to mode `n` is the power's
exchange. -/
theorem modeIncl_bagPerm (A : WireSpan El) (σ : ∀ n, Equiv.Perm (Fin n))
    (n : ℕ) :
    modeIncl A n ≫ bagPerm A σ = powPerm (σ n) ≫ modeIncl A n := rfl

/-- **Equivariance**: component renames commute with the exchange
action. -/
theorem bagPerm_bagMap {A B : WireSpan El} (ρ : A ⟶ B)
    (σ : ∀ n, Equiv.Perm (Fin n)) :
    bagMap ρ ≫ bagPerm B σ = bagPerm A σ ≫ bagMap ρ :=
  funext fun w => by cases w <;> rfl

/-! ## Exchange-invariant presentations

The spec-tier face of the exchange quotient: a DNF presentation over
the bag is *exchange-invariant* when transport along every exchange
rename fixes it.  Specs a bag composite legitimately exposes — the
aggregate dictionary of count and symmetric observables — live in this
class, and the class is closed under the transports the composite
performs. -/

/-- Exchange-invariance of a DNF presentation over the bag. -/
def ExchangeInvariant {A : WireSpan El} (D : DnfSpec (bagObj A)) : Prop :=
  ∀ σ : ∀ n, Equiv.Perm (Fin n), dnfPull (res (bagPerm A σ)) D = D

/-- Count-wire specs are exchange-invariant: anything read off the
count observable ignores token identity. -/
theorem exchangeInvariant_count {A : WireSpan El}
    (D : DnfSpec (countObj (El := El))) :
    ExchangeInvariant (dnfPull (res (countIncl A)) D) := by
  intro σ
  rw [dnfPull_dnfPull]
  rfl

/-- The exchange-invariant class is closed under component-rename
transport: symmetric specs pull back to symmetric specs.  (With
`exchangeInvariant_count`, the machine form of "the aggregate
dictionary is forced by the quotient".) -/
theorem exchangeInvariant_map {A B : WireSpan El} (ρ : A ⟶ B)
    {D : DnfSpec (bagObj A)} (hD : ExchangeInvariant D) :
    ExchangeInvariant (dnfPull (res (bagMap ρ)) D) := by
  intro σ
  rw [dnfPull_dnfPull]
  have hcomp : res (bagMap ρ) ∘ res (bagPerm B σ)
      = res (bagPerm A σ) ∘ res (bagMap ρ) := by
    have := congrArg (res (A := bagObj A) (B := bagObj B))
      (bagPerm_bagMap ρ σ)
    exact this
  rw [hcomp, ← dnfPull_dnfPull, hD σ]

/-! ## The multiset denotation and the quotient identification -/

/-- Token `i`'s state readout from a mode-`n` state. -/
def powState {A : WireSpan El} {n : ℕ} (t : states (powObj A n))
    (i : Fin n) : states A :=
  fun w => t (i, w)

theorem powState_res_tokenRes {A : WireSpan El} {n : ℕ}
    (t : states (powObj A n)) (i : Fin n) :
    res (tokenRes A n i) t = powState t i := rfl

/-- The multiset denotation of a mode-`n` state: its bag of token
states. -/
def powBag {A : WireSpan El} (n : ℕ) (t : states (powObj A n)) :
    Multiset (states A) :=
  Finset.univ.val.map (powState t)

@[simp] theorem powBag_card {A : WireSpan El} (n : ℕ)
    (t : states (powObj A n)) :
    Multiset.card (powBag n t) = n := by
  simp [powBag]

/-! ### The tuple lemma

Two tuples enumerate equal multisets iff a permutation of indices
relates them.  The backward direction is permutation-invariance of the
enumeration; the forward direction is the completeness of the multiset
invariant, by induction on the length, peeling the head against a
matching entry and reassembling the permutation through
`finSuccEquiv`. -/

/-- Peeling the head off a tuple enumeration. -/
theorem map_univ_val_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) :
    Finset.univ.val.map f
      = f 0 ::ₘ Finset.univ.val.map (f ∘ Fin.succ) := by
  rw [Fin.univ_succ]
  simp [Function.comp_def]

/-- Peeling an arbitrary entry off a tuple enumeration (the
`succAbove` pivot form; the ordinary-arc identity of
`SuFunctor.TokenArcs` consumes it). -/
theorem map_univ_val_succAbove {α : Type*} {n : ℕ}
    (g : Fin (n + 1) → α) (p : Fin (n + 1)) :
    Finset.univ.val.map g
      = g p ::ₘ Finset.univ.val.map (g ∘ p.succAbove) := by
  rw [Fin.univ_succAbove n p]
  simp [Function.comp_def]

/-- Two tuples enumerate equal multisets iff a permutation of indices
relates them. -/
theorem map_univ_val_eq_iff {α : Type*} {n : ℕ} {f g : Fin n → α} :
    Finset.univ.val.map f = Finset.univ.val.map g
      ↔ ∃ σ : Equiv.Perm (Fin n), f = g ∘ σ := by
  constructor
  · induction n with
    | zero =>
      exact fun _ => ⟨1, funext fun i => i.elim0⟩
    | succ n ih =>
      intro h
      have h0 : f 0 ∈ Finset.univ.val.map g := by
        rw [← h]
        exact Multiset.mem_map_of_mem f (Finset.mem_val.mpr (Finset.mem_univ 0))
      obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h0
      rw [map_univ_val_succ f, map_univ_val_succAbove g j, ← hj] at h
      obtain ⟨τ, hτ⟩ := ih (Multiset.cons_inj_right _ |>.mp h)
      refine ⟨(finSuccEquiv n).trans
        ((Equiv.optionCongr τ).trans (finSuccEquiv' j).symm), funext fun i => ?_⟩
      induction i using Fin.cases with
      | zero =>
        simp [finSuccEquiv_zero, finSuccEquiv'_symm_none, hj]
      | succ x =>
        have := congrFun hτ x
        simp only [Function.comp_apply] at this
        simp [finSuccEquiv_succ, finSuccEquiv'_symm_some, this]
  · rintro ⟨σ, rfl⟩
    show Finset.univ.val.map (g ∘ σ) = Finset.univ.val.map g
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- The multiset denotation is exchange-invariant. -/
theorem powBag_perm {A : WireSpan El} {n : ℕ} (σ : Equiv.Perm (Fin n))
    (t : states (powObj A n)) :
    powBag n (res (powPerm σ) t) = powBag n t := by
  show Finset.univ.val.map (fun i => powState t (σ i))
    = Finset.univ.val.map (powState t)
  rw [show (fun i => powState t (σ i)) = powState t ∘ σ from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- **The quotient identification**: the multiset denotation is a
*complete* exchange invariant — two mode-`n` states have equal bags iff
an exchange rename relates them.  With `powBag_perm`, mode-`n` states
modulo exchange are exactly the size-`n` multisets of component states
(`Sym^n` of the state space), with no order on states demanded. -/
theorem powBag_eq_iff {A : WireSpan El} {n : ℕ}
    (t t' : states (powObj A n)) :
    powBag n t = powBag n t'
      ↔ ∃ σ : Equiv.Perm (Fin n), t = res (powPerm σ) t' := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := map_univ_val_eq_iff.mp h
    refine ⟨σ, funext fun p => ?_⟩
    exact congrFun (congrFun hσ p.1) p.2
  · rintro ⟨σ, rfl⟩
    exact powBag_perm σ t'

/-! ### The bag-level readouts -/

/-- The mode-`n` bag readout of a bag state. -/
def toBag {A : WireSpan El} (n : ℕ) (s : states (bagObj A)) :
    Multiset (states A) :=
  powBag n (res (modeIncl A n) s)

@[simp] theorem toBag_card {A : WireSpan El} (n : ℕ)
    (s : states (bagObj A)) :
    Multiset.card (toBag n s) = n :=
  powBag_card n _

/-- The bag readouts are exchange-invariant. -/
theorem toBag_bagPerm {A : WireSpan El} (σ : ∀ n, Equiv.Perm (Fin n))
    (n : ℕ) (s : states (bagObj A)) :
    toBag n (res (bagPerm A σ) s) = toBag n s := by
  show powBag n (res (modeIncl A n) (res (bagPerm A σ) s)) = toBag n s
  have : res (modeIncl A n) (res (bagPerm A σ) s)
      = res (powPerm (σ n)) (res (modeIncl A n) s) := rfl
  rw [this]
  exact powBag_perm (σ n) _

/-- Token readouts are members of the bag readout. -/
theorem tokenIncl_mem_toBag {A : WireSpan El} {n : ℕ} (i : Fin n)
    (s : states (bagObj A)) :
    res (tokenIncl A n i) s ∈ toBag n s :=
  Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ i))

/-! ## The monad structure's static shadows

The value-stratum monad (`DoubleCat.BagMonad`) has `η x = {x}` and
`μ = bind` on quotient classes (`toMultiset_bagEta`,
`toMultiset_bagMu`).  These are their shadows at the interface
stratum: what the unit and multiplication do to the multiset
denotation of static states.  Dynamics preservation is a
process-stratum obligation (enumerated in `DoubleCat.BagMonad`'s
header), deliberately not claimed here. -/

/-- The unit's static shadow: a mode-1 bag is the singleton of its
token readout. -/
theorem toBag_one {A : WireSpan El} (s : states (bagObj A)) :
    toBag 1 s = {res (tokenIncl A 1 0) s} := by
  show Finset.univ.val.map (powState (res (modeIncl A 1) s)) = _
  rw [map_univ_val_succ, Finset.univ_eq_empty]
  rfl

/-- The per-shape flatten rename: mode `∑ c i` of a bag reads out of
mode `k` of the bag-of-bags whose inner mode profile is `c`, along the
sigma enumeration of tokens. -/
def flattenWires {A : WireSpan El} (k : ℕ) (c : Fin k → ℕ) :
    powObj A (∑ i, c i) ⟶ powObj (bagObj A) k :=
  fun p => ((finSigmaFinEquiv.symm p.1).1,
    some ⟨c (finSigmaFinEquiv.symm p.1).1,
      ((finSigmaFinEquiv.symm p.1).2, p.2)⟩)

/-- The multiplication's static shadow: the flatten rename denotes
multiset bind — the flattened bag is the bind of the inner bags. -/
theorem powBag_flatten {A : WireSpan El} (k : ℕ) (c : Fin k → ℕ)
    (t : states (powObj (bagObj A) k)) :
    powBag (∑ i, c i) (res (flattenWires k c) t)
      = Finset.univ.val.bind fun i => toBag (c i) (powState t i) := by
  show Finset.univ.val.map
      ((fun q : Σ i : Fin k, Fin (c i) =>
          powState (res (modeIncl A (c q.1)) (powState t q.1)) q.2)
        ∘ ⇑finSigmaFinEquiv.symm)
    = Finset.univ.val.bind fun i => toBag (c i) (powState t i)
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have huniv : (Finset.univ.val : Multiset (Σ i : Fin k, Fin (c i)))
      = Finset.univ.val.bind fun i =>
          (Finset.univ.val : Multiset (Fin (c i))).map (Sigma.mk i) := rfl
  rw [huniv, Multiset.map_bind]
  refine congrArg _ (funext fun i => ?_)
  rw [Multiset.map_map]
  rfl

end

end BagFormer

end SuFunctor
