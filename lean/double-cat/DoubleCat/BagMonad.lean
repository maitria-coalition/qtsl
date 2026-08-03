/-
The bag former's monad laws at the canonical-representative stratum.

The bag (finite-multiset) former underlies token-population system
constructions: a bag of components is a countably-indexed switched-mode
system — mode `n` holding `n` interchangeable tokens — and the exchange
quotient is what makes token identity non-semantic.  This module carries
the monad structure's statements at the *canonical-representative*
stratum: the quotient realized by representative rather than by type
former, so that quotient-equality is syntactic equality of canonical
values.

* `BagVal α` — canonical representatives: non-strictly sorted lists
  (`List.SortedLE`; duplicates legal — the indistinguishable-token
  diagonal).  The intended instantiation takes `α` to be a resolved
  token state with a decidable linear order (e.g. exact-rational colour
  vectors under lexicographic order).
* `bagEquiv : BagVal α ≃ Multiset α` — canonicalization is a section
  of the exchange quotient.  `ofMultiset_toMultiset` is the
  decidable-order half of the quotient identification, machine-checked:
  on sortable token types the representative is unique and total.
  (The measurable half — a Borel section of `B^n → Sym^n(B)` on
  real-valued colours and Markov-of-pushforward — is an analysis
  obligation at the process stratum, untouched here, deliberately.)
* `bagMap` / `bagEta` / `bagMu` and the seven laws (functoriality ×2,
  unit ×2, associativity, naturality ×2) — multiset algebra, zero
  analysis.
* the strong law `sumSplit` / `bagSumSplit`:
  `Bag(α ⊕ β) ≃ Bag(α) × Bag(β)` — "a place whose colour type is a
  sum is two places" (the colour/place exchange).

Obligations enumerated, NOT discharged here (each names its home):

1. **Arrow typing**: `η/μ` below act on VALUES.  As morphisms of
   systems they inhabit the total category's tight arrows (systems
   over varying interfaces — a bag's interface is the aggregate
   dictionary of count and symmetric observables, not the component's
   own interface); the transport of these value-level laws to
   simulation witnesses is an assembly obligation of the system
   category, and the per-value identities proven here are its leaf
   obligations.
2. **Dynamics preservation** — `η` (one token, no races) and `μ`
   (flatten preserves independent drivers) are exact simulations at
   the process-semantics stratum; that is an SDE/process statement,
   not statable at this stratum, and no lemma below claims it.
3. **The lax law** (double strength, `Bag S ⊞ Bag T → Bag(S ⊞ T)`)
   is deliberately ABSENT: its content is the noise-sharing
   obstruction — a statement about process laws with a
   zero-diffusion exactness locus — which has no shadow at the value
   stratum (the value-level map is trivially total; stating it here
   would overclaim exactly what the obstruction protects).

The static-interface face of the bag former — its wiring-base object,
the exchange action as wire renames, and the multiset denotation of
its states — lives in `SuFunctor.BagFormer`, whose readout lemmas are
the interface shadows of `bagEta`/`bagMu` below.
-/

import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Logic.Equiv.Basic

namespace BagMonad

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The canonical-representative type of the bag former at the
presentation stratum: token lists in non-strict ascending order.
An `abbrev` so `Subtype`/list order instances flow to nested bags. -/
abbrev BagVal (α : Type u) [LinearOrder α] : Type u :=
  {l : List α // l.SortedLE}

section Repr

variable [LinearOrder α]

/-- Forget the canonical order: the underlying multiset (the
exchange-quotient class the representative presents). -/
def toMultiset (b : BagVal α) : Multiset α := (b.1 : Multiset α)

/-- Canonicalize: sort.  Total on decidable linear orders — the
presentation-stratum section of the quotient. -/
def ofMultiset (s : Multiset α) : BagVal α :=
  ⟨s.sort, (Multiset.pairwise_sort s _).sortedLE⟩

@[simp] theorem toMultiset_ofMultiset (s : Multiset α) :
    toMultiset (ofMultiset s) = s := by
  simp [toMultiset, ofMultiset, Multiset.sort_eq]

/-- Uniqueness of the canonical representative (the decidable half of
the quotient identification): two sorted presentations of one multiset
are equal as lists — so `ofMultiset` is a genuine section and
quotient-equality is syntactic equality of canonical values. -/
@[simp] theorem ofMultiset_toMultiset (b : BagVal α) :
    ofMultiset (toMultiset b) = b := by
  obtain ⟨l, hl⟩ := b
  apply Subtype.ext
  exact
    (Multiset.coe_eq_coe.mp
        (by simp [toMultiset, ofMultiset,
                  List.mergeSort_perm])).eq_of_sortedLE
      (ofMultiset (toMultiset ⟨l, hl⟩)).2 hl

/-- Canonicalization as an equivalence between representatives and
quotient classes. -/
def bagEquiv : BagVal α ≃ Multiset α where
  toFun := toMultiset
  invFun := ofMultiset
  left_inv := ofMultiset_toMultiset
  right_inv := toMultiset_ofMultiset

theorem toMultiset_injective :
    Function.Injective (toMultiset (α := α)) :=
  (bagEquiv (α := α)).injective

/-- The count observable is derived data (no stored count): tokens of
the class, counted on the representative. -/
@[simp] theorem card_toMultiset (b : BagVal α) :
    Multiset.card (toMultiset b) = b.1.length := by
  simp [toMultiset]

end Repr

/-! ## The monad structure on canonical representatives

Each operation is conjugation through `bagEquiv` of the standard
multiset operation; each law is the multiset law plus the equiv's
inverse laws.  This is deliberate: the SEMANTIC object is the
quotient (collective token semantics), and the representative
operations are the quotient operations read through the section —
no law below depends on how ties are broken, which is the
machine-checked shadow of "any choice agrees on the diagonal." -/

section MonadOps

variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Functor action on a simulation-witness shadow `f : α → β`:
map per token, re-canonicalize. -/
def bagMap (f : α → β) (b : BagVal α) : BagVal β :=
  ofMultiset ((toMultiset b).map f)

/-- Unit: `x ↦ (1, [x])` — variant 1, token = the state. -/
def bagEta (x : α) : BagVal α :=
  ofMultiset {x}

/-- Multiplication: flatten — token counts add, token lists merge,
re-canonicalize. -/
def bagMu (b : BagVal (BagVal α)) : BagVal α :=
  ofMultiset ((toMultiset b).bind toMultiset)

@[simp] theorem toMultiset_bagMap (f : α → β) (b : BagVal α) :
    toMultiset (bagMap f b) = (toMultiset b).map f := by
  simp [bagMap]

@[simp] theorem toMultiset_bagEta (x : α) :
    toMultiset (bagEta x) = {x} := by
  simp [bagEta]

@[simp] theorem toMultiset_bagMu (b : BagVal (BagVal α)) :
    toMultiset (bagMu b) = (toMultiset b).bind toMultiset := by
  simp [bagMu]

/-- Functor law: identity. -/
theorem bagMap_id (b : BagVal α) : bagMap id b = b := by
  apply toMultiset_injective
  simp

/-- Functor law: composition. -/
theorem bagMap_comp (f : α → β) (g : β → γ) (b : BagVal α) :
    bagMap (g ∘ f) b = bagMap g (bagMap f b) := by
  apply toMultiset_injective
  simp [Multiset.map_map]

/-- Left unit: `μ ∘ η_{Bag} = id` — a one-token bag of a bag
flattens to the bag. -/
theorem bagMu_bagEta (b : BagVal α) : bagMu (bagEta b) = b := by
  apply toMultiset_injective
  simp [Multiset.singleton_bind]

/-- Right unit: `μ ∘ Bag(η) = id` — flattening a bag of singletons
is the identity.  By induction on the quotient class (robust against
`bind`/`join` lemma drift). -/
theorem bagMu_map_bagEta (b : BagVal α) :
    bagMu (bagMap bagEta b) = b := by
  apply toMultiset_injective
  rw [toMultiset_bagMu, toMultiset_bagMap]
  induction toMultiset b using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.cons_bind, ih]

/-- Associativity: `μ ∘ μ_{Bag} = μ ∘ Bag(μ)` — the two flattenings
of a three-layer bag agree. -/
theorem bagMu_assoc (b : BagVal (BagVal (BagVal α))) :
    bagMu (bagMu b) = bagMu (bagMap bagMu b) := by
  apply toMultiset_injective
  rw [toMultiset_bagMu, toMultiset_bagMu, toMultiset_bagMu,
      toMultiset_bagMap]
  induction toMultiset b using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp [Multiset.cons_bind, Multiset.add_bind, ih]

/-- Naturality of the unit. -/
theorem bagEta_natural (f : α → β) (x : α) :
    bagMap f (bagEta x) = bagEta (f x) := by
  apply toMultiset_injective
  simp

/-- Naturality of the multiplication. -/
theorem bagMu_natural (f : α → β) (b : BagVal (BagVal α)) :
    bagMap f (bagMu b) = bagMu (bagMap (bagMap f) b) := by
  apply toMultiset_injective
  rw [toMultiset_bagMap, toMultiset_bagMu, toMultiset_bagMu,
      toMultiset_bagMap]
  induction toMultiset b using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp [Multiset.cons_bind, Multiset.map_add, ih]

/-- Interface compatibility, the count half (the aggregate
dictionary's count wire): the count of a flatten is the sum of the
counts. -/
theorem card_bagMu (b : BagVal (BagVal α)) :
    Multiset.card (toMultiset (bagMu b)) =
      ((toMultiset b).map fun inner =>
        Multiset.card (toMultiset inner)).sum := by
  rw [toMultiset_bagMu]
  induction toMultiset b using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.cons_bind, ih]

end MonadOps

/-! ## The strong law: a sum-coloured place is two places

Stated through the free-commutative-monoid exponential law, built on
bind algebra alone (`cons_bind`/`add_bind`/`singleton_bind`) so the
proofs are induction-stable. -/

section StrongLaw

/-- The left projection of a sum-coloured class. -/
def leftPart (s : Multiset (α ⊕ β)) : Multiset α :=
  s.bind (Sum.elim (fun a => {a}) (fun _ => 0))

/-- The right projection of a sum-coloured class. -/
def rightPart (s : Multiset (α ⊕ β)) : Multiset β :=
  s.bind (Sum.elim (fun _ => 0) (fun b => {b}))

@[simp] theorem leftPart_zero : leftPart (0 : Multiset (α ⊕ β)) = 0 := by
  simp [leftPart]

@[simp] theorem rightPart_zero : rightPart (0 : Multiset (α ⊕ β)) = 0 := by
  simp [rightPart]

@[simp] theorem leftPart_cons_inl (x : α) (s : Multiset (α ⊕ β)) :
    leftPart (Sum.inl x ::ₘ s) = x ::ₘ leftPart s := by
  simp [leftPart, Multiset.cons_bind, Multiset.singleton_add]

@[simp] theorem leftPart_cons_inr (y : β) (s : Multiset (α ⊕ β)) :
    leftPart (Sum.inr y ::ₘ s) = leftPart s := by
  simp [leftPart, Multiset.cons_bind]

@[simp] theorem rightPart_cons_inl (x : α) (s : Multiset (α ⊕ β)) :
    rightPart (Sum.inl x ::ₘ s) = rightPart s := by
  simp [rightPart, Multiset.cons_bind]

@[simp] theorem rightPart_cons_inr (y : β) (s : Multiset (α ⊕ β)) :
    rightPart (Sum.inr y ::ₘ s) = y ::ₘ rightPart s := by
  simp [rightPart, Multiset.cons_bind, Multiset.singleton_add]

private theorem leftPart_map_inl (s : Multiset α) :
    leftPart (β := β) (s.map Sum.inl) = s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem leftPart_map_inr (s : Multiset β) :
    leftPart (α := α) (s.map Sum.inr) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem rightPart_map_inl (s : Multiset α) :
    rightPart (β := β) (s.map Sum.inl) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem rightPart_map_inr (s : Multiset β) :
    rightPart (α := α) (s.map Sum.inr) = s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem leftPart_add (s t : Multiset (α ⊕ β)) :
    leftPart (s + t) = leftPart s + leftPart t := by
  simp [leftPart, Multiset.add_bind]

private theorem rightPart_add (s t : Multiset (α ⊕ β)) :
    rightPart (s + t) = rightPart s + rightPart t := by
  simp [rightPart, Multiset.add_bind]

/-- Multisets over a sum split as a product of multisets — the
exponential law of the free commutative monoid, in `Equiv` form. -/
def sumSplit : Multiset (α ⊕ β) ≃ Multiset α × Multiset β where
  toFun s := (leftPart s, rightPart s)
  invFun p := p.1.map Sum.inl + p.2.map Sum.inr
  left_inv s := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rcases a with x | y
      · simpa using congrArg (Sum.inl x ::ₘ ·) ih
      · simpa [Multiset.add_cons] using congrArg (Sum.inr y ::ₘ ·) ih
  right_inv p := by
    obtain ⟨sl, sr⟩ := p
    refine Prod.ext ?_ ?_
    · simp [leftPart_add, leftPart_map_inl, leftPart_map_inr]
    · simp [rightPart_add, rightPart_map_inl, rightPart_map_inr]

/-- The strong law at the canonical-representative stratum: a place
whose colour type is a sum IS two places.  (Any linear order on the
sum serves — the representative type depends on the order, the
quotient content does not, which is the section discipline again.) -/
def bagSumSplit [LinearOrder α] [LinearOrder β] [LinearOrder (α ⊕ β)] :
    BagVal (α ⊕ β) ≃ BagVal α × BagVal β :=
  (bagEquiv.trans sumSplit).trans
    (Equiv.prodCongr bagEquiv bagEquiv).symm

end StrongLaw

/-! ## Axiom receipts (the standard-three closure, per law) -/

#print axioms ofMultiset_toMultiset
#print axioms bagMap_id
#print axioms bagMap_comp
#print axioms bagMu_bagEta
#print axioms bagMu_map_bagEta
#print axioms bagMu_assoc
#print axioms bagEta_natural
#print axioms bagMu_natural
#print axioms card_bagMu
#print axioms sumSplit
#print axioms bagSumSplit

end BagMonad
