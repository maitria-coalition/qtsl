import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic

/-! # Negation normal form and duality for threshold atoms

This module proves the metatheory of the negation-normal-form (NNF) transform
used to compile Boolean state formulas into positive form.

* `Form α`: Boolean formulas over atoms `α`, with negation, conjunction, and
  disjunction; `NForm α`: negation-normal formulas, where negation appears only
  on literals (`NForm.negLit`).
* `Form.nnf`: the polarity-propagating NNF transform (via `Form.nnfAux`), with
  semantic correctness `denot_nnf`: the set denotation of `φ.nnf` equals that
  of `φ` for every denotation of the atoms.
* `NForm.negLits` and `Form.occs`: the negated literals of the normal form are
  exactly the negative-polarity atom occurrences of the source formula
  (`negLits_nnf`, `nnf_no_negLit_iff`).
* `NForm.elimNeg`: elimination of negated literals through an atom-level
  duality `d : α → α`; if `den (d a) = (den a)ᶜ` for every atom, denotation is
  preserved (`denot_elimNeg`) and no negated literals remain
  (`negLits_elimNeg`).
* The `AtomSwaps` section provides the concrete dualities for threshold atoms
  over a real-valued observable: the complement of each of `{x | f x ≤ c}`,
  `{x | f x < c}`, `{x | c ≤ f x}`, `{x | c < f x}` is the opposite
  strict/non-strict threshold set.
-/

namespace Qtsl.NNF

section AtomSwaps

variable {σ : Type*} (f : σ → ℝ) (c : ℝ)

/-- The complement of the non-strict sublevel set `{x | f x ≤ c}` is the strict
superlevel set `{x | c < f x}`. -/
theorem compl_le_atom : {x | f x ≤ c}ᶜ = {x | c < f x} := by
  ext x; simp [not_le]

/-- The complement of the strict sublevel set `{x | f x < c}` is the non-strict
superlevel set `{x | c ≤ f x}`. -/
theorem compl_lt_atom : {x | f x < c}ᶜ = {x | c ≤ f x} := by
  ext x; simp [not_lt]

/-- The complement of the non-strict superlevel set `{x | c ≤ f x}` is the
strict sublevel set `{x | f x < c}`. -/
theorem compl_ge_atom : {x | c ≤ f x}ᶜ = {x | f x < c} := by
  ext x; simp [not_le]

/-- The complement of the strict superlevel set `{x | c < f x}` is the
non-strict sublevel set `{x | f x ≤ c}`. -/
theorem compl_gt_atom : {x | c < f x}ᶜ = {x | f x ≤ c} := by
  ext x; simp [not_lt]

end AtomSwaps

/-- Boolean formulas over atoms `α`, built from atoms by negation, conjunction,
and disjunction. -/
inductive Form (α : Type*) where
  | atom : α → Form α
  | neg : Form α → Form α
  | and : Form α → Form α → Form α
  | or : Form α → Form α → Form α

/-- Formulas in negation normal form: negation occurs only in the literal
former `negLit`, and the connectives are conjunction and disjunction. -/
inductive NForm (α : Type*) where
  | pos : α → NForm α
  | negLit : α → NForm α
  | and : NForm α → NForm α → NForm α
  | or : NForm α → NForm α → NForm α

variable {α : Type*}

/-- Polarity-propagating normalization: `φ.nnfAux true` computes the negation
normal form of `φ`, while `φ.nnfAux false` computes that of `¬φ`, pushing
negations to the leaves by De Morgan duality. -/
def Form.nnfAux : Form α → Bool → NForm α
  | .atom a, true => .pos a
  | .atom a, false => .negLit a
  | .neg φ, b => φ.nnfAux (!b)
  | .and φ ψ, true => .and (φ.nnfAux true) (ψ.nnfAux true)
  | .and φ ψ, false => .or (φ.nnfAux false) (ψ.nnfAux false)
  | .or φ ψ, true => .or (φ.nnfAux true) (ψ.nnfAux true)
  | .or φ ψ, false => .and (φ.nnfAux false) (ψ.nnfAux false)

/-- The negation normal form of a Boolean formula. -/
def Form.nnf (φ : Form α) : NForm α := φ.nnfAux true

section Denotation

variable {σ : Type*} (den : α → Set σ)

/-- Set denotation of a Boolean formula, given a denotation of the atoms:
negation is complement, conjunction is intersection, disjunction is union. -/
def Form.denot (den : α → Set σ) : Form α → Set σ
  | .atom a => den a
  | .neg φ => (Form.denot den φ)ᶜ
  | .and φ ψ => Form.denot den φ ∩ Form.denot den ψ
  | .or φ ψ => Form.denot den φ ∪ Form.denot den ψ

/-- Set denotation of a negation-normal formula; a negated literal denotes the
complement of its atom's denotation. -/
def NForm.denot (den : α → Set σ) : NForm α → Set σ
  | .pos a => den a
  | .negLit a => (den a)ᶜ
  | .and φ ψ => NForm.denot den φ ∩ NForm.denot den ψ
  | .or φ ψ => NForm.denot den φ ∪ NForm.denot den ψ

/-- `φ.nnfAux b` denotes `φ` when `b = true` and the complement of `φ` when
`b = false`. -/
theorem denot_nnfAux : ∀ (φ : Form α) (b : Bool),
    (φ.nnfAux b).denot den = if b then φ.denot den else (φ.denot den)ᶜ := by
  intro φ
  induction φ with
  | atom a => intro b; cases b <;> simp [Form.nnfAux, Form.denot, NForm.denot]
  | neg φ ih =>
    intro b
    cases b <;> simp [Form.nnfAux, Form.denot, ih]
  | and φ ψ ihφ ihψ =>
    intro b
    cases b <;> simp [Form.nnfAux, Form.denot, NForm.denot, ihφ, ihψ, Set.compl_inter]
  | or φ ψ ihφ ihψ =>
    intro b
    cases b <;> simp [Form.nnfAux, Form.denot, NForm.denot, ihφ, ihψ, Set.compl_union]

/-- Semantic correctness of the NNF transform: `φ.nnf` and `φ` have the same
set denotation. -/
theorem denot_nnf (φ : Form α) : (φ.nnf).denot den = φ.denot den := by
  simpa [Form.nnf] using denot_nnfAux den φ true

end Denotation

/-- The set of atoms occurring as negated literals in a negation-normal
formula. -/
def NForm.negLits : NForm α → Set α
  | .pos _ => ∅
  | .negLit a => {a}
  | .and φ ψ => φ.negLits ∪ ψ.negLits
  | .or φ ψ => φ.negLits ∪ ψ.negLits

/-- `φ.occs b` is the set of atoms occurring in `φ` with polarity `b`
(`true` for positive occurrences, `false` for negative ones); negation flips
the polarity. -/
def Form.occs : Form α → Bool → Set α
  | .atom a, true => {a}
  | .atom _, false => ∅
  | .neg φ, b => φ.occs (!b)
  | .and φ ψ, b => φ.occs b ∪ ψ.occs b
  | .or φ ψ, b => φ.occs b ∪ ψ.occs b

/-- The negated literals of `φ.nnfAux b` are exactly the occurrences of `φ`
with the opposite polarity `!b`. -/
theorem negLits_nnfAux : ∀ (φ : Form α) (b : Bool),
    (φ.nnfAux b).negLits = φ.occs (!b) := by
  intro φ
  induction φ with
  | atom a => intro b; cases b <;> rfl
  | neg φ ih =>
    intro b
    rw [Form.nnfAux, ih, Form.occs]
  | and φ ψ ihφ ihψ =>
    intro b
    cases b <;> simp [Form.nnfAux, Form.occs, NForm.negLits, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    intro b
    cases b <;> simp [Form.nnfAux, Form.occs, NForm.negLits, ihφ, ihψ]

/-- The negated literals of the negation normal form are exactly the
negative-polarity atom occurrences of the source formula. -/
theorem negLits_nnf (φ : Form α) : (φ.nnf).negLits = φ.occs false := by
  simpa [Form.nnf] using negLits_nnfAux φ true

/-- A predicate fails on every negated literal of `φ.nnf` iff it fails on every
negative-polarity occurrence of `φ`. -/
theorem nnf_no_negLit_iff (φ : Form α) (P : α → Prop) :
    (∀ a ∈ (φ.nnf).negLits, ¬ P a) ↔ ∀ a ∈ φ.occs false, ¬ P a := by
  rw [negLits_nnf]

/-- Eliminate negated literals by replacing each `negLit a` with the positive
literal on the dual atom `d a`. -/
def NForm.elimNeg (d : α → α) : NForm α → NForm α
  | .pos a => .pos a
  | .negLit a => .pos (d a)
  | .and φ ψ => .and (φ.elimNeg d) (ψ.elimNeg d)
  | .or φ ψ => .or (φ.elimNeg d) (ψ.elimNeg d)

/-- After `elimNeg`, no negated literals remain. -/
theorem negLits_elimNeg (d : α → α) : ∀ φ : NForm α, (φ.elimNeg d).negLits = ∅ := by
  intro φ
  induction φ with
  | pos a => rfl
  | negLit a => rfl
  | and φ ψ ihφ ihψ => simp [NForm.elimNeg, NForm.negLits, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [NForm.elimNeg, NForm.negLits, ihφ, ihψ]

/-- If each dual atom denotes the complement of its source atom
(`den (d a) = (den a)ᶜ`), then `elimNeg` preserves denotation. -/
theorem denot_elimNeg {σ : Type*} (den : α → Set σ) (d : α → α)
    (hd : ∀ a, den (d a) = (den a)ᶜ) :
    ∀ φ : NForm α, (φ.elimNeg d).denot den = φ.denot den := by
  intro φ
  induction φ with
  | pos a => rfl
  | negLit a => simp [NForm.elimNeg, NForm.denot, hd]
  | and φ ψ ihφ ihψ => simp [NForm.elimNeg, NForm.denot, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [NForm.elimNeg, NForm.denot, ihφ, ihψ]

end Qtsl.NNF
