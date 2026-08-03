import Qtsl.Catalogue

/-! # Graded satisfaction judgments and formal conjunction

The verdict object of the semantic universe is a *pair* of prevision
operators — lower and upper expectations — and a judgment *kind* selects
which component it constrains:

* `seqValid seq` — a sequent of the certificate calculus, read as the
  degenerate allowed-or-forbidden face: the **upper** probability of the
  violation event (`pre` holds, `post` fails) is bounded by `0`;
* `probGE t φ` — a probability-threshold judgment binding the **lower**
  probability of the event `⟦φ⟧` from below by `t`;
* `probLE t φ` — the dual risk bound, binding the **upper** probability
  of `⟦φ⟧` from above by `t`.

The two components are primitive rather than conjugate: for
subprobability models (mass loss licensed), `inf μ(A)` is not determined
by `sup μ(¬A)`, so no kind is canonicalized away through complements.
The collapse to a single component is a theorem of the total-mass face,
not a definition.

## Composition is formal conjunction

Loose arrows of the source double category are **finite lists of
judgments**, read as formal conjunctions: loose composition is list
concatenation (the free monoid on judgments), the loose identity is the
empty list, and `Judgment.comp` — the composite of two atomic
judgments — is the two-element list.  The composite is a formal object:
it retains both factors and forgets nothing, so the structural
obligations of a composition (associator and unitor squares, congruence
under entailment) are list bookkeeping, discharged once and for all by
`satCoherence` (archived in `SuFunctorLegacy.Functor`).

An earlier revision instead defined composition by a *kind table*: a
total binary operation on single judgments whose informative rows were
the Fréchet and Boole inequalities read as syntax (two lower bounds
composed to a Fréchet-discounted lower bound on the conjunction, two
upper bounds to a Boole sum on the disjunction, two sequents to the
conjunct sequent), with projection rows and a vacuous row making the
table total.  That table was refuted as a loose composition: it sent
the two semantic tautologies — the tautological sequent and the
nonbinding lower bound — through different rows (one erased by
projection, one taxed a full threshold unit by Fréchet), so the
associator squares and the congruence of composition under entailment
failed, uniformly in the model class; and no sound, unital, syntactic
single-judgment table could satisfy all three obligations at once.
`SuFunctorLegacy.Refute` keeps that episode as regression pins.  The table's
informative rows survive, demoted from composition-defining to
*derivable cells* — entailments out of two-element lists, packaged as
rule families in `SuFunctorLegacy.Squares` with their inequality content
intact.
-/

namespace SuFunctor

open PPLC

/-- A graded satisfaction judgment: a constraint on the denotation-level
verdict pair.  The kind selects the constrained component (see the module
docstring).  Thresholds are rational and unconstrained: a lower-kind
judgment with nonpositive threshold, or an upper-kind judgment with
threshold `≥ 1`, is vacuous rather than ill-formed. -/
inductive Judgment : Type
  /-- A sequent of the certificate calculus, as the degenerate
  (allowed-or-forbidden) face: upper probability of violation `≤ 0`. -/
  | seqValid (seq : Sequent)
  /-- Lower-component threshold: `t ≤ P̲(⟦φ⟧)`. -/
  | probGE (t : ℚ) (φ : Formula)
  /-- Upper-component threshold: `P̅(⟦φ⟧) ≤ t`. -/
  | probLE (t : ℚ) (φ : Formula)

namespace Judgment

/-- The sequent face of the judgment layer (the checker's semantic
anchor: a checked sequent enters the graded layer through this
constructor). -/
def ofSequent (seq : Sequent) : Judgment := seqValid seq

/-- The tautological sequent judgment `tt ⊢ tt`, satisfied by every
model.  The loose identity of the source double category is the empty
list; this atom is its one-element shadow, and the cell from `[unit]`
down to `[]` is an instance of the structural (projection) family. -/
def unit : Judgment := seqValid ⟨.tt, .tt⟩

/-- The vacuous probability judgment (a nonbinding lower bound),
likewise satisfied by every model. -/
def vacuous : Judgment := probGE 0 .tt

/-- Composition of two atomic judgments: the formal pair.  This is the
restriction of loose composition (list concatenation) to single
judgments — `[m] ++ [n] = m.comp n` holds definitionally — and it
retains both components: nothing is projected, taxed, or funnelled. -/
def comp (m n : Judgment) : List Judgment := [m, n]

@[simp] theorem comp_def (m n : Judgment) : m.comp n = [m, n] := rfl

/-- Atomic composition is loose composition of singletons, on the
nose. -/
theorem singleton_append_singleton (m n : Judgment) :
    [m] ++ [n] = m.comp n := rfl

end Judgment

end SuFunctor
