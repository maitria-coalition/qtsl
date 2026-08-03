/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: regression pins for the retired kind-table composition.
The design decision the pins guard — loose composition as formal
conjunction — remains live in `SuFunctor.Judgment`; the pins themselves
are stated against this retired tier's satisfaction semantics, so they
are archived with it.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Functor

/-! # Regression pins: the retired kind-table composition

An earlier revision of this package defined loose composition as a
*kind table*: a total binary operation on single judgments
(`Judgment.comp : Judgment → Judgment → Judgment`) whose informative
rows were the Fréchet and Boole inequalities read as syntax, with
projection rows and a vacuous row making the table total.  This module
then proved the three structural obligations of the semantic functor
**false** for that table, uniformly in the hypernet: the table sent its
two semantic tautologies — the tautological sequent and the nonbinding
lower bound — through different rows (one erased by projection, one
taxed a full threshold unit by Fréchet), and the associator squares and
the congruence of composition under entailment all failed on exactly
that asymmetry, witnessed by the zero mass function (`SubPMF.zero`,
now in `SuFunctor.Target`) at thresholds inside `[0, 1]` with
`tt`-only formulas.  A hand-verified analysis bounded the repair space:
no sound, unital, syntactic single-judgment table satisfies all three
obligations — soundness pins the graded rows at or below the Fréchet
threshold (the inequality is tight on generic events), the proved
unitor squares force unit transparency, and syntacticity forbids the
table from reading event emptiness.

The repair moved structure instead of thresholds: loose composition is
now **formal conjunction** (`Judgment.comp` returns the two-element
list; lists compose by concatenation), the three obligations are the
proven `satCoherence`, and the table's informative rows are demoted to
derivable cells (`unionBoundFamily`, `frechetFamily`, `seqConjFamily`,
with the projection rows in `projFamily`).

This module keeps the refutations in their strongest surviving form:
**the retired design's characteristic sentences no longer typecheck.**
Each pin below asserts, via `#guard_msgs`, that such a sentence is a
type error against the repaired definitions; each is paired with a
positive twin asserting the repaired meaning of the same sentence, so
that a rename or refactor breaks the twin loudly rather than letting
its pin pass vacuously.  If a future revision reintroduces a
single-judgment composition, these pins fail the build, and the
countermodels recorded above must be confronted again: any total table
whose unit is transparent and whose graded rows are sound taxes some
tautology that another grouping erases. -/

namespace SuFunctor

open PPLC

/-! ## Pin 1: the mixed-row funnel

The retired table collapsed every mixed lower/upper premise pair to the
vacuous judgment — the interface obstruction that blocked the safety
battery's family entry.  The collapse was once provable by `rfl`; its
statement is now a type error, because composition returns the pair. -/

/--
error: Type mismatch
  Judgment.vacuous
has type
  Judgment
but is expected to have type
  List Judgment
-/
#guard_msgs in
example (p : ℚ) (U : Formula) : Prop :=
  (Judgment.probLE (1 - p) U).comp (Judgment.probGE 1 .tt) =
    Judgment.vacuous

/-- Positive twin: the same composite retains the pair, on the nose. -/
example (p : ℚ) (U : Formula) :
    (Judgment.probLE (1 - p) U).comp (Judgment.probGE 1 .tt) =
      [.probLE (1 - p) U, .probGE 1 .tt] :=
  rfl

/-! ## Pin 2: the Fréchet row as a composition

The graded row that taxed the vacuous judgment — composing two lower
bounds *into a single judgment* at the Fréchet-discounted threshold —
is no longer a statement about composition.  (Its inequality content
survives as the derivable cell `frechetFamily`.) -/

/--
error: Type mismatch
  Judgment.probGE (t₁ + t₂ - 1) (φ₁.and φ₂)
has type
  Judgment
but is expected to have type
  List Judgment
-/
#guard_msgs in
example (t₁ t₂ : ℚ) (φ₁ φ₂ : Formula) : Prop :=
  (Judgment.probGE t₁ φ₁).comp (Judgment.probGE t₂ φ₂) =
    Judgment.probGE (t₁ + t₂ - 1) (.and φ₁ φ₂)

/-- Positive twin: the composite of two lower bounds is their formal
pair; no threshold arithmetic happens at composition time. -/
example (t₁ t₂ : ℚ) (φ₁ φ₂ : Formula) :
    (Judgment.probGE t₁ φ₁).comp (Judgment.probGE t₂ φ₂) =
      [.probGE t₁ φ₁, .probGE t₂ φ₂] :=
  rfl

/-! ## Pin 3: satisfaction of a one-slot composite

`Sat` reads atomic judgments; loose arrows are lists, read by
`SatConj`.  The retired design's `Sat H (m.comp n) μ` — satisfaction of
a composite *judgment* — is a type error. -/

/--
error: Application type mismatch: The argument
  m.comp n
has type
  List Judgment
but is expected to have type
  Judgment
in the application
  Sat H (m.comp n)
-/
#guard_msgs in
example (H : Hypernet) (m n : Judgment) (μ : SubPMF (AdmVal H)) : Prop :=
  Sat H (m.comp n) μ

/-- Positive twin: the composite is read conjunctively. -/
example (H : Hypernet) (m n : Judgment) (μ : SubPMF (AdmVal H)) : Prop :=
  SatConj H (m.comp n) μ

/-! ## Pin 4: the coherence bundle quantifies over lists

The bundle's fields once took single judgments — and were refuted.
They now take formal conjunctions, and the bundle is a theorem. -/

/--
error: Application type mismatch: The argument
  m
has type
  Judgment
but is expected to have type
  List Judgment
in the application
  hC.assoc m
-/
#guard_msgs in
example (H : Hypernet) (hC : SatCoherence H) (m n p : Judgment) :=
  hC.assoc m n p

/-- Positive twin: the proven bundle, applied at lists.  (Reverting to
any composition for which this bundle is unprovable breaks
`satCoherence`, which is the positive direction of this regression
instrument.) -/
example (H : Hypernet) (m n p : List Judgment) (μ : SubPMF (AdmVal H))
    (h : SatConj H ((m ++ n) ++ p) μ) : SatConj H (m ++ (n ++ p)) μ :=
  (satCoherence H).assoc m n p μ h

end SuFunctor
