import SuFunctor.Adequacy.Dtmc

/-! # Adequacy: continuous-time Markov chains, jump-chain face

The continuous-time adequacy square at its **time-abstract stratum**.
A finite continuous-time Markov chain is presented classically — a
finite state space, nonnegative off-diagonal transition rates, an
initial distribution (Norris, *Markov Chains*, §2.6: the jump chain /
holding times decomposition) — and compiled to the sparse row grain of
the CTMC system profile: off-diagonal rate rows keyed `(src, dst)` with
`src ≠ dst` *as a formation premise* — a diagonal entry is
unrepresentable rather than linted, mirroring the shipped theory — plus
initial-distribution rows.  The diagonal of the literature's Q-matrix
is *determined* (`q(s,s) = -q(s)` with `q(s)` the exit rate) and
deliberately not stored; nothing in this module ever reads it, and the
blindness receipts (`compileCtmc_diag_blind`, `jumpLaw_diag_blind`)
state that design fact as theorems.

**The jump chain.**  The embedded discrete-time skeleton of the chain:
from a non-absorbing state `s` the next state is `s'` with probability
`q(s,s') / q(s)`; an absorbing state (exit rate zero) holds itself with
probability one — Norris's jump-matrix convention.  This is exact
rational arithmetic, and the jump chain of a well-formed rate object is
row-stochastic *by theorem*: the rate grain's well-formedness carries
no row-sum constraint (rates are unconstrained nonnegatives — the
frame's whole point), so the stochasticity of the jump chain is
derived, never assumed.

**The square** (`ctmc_jump_adequacy`): compile the rate rows, close
them to jump rows at the row level, denote — and this agrees, by an
invertible globular cell of `Crd (Traj S k)`, with interpreting
classically (the path law of the jump chain at jump horizon `k`) and
including through `singletonC`.  The proof is the chain square
*instantiated at the jump chain*: the one CTMC-specific identity is the
compile-commutes triangle `compile_jump_comm` — jump-closing before or
after compilation stores the same rows — and `dtmc_adequacy` finishes.
No new induction: every stochasticity fact was already spent, once, in
the chain engine.  The record space is **jump-indexed** — `Traj S k`
records the first `k` jumps — not time-indexed.

The rate-factorization identity (`jumpChain_step_mul_exit`,
unconditional: absorbing states included) recovers the rates from the
jump probabilities and the exit rates — the seam a Markov-automaton
rate closure consumes.

**Semantic-universe anchor** (the descent direction, explicit): this
square is a descent statement of the mathematical-models chapter,
derived downward from the mechanized semantic universe.  Its storey is
the SU's spec fibres — `SpecDnf (Plain.Joint (Traj S k))`, the very
fibres the spacetime total inherits definitionally
(`spacetimeSpecFunctor_fibre_eq`) — judged by `CoupledSat`; the landed
theorems it rides are the chain engine (`satAtoms_iff`,
`dtmc_adequacy`) and the judgment bridge
(`coupledSat_idealPoint_cwall_iff`, consumed through `su_dtmc_wiring`);
its own SU citizenship is mechanized in the same leg
(`su_ctmc_jump_adequacy`, `SemanticUniverseWiring`).  No new fibre
vocabulary is introduced: the compiled grain mirrored is the shipped
theory's, and the closure is stated against the landed per-element
stratum, not a pre-universe certificate dialect.

Deliberately separate strata, named: the **time-law stratum** —
exponential holding times `Exp(q(s))`, whose transients (`e^{-q(s)t}`)
are irrational, hence outside this exact-rational grain; the full
continuous-time path semantics is this square *plus* that stratum, and
the finite-state path-measure construction the chapter's Semantics
paragraph names lives there.  **Uniformization** is a *different*
discrete reduction (self-loops against a common rate, Poisson
subordination), not this one.  The infinite-horizon extension is
separate exactly as for chains.  mathlib has no continuous-time Markov
machinery, so the community-vocabulary connector is the chain connector
transported through the jump chain (`jumpTrajPMF_eq`) — stated as such,
not dressed as more. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## The classical object -/

/-- A finite continuous-time Markov chain, as the literature presents
it: a finite state space, transition rates, an initial distribution
(Norris, *Markov Chains*, Ch. 2).  Entries are rational — the
exact-arithmetic class of the compiled rows.  Only the off-diagonal
rates are data: the literature's diagonal `q(s,s) = -q(s)` is
determined, so it is neither stored nor constrained here, and no
definition below reads it (the blindness receipts state this as
theorems). -/
structure FinCTMC (S : Type) [Fintype S] where
  /-- Transition rate from the first state to the second; only
  off-diagonal values are ever consulted. -/
  rate : S → S → ℚ
  /-- Initial-distribution mass at a state. -/
  init : S → ℚ
  rate_nonneg : ∀ s s', s ≠ s' → 0 ≤ rate s s'
  init_nonneg : ∀ s, 0 ≤ init s
  init_sum : ∑ s, init s = 1

/-- The off-diagonal rate read: zero on the diagonal, the stored rate
off it.  Every consumer of the rates goes through this read — the
"diagonal determined" convention held semantically. -/
def FinCTMC.offRate (M : FinCTMC S) (s s' : S) : ℚ :=
  if _h : s = s' then 0 else M.rate s s'

theorem FinCTMC.offRate_nonneg (M : FinCTMC S) (s s' : S) :
    0 ≤ M.offRate s s' := by
  unfold FinCTMC.offRate
  split
  · exact le_rfl
  · exact M.rate_nonneg s s' ‹s ≠ s'›

@[simp] theorem FinCTMC.offRate_diag (M : FinCTMC S) (s : S) :
    M.offRate s s = 0 := by
  unfold FinCTMC.offRate
  rw [dif_pos rfl]

theorem FinCTMC.offRate_of_ne (M : FinCTMC S) {s s' : S} (h : s ≠ s') :
    M.offRate s s' = M.rate s s' := by
  unfold FinCTMC.offRate
  rw [dif_neg h]

/-- The exit rate: total rate out of a state.  The literature's
`q(s)`; the determined diagonal is `-q(s)`. -/
def FinCTMC.exitRate (M : FinCTMC S) (s : S) : ℚ :=
  ∑ s', M.offRate s s'

theorem FinCTMC.exitRate_nonneg (M : FinCTMC S) (s : S) :
    0 ≤ M.exitRate s :=
  Finset.sum_nonneg fun s' _ => M.offRate_nonneg s s'

/-- An absorbing state has no outgoing rate at all: a zero exit rate
kills every off-diagonal entry (nonnegative terms summing to zero). -/
theorem FinCTMC.offRate_eq_zero_of_exitRate_eq_zero (M : FinCTMC S)
    {s : S} (h : M.exitRate s = 0) (s' : S) : M.offRate s s' = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => M.offRate_nonneg s t)).mp h s' (mem_univ s')

/-! ## The jump step: one normalizer, shared by the classical and the
row-level readings -/

/-- The jump-step normalizer of an arbitrary rate read: from a state
with nonzero total outgoing rate, each destination in proportion to its
rate; from a state with zero total rate, the absorbing self-loop —
Norris's jump-matrix convention (`Markov Chains`, §2.6).  Defined over
a bare rate function so the classical chain and the compiled rows read
through the *same* normalizer, which is what makes the
compile-commutes triangle definitional. -/
def jumpStep (r : S → S → ℚ) (s s' : S) : ℚ :=
  if _h : (∑ t, r s t) = 0 then (if s' = s then 1 else 0)
  else r s s' / ∑ t, r s t

theorem jumpStep_nonneg (r : S → S → ℚ) (s : S)
    (hr : ∀ t, 0 ≤ r s t) (s' : S) : 0 ≤ jumpStep r s s' := by
  unfold jumpStep
  split
  · split <;> norm_num
  · exact div_nonneg (hr s') (Finset.sum_nonneg fun t _ => hr t)

/-- The jump step is row-stochastic *unconditionally*: the absorbing
branch is a point mass, and the normalized branch telescopes to
`q(s)/q(s)`.  No nonnegativity is needed — the stochasticity of the
jump chain is arithmetic, not an assumption. -/
theorem jumpStep_row_sum (r : S → S → ℚ) (s : S) :
    ∑ s', jumpStep r s s' = 1 := by
  unfold jumpStep
  by_cases h : (∑ t, r s t) = 0
  · simp only [dif_pos h]
    rw [Finset.sum_ite_eq' univ s (fun _ => (1 : ℚ))]
    simp
  · simp only [dif_neg h]
    rw [← Finset.sum_div]
    exact div_self h

/-! ## The jump chain, classically -/

/-- The jump chain of a continuous-time Markov chain: the embedded
discrete-time skeleton, exact-rational.  Row-stochasticity is proved,
not assumed: the rate object carries no row-sum constraint. -/
noncomputable def FinCTMC.jumpChain (M : FinCTMC S) : FinDTMC S where
  step := jumpStep M.offRate
  init := M.init
  step_nonneg s s' := jumpStep_nonneg M.offRate s
    (fun t => M.offRate_nonneg s t) s'
  step_row_sum s := jumpStep_row_sum M.offRate s
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

@[simp] theorem FinCTMC.jumpChain_init (M : FinCTMC S) (s : S) :
    M.jumpChain.init s = M.init s := rfl

/-- The jump-chain step, spelled at the exit-rate vocabulary. -/
theorem FinCTMC.jumpChain_step (M : FinCTMC S) (s s' : S) :
    M.jumpChain.step s s' =
      if M.exitRate s = 0 then (if s' = s then 1 else 0)
      else M.offRate s s' / M.exitRate s := by
  show jumpStep M.offRate s s' = _
  unfold jumpStep FinCTMC.exitRate
  by_cases h : (∑ t, M.offRate s t) = 0
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

/-- **The rate-factorization identity**, unconditional: jump
probability times exit rate recovers the off-diagonal rate — at
absorbing states both sides vanish.  This is the recovery direction of
the jump-chain/holding-time decomposition, and the seam a
Markov-automaton rate closure consumes. -/
theorem FinCTMC.jumpChain_step_mul_exit (M : FinCTMC S) (s s' : S) :
    M.jumpChain.step s s' * M.exitRate s = M.offRate s s' := by
  rw [FinCTMC.jumpChain_step]
  by_cases h : M.exitRate s = 0
  · rw [if_pos h, h, mul_zero,
      M.offRate_eq_zero_of_exitRate_eq_zero h s']
  · rw [if_neg h, div_mul_cancel₀ _ h]

/-- A state is absorbing exactly when its jump chain holds it with
probability one. -/
theorem FinCTMC.absorbing_iff (M : FinCTMC S) (s : S) :
    M.exitRate s = 0 ↔ M.jumpChain.step s s = 1 := by
  rw [FinCTMC.jumpChain_step]
  constructor
  · intro h
    rw [if_pos h, if_pos rfl]
  · intro h
    by_contra hne
    rw [if_neg hne, FinCTMC.offRate_diag, zero_div] at h
    exact one_ne_zero h.symm

/-- **The classical semantics of the jump-chain face**: the path law of
the embedded jump chain at jump horizon `k` — which states, in which
order, the first `k` jumps visit.  The holding times are the separate
time-law stratum. -/
noncomputable def FinCTMC.jumpLaw (M : FinCTMC S) (k : ℕ) :
    SubPMF (Traj S k) :=
  M.jumpChain.pathLaw k

/-- The jump-chain face spends its whole mass — inherited from the
chain engine, one line. -/
theorem FinCTMC.jumpLaw_mass (M : FinCTMC S) (k : ℕ) :
    (M.jumpLaw k).mass = 1 :=
  FinDTMC.pathLaw_mass M.jumpChain k

/-! ## The compiled rows: off-diagonal keys by construction -/

/-- The compiled presentation: the row grain of the CTMC system
profile.  Rate rows are keyed by *off-diagonal* pairs — `src ≠ dst` is
part of the key's type, so a diagonal entry is unrepresentable rather
than linted, exactly the shipped theory's convention.  Sparse: an
absent row and a zero entry are the same datum. -/
structure CtmcRows (S : Type) where
  /-- Off-diagonal rate rows: `(src, dst) ↦` stored rate, with
  `src ≠ dst` carried by the key. -/
  rateRow : {p : S × S // p.1 ≠ p.2} →₀ ℚ
  /-- Initial-distribution rows: `state ↦` stored mass. -/
  initRow : S →₀ ℚ

/-- Well-formedness of a rate-row set: nonnegative rates, initial rows
a distribution.  Deliberately **no row-sum constraint on the rates**:
rates are unconstrained nonnegatives, and the row-stochasticity of the
jump closure is a theorem (`jumpRows_wf`), never a hypothesis. -/
structure CtmcRows.WF [Fintype S] (R : CtmcRows S) : Prop where
  rate_nonneg : ∀ p, 0 ≤ R.rateRow p
  init_nonneg : ∀ s, 0 ≤ R.initRow s
  init_sum : ∑ s, R.initRow s = 1

/-- The total off-diagonal read of a row set: zero on the diagonal —
where no key exists — and the stored row off it.  The row-level twin
of `FinCTMC.offRate`, with the same definitional shape. -/
def CtmcRows.rateAt (R : CtmcRows S) (s s' : S) : ℚ :=
  if h : s = s' then 0 else R.rateRow ⟨(s, s'), h⟩

theorem CtmcRows.rateAt_nonneg {R : CtmcRows S} (hR : R.WF) (s s' : S) :
    0 ≤ R.rateAt s s' := by
  unfold CtmcRows.rateAt
  split
  · exact le_rfl
  · exact hR.rate_nonneg _

@[simp] theorem CtmcRows.rateAt_diag (R : CtmcRows S) (s : S) :
    R.rateAt s s = 0 := by
  unfold CtmcRows.rateAt
  rw [dif_pos rfl]

/-- The row-level exit rate. -/
def CtmcRows.exitRow (R : CtmcRows S) (s : S) : ℚ :=
  ∑ s', R.rateAt s s'

/-- Compilation: store the off-diagonal entries — the key's type is
what makes compilation *unable* to read the diagonal — and the initial
distribution.  Dropping zero rows is definitionally invisible on the
finitely supported representation. -/
noncomputable def compileCtmc (M : FinCTMC S) : CtmcRows S where
  rateRow := Finsupp.onFinset univ (fun p => M.rate p.1.1 p.1.2)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ M.init (fun _ _ => mem_univ _)

@[simp] theorem compileCtmc_rateRow (M : FinCTMC S)
    (p : {p : S × S // p.1 ≠ p.2}) :
    (compileCtmc M).rateRow p = M.rate p.1.1 p.1.2 := rfl

@[simp] theorem compileCtmc_initRow (M : FinCTMC S) (s : S) :
    (compileCtmc M).initRow s = M.init s := rfl

theorem compileCtmc_wf (M : FinCTMC S) : (compileCtmc M).WF where
  rate_nonneg p := M.rate_nonneg p.1.1 p.1.2 p.2
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

/-- The compiled off-diagonal read is the classical one — both sides
are the same dite on the same data. -/
theorem compileCtmc_rateAt (M : FinCTMC S) :
    (compileCtmc M).rateAt = M.offRate := rfl

/-! ## The row-level jump closure and the triangle -/

/-- **The jump closure at the row level**: close the compiled rate rows
to ordinary chain rows through the shared normalizer; the initial rows
pass through.  This is the composite the compiled grain means by "the
jump chain is derived from the rates": assembled from the stored rows,
not stored itself. -/
noncomputable def jumpRows (R : CtmcRows S) : DtmcRows S where
  outcome := Finsupp.onFinset univ
    (fun p => jumpStep R.rateAt p.1 p.2) (fun _ _ => mem_univ _)
  initRow := R.initRow

@[simp] theorem jumpRows_outcome (R : CtmcRows S) (p : S × S) :
    (jumpRows R).outcome p = jumpStep R.rateAt p.1 p.2 := rfl

@[simp] theorem jumpRows_initRow (R : CtmcRows S) (s : S) :
    (jumpRows R).initRow s = R.initRow s := rfl

/-- Jump closure preserves well-formedness — and *creates* the row-sum
facts: the closed rows are row-stochastic although the rate rows
carried no such constraint.  The derived-stochasticity theorem at the
row level. -/
theorem jumpRows_wf {R : CtmcRows S} (hR : R.WF) : (jumpRows R).WF where
  outcome_nonneg p := jumpStep_nonneg R.rateAt p.1
    (fun t => CtmcRows.rateAt_nonneg hR p.1 t) p.2
  row_sum s := jumpStep_row_sum R.rateAt s
  init_nonneg := hR.init_nonneg
  init_sum := hR.init_sum

/-- **The compile-commutes triangle**: jump-closing the compiled rate
rows is the compilation of the classical jump chain.  Definitional —
both routes read the same off-diagonal data through the same
normalizer — and the square's one genuinely CTMC-shaped obligation:
well-formedness alone cannot see the rates (any rate row set closes to
*some* stochastic rows); this triangle is what pins the closure to the
declared rates. -/
theorem compile_jump_comm (M : FinCTMC S) :
    jumpRows (compileCtmc M) = compile M.jumpChain := rfl

/-! ## The square -/

/-- **Adequacy of the CTMC compilation, jump-chain face.**

In the double category `Crd (Traj S k)` of per-element credal
constraints over jump-horizon-`k` trajectories: the loose-arrow diagram
denoted by the *jump closure* of the compiled rate rows — off-diagonal
rate rows, closed to chain rows at the row level — is isomorphic, by an
invertible globular cell, to the singleton-credal inclusion of the
classical jump chain's path law.  Compile-close-denote agrees with
interpret-then-include, at the time-abstract stratum.

The proof is the chain square instantiated at the jump chain: by
`compile_jump_comm` the closure's rows *are* the jump chain's compiled
rows, and `dtmc_adequacy` finishes.  No new induction — the engine is
reused wholesale. -/
theorem ctmc_jump_adequacy (M : FinCTMC S) (k : ℕ) {a : Crd (Traj S k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows (compileCtmc M)) k) : Loose a a)
        (singletonC (M.jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  dtmc_adequacy M.jumpChain k

/-! ## The blindness receipts -/

/-- **Compilation is diagonal-blind, structurally**: two chains
agreeing off-diagonally and on the initial distribution compile to
*equal* rows — the key type cannot express a diagonal read.  The
design receipt for "diagonal determined, diagonal tamper
unrepresentable", at the compilation level. -/
theorem compileCtmc_diag_blind (M M' : FinCTMC S)
    (hoff : ∀ s s', s ≠ s' → M.rate s s' = M'.rate s s')
    (hinit : M.init = M'.init) : compileCtmc M = compileCtmc M' := by
  unfold compileCtmc
  congr 1
  · exact Finsupp.ext fun p => hoff p.1.1 p.1.2 p.2
  · exact Finsupp.ext fun s => congrFun hinit s

/-- The off-diagonal read is diagonal-blind. -/
theorem FinCTMC.offRate_diag_blind (M M' : FinCTMC S)
    (hoff : ∀ s s', s ≠ s' → M.rate s s' = M'.rate s s') :
    M.offRate = M'.offRate := by
  funext s s'
  unfold FinCTMC.offRate
  split
  · rfl
  · exact hoff s s' ‹s ≠ s'›

/-- **The jump-chain law is diagonal-blind**: the classical semantics
of the jump-chain face depends only on the data the compiled grain
stores.  The design receipt at the path-law level, at every jump
horizon. -/
theorem FinCTMC.jumpLaw_diag_blind (M M' : FinCTMC S)
    (hoff : ∀ s s', s ≠ s' → M.rate s s' = M'.rate s s')
    (hinit : M.init = M'.init) (k : ℕ) :
    M.jumpLaw k = M'.jumpLaw k := by
  have hstep : M.jumpChain.step = M'.jumpChain.step := by
    show jumpStep M.offRate = jumpStep M'.offRate
    rw [FinCTMC.offRate_diag_blind M M' hoff]
  refine SubPMF.ext' (Finsupp.ext fun ω => ?_)
  show chainWt M.jumpChain.init M.jumpChain.step ω =
    chainWt M'.jumpChain.init M'.jumpChain.step ω
  rw [hstep]
  show chainWt M.init M'.jumpChain.step ω =
    chainWt M'.init M'.jumpChain.step ω
  rw [hinit]

/-! ## The connector, transported

mathlib has no continuous-time Markov machinery, so there is no
community-mechanized object for the full continuous-time law; the
community tie of this face is the chain connector at the jump-chain
instance — the jump chain *is* a discrete-time chain, and its law is
the standard iterated monadic construction.  The exponential time-law
stratum is deliberately elsewhere. -/

/-- The jump-chain trajectory law by the standard monadic
construction — the chain construction at the jump chain. -/
noncomputable def FinCTMC.jumpTrajPMF (M : FinCTMC S) (k : ℕ) :
    PMF (Traj S k) :=
  M.jumpChain.trajPMF k

/-- **The connector, transported**: the exact-rational jump-chain law
and the monadic construction agree under the canonical coercion — the
chain connector at the jump-chain instance. -/
theorem FinCTMC.jumpTrajPMF_eq (M : FinCTMC S) (k : ℕ) (ω : Traj S k) :
    M.jumpTrajPMF k ω = q2e ((M.jumpLaw k).wt ω) :=
  FinDTMC.trajPMF_eq M.jumpChain k ω

end Adequacy
end SuFunctor
