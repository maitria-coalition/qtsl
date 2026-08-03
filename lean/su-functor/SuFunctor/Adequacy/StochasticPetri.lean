import SuFunctor.Adequacy.SemanticUniverseWiring
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Basic

/-! # Adequacy: stochastic Petri frames, delay-race face

The dynamics faces of the stochastic-Petri adequacy story that are
honestly materializable at the finite time-abstract stratum — the
companion, one stratum down, of the statics square of
`SuFunctor.TokenGame`.

**The fragment.**  Uncoloured nets with declared capacity `B` (bounded
markings `P → Fin (B + 1)`; a capacity declaration is the monotone
fragment's standard price of admission, and firing blocks at capacity),
finitely many delay transitions with constant rational rates, and an
initial distribution over markings.  Inhibitor arcs do not exist in
this fragment either — the formation restriction of the statics module
carries over unchanged.

**The community semantics** ([EB10a] delay-transition execution: each
pre-enabled *ordered assignment of tokens to input arcs* races its own
exponential clock): at constant rates the race from a marking is
exponential with total transition rate

  `raceRate m m' = ∑ t [fires to m'] raceCount t m · rate t`,

where `raceCount` is the **ordered census** — per place, the falling
factorial of the token count over the arc demand (`descFactorial`
vanishes exactly when a place is under-supplied, so pre-enabling is
built into the count).  The community object is the race chain
`raceCtmc : FinCTMC`, and its time-abstract semantics is the jump-chain
path law, exactly as for the plain continuous-time square (the
holding-time stratum — exponential, irrational — stays deliberately
separate, as there).

**The compiled side** carries the house convention: rate rows in the
**unordered** grain, one selection per token *set*, with the
arc-multiplicity dictionary `∏ₚ (demand p)!` owned by the compiler.
The compile-commutes triangle (`compile_race_comm`) is therefore *not*
`rfl` — deliberately, unlike the plain continuous-time square: the two
conventions genuinely differ by the dictionary, and the triangle **is**
the multiplicity-dictionary theorem (`raceCount_eq_dict`) applied
rowwise.  The census ties the count to actual selection objects
(`raceCount_eq_card_embeddings`: the ordered assignments are the
embeddings of arc indices into tokens — the counting shadow of the
exchange-orbit selection families of the statics).

**The square** (`spn_delay_adequacy`): compile the net's race rows in
the unordered convention, close to jump rows, denote — and this agrees,
by an invertible globular cell, with interpreting the net as the
community's race chain and including its jump-chain path law.  The
proof is the continuous-time square instantiated at the race chain —
engine reuse through the dictionary triangle, zero new inductions.
The compiled init rows carry the initial-marking face on the same
ride.

**Deliberately separate, named**: coloured firing measures (the kernel
*presentation* is a seam reserved for the probabilistic-hypernet
vocabulary — this module's outcomes are deterministic and its rates
bare rationals, so nothing here entrenches a kernel encoding); guard
and immediate species (boundary-hitting and cascade closure — the
latter's donor is the Markov-automaton closure, whose instantaneous
states are exactly the vanishing markings); self-loop firings (a
transition whose outcome equals its source contributes only to the
diagonal, which the off-diagonal row grain thins away — the standard
jump-chain convention, received as the thinning receipt
`spn_jumpLaw_thinning`). -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

/-! ## The fragment -/

/-- Bounded markings: per place, a token count at most `B`. -/
abbrev BMarking (P : Type) (B : ℕ) := P → Fin (B + 1)

variable {P T : Type} [Fintype P] [DecidableEq P] [Fintype T] {B : ℕ}

/-- An uncoloured stochastic Petri net with declared capacity `B` and
delay transitions at constant rational rates: ordinary input arcs
(`pre`), enabling arcs (`read` — reserved, never removed), output arcs
(`post`), a rate per transition, and an initial distribution over
bounded markings.  No inhibitor field exists — the formation
restriction of the statics fragment, unchanged. -/
structure FinSPN (P T : Type) [Fintype P] [DecidableEq P] (B : ℕ) where
  /-- Ordinary input arcs per transition and place. -/
  pre : T → P → ℕ
  /-- Enabling arcs per transition and place. -/
  read : T → P → ℕ
  /-- Ordinary output arcs per transition and place. -/
  post : T → P → ℕ
  /-- The delay rate. -/
  rate : T → ℚ
  rate_nonneg : ∀ t, 0 ≤ rate t
  /-- Initial-distribution mass at a marking. -/
  init : BMarking P B → ℚ
  init_nonneg : ∀ m, 0 ≤ init m
  init_sum : ∑ m, init m = 1

namespace FinSPN

variable (N : FinSPN P T B)

/-- The arc demand at a place: one token per ordinary and enabling
input arc (the pre-enabling reservation). -/
def demand (t : T) (p : P) : ℕ := N.pre t p + N.read t p

/-- The outcome count at a place. -/
def outAt (t : T) (m : BMarking P B) (p : P) : ℕ :=
  (m p : ℕ) - N.pre t p + N.post t p

/-- Enabledness in the capacity fragment: the reservation is supplied
and the outcome respects the capacity (firing blocks at capacity — the
fragment's declared convention). -/
def Enabled (t : T) (m : BMarking P B) : Prop :=
  ∀ p, N.demand t p ≤ (m p : ℕ) ∧ N.outAt t m p ≤ B

instance (t : T) (m : BMarking P B) : Decidable (N.Enabled t m) :=
  inferInstanceAs
    (Decidable (∀ p, N.demand t p ≤ (m p : ℕ) ∧ N.outAt t m p ≤ B))

/-- The fired marking (truncated at capacity for totality; under
`Enabled` the truncation is inert). -/
def fire (t : T) (m : BMarking P B) : BMarking P B :=
  fun p => ⟨min (N.outAt t m p) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-! ## The race census -/

/-- **The ordered race census** (the community's object): the number of
ordered assignments of distinct tokens to the input arcs — per place,
the falling factorial of supply over demand.  `descFactorial` vanishes
exactly on under-supply, so the census carries pre-enabling with it. -/
def raceCount (t : T) (m : BMarking P B) : ℕ :=
  ∏ p, ((m p : ℕ)).descFactorial (N.demand t p)

/-- The unordered selection count: one selection per token *set*. -/
def selCount (t : T) (m : BMarking P B) : ℕ :=
  ∏ p, ((m p : ℕ)).choose (N.demand t p)

/-- The arc-multiplicity dictionary: the per-place factorials of the
demands. -/
def dict (t : T) : ℕ := ∏ p, (N.demand t p).factorial

omit [Fintype T] in
/-- The census counts actual selection objects: ordered assignments are
the embeddings of arc indices into tokens — the counting shadow of the
statics' exchange-orbit selection families. -/
theorem raceCount_eq_card_embeddings (t : T) (m : BMarking P B) :
    N.raceCount t m
      = ∏ p, Fintype.card (Fin (N.demand t p) ↪ Fin (m p : ℕ)) := by
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Fintype.card_embedding_eq]
  simp

omit [Fintype T] in
/-- **The multiplicity dictionary, as a theorem**: the ordered census
factors as the dictionary times the unordered selection count — the
compiler-owned `∏ₚ (demand p)!` convention, verified against the
community's ordered races. -/
theorem raceCount_eq_dict (t : T) (m : BMarking P B) :
    N.raceCount t m = N.dict t * N.selCount t m := by
  unfold raceCount dict selCount
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ =>
    Nat.descFactorial_eq_factorial_mul_choose _ _

/-! ## The community object: the race chain -/

/-- The total race intensity between markings: every ordered assignment
races its own clock at the transition's rate, so the intensity to a
target marking is the census-weighted rate sum. -/
def raceRate (m m' : BMarking P B) : ℚ :=
  ∑ t, if N.Enabled t m ∧ N.fire t m = m'
    then (N.raceCount t m : ℚ) * N.rate t else 0

theorem raceRate_nonneg (m m' : BMarking P B) : 0 ≤ N.raceRate m m' :=
  Finset.sum_nonneg fun t _ => by
    by_cases h : N.Enabled t m ∧ N.fire t m = m'
    · rw [if_pos h]
      exact mul_nonneg (Nat.cast_nonneg _) (N.rate_nonneg t)
    · rw [if_neg h]

/-- **The community semantics of the fragment**: the race chain — the
finite continuous-time Markov chain whose off-diagonal rates are the
race intensities and whose initial distribution is the net's.  Its
time-abstract face is the jump-chain path law, exactly as for the
plain continuous-time square. -/
def raceCtmc (N : FinSPN P T B) : FinCTMC (BMarking P B) where
  rate := N.raceRate
  init := N.init
  rate_nonneg := fun m m' _ => N.raceRate_nonneg m m'
  init_nonneg := N.init_nonneg
  init_sum := N.init_sum

/-! ## The compiled rows: the unordered convention -/

/-- **Compilation in the house convention**: rate rows in the unordered
grain — dictionary times unordered selection count times rate — and the
initial-distribution rows.  The off-diagonal key type is inherited from
the continuous-time row grain: a self-loop firing is unrepresentable
rather than linted (the thinning convention). -/
noncomputable def compileSpn (N : FinSPN P T B) :
    CtmcRows (BMarking P B) where
  rateRow := Finsupp.onFinset univ
    (fun q => ∑ t, if N.Enabled t q.1.1 ∧ N.fire t q.1.1 = q.1.2
      then ((N.dict t * N.selCount t q.1.1 : ℕ) : ℚ) * N.rate t else 0)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ N.init (fun _ _ => mem_univ _)

/-- **The compile-commutes triangle — the dictionary, applied**: the
unordered-convention rows are the compilation of the community's race
chain.  Deliberately not definitional: the two sides genuinely differ
by the arc-multiplicity dictionary, and this triangle is
`raceCount_eq_dict` rowwise. -/
theorem compile_race_comm (N : FinSPN P T B) :
    compileSpn N = compileCtmc (raceCtmc N) := by
  have ext2 : ∀ X Y : CtmcRows (BMarking P B),
      X.rateRow = Y.rateRow → X.initRow = Y.initRow → X = Y := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2
    cases h1
    cases h2
    rfl
  refine ext2 _ _ (Finsupp.ext fun q => ?_) rfl
  show (∑ t, if N.Enabled t q.1.1 ∧ N.fire t q.1.1 = q.1.2
      then ((N.dict t * N.selCount t q.1.1 : ℕ) : ℚ) * N.rate t else 0)
    = N.raceRate q.1.1 q.1.2
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : N.Enabled t q.1.1 ∧ N.fire t q.1.1 = q.1.2
  · rw [if_pos hc, if_pos hc]
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (N.raceCount_eq_dict t q.1.1).symm
  · rw [if_neg hc, if_neg hc]

/-! ## The square -/

/-- **Adequacy of the stochastic-Petri compilation, delay-race face.**

In the double category `Crd (Traj (BMarking P B) k)` of per-element
credal constraints over jump-horizon-`k` marking trajectories: the
loose-arrow diagram denoted by the jump closure of the net's compiled
rate rows — emitted in the unordered convention with the compiler-owned
multiplicity dictionary — is isomorphic, by an invertible globular
cell, to the singleton-credal inclusion of the community race chain's
jump-chain path law.  Compile-close-denote agrees with
interpret-then-include, at the time-abstract stratum; the compiled init
rows carry the initial-marking face on the same ride.

The proof is the continuous-time square instantiated at the race chain,
through the dictionary triangle — engine reuse, zero new inductions. -/
theorem spn_delay_adequacy (N : FinSPN P T B) (k : ℕ)
    {a : Crd (Traj (BMarking P B) k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows (compileSpn N)) k) : Loose a a)
        (singletonC ((raceCtmc N).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  rw [compile_race_comm]
  exact ctmc_jump_adequacy (raceCtmc N) k

/-- **The thinning receipt**: nets whose race intensities agree between
*distinct* markings (and whose initial distributions agree) have equal
jump-chain laws — a transition firing back to its source marking
contributes only to the diagonal, which the off-diagonal grain thins
away.  The standard jump-chain convention, stated as a theorem. -/
theorem spn_jumpLaw_thinning {T' : Type} [Fintype T']
    (N : FinSPN P T B) (N' : FinSPN P T' B)
    (hoff : ∀ m m', m ≠ m' → N.raceRate m m' = N'.raceRate m m')
    (hinit : N.init = N'.init) (k : ℕ) :
    (raceCtmc N).jumpLaw k = (raceCtmc N').jumpLaw k :=
  FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k

/-! ## The semantic-universe wiring (in-module, per the standing
precedent for squares landing while the shared wiring file is hot) -/

/-- The compiled net's presentation in the semantic universe's fibre
over jump-horizon-`k` marking trajectories. -/
noncomputable def spnDnf (N : FinSPN P T B) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj (BMarking P B) k)) :=
  ctmcJumpDnf (compileSpn N) k

/-- **The delay-race square, wired to the semantic universe**: the
ideal point of a law models the compiled net's presentation exactly
when the law is the community race chain's jump-chain path law. -/
theorem su_spn_delay_adequacy (N : FinSPN P T B) (k : ℕ)
    (μ : SubPMF (Traj (BMarking P B) k)) :
    idealPoint μ ∈ (spnDnf N k).modelClass
      ↔ μ = (raceCtmc N).jumpLaw k := by
  unfold spnDnf
  rw [compile_race_comm]
  exact su_ctmc_jump_adequacy (raceCtmc N) k μ

/-- The positive face: the race chain's jump law models the compiled
net. -/
theorem su_spn_jumpLaw_mem (N : FinSPN P T B) (k : ℕ) :
    idealPoint ((raceCtmc N).jumpLaw k) ∈ (spnDnf N k).modelClass :=
  (su_spn_delay_adequacy N k _).mpr rfl

/-- Ex falso at the net corner. -/
theorem su_spn_bottom (N : FinSPN P T B) (k : ℕ) :
    (⊤ : Plain.Pen (Traj (BMarking P B) k)) ∉ (spnDnf N k).modelClass := by
  unfold spnDnf ctmcJumpDnf
  exact top_notMem_diagramDnf _

/-- The credal reading at the net corner, through the slice. -/
theorem su_spn_slice (N : FinSPN P T B) (k : ℕ)
    (μ : SubPMF (Traj (BMarking P B) k)) :
    idealPoint μ ∈ (spnDnf N k).modelClass
      ↔ maxSlice (rayC ((raceCtmc N).jumpLaw k)) μ :=
  (su_spn_delay_adequacy N k μ).trans
    (maxSlice_rayC (FinCTMC.jumpLaw_ne_zero _ k) μ).symm

end FinSPN

/-! ## Controls

Concrete closed forms pinning the census, the dictionary, and the
capacity gate, with proofs deliberately independent of the lemmas they
guard (decidability, not rewriting) — second witnesses at the designed
mutant loci. -/

namespace SpnControls

/-- One place, one transition, capacity `3`: demand two tokens
(consume both), produce none. -/
def race₀ : FinSPN (Fin 1) (Fin 1) 3 where
  pre := fun _ _ => 2
  read := fun _ _ => 0
  post := fun _ _ => 0
  rate := fun _ => 1
  rate_nonneg := fun _ => zero_le_one
  init := fun m => if m = fun _ => (3 : Fin 4) then 1 else 0
  init_nonneg := fun m => by
    by_cases h : m = fun _ => (3 : Fin 4) <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- Three tokens, demand two: the ordered census is the falling
factorial `3 · 2 = 6`. -/
example : race₀.raceCount 0 (fun _ => (3 : Fin 4)) = 6 := by decide

/-- The same count through the dictionary: `2! · C(3,2) = 2 · 3`. -/
example :
    race₀.dict 0 * race₀.selCount 0 (fun _ => (3 : Fin 4)) = 6 := by
  decide

/-- One place, one transition, capacity `3`: produce four tokens from
nothing — blocked at capacity from every marking, so the race intensity
out of the full marking vanishes identically. -/
def cap₀ : FinSPN (Fin 1) (Fin 1) 3 where
  pre := fun _ _ => 0
  read := fun _ _ => 0
  post := fun _ _ => 4
  rate := fun _ => 1
  rate_nonneg := fun _ => zero_le_one
  init := fun m => if m = fun _ => (3 : Fin 4) then 1 else 0
  init_nonneg := fun m => by
    by_cases h : m = fun _ => (3 : Fin 4) <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- The capacity gate has teeth: no target marking receives any rate. -/
example (m' : BMarking (Fin 1) 3) :
    cap₀.raceRate (fun _ => (3 : Fin 4)) m' = 0 := by
  unfold FinSPN.raceRate
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  rintro ⟨he, -⟩
  exact absurd ((he 0).2) (by decide +revert)

end SpnControls

end Adequacy
end SuFunctor
