import SuFunctor.Adequacy.StochasticPetri
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Adequacy: stochastic Petri frames, immediate/cascade face

The immediate-transition face of the stochastic-Petri adequacy story,
one species beyond the delay-race face of
`SuFunctor.Adequacy.StochasticPetri` — and one reuse of the landed
Markov-automaton square, on the nose.

**The fragment.**  The delay fragment of the companion module (uncoloured
nets, declared capacity `B`, delay transitions at constant rational
rates, blocking-at-capacity), extended by **immediate transitions**:
transitions that fire in zero time, with priority over the delay species
(the community's maximal-progress rule), carrying arcs but no rates and
no weights — exactly the community presentation ([EB10a] arXiv:1003.4812
pp. 233–234: immediate transitions fire on pre-enabling, with priority
R0; cascades fire "until no more immediate transitions are enabled").
Guard transitions remain a separate face, as do coloured firing
measures; inhibitors do not exist, by formation, as before.

**Vanishing markings are instantaneous states — structurally.**  A
marking that pre-enables an immediate transition is *vanishing*: the
community excludes it from the state space of the observed process
(p. 250: the discrete state space "is composed of those nodes … that do
not enable an immediate transition").  Here the exclusion is carried by
the type: the net's markings split into the *tangible* and the
*vanishing* subtypes, and the net compiles to a two-sorted Markov
automaton (`FinMA`) whose Markovian sort is the tangible markings and
whose instantaneous sort is the vanishing ones.  A delay row at a
vanishing marking is thereby **unrepresentable** — the maximal-progress
priority is the domain type of the rate field, exactly as the automaton
square ships it.

**The cascade is scheduler-closure absorption.**  From a vanishing
marking, an enabled immediate transition fires; the result may again be
vanishing; the cascade continues until a tangible marking absorbs it.
This is the automaton square's absorbing computation consumed as built:
immediate firings are the action-keyed branches (one action per
immediate transition; firing is deterministic at this uncoloured
stratum, so each branch is a point mass), a **declared scheduler**
resolves which enabled transition fires, and the fixed-scheduler closure
`FinMA.close` delivers the observed process on tangible markings — the
community's reduced tangible chain.  Cascade termination is the
`ZenoFree` rank certificate: a rank on vanishing markings that every
enabled immediate firing strictly decreases (`CascadeRank` — the
community's cascade-termination condition as a ranking argument, the
house's certificate genus).

**Conflict resolution is scheduler-generic, dominating the community's
randomization.**  The community resolves simultaneous immediate
enablings by randomization (uniform choice among maximal combinations;
rules R2/R4).  At this stratum the square is proven for **every**
declared memoryless randomized scheduler at once, which dominates any
particular randomization; the concrete instance shipped is the
single-firing shadow of the community's rule, `uniformPolicy` — uniform
among the enabled immediate transitions.  A scheduler must respect
enabling (`RespectsEnabling`): the disabled-action branch is the honest
zero-time no-op (a point mass at the source), so a scheduler that chose
a disabled action would sit still in zero time — a Zeno behaviour, and
the rank machinery refuses it rather than papering over it.  The
simultaneous *composite* firing of non-conflicting immediates (rules
R1/R3) is a deliberately separate stratum: a composite is a chain of
single firings, and the set-action face is named at the end of this
docstring, not silently discharged.

**No initial-tangibility premise.**  The community's mapping theorems
assume the initial marking enables no immediate transition.  This face
does not inherit that premise: the closure pushes vanishing initial mass
through the cascade (absorption applied to the initial rows), a strict
widening; the receipt `tangibleChain_init_of_tangible` shows the initial
distribution passes through untouched exactly when the community's
premise holds.

**The square** (`ispn_cascade_adequacy`): compile the net's rows — timed
rows in the delay face's **unordered convention** with the
compiler-owned multiplicity dictionary, immediate branch rows, initial
rows — close through the compiled scheduler rows, jump-close, denote;
and this agrees, by an invertible globular cell, with interpreting the
net as its Markov automaton, closing classically, and including the
tangible path law.  The proof is **five-storey engine reuse** — net →
automaton → closed chain → jump chain → discrete chain: the one
net-shaped obligation is the compile triangle `compile_ispn_comm`, which
is *not* definitional on the timed rows (the two conventions differ by
the arc-multiplicity dictionary; the triangle is the delay face's
dictionary theorem `raceCount_eq_dict` applied rowwise, one storey up)
and definitional on the immediate and initial rows; `ma_adequacy`
finishes.  Zero new inductions: every absorption fact was spent once, in
the automaton square, every stochasticity fact once, in the chain
engine.

**Deliberately separate, named**: composite firings of non-conflicting
immediates (the set-action face; R1/R3); the community's exact
randomization over maximal combinations (dominated by
scheduler-genericity; the demonic face of the automaton square is the
uniform-over-schedulers instrument, instantiable at these compiled rows);
coloured immediate firing measures (the kernel-presentation seam — the
branches here are point masses and nothing entrenches an encoding);
guard transitions (boundary forcing); the exponential time-law stratum,
exactly as for the delay face. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {B : ℕ}

/-! ## The fragment: a net with immediate transitions -/

/-- An uncoloured stochastic Petri net with declared capacity `B`,
delay transitions at constant rational rates, and **immediate
transitions**: the delay layer is a `FinSPN` (carrying the net's
initial distribution), and each immediate transition carries ordinary
input arcs, enabling arcs, and output arcs — no rate and no weight,
exactly the community presentation.  No inhibitor field exists on
either species, as before. -/
structure FinISPN (P T U : Type) [Fintype P] [DecidableEq P] (B : ℕ) where
  /-- The delay layer: delay transitions, rates, and the initial
  distribution over bounded markings. -/
  delay : FinSPN P T B
  /-- Ordinary input arcs per immediate transition and place. -/
  ipre : U → P → ℕ
  /-- Enabling arcs per immediate transition and place. -/
  iread : U → P → ℕ
  /-- Ordinary output arcs per immediate transition and place. -/
  ipost : U → P → ℕ

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## The immediate token game, mirroring the delay fragment -/

/-- The arc demand of an immediate transition at a place. -/
def iDemand (u : U) (p : P) : ℕ := N.ipre u p + N.iread u p

/-- The outcome count of an immediate firing at a place. -/
def iOutAt (u : U) (m : BMarking P B) (p : P) : ℕ :=
  (m p : ℕ) - N.ipre u p + N.ipost u p

/-- Enabledness of an immediate transition: the reservation is supplied
and the outcome respects the capacity — the fragment's conventions,
unchanged across species. -/
def IEnabled (u : U) (m : BMarking P B) : Prop :=
  ∀ p, N.iDemand u p ≤ (m p : ℕ) ∧ N.iOutAt u m p ≤ B

instance (u : U) (m : BMarking P B) : Decidable (N.IEnabled u m) :=
  inferInstanceAs
    (Decidable (∀ p, N.iDemand u p ≤ (m p : ℕ) ∧ N.iOutAt u m p ≤ B))

/-- The immediate firing (truncated at capacity for totality; under
`IEnabled` the truncation is inert). -/
def ifire (u : U) (m : BMarking P B) : BMarking P B :=
  fun p => ⟨min (N.iOutAt u m p) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-! ## Vanishing and tangible markings -/

/-- A marking is **vanishing** when it pre-enables some immediate
transition — the community's zero-sojourn markings, excluded from the
state space of the observed process. -/
def IsVanishing (m : BMarking P B) : Prop := ∃ u, N.IEnabled u m

instance (m : BMarking P B) : Decidable (N.IsVanishing m) :=
  inferInstanceAs (Decidable (∃ u, N.IEnabled u m))

/-- The tangible markings: the Markovian sort of the compiled
automaton. -/
abbrev Tangible := {m : BMarking P B // ¬ N.IsVanishing m}

/-- The vanishing markings: the instantaneous sort of the compiled
automaton. -/
abbrev Vanishing := {m : BMarking P B // N.IsVanishing m}

/-- Forget the classification. -/
def ofSum : N.Tangible ⊕ N.Vanishing → BMarking P B :=
  Sum.elim Subtype.val Subtype.val

/-- Classify a marking as tangible or vanishing. -/
def toSum (m : BMarking P B) : N.Tangible ⊕ N.Vanishing :=
  if h : N.IsVanishing m then Sum.inr ⟨m, h⟩ else Sum.inl ⟨m, h⟩

omit [Fintype T] [Fintype U] in
@[simp] theorem ofSum_inl (s : N.Tangible) : N.ofSum (Sum.inl s) = s.1 := rfl

omit [Fintype T] [Fintype U] in
@[simp] theorem ofSum_inr (i : N.Vanishing) : N.ofSum (Sum.inr i) = i.1 := rfl

omit [Fintype T] in
@[simp] theorem ofSum_toSum (m : BMarking P B) : N.ofSum (N.toSum m) = m := by
  unfold toSum
  split <;> rfl

omit [Fintype T] in
@[simp] theorem toSum_ofSum (x : N.Tangible ⊕ N.Vanishing) :
    N.toSum (N.ofSum x) = x := by
  cases x with
  | inl s => rw [ofSum_inl]; exact dif_neg s.2
  | inr i => rw [ofSum_inr]; exact dif_pos i.2

/-- The classification is a bijection: tangible-or-vanishing markings
are all the markings — the community's state-space split, as an
equivalence. -/
def markingEquiv : (N.Tangible ⊕ N.Vanishing) ≃ BMarking P B where
  toFun := N.ofSum
  invFun := N.toSum
  left_inv := N.toSum_ofSum
  right_inv := N.ofSum_toSum

/-! ## The Markov automaton of the net

Maximal progress (the community's priority rule) is *structure* here:
the automaton's rate field takes tangible sources only, so a delay row
at a vanishing marking is unrepresentable rather than linted. -/

/-- The Markov-automaton reading of the net: tangible markings are the
Markovian states (their timed rows are the delay layer's race
intensities, read off the companion module's community object);
vanishing markings are the instantaneous states, with one action per
immediate transition — an enabled action is a point mass at the fired
marking, a disabled action is the honest zero-time no-op (a point mass
at the source; a scheduler that chooses it sits still in zero time,
which the rank machinery refuses as Zeno rather than this definition
papering over). -/
def toFinMA : FinMA N.Tangible N.Vanishing U where
  rate s x := N.delay.raceRate s.1 (N.ofSum x)
  branch i u x :=
    if N.IEnabled u i.1 then (if N.toSum (N.ifire u i.1) = x then 1 else 0)
    else (if Sum.inr i = x then 1 else 0)
  init x := N.delay.init (N.ofSum x)
  rate_nonneg s x _ := N.delay.raceRate_nonneg s.1 (N.ofSum x)
  branch_nonneg i u x := by
    split <;> split <;> norm_num
  branch_row_sum i u := by
    by_cases h : N.IEnabled u i.1
    · simp only [if_pos h]
      rw [Finset.sum_ite_eq univ (N.toSum (N.ifire u i.1)) fun _ => (1 : ℚ)]
      simp
    · simp only [if_neg h]
      rw [Finset.sum_ite_eq univ (Sum.inr i : N.Tangible ⊕ N.Vanishing)
        fun _ => (1 : ℚ)]
      simp
  init_nonneg x := N.delay.init_nonneg (N.ofSum x)
  init_sum := (Equiv.sum_comp N.markingEquiv N.delay.init).trans
    N.delay.init_sum

@[simp] theorem toFinMA_rate (s : N.Tangible) (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.rate s x = N.delay.raceRate s.1 (N.ofSum x) := rfl

@[simp] theorem toFinMA_branch (i : N.Vanishing) (u : U)
    (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.branch i u x
      = if N.IEnabled u i.1
          then (if N.toSum (N.ifire u i.1) = x then 1 else 0)
          else (if Sum.inr i = x then 1 else 0) := rfl

@[simp] theorem toFinMA_init (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.init x = N.delay.init (N.ofSum x) := rfl

/-! ## The community scheduler and the cascade-termination certificate -/

/-- The number of immediate transitions enabled at a vanishing
marking. -/
def enabledCount (i : N.Vanishing) : ℕ :=
  (univ.filter fun u => N.IEnabled u i.1).card

omit [Fintype T] in
theorem enabledCount_pos (i : N.Vanishing) : 0 < N.enabledCount i := by
  obtain ⟨u, hu⟩ := i.2
  exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨mem_univ u, hu⟩⟩

/-- The community's conflict resolution at the single-firing stratum:
uniform choice among the enabled immediate transitions — the
single-firing shadow of the uniform-among-maximal-combinations rule.
The square never depends on this particular scheduler (it is proven for
every declared one); this is the concrete instance the controls pin. -/
def uniformPolicy : Policy N.Vanishing U where
  choice i u := if N.IEnabled u i.1 then (N.enabledCount i : ℚ)⁻¹ else 0
  nonneg i u := by
    split
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  row_sum i := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      nsmul_eq_mul]
    exact mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr (N.enabledCount_pos i).ne')

/-- A scheduler **respects enabling** when it never weights a disabled
immediate transition.  The community's schedulers all do; one that did
not would sit still in zero time — Zeno — and the rank machinery below
is what says so. -/
def RespectsEnabling (σ : Policy N.Vanishing U) : Prop :=
  ∀ i u, σ.choice i u ≠ 0 → N.IEnabled u i.1

omit [Fintype T] in
theorem uniformPolicy_respects : N.RespectsEnabling N.uniformPolicy := by
  intro i u h
  by_contra hne
  exact h (if_neg hne)

/-- **Cascade termination as a ranking certificate**: a rank on
vanishing markings that strictly decreases along every enabled
immediate firing landing in a vanishing marking — the community's
"cascades terminate" condition, carried as the house's certificate
genus.  Decidable at concrete nets, so controls can discharge it by
computation. -/
def CascadeRank (r : N.Vanishing → ℕ) : Prop :=
  ∀ (i : N.Vanishing) (u : U), N.IEnabled u i.1 →
    ∀ j : N.Vanishing, N.toSum (N.ifire u i.1) = Sum.inr j → r j < r i

instance (r : N.Vanishing → ℕ) : Decidable (N.CascadeRank r) :=
  inferInstanceAs
    (Decidable (∀ (i : N.Vanishing) (u : U), N.IEnabled u i.1 →
      ∀ j : N.Vanishing, N.toSum (N.ifire u i.1) = Sum.inr j → r j < r i))

/-- A cascade rank certifies Zeno-freedom for every scheduler that
respects enabling — the policy-aware analogue of the automaton square's
branch-level sufficient condition, which cannot apply verbatim here:
the disabled-action stay rows would demand `r i < r i`, and it is the
scheduler's enabling-respect that keeps them out of the mixture's
support. -/
theorem zenoFree_of_cascadeRank (σ : Policy N.Vanishing U)
    (hσ : N.RespectsEnabling σ) {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) : ZenoFree (N.toFinMA.imStep σ) r := by
  intro i j hne
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hen : N.IEnabled u i.1 := hσ i u (left_ne_zero_of_mul hu)
  have hb : N.toFinMA.branch i u (Sum.inr j) ≠ 0 :=
    right_ne_zero_of_mul hu
  rw [toFinMA_branch, if_pos hen] at hb
  refine hr i u hen j ?_
  by_contra hns
  exact hb (if_neg hns)

/-- The uniform scheduler inherits Zeno-freedom from any cascade
rank. -/
theorem zenoFree_uniform {r : N.Vanishing → ℕ} (hr : N.CascadeRank r) :
    ZenoFree (N.toFinMA.imStep N.uniformPolicy) r :=
  N.zenoFree_of_cascadeRank N.uniformPolicy N.uniformPolicy_respects hr

/-! ## The observed process: the tangible chain -/

/-- **The reduced tangible chain**: the community's observed process on
non-vanishing markings — the fixed-scheduler closure of the net's
automaton, by the landed absorbing computation.  Delay races feed the
cascade; the cascade absorbs, within the rank, into tangible markings;
returned mass dies on the off-diagonal grain (self-loop thinning,
structurally, as the automaton square ships it). -/
def tangibleChain (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) : FinCTMC N.Tangible :=
  N.toFinMA.close σ r hr

theorem tangibleChain_eq (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) :
    N.tangibleChain σ r hr = N.toFinMA.close σ r hr := rfl

/-- The time-abstract semantics of the net under the declared
scheduler: the tangible chain's jump-chain path law at jump horizon
`k`. -/
noncomputable def tangiblePathLaw (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) : SubPMF (Traj N.Tangible k) :=
  N.toFinMA.pathLaw σ r hr k

theorem tangiblePathLaw_eq (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r) (k : ℕ) :
    N.tangiblePathLaw σ r hr k = N.toFinMA.pathLaw σ r hr k := rfl

/-- **The initial-tangibility receipt**: the community's mapping
theorems assume the initial marking enables no immediate transition;
this face needs no such premise (vanishing initial mass is pushed
through the cascade by the closure).  When the premise *does* hold —
no vanishing marking carries initial mass — the initial distribution
passes through the closure untouched. -/
theorem tangibleChain_init_of_tangible (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hsupp : ∀ m : BMarking P B, N.IsVanishing m → N.delay.init m = 0)
    (s : N.Tangible) :
    (N.tangibleChain σ r hr).init s = N.delay.init s.1 := by
  show (∑ x, N.toFinMA.init x * N.toFinMA.absorb σ r x s) = _
  rw [Fintype.sum_sum_type]
  have h2 : ∀ i : N.Vanishing,
      N.toFinMA.init (Sum.inr i) * N.toFinMA.absorb σ r (Sum.inr i) s
        = 0 := by
    intro i
    rw [toFinMA_init, ofSum_inr, hsupp i.1 i.2, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const_zero,
    add_zero]
  have h1 : ∀ m' : N.Tangible,
      N.toFinMA.init (Sum.inl m') * N.toFinMA.absorb σ r (Sum.inl m') s
        = if m' = s then N.delay.init m'.1 else 0 := by
    intro m'
    have habs : N.toFinMA.absorb σ r (Sum.inl m') s
        = hitMass (Sum.inl m' : N.Tangible ⊕ N.Vanishing) s :=
      absorbIter_inl _ _ m' s
    rw [habs, hitMass_inl, toFinMA_init, ofSum_inl]
    by_cases h : m' = s <;> simp [h]
  rw [Finset.sum_congr rfl fun m' _ => h1 m']
  rw [Finset.sum_ite_eq' univ s fun m' => N.delay.init m'.1]
  simp

/-! ## The compiled rows: the unordered convention, both species -/

/-- **Compilation in the house convention**: timed rows in the
unordered grain — the compiler-owned arc-multiplicity dictionary times
the unordered selection count times the rate, exactly the delay face's
convention, now emitted at the automaton row grain (Markovian sources
and off-diagonal destinations carried by the key type); immediate
branch rows and initial rows read off the net's arcs. -/
noncomputable def compileIspn : MaRows N.Tangible N.Vanishing U where
  rateRow := Finsupp.onFinset univ
    (fun q => ∑ t,
      if N.delay.Enabled t q.1.1.1 ∧ N.delay.fire t q.1.1.1 = N.ofSum q.1.2
      then ((N.delay.dict t * N.delay.selCount t q.1.1.1 : ℕ) : ℚ)
        * N.delay.rate t
      else 0)
    (fun _ _ => mem_univ _)
  branchRow := Finsupp.onFinset univ
    (fun p =>
      if N.IEnabled p.2.1 p.1.1
      then (if N.toSum (N.ifire p.2.1 p.1.1) = p.2.2 then 1 else 0)
      else (if Sum.inr p.1 = p.2.2 then 1 else 0))
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ (fun x => N.delay.init (N.ofSum x))
    (fun _ _ => mem_univ _)

/-- **The compile-commutes triangle — the dictionary, one storey up**:
the compiled rows are the compilation of the net's automaton.
Deliberately not definitional on the timed component: the unordered
convention and the community's ordered census genuinely differ by the
arc-multiplicity dictionary, and the triangle is the delay face's
dictionary theorem applied rowwise at the automaton grain.  The
immediate and initial components are definitional. -/
theorem compile_ispn_comm : N.compileIspn = compileMa N.toFinMA := by
  have ext3 : ∀ X Y : MaRows N.Tangible N.Vanishing U,
      X.rateRow = Y.rateRow → X.branchRow = Y.branchRow →
      X.initRow = Y.initRow → X = Y := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  refine ext3 _ _ (Finsupp.ext fun q => ?_) rfl rfl
  show (∑ t,
      if N.delay.Enabled t q.1.1.1 ∧ N.delay.fire t q.1.1.1 = N.ofSum q.1.2
      then ((N.delay.dict t * N.delay.selCount t q.1.1.1 : ℕ) : ℚ)
        * N.delay.rate t
      else 0)
    = N.delay.raceRate q.1.1.1 (N.ofSum q.1.2)
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : N.delay.Enabled t q.1.1.1
      ∧ N.delay.fire t q.1.1.1 = N.ofSum q.1.2
  · rw [if_pos hc, if_pos hc]
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (N.delay.raceCount_eq_dict t q.1.1.1).symm
  · rw [if_neg hc, if_neg hc]

/-- The compiled rows are well-formed — through the triangle, from the
automaton compilation. -/
theorem compileIspn_wf : N.compileIspn.WF :=
  N.compile_ispn_comm ▸ compileMa_wf N.toFinMA

/-! ## The square -/

/-- **Adequacy of the stochastic-Petri compilation, immediate/cascade
face.**

In the double category `Crd (Traj N.Tangible k)` of per-element credal
constraints over jump-horizon-`k` trajectories of tangible markings:
the loose-arrow diagram denoted by the *jump closure of the scheduler
closure* of the net's compiled rows — timed rows in the unordered
convention with the compiler-owned dictionary, immediate rows
action-keyed, closed at the working fuel of the declared cascade rank —
is isomorphic, by an invertible globular cell, to the singleton-credal
inclusion of the net's tangible path law under the declared scheduler.
Compile-close-close-denote agrees with interpret-then-include, at the
time-abstract stratum; scheduler-generic, hence dominating the
community's randomized conflict resolution.

The proof is five-storey engine reuse: the dictionary triangle
rewrites the compiled rows into the automaton compilation, and
`ma_adequacy` — itself the chain square through the automaton closure —
finishes.  Zero new inductions. -/
theorem ispn_cascade_adequacy (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r) (k : ℕ)
    {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows N.compileIspn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (singletonC (N.tangiblePathLaw σ r hr k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  rw [compile_ispn_comm]
  exact ma_adequacy N.toFinMA σ r hr k

/-! ## The semantic-universe wiring (in-module, per the standing
precedent for squares landing while the shared wiring file is hot) -/

/-- The compiled net's presentation in the semantic universe's fibre
over jump-horizon-`k` tangible trajectories: the automaton presentation
at the compiled rows and scheduler rows, at the working fuel. -/
noncomputable def ispnDnf (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj N.Tangible k)) :=
  maDnf N.compileIspn (compilePolicy σ) (absFuel r) k

/-- **The cascade square, wired to the semantic universe**: the ideal
point of a law models the compiled net-and-scheduler presentation
exactly when the law is the tangible path law. -/
theorem su_ispn_cascade_adequacy (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r) (k : ℕ)
    (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.ispnDnf σ r k).modelClass
      ↔ μ = N.tangiblePathLaw σ r hr k := by
  unfold ispnDnf
  rw [compile_ispn_comm]
  exact su_ma_adequacy N.toFinMA σ r hr k μ

/-- The positive face: the tangible path law models the compiled
net. -/
theorem su_ispn_pathLaw_mem (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) :
    idealPoint (N.tangiblePathLaw σ r hr k)
      ∈ (N.ispnDnf σ r k).modelClass :=
  (N.su_ispn_cascade_adequacy σ r hr k _).mpr rfl

/-- Ex falso at the net corner. -/
theorem su_ispn_bottom (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (k : ℕ) :
    (⊤ : Plain.Pen (Traj N.Tangible k)) ∉ (N.ispnDnf σ r k).modelClass := by
  unfold ispnDnf maDnf ctmcJumpDnf
  exact top_notMem_diagramDnf _

/-- A tangible path law is never the bottom law. -/
theorem tangiblePathLaw_ne_zero (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) :
    N.tangiblePathLaw σ r hr k ≠ SubPMF.zero (Traj N.Tangible k) :=
  N.toFinMA.pathLaw_ne_zero σ r hr k

/-- The credal reading at the net corner, through the slice. -/
theorem su_ispn_slice (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) (k : ℕ)
    (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.ispnDnf σ r k).modelClass
      ↔ maxSlice (rayC (N.tangiblePathLaw σ r hr k)) μ :=
  (N.su_ispn_cascade_adequacy σ r hr k μ).trans
    (maxSlice_rayC (N.tangiblePathLaw_ne_zero σ r hr k) μ).symm

end FinISPN

/-! ## Controls

Concrete closed forms pinning the vanishing/tangible classification,
the uniform conflict split, the thinning of returned cascade mass, the
disabled-action stay convention, and a genuine two-step cascade — with
proofs deliberately independent of the lemmas they guard (decidability,
not rewriting): second witnesses at the designed mutant loci. -/

namespace SpnCascadeControls

open FinISPN

/-- The empty marking on two places, capacity 1. -/
def m00 : BMarking (Fin 2) 1 := fun _ => 0

/-- One token in place 0. -/
def m10 : BMarking (Fin 2) 1 := fun p => if p = 0 then 1 else 0

/-- One token in place 1. -/
def m01 : BMarking (Fin 2) 1 := fun p => if p = 1 then 1 else 0

/-- Tokens in both places. -/
def m11 : BMarking (Fin 2) 1 := fun _ => 1

/-- Two places, capacity 1; one delay transition feeding place 0 at
rate 3; two immediate transitions consuming the place-0 token — one
discards it, one moves it to place 1.  At the marking with one token in
place 0 both immediates are enabled (the uniform scheduler splits ½/½);
at the full marking the move is blocked by capacity and only the
discard is enabled. -/
def net₁ : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ p => if p = 0 then 1 else 0
      rate := fun _ => 3
      rate_nonneg := fun _ => by norm_num
      init := fun m => if m = m00 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m00 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (Finset.mem_univ _)) }
  ipre := fun _ p => if p = 0 then 1 else 0
  iread := fun _ _ => 0
  ipost := fun u p => if u = 1 ∧ p = 1 then 1 else 0

/-- The marking with a place-0 token is vanishing (an immediate is
enabled): the community's state-space exclusion, pinned. -/
theorem net₁_vanishing : net₁.IsVanishing m10 := by decide

/-- The empty marking is tangible. -/
theorem net₁_tangible : ¬ net₁.IsVanishing m00 := by decide

/-- The classified elements of `net₁`, named for the controls. -/
def t00 : net₁.Tangible := ⟨m00, by decide⟩
def t01 : net₁.Tangible := ⟨m01, by decide⟩
def i10 : net₁.Vanishing := ⟨m10, by decide⟩
def i11 : net₁.Vanishing := ⟨m11, by decide⟩

theorem net₁_tangible_univ :
    (Finset.univ : Finset net₁.Tangible) = {t00, t01} := by decide

theorem net₁_vanishing_univ :
    (Finset.univ : Finset net₁.Vanishing) = {i10, i11} := by decide

/-- The discard's firing outcome, classified: the empty marking,
tangible.  (Firing facts are proven by marking-equality computation
plus the classifier's dite — the classifier itself is not asked to
reduce inside a kernel equality.) -/
theorem net₁_fire_discard :
    net₁.toSum (net₁.ifire 0 i10.1) = Sum.inl t00 := by
  rw [show net₁.ifire 0 i10.1 = m00 from by decide]
  exact dif_neg (by decide)

/-- The move's firing outcome, classified: the place-1 marking,
tangible. -/
theorem net₁_fire_move :
    net₁.toSum (net₁.ifire 1 i10.1) = Sum.inl t01 := by
  rw [show net₁.ifire 1 i10.1 = m01 from by decide]
  exact dif_neg (by decide)

/-- The trivial rank: no immediate firing of `net₁` lands in a
vanishing marking. -/
def r₁ : net₁.Vanishing → ℕ := fun _ => 0

theorem net₁_rank : net₁.CascadeRank r₁ := by decide

theorem net₁_zenoFree :
    ZenoFree (net₁.toFinMA.imStep net₁.uniformPolicy) r₁ :=
  net₁.zenoFree_uniform net₁_rank

/-! Kernel note (established by committed discrimination probes, barn
job su-functor-e78f8fc6e-104333-1476, since pruned): on the pinned
toolchain the kernel does not reduce rational arithmetic
(`Rat.add`/`Rat.mul` are extern-backed), so `decide` discharges only
the ℕ/Fin/marking-equality controls; the rational-valued controls
below evaluate their finite sums explicitly and close with
`norm_num`. -/

/-- The uniform scheduler splits the two-way conflict evenly: the
enabled discard gets `½`. -/
theorem net₁_uniform_choice : net₁.uniformPolicy.choice i10 0 = 2⁻¹ := by
  show (if net₁.IEnabled 0 i10.1
    then ((net₁.enabledCount i10 : ℕ) : ℚ)⁻¹ else 0) = 2⁻¹
  rw [if_pos (by decide), show net₁.enabledCount i10 = 2 from by decide]
  norm_num

/-- Renormalization on the singleton enabled set: at the full marking
only the discard is enabled, and it gets the whole mass — the control
that discriminates a normalizer over all actions from one over the
enabled ones. -/
theorem net₁_singleton_renorm :
    net₁.uniformPolicy.choice i11 0 = 1 := by
  show (if net₁.IEnabled 0 i11.1
    then ((net₁.enabledCount i11 : ℕ) : ℚ)⁻¹ else 0) = 1
  rw [if_pos (by decide), show net₁.enabledCount i11 = 1 from by decide]
  norm_num

/-- The enabledness filter: the capacity-blocked move gets zero
scheduler mass. -/
theorem net₁_enabling_filter :
    net₁.uniformPolicy.choice i11 1 = 0 := by
  show (if net₁.IEnabled 1 i11.1
    then ((net₁.enabledCount i11 : ℕ) : ℚ)⁻¹ else 0) = 0
  rw [if_neg (by decide)]

/-- The race intensity of the delay layer out of the empty marking:
all of it goes to the vanishing marking. -/
theorem net₁_race_to_vanishing : net₁.delay.raceRate m00 m10 = 3 := by
  show (∑ t : Fin 1,
      if net₁.delay.Enabled t m00 ∧ net₁.delay.fire t m00 = m10
      then ((net₁.delay.raceCount t m00 : ℚ)) * net₁.delay.rate t
      else 0) = 3
  rw [Fin.sum_univ_one, if_pos ⟨by decide, by decide⟩,
    show net₁.delay.raceCount 0 m00 = 1 from by decide,
    show net₁.delay.rate 0 = 3 from rfl]
  norm_num

theorem net₁_race_to_t01 : net₁.delay.raceRate m00 m01 = 0 := by
  show (∑ t : Fin 1,
      if net₁.delay.Enabled t m00 ∧ net₁.delay.fire t m00 = m01
      then ((net₁.delay.raceCount t m00 : ℚ)) * net₁.delay.rate t
      else 0) = 0
  rw [Fin.sum_univ_one, if_neg (by decide)]

theorem net₁_race_to_i11 : net₁.delay.raceRate m00 m11 = 0 := by
  show (∑ t : Fin 1,
      if net₁.delay.Enabled t m00 ∧ net₁.delay.fire t m00 = m11
      then ((net₁.delay.raceCount t m00 : ℚ)) * net₁.delay.rate t
      else 0) = 0
  rw [Fin.sum_univ_one, if_neg (by decide)]

/-- The mixed immediate kernel at the conflict marking, move leg: the
uniform half rides the move to the place-1 marking. -/
theorem net₁_imStep_move :
    net₁.toFinMA.imStep net₁.uniformPolicy i10 (Sum.inl t01) = 2⁻¹ := by
  show (∑ u : Fin 2, net₁.uniformPolicy.choice i10 u
      * net₁.toFinMA.branch i10 u (Sum.inl t01)) = 2⁻¹
  rw [Fin.sum_univ_two, net₁_uniform_choice,
    show net₁.uniformPolicy.choice i10 1 = 2⁻¹ from by
      show (if net₁.IEnabled 1 i10.1
        then ((net₁.enabledCount i10 : ℕ) : ℚ)⁻¹ else 0) = 2⁻¹
      rw [if_pos (by decide),
        show net₁.enabledCount i10 = 2 from by decide]
      norm_num]
  simp only [toFinMA_branch]
  rw [net₁_fire_discard, net₁_fire_move,
    if_pos (show net₁.IEnabled 0 i10.1 by decide),
    if_neg (show ¬ (Sum.inl t00 : net₁.Tangible ⊕ net₁.Vanishing)
      = Sum.inl t01 by decide),
    if_pos (show net₁.IEnabled 1 i10.1 by decide), if_pos rfl]
  norm_num

/-- Absorption out of the conflict marking, at the working fuel of the
trivial rank: half the mass reaches the place-1 marking in one
zero-time step. -/
theorem net₁_absorb_i10 :
    net₁.toFinMA.absorb net₁.uniformPolicy r₁ (Sum.inr i10) t01 = 2⁻¹ := by
  show absorbIter (net₁.toFinMA.imStep net₁.uniformPolicy)
    (absFuel r₁) (Sum.inr i10) t01 = 2⁻¹
  rw [show absFuel r₁ = 0 + 1 from by decide, absorbIter_succ_inr,
    Fintype.sum_sum_type, net₁_tangible_univ, net₁_vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [absorbIter_zero, hitMass_inr]
  rw [show hitMass (Sum.inl t00 : net₁.Tangible ⊕ net₁.Vanishing) t01 = 0
      from by rw [hitMass_inl]; exact if_neg (by decide),
    show hitMass (Sum.inl t01 : net₁.Tangible ⊕ net₁.Vanishing) t01 = 1
      from by rw [hitMass_inl]; exact if_pos rfl,
    net₁_imStep_move]
  norm_num

/-- Absorption out of the capacity-blocked marking: the discard is the
only enabled immediate, and it lands in the wrong tangible marking for
the split control — zero mass at the empty marking's neighbour is not
needed; what the closed-rate control consumes is that this state is
never fed by the delay layer (`net₁_race_to_i11`). -/
theorem net₁_absorb_inl_t00 :
    net₁.toFinMA.absorb net₁.uniformPolicy r₁ (Sum.inl t00) t01 = 0 := by
  show absorbIter (net₁.toFinMA.imStep net₁.uniformPolicy)
    (absFuel r₁) (Sum.inl t00) t01 = 0
  rw [absorbIter_inl, hitMass_inl, if_neg (show ¬ t00 = t01 by decide)]

theorem net₁_absorb_inl_t01 :
    net₁.toFinMA.absorb net₁.uniformPolicy r₁ (Sum.inl t01) t01 = 1 := by
  show absorbIter (net₁.toFinMA.imStep net₁.uniformPolicy)
    (absFuel r₁) (Sum.inl t01) t01 = 1
  rw [absorbIter_inl, hitMass_inl, if_pos rfl]

/-- **The uniform conflict split**: the closed rate from the empty
marking to the place-1 marking is `3 · ½ = 3/2` — the delay race feeds
the vanishing marking, the uniform scheduler gives the move half the
mass, and the discard's half returns to the source where the
off-diagonal grain thins it. -/
theorem net₁_uniform_split :
    (net₁.tangibleChain net₁.uniformPolicy r₁ net₁_zenoFree).rate
      t00 t01 = 3 / 2 := by
  show (∑ x, net₁.toFinMA.offRate t00 x
      * net₁.toFinMA.absorb net₁.uniformPolicy r₁ x t01) = 3 / 2
  rw [Fintype.sum_sum_type, net₁_tangible_univ, net₁_vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show net₁.toFinMA.offRate t00 (Sum.inl t00) = 0 from
      net₁.toFinMA.offRate_diag t00,
    show net₁.toFinMA.offRate t00 (Sum.inl t01)
        = net₁.delay.raceRate m00 m01 from
      net₁.toFinMA.offRate_of_ne (by decide),
    show net₁.toFinMA.offRate t00 (Sum.inr i10)
        = net₁.delay.raceRate m00 m10 from
      net₁.toFinMA.offRate_of_ne (by decide),
    show net₁.toFinMA.offRate t00 (Sum.inr i11)
        = net₁.delay.raceRate m00 m11 from
      net₁.toFinMA.offRate_of_ne (by decide),
    net₁_race_to_t01, net₁_race_to_vanishing, net₁_race_to_i11,
    net₁_absorb_i10]
  norm_num

/-- **The thinning of returned cascade mass**: the closed exit rate of
the empty marking is `3 − 3·½ = 3/2` — the discard's half returned to
the source and died on the off-diagonal grain. -/
theorem net₁_thinning :
    (net₁.tangibleChain net₁.uniformPolicy r₁ net₁_zenoFree).exitRate
      t00 = 3 / 2 := by
  show (∑ s', (net₁.tangibleChain net₁.uniformPolicy r₁
      net₁_zenoFree).offRate t00 s') = 3 / 2
  rw [net₁_tangible_univ, Finset.sum_insert (by decide),
    Finset.sum_singleton, FinCTMC.offRate_diag,
    FinCTMC.offRate_of_ne _ (show t00 ≠ t01 by decide),
    net₁_uniform_split]
  norm_num

/-- **The stay convention, pinned**: at the full marking the move is
disabled by capacity, and its branch row is the point mass at the
source — the zero-time no-op, not a firing. -/
theorem net₁_stay_branch :
    net₁.toFinMA.branch i11 1 (Sum.inr i11) = 1 := by decide

/-- Two places, capacity 1; an inert delay layer; two immediate
transitions forming a genuine cascade: move the place-0 token to
place 1, then consume it — from the place-0 marking the cascade takes
**two** zero-time steps through a vanishing intermediate before
absorbing in the empty marking. -/
def net₂ : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ _ => 0
      rate := fun _ => 0
      rate_nonneg := fun _ => le_rfl
      init := fun m => if m = m00 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m00 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (Finset.mem_univ _)) }
  ipre := fun u p => if (u = 0 ∧ p = 0) ∨ (u = 1 ∧ p = 1) then 1 else 0
  iread := fun _ _ => 0
  ipost := fun u p => if u = 0 ∧ p = 1 then 1 else 0

/-- The classified elements of `net₂`, named for the controls. -/
def s00 : net₂.Tangible := ⟨m00, by decide⟩
def j10 : net₂.Vanishing := ⟨m10, by decide⟩
def j01 : net₂.Vanishing := ⟨m01, by decide⟩
def j11 : net₂.Vanishing := ⟨m11, by decide⟩

theorem net₂_tangible_univ :
    (Finset.univ : Finset net₂.Tangible) = {s00} := by decide

theorem net₂_vanishing_univ :
    (Finset.univ : Finset net₂.Vanishing) = {j10, j01, j11} := by decide

/-- The move's firing outcome: the vanishing intermediate. -/
theorem net₂_fire_move :
    net₂.toSum (net₂.ifire 0 j10.1) = Sum.inr j01 := by
  rw [show net₂.ifire 0 j10.1 = m01 from by decide]
  exact dif_pos (by decide)

/-- The consume's firing outcome from the intermediate: the empty
marking, tangible. -/
theorem net₂_fire_consume :
    net₂.toSum (net₂.ifire 1 j01.1) = Sum.inl s00 := by
  rw [show net₂.ifire 1 j01.1 = m00 from by decide]
  exact dif_neg (by decide)

/-- The consume's firing outcome from the full marking: the place-0
marking, still vanishing. -/
theorem net₂_fire_full :
    net₂.toSum (net₂.ifire 1 j11.1) = Sum.inr j10 := by
  rw [show net₂.ifire 1 j11.1 = m10 from by decide]
  exact dif_pos (by decide)

/-- A rank for `net₂`'s cascade: the weighted token count
`2·(place 0) + (place 1)` — the move `(1,0) ↦ (0,1)` descends `2 ↦ 1`,
the consume `(0,1) ↦ (0,0)` leaves the vanishing sort, and the
full-marking consume `(1,1) ↦ (1,0)` descends `3 ↦ 2`. -/
def r₂ : net₂.Vanishing → ℕ := fun i => 2 * (i.1 0 : ℕ) + (i.1 1 : ℕ)

theorem net₂_rank : net₂.CascadeRank r₂ := by
  intro i u hu j hj
  have hi : i = j10 ∨ i = j01 ∨ i = j11 := by
    have h := Finset.mem_univ i
    rw [net₂_vanishing_univ] at h
    simpa using h
  rcases hi with rfl | rfl | rfl
  · obtain rfl : u = 0 :=
      (by decide : ∀ v : Fin 2, net₂.IEnabled v j10.1 → v = 0) u hu
    rw [net₂_fire_move] at hj
    obtain rfl : j01 = j := by simpa using hj
    decide
  · obtain rfl : u = 1 :=
      (by decide : ∀ v : Fin 2, net₂.IEnabled v j01.1 → v = 1) u hu
    rw [net₂_fire_consume] at hj
    simp at hj
  · obtain rfl : u = 1 :=
      (by decide : ∀ v : Fin 2, net₂.IEnabled v j11.1 → v = 1) u hu
    rw [net₂_fire_full] at hj
    obtain rfl : j10 = j := by simpa using hj
    decide

theorem net₂_zenoFree :
    ZenoFree (net₂.toFinMA.imStep net₂.uniformPolicy) r₂ :=
  net₂.zenoFree_uniform net₂_rank

/-- The first cascade step: the move carries the whole mass to the
vanishing intermediate. -/
theorem net₂_imStep_move :
    net₂.toFinMA.imStep net₂.uniformPolicy j10 (Sum.inr j01) = 1 := by
  show (∑ u : Fin 2, net₂.uniformPolicy.choice j10 u
      * net₂.toFinMA.branch j10 u (Sum.inr j01)) = 1
  rw [Fin.sum_univ_two,
    show net₂.uniformPolicy.choice j10 0 = 1 from by
      show (if net₂.IEnabled 0 j10.1
        then ((net₂.enabledCount j10 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show net₂.enabledCount j10 = 1 from by decide]
      norm_num,
    show net₂.uniformPolicy.choice j10 1 = 0 from by
      show (if net₂.IEnabled 1 j10.1
        then ((net₂.enabledCount j10 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)]]
  simp only [toFinMA_branch]
  rw [net₂_fire_move, if_pos (show net₂.IEnabled 0 j10.1 by decide),
    if_pos rfl]
  norm_num

/-- The second cascade step: the consume carries the whole mass to the
empty tangible marking. -/
theorem net₂_imStep_consume :
    net₂.toFinMA.imStep net₂.uniformPolicy j01 (Sum.inl s00) = 1 := by
  show (∑ u : Fin 2, net₂.uniformPolicy.choice j01 u
      * net₂.toFinMA.branch j01 u (Sum.inl s00)) = 1
  rw [Fin.sum_univ_two,
    show net₂.uniformPolicy.choice j01 0 = 0 from by
      show (if net₂.IEnabled 0 j01.1
        then ((net₂.enabledCount j01 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)],
    show net₂.uniformPolicy.choice j01 1 = 1 from by
      show (if net₂.IEnabled 1 j01.1
        then ((net₂.enabledCount j01 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show net₂.enabledCount j01 = 1 from by decide]
      norm_num]
  simp only [toFinMA_branch]
  rw [net₂_fire_consume, if_pos (show net₂.IEnabled 1 j01.1 by decide),
    if_pos rfl]
  norm_num

/-- The off-path legs of the first step carry no mass. -/
theorem net₂_imStep_move_off (y : net₂.Tangible ⊕ net₂.Vanishing)
    (hy : y ≠ Sum.inr j01) :
    net₂.toFinMA.imStep net₂.uniformPolicy j10 y = 0 := by
  show (∑ u : Fin 2, net₂.uniformPolicy.choice j10 u
      * net₂.toFinMA.branch j10 u y) = 0
  rw [Fin.sum_univ_two,
    show net₂.uniformPolicy.choice j10 0 = 1 from by
      show (if net₂.IEnabled 0 j10.1
        then ((net₂.enabledCount j10 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show net₂.enabledCount j10 = 1 from by decide]
      norm_num,
    show net₂.uniformPolicy.choice j10 1 = 0 from by
      show (if net₂.IEnabled 1 j10.1
        then ((net₂.enabledCount j10 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)]]
  simp only [toFinMA_branch]
  rw [net₂_fire_move, if_pos (show net₂.IEnabled 0 j10.1 by decide),
    if_neg (show ¬ (Sum.inr j01 : net₂.Tangible ⊕ net₂.Vanishing) = y
      from fun h => hy h.symm)]
  norm_num

/-- The off-path legs of the second step carry no mass. -/
theorem net₂_imStep_consume_off (y : net₂.Tangible ⊕ net₂.Vanishing)
    (hy : y ≠ Sum.inl s00) :
    net₂.toFinMA.imStep net₂.uniformPolicy j01 y = 0 := by
  show (∑ u : Fin 2, net₂.uniformPolicy.choice j01 u
      * net₂.toFinMA.branch j01 u y) = 0
  rw [Fin.sum_univ_two,
    show net₂.uniformPolicy.choice j01 0 = 0 from by
      show (if net₂.IEnabled 0 j01.1
        then ((net₂.enabledCount j01 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)],
    show net₂.uniformPolicy.choice j01 1 = 1 from by
      show (if net₂.IEnabled 1 j01.1
        then ((net₂.enabledCount j01 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show net₂.enabledCount j01 = 1 from by decide]
      norm_num]
  simp only [toFinMA_branch]
  rw [net₂_fire_consume, if_pos (show net₂.IEnabled 1 j01.1 by decide),
    if_neg (show ¬ (Sum.inl s00 : net₂.Tangible ⊕ net₂.Vanishing) = y
      from fun h => hy h.symm)]
  norm_num

/-- Absorption from the vanishing intermediate, one fuel short of the
working fuel: one consume step, then the Markovian point mass. -/
theorem net₂_absorb_mid :
    absorbIter (net₂.toFinMA.imStep net₂.uniformPolicy) 3
      (Sum.inr j01) s00 = 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, absorbIter_succ_inr,
    Fintype.sum_sum_type, net₂_tangible_univ, net₂_vanishing_univ,
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    net₂_imStep_consume,
    net₂_imStep_consume_off (Sum.inr j10) (by decide),
    net₂_imStep_consume_off (Sum.inr j01) (by decide),
    net₂_imStep_consume_off (Sum.inr j11) (by decide),
    show absorbIter (net₂.toFinMA.imStep net₂.uniformPolicy) 2
        (Sum.inl s00) s00 = 1 from by
      rw [absorbIter_inl, hitMass_inl, if_pos rfl]]
  norm_num

/-- **The two-step cascade absorbs whole**: from the place-0 marking,
absorption reaches the empty marking with mass 1 — two immediate steps
through the vanishing intermediate, pinning the absorbing computation
beyond depth one. -/
theorem net₂_cascade_absorb :
    net₂.toFinMA.absorb net₂.uniformPolicy r₂
      (Sum.inr j10) s00 = 1 := by
  show absorbIter (net₂.toFinMA.imStep net₂.uniformPolicy)
    (absFuel r₂) (Sum.inr j10) s00 = 1
  rw [show absFuel r₂ = 3 + 1 from by decide, absorbIter_succ_inr,
    Fintype.sum_sum_type, net₂_tangible_univ, net₂_vanishing_univ,
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    net₂_imStep_move, net₂_absorb_mid,
    net₂_imStep_move_off (Sum.inl s00) (by decide),
    net₂_imStep_move_off (Sum.inr j10) (by decide),
    net₂_imStep_move_off (Sum.inr j11) (by decide)]
  norm_num

end SpnCascadeControls

end Adequacy
end SuFunctor
