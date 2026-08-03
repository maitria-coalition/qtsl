import SuFunctor.Adequacy.CtmcJumpChain
import SuFunctor.Adequacy.Mdp

/-! # Adequacy: Markov automata, fixed-scheduler face

The continuous-time adequacy square with nondeterminism resolved: a
closed Markov automaton (Eisentraut–Hermanns–Zhang, LICS 2010) under a
**declared memoryless randomized scheduler**, at the **time-abstract
stratum**.  A Markov automaton combines the chain frame's exponential
races with the decision frame's immediate probabilistic actions under
the maximal-progress assumption: a state with an enabled action is
*instantaneous* (zero sojourn), a state without is *Markovian*.  The
presentation here is two-sorted — `S` the Markovian states, `I` the
instantaneous ones — so that maximal progress is *structure*: a timed
row at an instantaneous state is unrepresentable by the domain type,
mirroring the shipped theory's axiom exactly as the chain grain's
off-diagonal key mirrors "diagonal determined".  The closed reading
(every immediate action internal) is the right one for a
declared-scheduler square, since schedulers resolve closed systems;
the visible-action/parallel-composition face is a deliberately
separate stratum.

**The fixed-scheduler reduction.**  Under a scheduler `σ` — a
per-state distribution over actions, exactly the decision square's
`Policy` grain, reused verbatim — the immediate part becomes a
subchain over the instantaneous states, absorbing in the Markovian
ones.  When that subchain is **Zeno-free** — certified here by a rank
witness, the house's ranking-argument genus: a rank on instantaneous
states that every scheduler-supported immediate transition strictly
decreases — each instantaneous state `x` absorbs, within finitely many
immediate steps, into a distribution over Markovian states, and the
observed process is the finite chain with rates

  `q^σ(s, s') = ∑ x, q(s, x) · P^σ(x)(s')`,

because immediate excursions occupy zero time almost surely.  The
absorption kernel `P^σ` is computed by a fuel-indexed iteration
(`absorbIter`), and the **acyclic-absorption package** proves it is
the genuine article: fuel past the rank is idle (`absorbIter_stab`),
absorption is a full distribution over Markovian states
(`absorbIter_mass` — Zeno-freedom is *spent* exactly here, and the
closed object's distribution facts are created by this lemma, never
assumed), and any solution of the absorbing-system equations agrees
with it (`absorbIter_unique` — the computed kernel is *the* absorbing
distribution, not a choice).

**Self-loop thinning is structural.**  Immediate branches returning to
their Markovian source would be self-loops of the closed chain; the
literature drops them (memorylessness: self-loops change no path
probabilities).  Here nothing drops them — they die on the landed
grain: the closed chain's diagonal is dead data by the off-diagonal
key type of the chain rows, and the thinning identity
(`close_exitRate_thinning`: closed exit rate = original exit rate
minus returned mass) together with `close_exitRate_le` (a scheduler
can only remove activity, never add rate mass) states the design fact
as theorems.  Likewise the scheduler *cannot touch rates*: its entire
influence enters through the branch masses of the absorption kernel.

**The square** (`ma_adequacy`): compile the automaton's rows and the
scheduler rows, close the scheduler at the row level to chain-grain
rate rows, jump-close those, denote — and this agrees, by an
invertible globular cell of `Crd (Traj S k)`, with interpreting
classically (the closed chain's jump-chain path law at jump horizon
`k`) and including through `singletonC`.  The proof is **three-storey
engine reuse**: the one genuinely automaton-shaped identity is the
rate-closure triangle `compile_closeMa_comm` — scheduler-closing
before or after compilation stores the same rate rows, definitional by
the shared-normalizer discipline — and `ctmc_jump_adequacy` finishes,
which is itself `dtmc_adequacy` at the jump chain.  No new induction:
every stochasticity fact was spent once, in the chain engine, and
every rate fact once, in the continuous-time square.

The rate-factorization seam of the continuous-time square is consumed
here as promised there: `close_offRate_factor` proves the two
community spellings of the closure formula — Norris's rate spelling
above, and the race-then-jump-then-absorb probabilistic spelling —
agree, by `jumpChain_step_mul_exit` at the automaton's *pre-chain*
(its timed part as a chain on the full two-sorted state space, where
maximal progress makes instantaneous states rate-absorbing).

**Semantic-universe anchor** (the descent direction, explicit): this
square is a descent statement of the mathematical-models chapter,
derived downward from the mechanized semantic universe.  Its storey is
the SU's spec fibres — `SpecDnf (Plain.Joint (Traj S k))`, the fibres
the spacetime total inherits definitionally — judged by `CoupledSat`;
the landed theorems it rides are the continuous-time square
(`ctmc_jump_adequacy`, `jumpChain_step_mul_exit`), the decision
square's scheduler grain (`Policy`, `PolicyRows`, `compilePolicy`),
and the judgment bridge (consumed through `su_ctmc_jump_adequacy`);
its own SU citizenship is mechanized in the same leg (`su_ma_adequacy`,
`SemanticUniverseWiring`).  No new fibre vocabulary: the compiled grain
mirrored is the shipped formation rule's, and both closures land in
the landed row grains.

Deliberately separate strata, named: the **time-law stratum**
(exponential holding times — inherited unchanged from the
continuous-time square); **scheduler quantification** (bounds uniform
over schedulers — the envelope stratum, exactly as the decision
square's demonic face); **parallel composition and visible actions**
(the open-automaton face; this square stages one closed component);
**history-dependent or time-dependent schedulers** (the grain here is
memoryless randomized, deterministic as the probability-one special
case); and **non-Zeno-free automata** (immediate cycles under the
scheduler — outside this square by hypothesis, never silently
discharged).  mathlib has no Markov-automaton machinery, so the
community-vocabulary connector is the chain connector transported
twice — through the closure, then the jump chain — stated as such. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S I : Type} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I]

/-! ## The absorbing computation, over a bare immediate kernel

Everything in this stretch is stated over a bare kernel
`f : I → S ⊕ I → ℚ`, so the classical reading (the scheduler-mixed
branches) and the row-level reading (the scheduler rows mixing the
compiled rows) consume one definition and one lemma package — the
shared-normalizer discipline that makes the rate-closure triangle
definitional. -/

/-- The Markovian point mass: absorption already complete. -/
def hitMass (x : S ⊕ I) (m : S) : ℚ :=
  if x = Sum.inl m then 1 else 0

omit [Fintype S] [Fintype I] in
theorem hitMass_nonneg (x : S ⊕ I) (m : S) : 0 ≤ hitMass x m := by
  unfold hitMass
  split <;> norm_num

omit [Fintype S] [Fintype I] in
@[simp] theorem hitMass_inl (m' m : S) :
    hitMass (Sum.inl m' : S ⊕ I) m = if m' = m then 1 else 0 := by
  simp [hitMass]

omit [Fintype S] [Fintype I] in
@[simp] theorem hitMass_inr (i : I) (m : S) :
    hitMass (Sum.inr i : S ⊕ I) m = 0 := by
  simp [hitMass]

/-- Zeno-freedom of an immediate kernel, certified by a rank witness:
every supported immediate transition between instantaneous states
strictly decreases the rank.  This is the theory's "immediate part is
acyclic under the scheduler" assertion carried as a ranking argument —
the certificate genus — stated over a bare kernel so the classical and
row-level readings share it. -/
def ZenoFree (f : I → S ⊕ I → ℚ) (r : I → ℕ) : Prop :=
  ∀ i j, f i (Sum.inr j) ≠ 0 → r j < r i

/-- The fuel-indexed absorbing computation of an immediate kernel:
from a Markovian state, the point mass (already absorbed, any fuel);
from an instantaneous state, one immediate composition per unit of
fuel.  Fuel `0` at an instantaneous state is the not-yet-absorbed
zero — the honest reading of an unfinished computation. -/
def absorbIter (f : I → S ⊕ I → ℚ) : ℕ → S ⊕ I → S → ℚ
  | 0, x, m => hitMass x m
  | n + 1, x, m =>
    match x with
    | Sum.inl m' => hitMass (Sum.inl m' : S ⊕ I) m
    | Sum.inr i => ∑ y, f i y * absorbIter f n y m

@[simp] theorem absorbIter_zero (f : I → S ⊕ I → ℚ) (x : S ⊕ I)
    (m : S) : absorbIter f 0 x m = hitMass x m := rfl

@[simp] theorem absorbIter_succ_inr (f : I → S ⊕ I → ℚ) (n : ℕ)
    (i : I) (m : S) :
    absorbIter f (n + 1) (Sum.inr i) m = ∑ y, f i y * absorbIter f n y m :=
  rfl

/-- Markovian states are absorbed at every fuel. -/
@[simp] theorem absorbIter_inl (f : I → S ⊕ I → ℚ) (n : ℕ) (m' : S)
    (m : S) :
    absorbIter f n (Sum.inl m') m = hitMass (Sum.inl m' : S ⊕ I) m := by
  cases n <;> rfl

theorem absorbIter_nonneg (f : I → S ⊕ I → ℚ)
    (hf : ∀ i y, 0 ≤ f i y) :
    ∀ (n : ℕ) (x : S ⊕ I) (m : S), 0 ≤ absorbIter f n x m
  | 0, x, m => hitMass_nonneg x m
  | _ + 1, Sum.inl m', m => hitMass_nonneg (Sum.inl m' : S ⊕ I) m
  | n + 1, Sum.inr i, m => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hf i y) (absorbIter_nonneg f hf n y m)

/-! ## The acyclic-absorption package -/

/-- Fuel past the rank is idle: one more unit of fuel changes nothing
once the rank is exceeded.  Strong induction along the rank — the
first of the three places Zeno-freedom is spent. -/
theorem absorbIter_succ_stab (f : I → S ⊕ I → ℚ) (r : I → ℕ)
    (hr : ZenoFree f r) :
    ∀ (n : ℕ) (i : I) (m : S), r i < n →
      absorbIter f (n + 1) (Sum.inr i) m = absorbIter f n (Sum.inr i) m
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, m, hn => by
    rw [absorbIter_succ_inr, absorbIter_succ_inr]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hz : f i y = 0
    · rw [hz, zero_mul, zero_mul]
    · congr 1
      cases y with
      | inl m' => rw [absorbIter_inl, absorbIter_inl]
      | inr j =>
        exact absorbIter_succ_stab f r hr n j m
          (lt_of_lt_of_le (hr i j hz) (Nat.lt_succ_iff.mp hn))

theorem absorbIter_add_stab (f : I → S ⊕ I → ℚ) (r : I → ℕ)
    (hr : ZenoFree f r) (i : I) (m : S) {n : ℕ} (hn : r i < n) :
    ∀ d : ℕ, absorbIter f (n + d) (Sum.inr i) m
      = absorbIter f n (Sum.inr i) m
  | 0 => rfl
  | d + 1 =>
    (absorbIter_succ_stab f r hr (n + d) i m
        (lt_of_lt_of_le hn (Nat.le_add_right n d))).trans
      (absorbIter_add_stab f r hr i m hn d)

/-- Any two fuels past the rank agree: the absorbing computation has
stabilized. -/
theorem absorbIter_stab (f : I → S ⊕ I → ℚ) (r : I → ℕ)
    (hr : ZenoFree f r) (i : I) (m : S) {n n' : ℕ}
    (h : r i < n) (h' : r i < n') :
    absorbIter f n (Sum.inr i) m = absorbIter f n' (Sum.inr i) m := by
  rcases le_total n n' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (absorbIter_add_stab f r hr i m h d).symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact absorbIter_add_stab f r hr i m h' d

theorem absorbIter_inl_mass (f : I → S ⊕ I → ℚ) (n : ℕ) (m' : S) :
    ∑ m, absorbIter f n (Sum.inl m') m = 1 := by
  simp_rw [absorbIter_inl, hitMass_inl]
  rw [Finset.sum_ite_eq univ m' fun _ => (1 : ℚ)]
  simp

/-- **The acyclic-absorption lemma**: past the rank, absorption from an
instantaneous state is a full distribution over the Markovian states.
Zeno-freedom is *spent* exactly here — an immediate self-loop would
never absorb — and the closed object's distribution facts are created
by this lemma, never assumed: the immediate rows carry masses, the
rate rows carry no sums, and stochasticity of the closure is derived.
No sign hypothesis is needed: the argument is mass bookkeeping. -/
theorem absorbIter_mass (f : I → S ⊕ I → ℚ) (r : I → ℕ)
    (hr : ZenoFree f r) (hrow : ∀ i, ∑ y, f i y = 1) :
    ∀ (n : ℕ) (i : I), r i < n →
      ∑ m, absorbIter f n (Sum.inr i) m = 1
  | 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, hn => by
    simp_rw [absorbIter_succ_inr]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hterm : ∀ y, f i y * (∑ m, absorbIter f n y m) = f i y * 1 := by
      intro y
      by_cases hz : f i y = 0
      · rw [hz, zero_mul, zero_mul]
      · congr 1
        cases y with
        | inl m' => exact absorbIter_inl_mass f n m'
        | inr j =>
          exact absorbIter_mass f r hr hrow n j
            (lt_of_lt_of_le (hr i j hz) (Nat.lt_succ_iff.mp hn))
    rw [Finset.sum_congr rfl fun y _ => hterm y]
    simp_rw [mul_one]
    exact hrow i

/-- **Uniqueness of absorption**: any kernel satisfying the
absorbing-system equations — the Markovian point mass on Markovian
states, the one-step fixed point through the immediate kernel on
instantaneous ones — agrees with the computed absorption past the
rank.  The community tie of the closure: under Zeno-freedom the
absorbing distribution of the resolved immediate part is unique, so
the computed kernel is *the* absorbing distribution, not a choice. -/
theorem absorbIter_unique (f : I → S ⊕ I → ℚ) (r : I → ℕ)
    (hr : ZenoFree f r) (g : S ⊕ I → S → ℚ)
    (hg_inl : ∀ m' m, g (Sum.inl m') m = hitMass (Sum.inl m' : S ⊕ I) m)
    (hg_step : ∀ i m, g (Sum.inr i) m = ∑ y, f i y * g y m) :
    ∀ (n : ℕ) (i : I) (m : S), r i < n →
      g (Sum.inr i) m = absorbIter f n (Sum.inr i) m
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, m, hn => by
    rw [hg_step, absorbIter_succ_inr]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hz : f i y = 0
    · rw [hz, zero_mul, zero_mul]
    · congr 1
      cases y with
      | inl m' => rw [hg_inl, absorbIter_inl]
      | inr j =>
        exact absorbIter_unique f r hr g hg_inl hg_step n j m
          (lt_of_lt_of_le (hr i j hz) (Nat.lt_succ_iff.mp hn))

/-! ## The working fuel -/

/-- The working fuel: one past the largest rank — enough for every
instantaneous state to have absorbed. -/
def absFuel (r : I → ℕ) : ℕ := univ.sup r + 1

omit [Fintype S] [DecidableEq S] [DecidableEq I] in
theorem lt_absFuel (r : I → ℕ) (i : I) : r i < absFuel r :=
  Nat.lt_succ_of_le (Finset.le_sup (mem_univ i))

variable {A : Type} [Fintype A]

/-- A convex mixture of row-stochastic kernels is row-stochastic — the
decision square's mixing exchange, factored over bare data so the
classical and the row-level readings consume one proof. -/
theorem mix_row_sum {W X : Type} [Fintype W] [Fintype X]
    (w : W → ℚ) (g : W → X → ℚ)
    (hw : ∑ a, w a = 1) (hg : ∀ a, ∑ x, g a x = 1) :
    ∑ x, ∑ a, w a * g a x = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hg, mul_one]
  exact hw

/-! ## The classical object -/

/-- A finite closed Markov automaton, two-sorted
(Eisentraut–Hermanns–Zhang, LICS 2010, at the closed reading): `S` the
Markovian states, `I` the instantaneous ones, `A` the actions.  Timed
transitions carry rational rates and have **Markovian sources only** —
maximal progress stated as structure: a timed row at an instantaneous
state is unrepresentable by the domain type.  Immediate transitions
are action-keyed probabilistic branches from instantaneous states —
the decision frame's kernel idiom, row-stochastic per (state, action),
the literature's own well-formedness.  Only off-diagonal rates are
data: the rate of a Markovian state to itself is never consulted, as
for chains. -/
structure FinMA (S I A : Type) [Fintype S] [Fintype I] [Fintype A] where
  /-- Timed transition rate from a Markovian state to any state; only
  off-diagonal values are ever consulted. -/
  rate : S → S ⊕ I → ℚ
  /-- Immediate branch probability: from an instantaneous state, under
  an action, to any state. -/
  branch : I → A → S ⊕ I → ℚ
  /-- Initial-distribution mass at a state (either sort). -/
  init : S ⊕ I → ℚ
  rate_nonneg : ∀ s x, Sum.inl s ≠ x → 0 ≤ rate s x
  branch_nonneg : ∀ i a x, 0 ≤ branch i a x
  branch_row_sum : ∀ i a, ∑ x, branch i a x = 1
  init_nonneg : ∀ x, 0 ≤ init x
  init_sum : ∑ x, init x = 1

/-- The off-diagonal timed read: zero at the Markovian source itself,
the stored rate elsewhere.  Every consumer of the rates goes through
this read — the chain grain's "diagonal determined" convention held
semantically, at the automaton. -/
def FinMA.offRate (M : FinMA S I A) (s : S) (x : S ⊕ I) : ℚ :=
  if _h : Sum.inl s = x then 0 else M.rate s x

theorem FinMA.offRate_nonneg (M : FinMA S I A) (s : S) (x : S ⊕ I) :
    0 ≤ M.offRate s x := by
  unfold FinMA.offRate
  split
  · exact le_rfl
  · exact M.rate_nonneg s x ‹Sum.inl s ≠ x›

@[simp] theorem FinMA.offRate_diag (M : FinMA S I A) (s : S) :
    M.offRate s (Sum.inl s) = 0 := by
  unfold FinMA.offRate
  rw [dif_pos rfl]

theorem FinMA.offRate_of_ne (M : FinMA S I A) {s : S} {x : S ⊕ I}
    (h : Sum.inl s ≠ x) : M.offRate s x = M.rate s x := by
  unfold FinMA.offRate
  rw [dif_neg h]

/-- The exit rate of a Markovian state: total timed rate out. -/
def FinMA.exitRate (M : FinMA S I A) (s : S) : ℚ :=
  ∑ x, M.offRate s x

theorem FinMA.exitRate_nonneg (M : FinMA S I A) (s : S) :
    0 ≤ M.exitRate s :=
  Finset.sum_nonneg fun x _ => M.offRate_nonneg s x

/-! ## The scheduler and the mixed immediate kernel

The scheduler grain is the decision square's `Policy`, reused
verbatim: a memoryless randomized scheduler is a per-state
distribution over actions, a deterministic one the probability-one
special case (`Policy.det`). -/

/-- The scheduler-closed immediate kernel: mix the action-keyed
branches through the scheduler — the decision square's closed-loop
mixing, aimed at the immediate transitions. -/
def FinMA.imStep (M : FinMA S I A) (σ : Policy I A) (i : I)
    (x : S ⊕ I) : ℚ :=
  ∑ a, σ.choice i a * M.branch i a x

omit [DecidableEq S] [DecidableEq I] in
theorem FinMA.imStep_nonneg (M : FinMA S I A) (σ : Policy I A) (i : I)
    (x : S ⊕ I) : 0 ≤ M.imStep σ i x :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (σ.nonneg i a) (M.branch_nonneg i a x)

omit [DecidableEq S] [DecidableEq I] in
/-- The mixed immediate kernel is row-stochastic — the `Policy` mixing
exchange at the immediate transitions. -/
theorem FinMA.imStep_row_sum (M : FinMA S I A) (σ : Policy I A)
    (i : I) : ∑ x, M.imStep σ i x = 1 :=
  mix_row_sum (σ.choice i) (M.branch i) (σ.row_sum i)
    (M.branch_row_sum i)

omit [DecidableEq S] [DecidableEq I] in
/-- The scheduler-free sufficient condition for Zeno-freedom: a rank
that decreases on every branch row is Zeno-free for *every*
scheduler's mixed kernel — mixture support lies in the union of branch
supports. -/
theorem zenoFree_of_branch (M : FinMA S I A) (r : I → ℕ)
    (hb : ∀ i a j, M.branch i a (Sum.inr j) ≠ 0 → r j < r i)
    (σ : Policy I A) : ZenoFree (M.imStep σ) r := by
  intro i j hne
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hb i a j (right_ne_zero_of_mul ha)

/-! ## The absorption kernel of the automaton -/

/-- The absorption kernel of the automaton under the scheduler: the
absorbing computation of the mixed immediate kernel, at the working
fuel. -/
def FinMA.absorb (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ) :
    S ⊕ I → S → ℚ :=
  absorbIter (M.imStep σ) (absFuel r)

theorem FinMA.absorb_nonneg (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (x : S ⊕ I) (m : S) : 0 ≤ M.absorb σ r x m :=
  absorbIter_nonneg (M.imStep σ) (M.imStep_nonneg σ) (absFuel r) x m

/-- Absorption is a distribution over Markovian states, from *every*
state — the working fuel exceeds every rank. -/
theorem FinMA.absorb_mass (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (x : S ⊕ I) :
    ∑ m, M.absorb σ r x m = 1 := by
  cases x with
  | inl m' => exact absorbIter_inl_mass (M.imStep σ) (absFuel r) m'
  | inr i =>
    exact absorbIter_mass (M.imStep σ) r hr (M.imStep_row_sum σ)
      (absFuel r) i (lt_absFuel r i)

/-- The fixed-point property at the working fuel: absorption from an
instantaneous state is one immediate step, then absorption. -/
theorem FinMA.absorb_step (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (i : I) (m : S) :
    M.absorb σ r (Sum.inr i) m
      = ∑ y, M.imStep σ i y * M.absorb σ r y m := by
  show absorbIter (M.imStep σ) (univ.sup r + 1) (Sum.inr i) m = _
  rw [absorbIter_succ_inr]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hz : M.imStep σ i y = 0
  · rw [hz, zero_mul, zero_mul]
  · congr 1
    cases y with
    | inl m' =>
      show absorbIter (M.imStep σ) (univ.sup r) (Sum.inl m') m
        = absorbIter (M.imStep σ) (absFuel r) (Sum.inl m') m
      rw [absorbIter_inl, absorbIter_inl]
    | inr j =>
      exact absorbIter_stab (M.imStep σ) r hr j m
        (lt_of_lt_of_le (hr i j hz) (Finset.le_sup (mem_univ i)))
        (lt_absFuel r j)

/-! ## The closure, classically -/

/-- **The fixed-scheduler closure**: the closed continuous-time chain
of the automaton under the scheduler — rates
`q^σ(s, s') = ∑ x, q(s, x) · P^σ(x)(s')`, initial distribution pushed
through absorption.  This is the object the literature's
fixed-scheduler reduction assigns to the pair.  The stored diagonal is
the un-thinned return mass and is dead data: the chain grain never
reads it — **self-loop thinning is the landed diagonal-blindness,
structurally**.  The scheduler cannot touch rates: its entire
influence enters through the absorption kernel's branch masses. -/
def FinMA.close (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ)
    (hr : ZenoFree (M.imStep σ) r) : FinCTMC S where
  rate s s' := ∑ x, M.offRate s x * M.absorb σ r x s'
  init m := ∑ x, M.init x * M.absorb σ r x m
  rate_nonneg s s' _ := Finset.sum_nonneg fun x _ =>
    mul_nonneg (M.offRate_nonneg s x) (M.absorb_nonneg σ r x s')
  init_nonneg m := Finset.sum_nonneg fun x _ =>
    mul_nonneg (M.init_nonneg x) (M.absorb_nonneg σ r x m)
  init_sum := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hterm : ∀ x, M.init x * (∑ m, M.absorb σ r x m)
        = M.init x * 1 := fun x => by rw [M.absorb_mass σ r hr x]
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    simp_rw [mul_one]
    exact M.init_sum

@[simp] theorem FinMA.close_rate (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (s s' : S) :
    (M.close σ r hr).rate s s'
      = ∑ x, M.offRate s x * M.absorb σ r x s' := rfl

@[simp] theorem FinMA.close_init (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (m : S) :
    (M.close σ r hr).init m = ∑ x, M.init x * M.absorb σ r x m := rfl

/-! ## The rate-closure receipts -/

/-- The automaton's pre-chain: its timed part as a continuous-time
chain on the full two-sorted state space.  Instantaneous states have
no timed rows at all — maximal progress makes them rate-absorbing
here, which is exactly what lets the landed jump-chain machinery
speak about the automaton's race-and-jump structure. -/
def FinMA.preChain (M : FinMA S I A) : FinCTMC (S ⊕ I) where
  rate x y :=
    match x with
    | Sum.inl s => M.rate s y
    | Sum.inr _ => 0
  init := M.init
  rate_nonneg x y h := by
    cases x with
    | inl s => exact M.rate_nonneg s y h
    | inr _ => exact le_rfl
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

theorem FinMA.preChain_offRate (M : FinMA S I A) (s : S) (x : S ⊕ I) :
    M.preChain.offRate (Sum.inl s) x = M.offRate s x := rfl

theorem FinMA.preChain_offRate_inr (M : FinMA S I A) (i : I)
    (y : S ⊕ I) : M.preChain.offRate (Sum.inr i) y = 0 := by
  unfold FinCTMC.offRate
  split <;> rfl

theorem FinMA.preChain_exitRate (M : FinMA S I A) (s : S) :
    M.preChain.exitRate (Sum.inl s) = M.exitRate s := rfl

/-- **The two community spellings of the closure agree**: the closed
off-diagonal rate is the exit rate times the jump-then-absorb
probability — Norris's rate spelling equals the
race-then-jump-then-absorb probabilistic spelling.  Proved by the
continuous-time square's rate-factorization identity
(`jumpChain_step_mul_exit`) at the pre-chain, consuming that seam
exactly as it was staged.  Unconditional in the source: absorbing
Markovian states included (both sides vanish). -/
theorem FinMA.close_offRate_factor (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) {s s' : S}
    (hne : s ≠ s') :
    (M.close σ r hr).offRate s s'
      = M.exitRate s * ∑ x, M.preChain.jumpChain.step (Sum.inl s) x
          * M.absorb σ r x s' := by
  rw [Finset.mul_sum]
  have hterm : ∀ x, M.exitRate s
        * (M.preChain.jumpChain.step (Sum.inl s) x * M.absorb σ r x s')
      = M.offRate s x * M.absorb σ r x s' := by
    intro x
    rw [← M.preChain_offRate s x,
      ← M.preChain.jumpChain_step_mul_exit (Sum.inl s) x,
      M.preChain_exitRate]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x,
    FinCTMC.offRate_of_ne _ hne]
  rfl

/-- **The self-loop thinning identity**: the closed chain's exit rate
is the original exit rate minus the mass returned to the source —
thinning only ever *removes* activity. -/
theorem FinMA.close_exitRate_thinning (M : FinMA S I A)
    (σ : Policy I A) (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r)
    (s : S) :
    (M.close σ r hr).exitRate s
      = M.exitRate s - ∑ x, M.offRate s x * M.absorb σ r x s := by
  have hoff : ∀ s' : S, (M.close σ r hr).offRate s s'
      = (∑ x, M.offRate s x * M.absorb σ r x s')
        - (if s = s' then ∑ x, M.offRate s x * M.absorb σ r x s'
           else 0) := by
    intro s'
    by_cases h : s = s'
    · subst h
      rw [FinCTMC.offRate_diag, if_pos rfl]
      ring
    · rw [FinCTMC.offRate_of_ne _ h, if_neg h, FinMA.close_rate]
      ring
  show ∑ s', (M.close σ r hr).offRate s s' = _
  rw [Finset.sum_congr rfl fun s' _ => hoff s', Finset.sum_sub_distrib,
    Finset.sum_ite_eq univ s
      (fun s' => ∑ x, M.offRate s x * M.absorb σ r x s'),
    if_pos (mem_univ s)]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hterm : ∀ x, M.offRate s x * (∑ s', M.absorb σ r x s')
      = M.offRate s x * 1 := fun x => by rw [M.absorb_mass σ r hr x]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp_rw [mul_one]
  rfl

/-- The closed exit rate never exceeds the original: a scheduler can
only remove activity. -/
theorem FinMA.close_exitRate_le (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (s : S) :
    (M.close σ r hr).exitRate s ≤ M.exitRate s := by
  rw [M.close_exitRate_thinning σ r hr s]
  have h : 0 ≤ ∑ x, M.offRate s x * M.absorb σ r x s :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (M.offRate_nonneg s x) (M.absorb_nonneg σ r x s)
  linarith

/-! ## The classical semantics of the fixed-scheduler face -/

/-- **The time-abstract semantics of the automaton under the declared
scheduler**: the path law of the closed chain's jump chain at jump
horizon `k` — which Markovian states, in which order.  The holding
times are the separate time-law stratum, exactly as for chains. -/
noncomputable def FinMA.pathLaw (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ) :
    SubPMF (Traj S k) :=
  (M.close σ r hr).jumpLaw k

/-- The fixed-scheduler face spends its whole mass — inherited through
two closures, one line. -/
theorem FinMA.pathLaw_mass (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ) :
    (M.pathLaw σ r hr k).mass = 1 :=
  FinCTMC.jumpLaw_mass (M.close σ r hr) k

/-! ## The compiled rows: both parents' disciplines by type -/

/-- The compiled presentation: the row grain of the Markov-automaton
system profile.  Rate rows are keyed by pairs with **Markovian source
and non-self destination** — a timed row at an instantaneous state and
a diagonal rate entry are both unrepresentable rather than linted,
mirroring the shipped formation rule; immediate rows are action-keyed,
the decision former's idiom; initial rows range over both sorts.
Sparse: an absent row and a zero entry are the same datum. -/
structure MaRows (S I A : Type) where
  /-- Off-diagonal timed rate rows: `(src, dst) ↦` stored rate, with
  the Markovian source in the key's first component and
  `Sum.inl src ≠ dst` carried by the key. -/
  rateRow : {p : S × (S ⊕ I) // Sum.inl p.1 ≠ p.2} →₀ ℚ
  /-- Action-keyed immediate rows: `(src, action, dst) ↦` stored
  probability. -/
  branchRow : I × A × (S ⊕ I) →₀ ℚ
  /-- Initial-distribution rows over both sorts. -/
  initRow : (S ⊕ I) →₀ ℚ

/-- Well-formedness of automaton rows: nonnegative rates, immediate
rows a distribution per (state, action), initial rows a distribution.
Deliberately **no row-sum constraint on the rates** (the chain grain's
honesty point, inherited) and **no stochasticity constraint on
absorption** — both are theorems of the closure, never hypotheses. -/
structure MaRows.WF [Fintype S] [Fintype I] [Fintype A]
    (R : MaRows S I A) : Prop where
  rate_nonneg : ∀ p, 0 ≤ R.rateRow p
  branch_nonneg : ∀ p, 0 ≤ R.branchRow p
  branch_row_sum : ∀ i a, ∑ x, R.branchRow (i, a, x) = 1
  init_nonneg : ∀ x, 0 ≤ R.initRow x
  init_sum : ∑ x, R.initRow x = 1

/-- The total off-diagonal timed read of a row set: zero at the source
itself — where no key exists — and the stored row elsewhere.  The
row-level twin of `FinMA.offRate`, with the same definitional
shape. -/
def MaRows.rateAt (R : MaRows S I A) (s : S) (x : S ⊕ I) : ℚ :=
  if h : Sum.inl s = x then 0 else R.rateRow ⟨(s, x), h⟩

theorem MaRows.rateAt_nonneg {R : MaRows S I A} (hR : R.WF) (s : S)
    (x : S ⊕ I) : 0 ≤ R.rateAt s x := by
  unfold MaRows.rateAt
  split
  · exact le_rfl
  · exact hR.rate_nonneg _

/-- The immediate row read. -/
def MaRows.branchAt (R : MaRows S I A) (i : I) (a : A) (x : S ⊕ I) : ℚ :=
  R.branchRow (i, a, x)

/-- Compilation: store the off-diagonal timed entries — the key's type
is what makes compilation unable to read a self-rate or a timed row at
an instantaneous state — the immediate entries, and the initial
distribution. -/
noncomputable def compileMa (M : FinMA S I A) : MaRows S I A where
  rateRow := Finsupp.onFinset univ (fun p => M.rate p.1.1 p.1.2)
    (fun _ _ => mem_univ _)
  branchRow := Finsupp.onFinset univ (fun p => M.branch p.1 p.2.1 p.2.2)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ M.init (fun _ _ => mem_univ _)

@[simp] theorem compileMa_rateRow (M : FinMA S I A)
    (p : {p : S × (S ⊕ I) // Sum.inl p.1 ≠ p.2}) :
    (compileMa M).rateRow p = M.rate p.1.1 p.1.2 := rfl

@[simp] theorem compileMa_branchRow (M : FinMA S I A)
    (p : I × A × (S ⊕ I)) :
    (compileMa M).branchRow p = M.branch p.1 p.2.1 p.2.2 := rfl

@[simp] theorem compileMa_initRow (M : FinMA S I A) (x : S ⊕ I) :
    (compileMa M).initRow x = M.init x := rfl

theorem compileMa_wf (M : FinMA S I A) : (compileMa M).WF where
  rate_nonneg p := M.rate_nonneg p.1.1 p.1.2 p.2
  branch_nonneg p := M.branch_nonneg p.1 p.2.1 p.2.2
  branch_row_sum i a := M.branch_row_sum i a
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

/-- The compiled timed read is the classical one — both sides are the
same dite on the same data. -/
theorem compileMa_rateAt (M : FinMA S I A) :
    (compileMa M).rateAt = M.offRate := rfl

/-- The compiled immediate read is the classical one. -/
theorem compileMa_branchAt (M : FinMA S I A) :
    (compileMa M).branchAt = M.branch := rfl

/-- **Compilation is self-rate-blind, structurally**: two automata
agreeing on off-diagonal rates, branches, and initial masses compile
to *equal* rows — the key type cannot express a self-rate read. -/
theorem compileMa_diag_blind (M M' : FinMA S I A)
    (hoff : ∀ s x, Sum.inl s ≠ x → M.rate s x = M'.rate s x)
    (hbr : M.branch = M'.branch) (hinit : M.init = M'.init) :
    compileMa M = compileMa M' := by
  unfold compileMa
  congr 1
  · exact Finsupp.ext fun p => hoff p.1.1 p.1.2 p.2
  · exact Finsupp.ext fun p =>
      congrFun (congrFun (congrFun hbr p.1) p.2.1) p.2.2
  · exact Finsupp.ext fun x => congrFun hinit x

/-! ## The row-level scheduler closure -/

/-- The row-level mixed immediate kernel: the scheduler rows mix the
compiled immediate rows — the same formula as the classical mixing,
read through the row grains, which is what makes the triangle
definitional. -/
def imStepRows (R : MaRows S I A) (σr : PolicyRows I A) (i : I)
    (x : S ⊕ I) : ℚ :=
  ∑ a, σr.rows (i, a) * R.branchAt i a x

omit [DecidableEq S] [DecidableEq I] in
theorem imStepRows_nonneg {R : MaRows S I A} {σr : PolicyRows I A}
    (hR : R.WF) (hσ : σr.WF) (i : I) (x : S ⊕ I) :
    0 ≤ imStepRows R σr i x :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (hσ.nonneg (i, a)) (hR.branch_nonneg (i, a, x))

omit [DecidableEq S] [DecidableEq I] in
theorem imStepRows_row_sum {R : MaRows S I A} {σr : PolicyRows I A}
    (hR : R.WF) (hσ : σr.WF) (i : I) :
    ∑ x, imStepRows R σr i x = 1 :=
  mix_row_sum (fun a => σr.rows (i, a)) (fun a x => R.branchAt i a x)
    (hσ.row_sum i) (fun a => hR.branch_row_sum i a)

/-- **The scheduler closure at the row level**: close the compiled
automaton rows through the scheduler rows to chain-grain rate rows,
at the given absorption fuel; the initial rows push through the same
absorption.  This is the composite the compiled grain means by "the
closure bridge delivers the closed object as an ordinary
continuous-time chain": assembled from the stored rows, not stored
itself. -/
noncomputable def closeMaRows (R : MaRows S I A) (σr : PolicyRows I A)
    (n : ℕ) : CtmcRows S where
  rateRow := Finsupp.onFinset univ
    (fun p => ∑ x, R.rateAt p.1.1 x
      * absorbIter (imStepRows R σr) n x p.1.2)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ
    (fun s => ∑ x, R.initRow x * absorbIter (imStepRows R σr) n x s)
    (fun _ _ => mem_univ _)

@[simp] theorem closeMaRows_rateRow (R : MaRows S I A)
    (σr : PolicyRows I A) (n : ℕ) (p : {p : S × S // p.1 ≠ p.2}) :
    (closeMaRows R σr n).rateRow p
      = ∑ x, R.rateAt p.1.1 x
          * absorbIter (imStepRows R σr) n x p.1.2 := rfl

@[simp] theorem closeMaRows_initRow (R : MaRows S I A)
    (σr : PolicyRows I A) (n : ℕ) (s : S) :
    (closeMaRows R σr n).initRow s
      = ∑ x, R.initRow x * absorbIter (imStepRows R σr) n x s := rfl

/-- The scheduler closure preserves well-formedness — and *creates*
the distribution facts: the closed initial rows are a distribution
although neither the rate rows nor the absorption carried such a
constraint.  The derived-stochasticity theorem at the row level, one
storey above the jump closure's. -/
theorem closeMaRows_wf {R : MaRows S I A} {σr : PolicyRows I A}
    (hR : R.WF) (hσ : σr.WF) (r : I → ℕ)
    (hr : ZenoFree (imStepRows R σr) r) :
    (closeMaRows R σr (absFuel r)).WF where
  rate_nonneg p := Finset.sum_nonneg fun x _ =>
    mul_nonneg (MaRows.rateAt_nonneg hR p.1.1 x)
      (absorbIter_nonneg _ (imStepRows_nonneg hR hσ) _ x p.1.2)
  init_nonneg s := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hR.init_nonneg x)
      (absorbIter_nonneg _ (imStepRows_nonneg hR hσ) _ x s)
  init_sum := by
    simp only [closeMaRows_initRow]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hterm : ∀ x, R.initRow x
          * (∑ m, absorbIter (imStepRows R σr) (absFuel r) x m)
        = R.initRow x * 1 := by
      intro x
      cases x with
      | inl m' => rw [absorbIter_inl_mass]
      | inr i =>
        rw [absorbIter_mass _ r hr (imStepRows_row_sum hR hσ) _ i
          (lt_absFuel r i)]
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    simp_rw [mul_one]
    exact hR.init_sum

/-! ## The rate-closure triangle and the square -/

/-- **The rate-closure triangle**: scheduler-closing the compiled rows
at the working fuel is the compilation of the classically closed
chain.  Definitional — both routes read the same rows through the same
guarded reads, the same mixing, and the same absorbing computation at
the same fuel — and the square's one genuinely automaton-shaped
obligation: well-formedness alone can see neither the scheduler nor
the rates (any scheduler's closure of any rate rows is *some*
chain-grain row set); this triangle is what pins the closure to the
declared scheduler and the declared rates. -/
theorem compile_closeMa_comm (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) :
    closeMaRows (compileMa M) (compilePolicy σ) (absFuel r)
      = compileCtmc (M.close σ r hr) := rfl

/-- **Adequacy of the Markov-automaton compilation, fixed-scheduler
face.**

In the double category `Crd (Traj S k)` of per-element credal
constraints over jump-horizon-`k` trajectories: the loose-arrow
diagram denoted by the *jump closure of the scheduler closure* of the
compiled automaton and scheduler rows is isomorphic, by an invertible
globular cell, to the singleton-credal inclusion of the closed chain's
jump-chain path law.  Compile-close-close-denote agrees with
interpret-then-include, at the time-abstract stratum.

The proof is three-storey engine reuse: by `compile_closeMa_comm` the
scheduler closure's rows *are* the closed chain's compiled rows, and
`ctmc_jump_adequacy` — itself the chain square at the jump chain —
finishes.  No new induction. -/
theorem ma_adequacy (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ)
    (hr : ZenoFree (M.imStep σ) r) (k : ℕ) {a : Crd (Traj S k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows (compileMa M) (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (singletonC (M.pathLaw σ r hr k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  ctmc_jump_adequacy (M.close σ r hr) k

/-! ## The connector, transported twice

The mechanized probability library has no Markov-automaton machinery
(nor continuous-time Markov machinery), so the community tie of this
face is the chain connector transported through both closures: the
closed chain's jump chain *is* a discrete-time chain, and its law is
the standard iterated monadic construction.  Stated as such — the
scheduler-resolution content of this square lives in the closure
receipts above, not in the connector. -/

/-- The closed jump-chain trajectory law by the standard monadic
construction. -/
noncomputable def FinMA.trajPMF (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ) :
    PMF (Traj S k) :=
  (M.close σ r hr).jumpTrajPMF k

/-- The exact-rational fixed-scheduler law and the monadic
construction agree under the canonical coercion — the chain connector
at the closed instance. -/
theorem FinMA.trajPMF_eq (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ)
    (ω : Traj S k) :
    M.trajPMF σ r hr k ω = q2e ((M.pathLaw σ r hr k).wt ω) :=
  FinCTMC.jumpTrajPMF_eq (M.close σ r hr) k ω

end Adequacy
end SuFunctor
