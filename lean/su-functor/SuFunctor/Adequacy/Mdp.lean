import SuFunctor.Adequacy.Dtmc

/-! # Adequacy: Markov decision processes, fixed-policy face

The second adequacy square, and the first to *reuse an engine
wholesale*.  A finite Markov decision process is presented classically
— finite state and action spaces, per-action row-stochastic kernels,
an initial distribution (Puterman, *Markov Decision Processes*,
Ch. 2) — together with a fixed **memoryless randomized policy**: a
per-state distribution over actions, the stationary randomized Markov
class of Puterman §5.5, and exactly the grain of the toolkit's
scheduler-declaration rows (a deterministic policy is the one-row,
probability-one special case).

The compiled presentation honors the shipped factoring: the decision
former's outcome rows are *action-keyed* — `(src, action, dst) ↦
probability` — and the policy is a **separate mechanism composed in**,
never a family of the decision former itself.  The closed loop is a
composite: a row-level compile (`closeRows`) mixes the action-keyed
rows through the policy rows and produces ordinary chain rows, and the
composite denotes exactly as a chain does.

**The square** (`mdp_adequacy`): compile both mechanisms, close the
loop at the row level, denote — and this agrees, by an invertible
globular cell of `Crd (Traj S k)`, with interpreting classically
(Puterman's fixed-policy trajectory law, the law of the closed-loop
chain with kernel $P_\pi(s,s') = \sum_a \pi(a \mid s)\,p(s' \mid
s,a)$) and including through `singletonC`.  The proof is the DTMC
square *instantiated at the closed-loop chain*: the only new identity
is the compile-commutes triangle `compile_close_comm` — closing the
loop before or after compilation is the same row set — which holds
definitionally, and the only new computation is the row-level mixing
exchange (`closedLoop`'s well-formedness).  No new induction: every
stochasticity fact was already spent, once, in the chain engine.

Deliberately separate strata, named: the **demonic / open-policy
face** (the bound uniform over all policies), whose bottom edge is a
*set* of laws — the credal, genuinely imprecise reading — belongs to
the envelope stratum and is not this square; **time-dependent
policies** (finite-horizon dynamic-programming output) close to a
time-inhomogeneous chain, outside the stationary chain grain mirrored
here; **Markov automata** under a declared scheduler share this
module's mixing machinery but carry exponential holding times, so
their square is continuous-time material.  The infinite-horizon
stratum is separate exactly as for chains. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-! ## The classical objects: MDP and policy -/

/-- A finite Markov decision process, as the literature presents it:
finite state and action spaces, one row-stochastic kernel per action,
an initial distribution (Puterman, Ch. 2; the per-(state, action) row
sums are the literature's own well-formedness fields).  Entries are
rational — the exact-arithmetic class of the compiled rows. -/
structure FinMDP (S A : Type) [Fintype S] [Fintype A] where
  /-- Transition probability to the third argument, from the first
  state under the second action. -/
  step : S → A → S → ℚ
  /-- Initial-distribution mass at a state. -/
  init : S → ℚ
  step_nonneg : ∀ s a s', 0 ≤ step s a s'
  step_row_sum : ∀ s a, ∑ s', step s a s' = 1
  init_nonneg : ∀ s, 0 ≤ init s
  init_sum : ∑ s, init s = 1

/-- A memoryless randomized policy: at each state, a distribution over
actions — Puterman's stationary randomized Markov class, and the grain
of the toolkit's scheduler-declaration rows.  A deterministic policy
is the one-row, probability-one special case (`Policy.det`). -/
structure Policy (S A : Type) [Fintype A] where
  /-- Probability of choosing the action (second argument) at the
  state (first argument). -/
  choice : S → A → ℚ
  nonneg : ∀ s a, 0 ≤ choice s a
  row_sum : ∀ s, ∑ a, choice s a = 1

/-- A deterministic policy in the scheduler-row grain: one row,
probability one. -/
def Policy.det (d : S → A) : Policy S A where
  choice s a := if a = d s then 1 else 0
  nonneg _ _ := by split <;> norm_num
  row_sum s := by
    rw [Finset.sum_ite_eq' univ (d s) (fun _ => (1 : ℚ))]
    simp

/-! ## The closed loop, classically -/

/-- The closed-loop chain of an MDP under a fixed policy: the kernel
mixes the per-action kernels through the policy —
$P_\pi(s, s') = \sum_a \pi(a \mid s)\, p(s' \mid s, a)$ — and the
initial distribution passes through.  This is the object Puterman's
fixed-policy semantics assigns to the pair: under a stationary
randomized policy, the decision process *is* a Markov chain. -/
def FinMDP.closedLoop (M : FinMDP S A) (π : Policy S A) : FinDTMC S where
  step s s' := ∑ a, π.choice s a * M.step s a s'
  init := M.init
  step_nonneg s s' := Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (M.step_nonneg s a s')
  step_row_sum s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinMDP.step_row_sum, mul_one]
    exact π.row_sum s
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

@[simp] theorem FinMDP.closedLoop_step (M : FinMDP S A) (π : Policy S A)
    (s s' : S) :
    (M.closedLoop π).step s s' = ∑ a, π.choice s a * M.step s a s' := rfl

@[simp] theorem FinMDP.closedLoop_init (M : FinMDP S A) (π : Policy S A)
    (s : S) : (M.closedLoop π).init s = M.init s := rfl

/-- Under a deterministic policy the closed-loop kernel reads the
chosen action's row directly. -/
theorem FinMDP.closedLoop_det (M : FinMDP S A) (d : S → A) (s s' : S) :
    (M.closedLoop (Policy.det d)).step s s' = M.step s (d s) s' := by
  rw [FinMDP.closedLoop_step]
  simp only [Policy.det, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' univ (d s) (fun a => M.step s a s')]
  simp

/-- **Puterman's fixed-policy trajectory law**: the horizon-`k` law of
the MDP under the policy is the closed-loop chain's path law.  At this
finite, exact-rational grain the fixed-policy reduction is
definitional once the mixed kernel is named; the product formula is
`FinMDP.pathLaw_wt`. -/
noncomputable def FinMDP.pathLaw (M : FinMDP S A) (π : Policy S A)
    (k : ℕ) : SubPMF (Traj S k) :=
  (M.closedLoop π).pathLaw k

/-- The explicit product form of the fixed-policy law: initial mass,
then one policy-mixed kernel entry per transition. -/
theorem FinMDP.pathLaw_wt (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (ω : Traj S k) :
    (M.pathLaw π k).wt ω =
      M.init (ω 0) * ∏ i : Fin k,
        ∑ a, π.choice (ω i.castSucc) a *
          M.step (ω i.castSucc) a (ω i.succ) := rfl

/-- A fixed-policy process spends its whole mass: the target stratum's
partiality allowance is available but unexercised — inherited from the
chain engine, one line. -/
theorem FinMDP.pathLaw_mass (M : FinMDP S A) (π : Policy S A) (k : ℕ) :
    (M.pathLaw π k).mass = 1 :=
  FinDTMC.pathLaw_mass (M.closedLoop π) k

/-! ## The compiled rows: action-keyed outcomes, policy rows, closure -/

/-- The compiled presentation of the decision former: outcome rows
keyed `(src, action, dst)` — every row action-keyed, the discipline
that separates this former from the chain former sharing its rows —
plus initial-distribution rows.  Sparse: an absent row and a zero
entry are the same datum. -/
structure MdpRows (S A : Type) where
  /-- Action-keyed outcome rows: `(src, action, dst) ↦` stored
  probability. -/
  outcome : S × A × S →₀ ℚ
  /-- Initial-distribution rows: `state ↦` stored mass. -/
  initRow : S →₀ ℚ

/-- Well-formedness of action-keyed rows: nonnegative entries, each
(source, action) pair's rows summing to one, initial rows summing to
one — the aggregation-seam obligations of the decision former's
grain. -/
structure MdpRows.WF [Fintype S] [Fintype A] (R : MdpRows S A) : Prop where
  outcome_nonneg : ∀ p, 0 ≤ R.outcome p
  row_sum : ∀ s a, ∑ s', R.outcome (s, a, s') = 1
  init_nonneg : ∀ s, 0 ≤ R.initRow s
  init_sum : ∑ s, R.initRow s = 1

/-- The compiled presentation of the policy mechanism: scheduler-grain
rows `(state, action) ↦` probability, memoryless randomized. -/
structure PolicyRows (S A : Type) where
  /-- Policy rows: `(state, action) ↦` stored choice probability. -/
  rows : S × A →₀ ℚ

/-- Well-formedness of policy rows: nonnegative, one distribution per
state. -/
structure PolicyRows.WF [Fintype A] (σ : PolicyRows S A) : Prop where
  nonneg : ∀ p, 0 ≤ σ.rows p
  row_sum : ∀ s, ∑ a, σ.rows (s, a) = 1

/-- Compilation of the decision former: store the entries; dropping
zero rows is definitionally invisible on the finitely supported
representation. -/
noncomputable def compileMdp (M : FinMDP S A) : MdpRows S A where
  outcome := Finsupp.onFinset univ (fun p => M.step p.1 p.2.1 p.2.2)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ M.init (fun _ _ => mem_univ _)

@[simp] theorem compileMdp_outcome (M : FinMDP S A) (p : S × A × S) :
    (compileMdp M).outcome p = M.step p.1 p.2.1 p.2.2 := rfl

@[simp] theorem compileMdp_initRow (M : FinMDP S A) (s : S) :
    (compileMdp M).initRow s = M.init s := rfl

theorem compileMdp_wf (M : FinMDP S A) : (compileMdp M).WF where
  outcome_nonneg p := M.step_nonneg p.1 p.2.1 p.2.2
  row_sum s a := M.step_row_sum s a
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

/-- Compilation of the policy mechanism: store the scheduler rows. -/
noncomputable def compilePolicy (π : Policy S A) : PolicyRows S A where
  rows := Finsupp.onFinset univ (fun p => π.choice p.1 p.2)
    (fun _ _ => mem_univ _)

@[simp] theorem compilePolicy_rows (π : Policy S A) (p : S × A) :
    (compilePolicy π).rows p = π.choice p.1 p.2 := rfl

theorem compilePolicy_wf (π : Policy S A) : (compilePolicy π).WF where
  nonneg p := π.nonneg p.1 p.2
  row_sum s := π.row_sum s

/-- **The closed-loop compile**: mix the action-keyed outcome rows
through the policy rows, at the row level, producing ordinary chain
rows; the initial rows pass through.  This is the composite the
shipped grain means by "the policy is a separate mechanism, composed
in": the closed loop is assembled from the two mechanisms' rows, not
stored as a monolith. -/
noncomputable def closeRows (R : MdpRows S A) (σ : PolicyRows S A) :
    DtmcRows S where
  outcome := Finsupp.onFinset univ
    (fun p => ∑ a, σ.rows (p.1, a) * R.outcome (p.1, a, p.2))
    (fun _ _ => mem_univ _)
  initRow := R.initRow

@[simp] theorem closeRows_outcome (R : MdpRows S A) (σ : PolicyRows S A)
    (p : S × S) :
    (closeRows R σ).outcome p =
      ∑ a, σ.rows (p.1, a) * R.outcome (p.1, a, p.2) := rfl

@[simp] theorem closeRows_initRow (R : MdpRows S A) (σ : PolicyRows S A)
    (s : S) : (closeRows R σ).initRow s = R.initRow s := rfl

/-- Closing the loop preserves well-formedness: the mixed rows are
row-stochastic — the row-level face of the mixing exchange. -/
theorem closeRows_wf {R : MdpRows S A} {σ : PolicyRows S A}
    (hR : R.WF) (hσ : σ.WF) : (closeRows R σ).WF where
  outcome_nonneg p := Finset.sum_nonneg fun a _ =>
    mul_nonneg (hσ.nonneg (p.1, a)) (hR.outcome_nonneg (p.1, a, p.2))
  row_sum s := by
    simp only [closeRows_outcome]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hR.row_sum, mul_one]
    exact hσ.row_sum s
  init_nonneg := hR.init_nonneg
  init_sum := hR.init_sum

/-! ## The square -/

/-- **The compile-commutes triangle**: closing the loop at the row
level, on compiled mechanisms, is the compilation of the classically
closed loop.  Definitional — the mixed entries are stored either way —
and the square's one genuinely new identity: well-formedness alone
cannot see the policy (any single action's rows are also
row-stochastic); this triangle is what pins the closure to the
declared policy. -/
theorem compile_close_comm (M : FinMDP S A) (π : Policy S A) :
    closeRows (compileMdp M) (compilePolicy π) =
      compile (M.closedLoop π) := rfl

/-- **Adequacy of the MDP compilation, fixed-policy face.**

In the double category `Crd (Traj S k)`: the loose-arrow diagram
denoted by the *composite* of the compiled decision former and the
compiled policy mechanism — action-keyed rows, closed through the
policy rows at the row level — is isomorphic, by an invertible
globular cell, to the singleton-credal inclusion of Puterman's
fixed-policy trajectory law.  Compile-close-denote agrees with
interpret-then-include.

The proof is the chain square instantiated at the closed-loop chain:
by `compile_close_comm` the composite's rows *are* the closed loop's
compiled rows, and `dtmc_adequacy` finishes.  No new induction — the
engine is reused wholesale. -/
theorem mdp_adequacy (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    {a : Crd (Traj S k)} :
    ∃ α : Cell
        (looseConj (atoms (closeRows (compileMdp M) (compilePolicy π)) k) :
          Loose a a)
        (singletonC (M.pathLaw π k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  dtmc_adequacy (M.closedLoop π) k

/-! ## The connector: policy selection in the monadic vocabulary

The chain connector (`FinDTMC.trajPMF_eq`) already ties the closed
loop's exact-rational law to the iterated-`PMF.bind` construction; it
transports to the MDP verbatim (`FinMDP.trajPMF_eq`).  What is
genuinely MDP-shaped is one more agreement: the closed-loop kernel is
itself a *monadic composition* — sample the action from the policy,
then the successor from that action's kernel — so "selecting through
the policy" is `PMF.bind` in the mechanized library's own
vocabulary. -/

section Connector

open scoped ENNReal

/-- The policy's per-state action distribution, in the mechanized
library's vocabulary. -/
noncomputable def Policy.actPMF (π : Policy S A) (s : S) : PMF A :=
  PMF.ofFintype (fun a => q2e (π.choice s a)) (by
    rw [← q2e_sum univ (π.choice s) (fun a _ => π.nonneg s a),
      π.row_sum s, q2e_one])

@[simp] theorem Policy.actPMF_apply (π : Policy S A) (s : S) (a : A) :
    π.actPMF s a = q2e (π.choice s a) := by
  simp [Policy.actPMF]

/-- One action-indexed kernel step, in the mechanized library's
vocabulary. -/
noncomputable def FinMDP.stepPMF (M : FinMDP S A) (s : S) (a : A) :
    PMF S :=
  PMF.ofFintype (fun s' => q2e (M.step s a s')) (by
    rw [← q2e_sum univ (M.step s a) (fun s' _ => M.step_nonneg s a s'),
      M.step_row_sum s a, q2e_one])

@[simp] theorem FinMDP.stepPMF_apply (M : FinMDP S A) (s : S) (a : A)
    (s' : S) : M.stepPMF s a s' = q2e (M.step s a s') := by
  simp [FinMDP.stepPMF]

/-- **The policy-selection connector**: the closed-loop kernel is the
monadic composition of the policy's action distribution with the
action-indexed kernel — mixing through the policy is `PMF.bind`. -/
theorem FinMDP.closedLoop_stepPMF (M : FinMDP S A) (π : Policy S A)
    (s : S) :
    (M.closedLoop π).stepPMF s =
      (π.actPMF s).bind (fun a => M.stepPMF s a) := by
  ext s'
  rw [PMF.bind_apply, tsum_fintype, FinDTMC.stepPMF_apply,
    FinMDP.closedLoop_step,
    q2e_sum univ _ (fun a _ =>
      mul_nonneg (π.nonneg s a) (M.step_nonneg s a s'))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [q2e_mul (π.nonneg s a), Policy.actPMF_apply, FinMDP.stepPMF_apply]

/-- The horizon-`k` trajectory law of the MDP under the policy, by the
standard monadic construction — the closed loop's. -/
noncomputable def FinMDP.trajPMF (M : FinMDP S A) (π : Policy S A)
    (k : ℕ) : PMF (Traj S k) :=
  (M.closedLoop π).trajPMF k

/-- **The connector, transported**: the exact-rational fixed-policy
law and the monadic construction agree under the canonical coercion —
the chain connector at the closed-loop instance. -/
theorem FinMDP.trajPMF_eq (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (ω : Traj S k) :
    M.trajPMF π k ω = q2e ((M.pathLaw π k).wt ω) :=
  FinDTMC.trajPMF_eq (M.closedLoop π) k ω

end Connector

end Adequacy
end SuFunctor
