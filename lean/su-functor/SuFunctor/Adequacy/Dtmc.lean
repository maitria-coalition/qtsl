import SuFunctor.Adequacy.Inclusions
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Adequacy: finite discrete-time Markov chains

The first adequacy square.  A finite discrete-time Markov chain is
presented classically — finite state space, row-stochastic matrix,
initial distribution (Kemeny–Snell, *Finite Markov Chains*, Ch. II) —
and compiled to the sparse row grain of the DTMC system profile:
outcome rows keyed (source, destination) with exact-rational
probabilities, and initial-distribution rows, an absent row and a zero
entry being the same datum.  The compiled rows denote in the credal
stratum as a *loose-arrow diagram* of `Crd (Traj S k)`: the formal
conjunction of one initial-distribution constraint and one
kernel-consistency constraint per time step, each a per-element
constraint on subprobability mass functions over horizon-`k`
trajectories.  The classical semantics — the finite-dimensional
distribution of the chain at horizon `k`, the generator of the
cylinder-set path measure in the sense of Baier–Katoen (*Principles of
Model Checking*, §10.1) — includes into the same stratum through the
singleton-credal inclusion `singletonC`.

**The square** (`dtmc_adequacy`): compile-then-denote equals
interpret-then-include — the two loose arrows are isomorphic in the
double category (an invertible globular cell).  Its pointwise engine
(`satAtoms_iff`) is the finite-cylinder Kolmogorov-extension argument:
the local constraints pin exactly one subprobability mass function,
the product-form path law.  In particular a fully probabilistic system
spends its entire mass (`pathLaw_mass`): partiality is native to the
target stratum but never exercised by a stochastic chain.

The infinite-horizon path measure (the Ionescu–Tulcea extension) is
deliberately a separate stratum: the horizon-`k` laws proved here are
the finite-dimensional distributions that determine it, and the
σ-additive extension lives with the measure-theoretic machinery.
Within the finite stratum, `trajPMF_eq` ties the exact-rational law to
the standard monadic construction of the chain law (iterated
`PMF.bind`), so the left edge agrees with the mechanized probability
library's own vocabulary rather than being a private restatement. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## The classical object and the compiled rows -/

/-- A finite discrete-time Markov chain, as the literature presents it:
a finite state space, a row-stochastic transition matrix, an initial
distribution.  Entries are rational — the exact-arithmetic class of the
compiled rows. -/
structure FinDTMC (S : Type) [Fintype S] where
  /-- Transition probability from the first state to the second. -/
  step : S → S → ℚ
  /-- Initial-distribution mass at a state. -/
  init : S → ℚ
  step_nonneg : ∀ s s', 0 ≤ step s s'
  step_row_sum : ∀ s, ∑ s', step s s' = 1
  init_nonneg : ∀ s, 0 ≤ init s
  init_sum : ∑ s, init s = 1

/-- The compiled presentation: the row grain of the DTMC system
profile.  Outcome rows are keyed (source, destination); initial rows
are keyed by state.  Rows are stored sparsely — a zero entry and an
absent row are the same datum, which is exactly the semantics of a
finitely supported function. -/
structure DtmcRows (S : Type) where
  /-- Outcome rows: `(src, dst) ↦` stored probability. -/
  outcome : S × S →₀ ℚ
  /-- Initial-distribution rows: `state ↦` stored mass. -/
  initRow : S →₀ ℚ

/-- Well-formedness of a row set: nonnegative entries, each source's
outcome rows summing to one, initial rows summing to one.  These are
the aggregation-seam obligations of the row grain — content facts a
consumer re-derives from the whole row set rather than reading off any
single row — and they are the hypotheses under which the rows denote a
chain. -/
structure DtmcRows.WF [Fintype S] (R : DtmcRows S) : Prop where
  outcome_nonneg : ∀ p, 0 ≤ R.outcome p
  row_sum : ∀ s, ∑ s', R.outcome (s, s') = 1
  init_nonneg : ∀ s, 0 ≤ R.initRow s
  init_sum : ∑ s, R.initRow s = 1

/-- Compilation: store the entries.  On the finitely supported
representation, dropping the zero rows is definitionally invisible —
an absent row reads back as zero — so compilation is lossless by the
representation's own semantics. -/
noncomputable def compile (M : FinDTMC S) : DtmcRows S where
  outcome := Finsupp.onFinset univ (fun p => M.step p.1 p.2)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ M.init (fun _ _ => mem_univ _)

@[simp] theorem compile_outcome (M : FinDTMC S) (p : S × S) :
    (compile M).outcome p = M.step p.1 p.2 := rfl

@[simp] theorem compile_initRow (M : FinDTMC S) (s : S) :
    (compile M).initRow s = M.init s := rfl

theorem compile_wf (M : FinDTMC S) : (compile M).WF where
  outcome_nonneg p := M.step_nonneg p.1 p.2
  row_sum s := M.step_row_sum s
  init_nonneg := M.init_nonneg
  init_sum := M.init_sum

/-! ## Trajectories and chain weights -/

/-- Horizon-`k` trajectories: `k` transitions, `k + 1` observed
states — the finite-cylinder record space of the compiled system. -/
abbrev Traj (S : Type) (k : ℕ) := Fin (k + 1) → S

/-- The chain weight of a trajectory against arbitrary entry
functions: initial mass at the first state times the product of
traversed kernel entries.  Both the classical law and the compiled
rows' law are instances. -/
def chainWt (ini : S → ℚ) (ker : S → S → ℚ) {k : ℕ} (ω : Traj S k) : ℚ :=
  ini (ω 0) * ∏ i : Fin k, ker (ω i.castSucc) (ω i.succ)

theorem chainWt_nonneg {ini : S → ℚ} {ker : S → S → ℚ}
    (hini : ∀ s, 0 ≤ ini s) (hker : ∀ s s', 0 ≤ ker s s') {k : ℕ}
    (ω : Traj S k) : 0 ≤ chainWt ini ker ω :=
  mul_nonneg (hini _) (Finset.prod_nonneg fun _ _ => hker _ _)

/-- Prepending a state multiplies in one initial mass and re-roots the
chain at the prepended state. -/
theorem chainWt_cons (ini : S → ℚ) (ker : S → S → ℚ) {k : ℕ} (s : S)
    (ρ : Traj S k) :
    chainWt ini ker (Fin.cons s ρ : Traj S (k + 1)) =
      ini s * chainWt (ker s) ker ρ := by
  unfold chainWt
  rw [Fin.prod_univ_succ]
  have e2 : ∀ i : Fin k,
      ker ((Fin.cons s ρ : Traj S (k + 1)) i.succ.castSucc)
          ((Fin.cons s ρ : Traj S (k + 1)) i.succ.succ) =
        ker (ρ i.castSucc) (ρ i.succ) := by
    intro i
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
  rw [Finset.prod_congr rfl fun i _ => e2 i]
  simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ]

/-- Appending a state multiplies in one kernel entry at the old last
state. -/
theorem chainWt_snoc (ini : S → ℚ) (ker : S → S → ℚ) {k : ℕ}
    (ρ : Traj S k) (s : S) :
    chainWt ini ker (Fin.snoc ρ s : Traj S (k + 1)) =
      chainWt ini ker ρ * ker (ρ (Fin.last k)) s := by
  unfold chainWt
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc ρ s : Traj S (k + 1)) 0 = ρ 0 := by
    rw [show (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc by
      rw [Fin.castSucc_zero], Fin.snoc_castSucc]
  have e2 : ∀ i : Fin k,
      ker ((Fin.snoc ρ s : Traj S (k + 1)) i.castSucc.castSucc)
          ((Fin.snoc ρ s : Traj S (k + 1)) i.castSucc.succ) =
        ker (ρ i.castSucc) (ρ i.succ) := by
    intro i
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  have elast :
      ker ((Fin.snoc ρ s : Traj S (k + 1)) (Fin.last k).castSucc)
          ((Fin.snoc ρ s : Traj S (k + 1)) (Fin.last k).succ) =
        ker (ρ (Fin.last k)) s := by
    rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.prod_congr rfl fun i _ => e2 i, elast, h0]
  ring

/-- Splitting a trajectory as head-state and tail. -/
private def consEquiv (S : Type) (k : ℕ) : S × Traj S k ≃ Traj S (k + 1) where
  toFun p := Fin.cons p.1 p.2
  invFun ω := (ω 0, fun i => ω i.succ)
  left_inv p := by
    obtain ⟨s, ρ⟩ := p
    simp
  right_inv ω := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Total chain mass: summing the chain weight over all horizon-`k`
trajectories returns the total initial mass, for any row-stochastic
kernel.  The one induction that carries every stochasticity fact
below. -/
theorem sum_chainWt (ker : S → S → ℚ)
    (hker : ∀ s, ∑ s', ker s s' = 1) :
    ∀ (k : ℕ) (ini : S → ℚ),
      ∑ ω : Traj S k, chainWt ini ker ω = ∑ s, ini s := by
  intro k
  induction k with
  | zero =>
    intro ini
    rw [← Fintype.sum_equiv ((Equiv.funUnique (Fin 1) S).symm)
      (fun s => chainWt ini ker ((Equiv.funUnique (Fin 1) S).symm s))
      (fun ω => chainWt ini ker ω) (fun _ => rfl)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [chainWt]
  | succ k ih =>
    intro ini
    rw [← Fintype.sum_equiv (consEquiv S k)
      (fun p => chainWt ini ker (consEquiv S k p))
      (fun ω => chainWt ini ker ω) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    calc ∑ s, ∑ ρ : Traj S k, chainWt ini ker (consEquiv S k (s, ρ))
        = ∑ s, ini s * ∑ ρ : Traj S k, chainWt (ker s) ker ρ := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ =>
            chainWt_cons ini ker s ρ
      _ = ∑ s, ini s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [ih (ker s), hker s, mul_one]

/-! ## The two path laws -/

/-- The path law of a well-formed row set: the subprobability mass
function on horizon-`k` trajectories whose weight is the chain weight
of the stored rows. -/
noncomputable def rowsLaw (R : DtmcRows S) (hR : R.WF) (k : ℕ) :
    SubPMF (Traj S k) where
  wt := Finsupp.onFinset univ
    (fun ω => chainWt R.initRow (fun a b => R.outcome (a, b)) ω)
    (fun _ _ => mem_univ _)
  nonneg ω :=
    chainWt_nonneg hR.init_nonneg (fun a b => hR.outcome_nonneg (a, b)) ω
  mass_le_one := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun ω _ _ =>
        chainWt_nonneg hR.init_nonneg
          (fun a b => hR.outcome_nonneg (a, b)) ω) ?_
    show (∑ ω : Traj S k,
      chainWt R.initRow (fun a b => R.outcome (a, b)) ω) ≤ 1
    rw [sum_chainWt _ hR.row_sum k _, hR.init_sum]

@[simp] theorem rowsLaw_wt (R : DtmcRows S) (hR : R.WF) (k : ℕ)
    (ω : Traj S k) :
    (rowsLaw R hR k).wt ω =
      chainWt R.initRow (fun a b => R.outcome (a, b)) ω := rfl

/-- The classical path law of the chain: the finite-dimensional
distribution at horizon `k`, by the product formula of the
literature. -/
noncomputable def FinDTMC.pathLaw (M : FinDTMC S) (k : ℕ) : SubPMF (Traj S k) where
  wt := Finsupp.onFinset univ (fun ω => chainWt M.init M.step ω)
    (fun _ _ => mem_univ _)
  nonneg ω := chainWt_nonneg M.init_nonneg M.step_nonneg ω
  mass_le_one := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun ω _ _ =>
        chainWt_nonneg M.init_nonneg M.step_nonneg ω) ?_
    show (∑ ω : Traj S k, chainWt M.init M.step ω) ≤ 1
    rw [sum_chainWt _ M.step_row_sum k _, M.init_sum]

@[simp] theorem FinDTMC.pathLaw_wt (M : FinDTMC S) (k : ℕ)
    (ω : Traj S k) :
    (M.pathLaw k).wt ω = chainWt M.init M.step ω := rfl

/-- A stochastic chain spends its whole mass: the target stratum's
partiality allowance is available but unexercised. -/
theorem FinDTMC.pathLaw_mass (M : FinDTMC S) (k : ℕ) :
    (M.pathLaw k).mass = 1 := by
  classical
  show (M.pathLaw k).prob Set.univ = 1
  rw [SubPMF.prob_eq_sum_univ]
  have h : ∀ ω : Traj S k,
      (Set.univ : Set (Traj S k)).indicator (M.pathLaw k).wt ω =
        chainWt M.init M.step ω := by
    intro ω
    rw [Set.indicator_univ, FinDTMC.pathLaw_wt]
  rw [Finset.sum_congr rfl fun ω _ => h ω,
    sum_chainWt M.step M.step_row_sum k M.init, M.init_sum]

/-! ## Prefix cylinders and the denotation constraints -/

/-- The prefix cylinder: trajectories agreeing with `ω` at every time
`≤ t`.  For `t ≥ k` this is the singleton `{ω}`; for `t < k` these
are the finite-cylinder generators of the classical path
semantics. -/
def cyl {k : ℕ} (t : ℕ) (ω : Traj S k) : Set (Traj S k) :=
  {ω' | ∀ i : Fin (k + 1), (i : ℕ) ≤ t → ω' i = ω i}

theorem cyl_of_le {k : ℕ} {t : ℕ} (hk : k ≤ t) (ω : Traj S k) :
    cyl t ω = {ω} := by
  ext ω'
  constructor
  · intro h
    exact funext fun i => h i (le_trans (Nat.le_of_lt_succ i.isLt) hk)
  · rintro rfl
    exact fun i _ => rfl

/-- Membership in the refined cylinder after pinning time `t + 1`:
agree up to `t`, and read the pinned value at `t + 1`. -/
theorem mem_cyl_update_iff {k : ℕ} {t : ℕ} (ht : t < k)
    (ω ω' : Traj S k) (s : S) :
    ω' ∈ cyl (t + 1)
        (Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s) ↔
      ω' ∈ cyl t ω ∧ ω' ⟨t + 1, by omega⟩ = s := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have hupd := h i (le_trans hi (Nat.le_succ t))
      rwa [Function.update_apply, if_neg (fun hc => by
        have hval : (i : ℕ) = t + 1 := by
          rw [hc]
        omega)] at hupd
    · have hupd := h ⟨t + 1, by omega⟩ le_rfl
      rwa [Function.update_apply, if_pos rfl] at hupd
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge (i : ℕ) (t + 1) with hlt | hge
    · rw [Function.update_apply, if_neg (fun hc => by
        have hval : (i : ℕ) = t + 1 := by
          rw [hc]
        omega)]
      exact h1 i (by omega)
    · have hie : i = ⟨t + 1, by omega⟩ := by
        apply Fin.ext
        show (i : ℕ) = t + 1
        omega
      rw [hie, Function.update_apply, if_pos rfl]
      exact h2

/-- Refining a cylinder by one time step partitions it: the
probability at prefix length `t` is the sum over the pinned value at
`t + 1`. -/
theorem prob_cyl_succ {k : ℕ} (μ : SubPMF (Traj S k)) {t : ℕ}
    (ht : t < k) (ω : Traj S k) :
    μ.prob (cyl t ω) =
      ∑ s, μ.prob (cyl (t + 1)
        (Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s)) := by
  classical
  simp_rw [SubPMF.prob_eq_sum_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  by_cases h : ω' ∈ cyl t ω
  · have hmem : ∀ s : S, ω' ∈ cyl (t + 1)
        (Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s) ↔
          ω' ⟨t + 1, by omega⟩ = s := by
      intro s
      rw [mem_cyl_update_iff ht]
      exact ⟨fun hp => hp.2, fun h2 => ⟨h, h2⟩⟩
    calc (cyl t ω).indicator μ.wt ω' = μ.wt ω' := by
          rw [Set.indicator_apply, if_pos h]
      _ = ∑ s, if ω' ⟨t + 1, by omega⟩ = s then μ.wt ω' else 0 := by
          rw [Finset.sum_ite_eq Finset.univ
            (ω' ⟨t + 1, by omega⟩) (fun _ => μ.wt ω')]
          rw [if_pos (mem_univ _)]
      _ = _ := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Set.indicator_apply]
          by_cases hs : ω' ⟨t + 1, by omega⟩ = s
          · rw [if_pos hs, if_pos ((hmem s).mpr hs)]
          · rw [if_neg hs, if_neg (fun hc => hs ((hmem s).mp hc))]
  · have hnone : ∀ s : S, ω' ∉ cyl (t + 1)
        (Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s) := by
      intro s hc
      exact h ((mem_cyl_update_iff ht ω ω' s).mp hc).1
    rw [Set.indicator_apply, if_neg h]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Set.indicator_apply, if_neg (hnone s)]

/-- The prefix weight: initial mass times the kernel entries of the
first `t` transitions — the value the classical semantics assigns to a
length-`t` prefix cylinder. -/
def prefixWt (ini : S → ℚ) (ker : S → S → ℚ) (t : ℕ) {k : ℕ}
    (ω : Traj S k) : ℚ :=
  ini (ω 0) *
    ∏ i ∈ univ.filter (fun i : Fin k => (i : ℕ) < t),
      ker (ω i.castSucc) (ω i.succ)

theorem prefixWt_zero (ini : S → ℚ) (ker : S → S → ℚ) {k : ℕ}
    (ω : Traj S k) : prefixWt ini ker 0 ω = ini (ω 0) := by
  unfold prefixWt
  rw [Finset.filter_false_of_mem (fun i _ => by omega),
    Finset.prod_empty, mul_one]

theorem prefixWt_of_le (ini : S → ℚ) (ker : S → S → ℚ) {k t : ℕ}
    (hk : k ≤ t) (ω : Traj S k) :
    prefixWt ini ker t ω = chainWt ini ker ω := by
  unfold prefixWt chainWt
  rw [Finset.filter_true_of_mem (fun i _ => lt_of_lt_of_le i.isLt hk)]

theorem filter_lt_succ_eq_insert {k t : ℕ} (ht : t < k) :
    univ.filter (fun i : Fin k => (i : ℕ) < t + 1) =
      insert (⟨t, ht⟩ : Fin k)
        (univ.filter (fun i : Fin k => (i : ℕ) < t)) := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  show (i : ℕ) < t + 1 ↔ (i : ℕ) = t ∨ (i : ℕ) < t
  omega

theorem prefixWt_succ (ini : S → ℚ) (ker : S → S → ℚ) {k t : ℕ}
    (ht : t < k) (ω : Traj S k) :
    prefixWt ini ker (t + 1) ω =
      prefixWt ini ker t ω *
        ker (ω (⟨t, ht⟩ : Fin k).castSucc)
          (ω (⟨t, ht⟩ : Fin k).succ) := by
  unfold prefixWt
  rw [filter_lt_succ_eq_insert ht, Finset.prod_insert (by
    simp only [mem_filter, mem_univ, true_and]
    omega)]
  ring

/-- Prefix weights strictly below the pinned position ignore the
update. -/
theorem prefixWt_update_high (ini : S → ℚ) (ker : S → S → ℚ)
    {k t t' : ℕ} (htt' : t < t') (ht' : t' < k + 1) (ω : Traj S k)
    (s : S) :
    prefixWt ini ker t
        (Function.update ω (⟨t', ht'⟩ : Fin (k + 1)) s) =
      prefixWt ini ker t ω := by
  unfold prefixWt
  have h0 : Function.update ω (⟨t', ht'⟩ : Fin (k + 1)) s 0 = ω 0 := by
    rw [Function.update_apply, if_neg (fun hc => by
      have hval : (0 : ℕ) = t' := by
        have := congrArg Fin.val hc
        simpa using this
      omega)]
  rw [h0]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hit : (i : ℕ) < t := by
    simpa using (Finset.mem_filter.mp hi).2
  have hcs : Function.update ω (⟨t', ht'⟩ : Fin (k + 1)) s i.castSucc
      = ω i.castSucc := by
    rw [Function.update_apply, if_neg (fun hc => by
      have hval : (i : ℕ) = t' := by
        have := congrArg Fin.val hc
        simpa using this
      omega)]
  have hsc : Function.update ω (⟨t', ht'⟩ : Fin (k + 1)) s i.succ
      = ω i.succ := by
    rw [Function.update_apply, if_neg (fun hc => by
      have hval : (i : ℕ) + 1 = t' := by
        have := congrArg Fin.val hc
        simpa using this
      omega)]
  rw [hcs, hsc]

/-- The one-step refinement of a prefix weight at a pinned value. -/
theorem prefixWt_update_succ (ini : S → ℚ) (ker : S → S → ℚ)
    {k t : ℕ} (ht : t < k) (ω : Traj S k) (s : S) :
    prefixWt ini ker (t + 1)
        (Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s) =
      prefixWt ini ker t ω *
        ker (ω (⟨t, by omega⟩ : Fin (k + 1))) s := by
  rw [prefixWt_succ ini ker ht,
    prefixWt_update_high ini ker (Nat.lt_succ_self t) (by omega) ω s]
  have h1 : Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s
      ((⟨t, ht⟩ : Fin k).castSucc) =
      ω (⟨t, by omega⟩ : Fin (k + 1)) := by
    rw [Function.update_apply, if_neg (fun hc => by
      have hval : (t : ℕ) = t + 1 := by
        have := congrArg Fin.val hc
        simpa using this
      omega)]
    exact congrArg ω (Fin.ext rfl)
  have h2 : Function.update ω (⟨t + 1, by omega⟩ : Fin (k + 1)) s
      ((⟨t, ht⟩ : Fin k).succ) = s := by
    rw [Function.update_apply, if_pos (by
      apply Fin.ext
      simp)]
  rw [h1, h2]

/-! ## The denotation of the rows: a loose-arrow diagram -/

/-- The initial-distribution constraint the compiled rows impose: the
time-`0` marginal reads the stored initial rows. -/
def initC (R : DtmcRows S) (k : ℕ) : SubPMF (Traj S k) → Prop :=
  fun μ => ∀ ω : Traj S k, μ.prob (cyl 0 ω) = R.initRow (ω 0)

/-- The step-`t` kernel-consistency constraint: refining a prefix
cylinder by its next observation multiplies its probability by the
stored outcome row. -/
def stepC (R : DtmcRows S) (k : ℕ) (t : Fin k) :
    SubPMF (Traj S k) → Prop :=
  fun μ => ∀ ω : Traj S k,
    μ.prob (cyl ((t : ℕ) + 1) ω) =
      μ.prob (cyl (t : ℕ) ω) * R.outcome (ω t.castSucc, ω t.succ)

/-- The compiled system's constraint atoms: one initial constraint,
then one step constraint per transition.  Their formal conjunction
(`looseConj`) is the system's denotation — a genuine loose-arrow
diagram of `Crd (Traj S k)` by `looseConj_cons`. -/
def atoms (R : DtmcRows S) (k : ℕ) : List (SubPMF (Traj S k) → Prop) :=
  initC R k :: (List.finRange k).map (stepC R k)

theorem satAtoms_unpack (R : DtmcRows S) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    looseConj (atoms R k) μ ↔
      initC R k μ ∧ ∀ t : Fin k, stepC R k t μ := by
  rw [looseConj_iff]
  unfold atoms
  constructor
  · intro h
    refine ⟨h _ List.mem_cons_self, fun t => ?_⟩
    exact h _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨t, List.mem_finRange t, rfl⟩))
  · rintro ⟨h0, hstep⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h0
    · rcases List.mem_map.mp hc with ⟨t, _, rfl⟩
      exact hstep t

/-! ## The pointwise engine: local constraints pin the product law -/

section Engine

variable {R : DtmcRows S} {k : ℕ}

private theorem rowsLaw_prob_cyl_of_le (hR : R.WF) {t : ℕ}
    (hk : k ≤ t) (ω : Traj S k) :
    (rowsLaw R hR k).prob (cyl t ω) =
      prefixWt R.initRow (fun a b => R.outcome (a, b)) t ω := by
  rw [cyl_of_le hk, SubPMF.prob_singleton, rowsLaw_wt,
    prefixWt_of_le _ _ hk]

/-- The closed form of the rows' law on prefix cylinders: downward
induction from the trajectory atoms, spending one row-sum per step —
the computational heart of the square. -/
theorem rowsLaw_prob_cyl (hR : R.WF) (t : ℕ) (ω : Traj S k) :
    (rowsLaw R hR k).prob (cyl t ω) =
      prefixWt R.initRow (fun a b => R.outcome (a, b)) t ω := by
  classical
  have aux : ∀ (d tt : ℕ), k ≤ tt + d → ∀ ω : Traj S k,
      (rowsLaw R hR k).prob (cyl tt ω) =
        prefixWt R.initRow (fun a b => R.outcome (a, b)) tt ω := by
    intro d
    induction d with
    | zero =>
      intro tt htt ω
      exact rowsLaw_prob_cyl_of_le hR (by omega) ω
    | succ d ih =>
      intro tt htt ω
      rcases Nat.lt_or_ge tt k with hlt | hge
      · rw [prob_cyl_succ _ hlt ω]
        have hstep : ∀ s : S,
            (rowsLaw R hR k).prob (cyl (tt + 1)
              (Function.update ω
                (⟨tt + 1, by omega⟩ : Fin (k + 1)) s)) =
            prefixWt R.initRow (fun a b => R.outcome (a, b)) tt ω *
              R.outcome (ω (⟨tt, by omega⟩ : Fin (k + 1)), s) := by
          intro s
          rw [ih (tt + 1) (by omega),
            prefixWt_update_succ _ _ hlt ω s]
        rw [Finset.sum_congr rfl fun s _ => hstep s, ← Finset.mul_sum]
        have hsum : (∑ s, R.outcome (ω (⟨tt, by omega⟩ : Fin (k + 1)), s))
            = 1 := hR.row_sum _
        rw [hsum, mul_one]
      · exact rowsLaw_prob_cyl_of_le hR hge ω
  exact aux k t (by omega) ω

/-- The rows' law satisfies every constraint atom. -/
theorem rowsLaw_satAtoms (hR : R.WF) :
    looseConj (atoms R k) (rowsLaw R hR k) := by
  rw [satAtoms_unpack]
  constructor
  · intro ω
    rw [rowsLaw_prob_cyl hR 0 ω, prefixWt_zero]
  · intro t ω
    have ht : (t : ℕ) < k := t.isLt
    rw [rowsLaw_prob_cyl hR ((t : ℕ) + 1) ω,
      rowsLaw_prob_cyl hR (t : ℕ) ω, prefixWt_succ _ _ ht]

/-- Any subprobability mass function satisfying every atom *is* the
rows' law: the constraints pin all prefix-cylinder probabilities by
induction on the prefix, hence all atomic weights at full depth. -/
theorem eq_rowsLaw_of_satAtoms (hR : R.WF)
    {μ : SubPMF (Traj S k)} (h : looseConj (atoms R k) μ) :
    μ = rowsLaw R hR k := by
  classical
  rw [satAtoms_unpack] at h
  obtain ⟨h0, hstep⟩ := h
  have key : ∀ t : ℕ, t ≤ k → ∀ ω : Traj S k,
      μ.prob (cyl t ω) =
        prefixWt R.initRow (fun a b => R.outcome (a, b)) t ω := by
    intro t
    induction t with
    | zero =>
      intro _ ω
      rw [h0 ω, prefixWt_zero]
    | succ t iht =>
      intro ht ω
      have htk : t < k := by omega
      have hs := hstep ⟨t, htk⟩ ω
      have hcast : ((⟨t, htk⟩ : Fin k) : ℕ) = t := rfl
      rw [hcast] at hs
      rw [hs, iht (by omega) ω, ← prefixWt_succ _ _ htk]
  have hwt : ∀ ω : Traj S k, μ.wt ω = (rowsLaw R hR k).wt ω := by
    intro ω
    have hk := key k le_rfl ω
    rw [cyl_of_le le_rfl, SubPMF.prob_singleton] at hk
    rw [hk, rowsLaw_wt, prefixWt_of_le _ _ le_rfl]
  exact SubPMF.ext' (Finsupp.ext hwt)

/-- **The pointwise adequacy equivalence**: a model satisfies the
compiled constraints exactly when it is the product-form path law —
the finite-cylinder Kolmogorov-extension argument, packaged. -/
theorem satAtoms_iff (hR : R.WF) (μ : SubPMF (Traj S k)) :
    looseConj (atoms R k) μ ↔ μ = rowsLaw R hR k :=
  ⟨eq_rowsLaw_of_satAtoms hR, fun h => h ▸ rowsLaw_satAtoms hR⟩

end Engine

/-! ## The square -/

/-- Compilation preserves the law: the sparse rows reconstruct the
classical product-form path law exactly.  Lossless by the
representation: an absent row reads back as the zero the classical
matrix stored. -/
theorem compile_rowsLaw (M : FinDTMC S) (k : ℕ) :
    rowsLaw (compile M) (compile_wf M) k = M.pathLaw k := rfl

/-- **Adequacy of the DTMC compilation** (the first adequacy square).

In the double category `Crd (Traj S k)` of per-element credal
constraints over horizon-`k` trajectories: the loose-arrow diagram
denoted by the *compiled* chain — the formal conjunction of its
initial-distribution constraint and its `k` kernel-consistency
constraints — is isomorphic, by an invertible globular cell, to the
singleton-credal inclusion of the chain's *classical* finite-horizon
path law.  Compile-then-denote agrees with interpret-then-include. -/
theorem dtmc_adequacy (M : FinDTMC S) (k : ℕ) {a : Crd (Traj S k)} :
    ∃ α : Cell (looseConj (atoms (compile M) k) : Loose a a)
        (singletonC (M.pathLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [singletonC_iff, satAtoms_iff (compile_wf M) μ, compile_rowsLaw]

/-! ## The connector: the left edge is the standard monadic law

The classical side of the square is stated above in exact rational
arithmetic (the product formula of the literature).  To pin it to the
mechanized probability library's own vocabulary, we rebuild the
horizon-`k` law as the standard monadic construction — the initial
distribution mapped to length-one trajectories, then `k` successive
`PMF.bind`s against the kernel — and prove the two agree under the
canonical coercion `ℚ → ℝ≥0∞`.  The infinite-horizon (Ionescu–Tulcea)
extension is the named next stratum; these finite laws are its
finite-dimensional distributions. -/

section Connector

open scoped ENNReal

/-- The canonical coercion of a rational weight into `ℝ≥0∞`. -/
noncomputable def q2e (q : ℚ) : ℝ≥0∞ := ENNReal.ofReal (q : ℝ)

theorem q2e_mul {p : ℚ} (hp : 0 ≤ p) (q : ℚ) :
    q2e (p * q) = q2e p * q2e q := by
  unfold q2e
  push_cast
  rw [ENNReal.ofReal_mul (by exact_mod_cast hp)]

theorem q2e_sum {ι : Type} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    q2e (∑ i ∈ s, f i) = ∑ i ∈ s, q2e (f i) := by
  unfold q2e
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => by exact_mod_cast hf i hi)]

@[simp] theorem q2e_one : q2e 1 = 1 := by
  simp [q2e]

variable (M : FinDTMC S)

/-- The initial distribution, in the mechanized library's
vocabulary. -/
noncomputable def FinDTMC.initPMF : PMF S :=
  PMF.ofFintype (fun s => q2e (M.init s)) (by
    rw [← q2e_sum univ M.init (fun s _ => M.init_nonneg s), M.init_sum,
      q2e_one])

/-- One kernel step, in the mechanized library's vocabulary. -/
noncomputable def FinDTMC.stepPMF (s : S) : PMF S :=
  PMF.ofFintype (fun s' => q2e (M.step s s')) (by
    rw [← q2e_sum univ (M.step s) (fun s' _ => M.step_nonneg s s'),
      M.step_row_sum s, q2e_one])

@[simp] theorem FinDTMC.initPMF_apply (s : S) :
    M.initPMF s = q2e (M.init s) := by
  simp [FinDTMC.initPMF]

@[simp] theorem FinDTMC.stepPMF_apply (s s' : S) :
    M.stepPMF s s' = q2e (M.step s s') := by
  simp [FinDTMC.stepPMF]

/-- The horizon-`k` trajectory law, by the standard monadic
construction: start from the initial distribution, then bind one
kernel step at a time. -/
noncomputable def FinDTMC.trajPMF : (k : ℕ) → PMF (Traj S k)
  | 0 => M.initPMF.map (fun s => fun _ => s)
  | k + 1 => (FinDTMC.trajPMF k).bind
      (fun ω => (M.stepPMF (ω (Fin.last k))).map (Fin.snoc ω))

/-- Decomposing a trajectory as its front and its last state, inside
an indicator double sum. -/
private theorem sum_snoc_ite {k : ℕ} (ω' : Traj S (k + 1))
    (X : Traj S k → S → ℝ≥0∞) :
    (∑ ω : Traj S k, ∑ s,
        if ω' = Fin.snoc ω s then X ω s else 0) =
      X (Fin.init ω') (ω' (Fin.last (k + 1))) := by
  classical
  have hiff : ∀ (ω : Traj S k) (s : S),
      ω' = Fin.snoc ω s ↔
        ω = Fin.init ω' ∧ s = ω' (Fin.last (k + 1)) := by
    intro ω s
    constructor
    · rintro rfl
      constructor <;> simp
    · rintro ⟨rfl, rfl⟩
      exact (Fin.snoc_init_self ω').symm
  have hrw : ∀ (ω : Traj S k) (s : S),
      (if ω' = Fin.snoc ω s then X ω s else 0) =
        if ω = Fin.init ω' then
          (if s = ω' (Fin.last (k + 1)) then X ω s else 0) else 0 := by
    intro ω s
    by_cases h1 : ω = Fin.init ω'
    · by_cases h2 : s = ω' (Fin.last (k + 1))
      · rw [if_pos ((hiff ω s).mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]
      · rw [if_neg (fun hc => h2 ((hiff ω s).mp hc).2), if_pos h1,
          if_neg h2]
    · rw [if_neg (fun hc => h1 ((hiff ω s).mp hc).1), if_neg h1]
  rw [Finset.sum_congr rfl fun ω _ =>
    Finset.sum_congr rfl fun s _ => hrw ω s]
  have hpull : ∀ ω : Traj S k,
      (∑ s, if ω = Fin.init ω' then
        (if s = ω' (Fin.last (k + 1)) then X ω s else 0) else 0) =
      if ω = Fin.init ω' then
        (∑ s, if s = ω' (Fin.last (k + 1)) then X ω s else 0) else 0 := by
    intro ω
    by_cases h : ω = Fin.init ω' <;> simp [h]
  rw [Finset.sum_congr rfl fun ω _ => hpull ω]
  rw [Finset.sum_ite_eq' univ (Fin.init ω')
    (fun ω => ∑ s, if s = ω' (Fin.last (k + 1)) then X ω s else 0)]
  rw [if_pos (mem_univ _)]
  rw [Finset.sum_ite_eq' univ (ω' (Fin.last (k + 1)))
    (fun s => X (Fin.init ω') s)]
  rw [if_pos (mem_univ _)]

/-- **The connector**: the exact-rational path law and the monadic
construction agree under the canonical coercion, at every horizon and
every trajectory. -/
theorem FinDTMC.trajPMF_eq :
    ∀ (k : ℕ) (ω : Traj S k),
      (M.trajPMF k) ω = q2e ((M.pathLaw k).wt ω) := by
  intro k
  induction k with
  | zero =>
    intro ω
    show (M.initPMF.map (fun s => fun _ => s)) ω = _
    have hω : ω = fun _ => ω 0 := funext fun i => by
      rw [Fin.fin_one_eq_zero i]
    rw [PMF.map_apply, tsum_fintype, FinDTMC.pathLaw_wt]
    unfold chainWt
    rw [Fin.prod_univ_zero, mul_one,
      show q2e (M.init (ω 0)) = M.initPMF (ω 0) from
        (FinDTMC.initPMF_apply M (ω 0)).symm]
    refine (Finset.sum_eq_single (ω 0) (fun b _ hb => ?_)
      (fun h => absurd (mem_univ _) h)).trans ?_
    · exact if_neg fun hc => hb (congrFun hc 0).symm
    · exact if_pos hω
  | succ k ih =>
    intro ω'
    show ((M.trajPMF k).bind
      (fun ω => (M.stepPMF (ω (Fin.last k))).map (Fin.snoc ω))) ω' = _
    rw [PMF.bind_apply, tsum_fintype]
    have hin : ∀ ω : Traj S k,
        M.trajPMF k ω *
          ((M.stepPMF (ω (Fin.last k))).map (Fin.snoc ω)) ω' =
        ∑ s, if ω' = Fin.snoc ω s then
          M.trajPMF k ω * M.stepPMF (ω (Fin.last k)) s else 0 := by
      intro ω
      rw [PMF.map_apply, tsum_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_ite, mul_zero]
      congr!
    simp only [hin]
    rw [sum_snoc_ite ω' (fun ω s =>
        M.trajPMF k ω * M.stepPMF (ω (Fin.last k)) s),
      ih (Fin.init ω'), FinDTMC.stepPMF_apply, FinDTMC.pathLaw_wt,
      FinDTMC.pathLaw_wt,
      ← q2e_mul (chainWt_nonneg M.init_nonneg M.step_nonneg _)]
    congr 1
    have hsnoc := chainWt_snoc M.init M.step (Fin.init ω')
      (ω' (Fin.last (k + 1)))
    rw [Fin.snoc_init_self ω'] at hsnoc
    exact hsnoc.symm

end Connector

end Adequacy
end SuFunctor
