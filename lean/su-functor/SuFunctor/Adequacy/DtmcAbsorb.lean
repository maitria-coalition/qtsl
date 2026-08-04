import SuFunctor.Adequacy.DtmcGenerator

/-! # Absorption brackets for the DTMC row grain

Finite-horizon absorption bounds for finite chains: the soundness
ingredients of the absorption-bracket certificate species.  From the
chain's distribution at one checkable horizon `T`, two-sided brackets
on the class-absorption mass at *every* later horizon — and hence on
any eventual absorption measure — plus the correlated-ratio bracket
that carries the bounds through normalization (conditional measures of
discrete probabilistic programs compiled to chains).

The forward object is the measure evolution `massAt` (`m_t = m_0 Kᵗ`
as a mass vector, exact rationals); `massAt_dual` grounds it in the
mechanized path law: the expectation of any observable against
`massAt` at time `t` is the observable's endpoint expectation under
the chain's horizon-`t` law.  Every bracket below is thereby a
statement about the adequacy square's semantics, not a private
restatement beside it.

* `dtmcAbsorb_mass_mono` — monotone absorption: mass on a set of
  absorbing states never decreases (one step:
  `dtmcAbsorb_mass_mono_step`).
* `dtmcAbsorbBracket_sound` — the conservation bracket: for a class
  `C` inside a set `Abs` of absorbing states and any `t' ≥ T`, the
  class mass lies in `[mass_T(C), mass_T(C) + (1 - mass_T(Abs))]` —
  class gain after `T` is bounded by the mass not yet absorbed at
  `T`, because the complement `Abs \ C` is itself a set of absorbing
  states and so also monotone.
* `dtmcPosteriorBracket_sound` — the correlated-ratio bracket, pure
  algebra with no chain in sight: lower bounds `N c` on true class
  masses `Mv c` with a shared total slack `R` bracket every
  normalized ratio `Mv c / Σ Mv` inside
  `[N c / (S + R), (N c + R) / (S + R)]` where `S = Σ N`.  The
  correlation is the point: numerator and denominator errors draw on
  one slack budget, so the bracket beats the interval quotient.
* `dtmcAbsorb_eventual_bracket` — the species' composed claim shape:
  endpoints verified against the horizon-`T` masses bracket the class
  mass at every `t' ≥ T`.  Stated universally rather than as a
  supremum: over `ℚ` the supremum of the (monotone, bounded) mass
  sequence need not exist as a rational, and the universally
  quantified form is the citable content — any completion-valued
  limit or supremum inherits the bracket from it.
* `massAt_expect_le_of_contraction` — the transfer-contraction
  induction (the generator-form strengthening's core): a one-step
  transfer contracting by a factor `c` at every state decays the
  observable's expectation geometrically.  At `c = 1` this subsumes
  the supermartingale consumption: `pathLaw_expect_le_of_genRow_nonpos`
  re-derives, through `massAt_dual`, exactly the statement shape of
  `rowsLaw_expect_le_of_nonpos` on compiled rows.
* `dtmcAbsorb_mass_le_reach` / `dtmcAbsorbBracket_reach_sound` — the
  **reachability-sharpened residual**: after `T` the class can only
  gain mass that sat, at `T`, on states that can still *reach* the
  class along positive-probability steps (`FinDTMC.Reaches`).  Mass on
  non-reachers is dead to the class: the non-reachers form a
  forward-closed set (`FinDTMC.ForwardClosed`), and mass on a
  forward-closed set is monotone (`dtmc_mass_mono_of_forwardClosed` —
  the generalization of monotone absorption, from which
  `dtmcAbsorb_mass_mono` now derives, an absorbing set being
  forward-closed).  The sharpened upper endpoint needs no absorbing
  hypothesis at all, and it never loosens the incumbent's:
  `dtmcAbsorb_reach_residual_le` bounds the reach-residual by the
  not-yet-absorbed residual `1 - mass_T(Abs)`.
* `dtmcAbsorb_eventual_bracket_reach` — the sharpened claim shape,
  mirroring `dtmcAbsorb_eventual_bracket` (universally quantified over
  `t' ≥ T`, for the same reason).
* `idBool_*` — the strict-improvement witness, kernel-checked: the
  two-state identity chain with the class unreachable from the alive
  state.  The incumbent residual is `1` at every horizon, the
  sharpened residual is `0`, and the sharpened bracket pins the class
  mass to exactly `0` — the regression tooth for the revision event
  that folds the sharpening into the incumbent rule. -/

namespace SuFunctor
namespace Adequacy

open Finset

variable {S : Type} [Fintype S]

/-! ## The forward measure evolution -/

/-- The chain's distribution at time `t`: the initial distribution
pushed forward `t` steps through the transition matrix — `m_t = m_0 Kᵗ`
as a mass vector, in exact rational arithmetic. -/
def massAt (M : FinDTMC S) : ℕ → S → ℚ
  | 0 => M.init
  | t + 1 => fun s' => ∑ s, massAt M t s * M.step s s'

@[simp] theorem massAt_zero (M : FinDTMC S) : massAt M 0 = M.init := rfl

theorem massAt_succ (M : FinDTMC S) (t : ℕ) (s' : S) :
    massAt M (t + 1) s' = ∑ s, massAt M t s * M.step s s' := rfl

theorem massAt_nonneg (M : FinDTMC S) (t : ℕ) (s : S) :
    0 ≤ massAt M t s := by
  induction t generalizing s with
  | zero => exact M.init_nonneg s
  | succ t ih =>
    rw [massAt_succ]
    exact Finset.sum_nonneg fun s' _ =>
      mul_nonneg (ih s') (M.step_nonneg s' s)

/-- The evolution conserves total mass: a stochastic row set moves
probability, never creates or leaks it. -/
theorem massAt_sum (M : FinDTMC S) (t : ℕ) : ∑ s, massAt M t s = 1 := by
  induction t with
  | zero => exact M.init_sum
  | succ t ih =>
    calc (∑ s', massAt M (t + 1) s')
        = ∑ s', ∑ s, massAt M t s * M.step s s' :=
          Finset.sum_congr rfl fun s' _ => massAt_succ M t s'
      _ = ∑ s, ∑ s', massAt M t s * M.step s s' := Finset.sum_comm
      _ = ∑ s, massAt M t s * ∑ s', M.step s s' :=
          Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ = ∑ s, massAt M t s :=
          Finset.sum_congr rfl fun s _ => by
            rw [M.step_row_sum s, mul_one]
      _ = 1 := ih

/-- Mass on a set of states at time `t`. -/
def massOn (M : FinDTMC S) (t : ℕ) (A : Finset S) : ℚ :=
  ∑ s ∈ A, massAt M t s

theorem massOn_nonneg (M : FinDTMC S) (t : ℕ) (A : Finset S) :
    0 ≤ massOn M t A :=
  Finset.sum_nonneg fun s _ => massAt_nonneg M t s

theorem massOn_le_of_subset (M : FinDTMC S) (t : ℕ) {A B : Finset S}
    (hAB : A ⊆ B) : massOn M t A ≤ massOn M t B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB
    fun s _ _ => massAt_nonneg M t s

theorem massOn_univ (M : FinDTMC S) (t : ℕ) :
    massOn M t Finset.univ = 1 :=
  massAt_sum M t

theorem massOn_le_one (M : FinDTMC S) (t : ℕ) (A : Finset S) :
    massOn M t A ≤ 1 :=
  (massOn_le_of_subset M t (Finset.subset_univ A)).trans_eq
    (massOn_univ M t)

/-- One forward step, in expectation form: expectation against
`massAt` at `t + 1` is the expectation of the one-step transfer
against `massAt` at `t`. -/
theorem massAt_expect_succ (M : FinDTMC S) (V : S → ℚ) (t : ℕ) :
    (∑ s', massAt M (t + 1) s' * V s') =
      ∑ s, massAt M t s * ∑ s', M.step s s' * V s' := by
  calc (∑ s', massAt M (t + 1) s' * V s')
      = ∑ s', (∑ s, massAt M t s * M.step s s') * V s' :=
        Finset.sum_congr rfl fun s' _ => by rw [massAt_succ]
    _ = ∑ s', ∑ s, massAt M t s * M.step s s' * V s' :=
        Finset.sum_congr rfl fun s' _ => by rw [Finset.sum_mul]
    _ = ∑ s, ∑ s', massAt M t s * M.step s s' * V s' := Finset.sum_comm
    _ = ∑ s, massAt M t s * ∑ s', M.step s s' * V s' := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s' _ => by ring

/-! ## The duality bridge to the path law

The forward evolution is the endpoint marginal of the mechanized path
law: expectation against `massAt` at time `t` equals the endpoint
expectation under the compiled rows' horizon-`t` law.  Proved by
transposing `rowsLaw_expect_succ` — one step of the backward
(observable) evolution per step of the forward (measure) evolution. -/

section DualityBridge

variable [DecidableEq S]

/-- **The duality bridge**: the forward measure evolution is the
endpoint marginal of the path law.  Expectation of any observable
against `massAt` at time `t` equals its endpoint expectation under the
chain's horizon-`t` law, so statements about `massAt` are statements
about the adequacy square's semantics. -/
theorem massAt_dual (M : FinDTMC S) :
    ∀ (t : ℕ) (V : S → ℚ),
      (∑ s, massAt M t s * V s) = expectQ (M.pathLaw t) (atLast V) := by
  intro t
  induction t with
  | zero =>
    intro V
    unfold expectQ atLast
    refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) S).symm)
      (fun s => massAt M 0 s * V s)
      (fun ω => (M.pathLaw 0).wt ω * V (ω (Fin.last 0)))
      (fun s => ?_)
    rw [FinDTMC.pathLaw_wt]
    simp [chainWt, Equiv.funUnique]
  | succ t ih =>
    intro V
    have h1 : expectQ (M.pathLaw (t + 1)) (atLast V) =
        expectQ (M.pathLaw t) (atLast (transferRow (compile M) V)) := by
      rw [← compile_rowsLaw M (t + 1), ← compile_rowsLaw M t]
      exact rowsLaw_expect_succ (compile M) (compile_wf M) t V
    rw [h1, ← ih (transferRow (compile M) V), massAt_expect_succ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [transferRow_compile]

/-- The set-mass reading of the bridge: mass on a set is the endpoint
expectation of its indicator under the path law. -/
theorem massOn_dual (M : FinDTMC S) (t : ℕ) (A : Finset S) :
    massOn M t A =
      expectQ (M.pathLaw t)
        (atLast (fun s => if s ∈ A then (1 : ℚ) else 0)) := by
  rw [← massAt_dual M t]
  unfold massOn
  rw [show (∑ s, massAt M t s * (if s ∈ A then (1 : ℚ) else 0)) =
      ∑ s, (if s ∈ A then massAt M t s else 0) from
    Finset.sum_congr rfl fun s _ => by
      by_cases h : s ∈ A <;> simp [h]]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end DualityBridge

/-! ## Forward-closed sets and monotone mass

The mass-monotonicity that drives every bracket below is not really
about absorption: it holds on any set the chain cannot leave.  A set
is *forward-closed* when every positive-probability step from inside
lands inside; on such a set the whole outgoing row of an inside state
stays inside (outside entries are zero, the row sums to one), so the
set's mass never decreases.  An absorbing set is the special case
where each inside state's row is its own self-loop. -/

/-- A set of states is forward-closed when every positive-probability
step from a state inside lands inside. -/
def FinDTMC.ForwardClosed (M : FinDTMC S) (D : Finset S) : Prop :=
  ∀ x ∈ D, ∀ y, 0 < M.step x y → y ∈ D

/-- From inside a forward-closed set, the outgoing row spends
everything inside: entries at outside states are zero (a positive
entry would witness a step out), so the inside row sum is the whole
row. -/
theorem one_le_row_sum_on_of_forwardClosed (M : FinDTMC S)
    {D : Finset S} (hD : M.ForwardClosed D) {s : S} (hs : s ∈ D) :
    1 ≤ ∑ s' ∈ D, M.step s s' := by
  have heq : (∑ s' ∈ D, M.step s s') = ∑ s', M.step s s' := by
    refine Finset.sum_subset (Finset.subset_univ D) fun y _ hyD => ?_
    by_contra h0
    exact hyD (hD s hs y
      (lt_of_le_of_ne (M.step_nonneg s y) (Ne.symm h0)))
  rw [heq, M.step_row_sum s]

/-- **Monotone mass on a forward-closed set, one step**: the next mass
sums every state's contribution `m_t(s) · K(s, D)`; keeping only the
states of `D` and reading the whole row at each already returns
today's mass. -/
theorem dtmc_mass_mono_step_of_forwardClosed (M : FinDTMC S)
    {D : Finset S} (hD : M.ForwardClosed D) (t : ℕ) :
    massOn M t D ≤ massOn M (t + 1) D := by
  have hswap : massOn M (t + 1) D =
      ∑ s, massAt M t s * ∑ s' ∈ D, M.step s s' := by
    unfold massOn
    calc (∑ s' ∈ D, massAt M (t + 1) s')
        = ∑ s' ∈ D, ∑ s, massAt M t s * M.step s s' :=
          Finset.sum_congr rfl fun s' _ => massAt_succ M t s'
      _ = ∑ s, ∑ s' ∈ D, massAt M t s * M.step s s' := Finset.sum_comm
      _ = ∑ s, massAt M t s * ∑ s' ∈ D, M.step s s' :=
          Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
  rw [hswap]
  calc massOn M t D
      = ∑ s ∈ D, massAt M t s := rfl
    _ ≤ ∑ s ∈ D, massAt M t s * ∑ s' ∈ D, M.step s s' :=
        Finset.sum_le_sum fun s hs =>
          le_mul_of_one_le_right (massAt_nonneg M t s)
            (one_le_row_sum_on_of_forwardClosed M hD hs)
    _ ≤ ∑ s, massAt M t s * ∑ s' ∈ D, M.step s s' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
          fun s _ _ => mul_nonneg (massAt_nonneg M t s)
            (Finset.sum_nonneg fun s' _ => M.step_nonneg s s')

/-- **Monotone mass on a forward-closed set**: mass on a set the chain
cannot leave is monotone in time. -/
theorem dtmc_mass_mono_of_forwardClosed (M : FinDTMC S)
    {D : Finset S} (hD : M.ForwardClosed D) {T t' : ℕ} (h : T ≤ t') :
    massOn M T D ≤ massOn M t' D := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    exact le_trans ih (dtmc_mass_mono_step_of_forwardClosed M hD n)

/-! ## Absorbing states and monotone absorption -/

/-- A state is absorbing when its self-loop carries the whole row. -/
def FinDTMC.Absorbing (M : FinDTMC S) (s : S) : Prop := M.step s s = 1

/-- From an absorbing state, positive-probability steps go nowhere
else: the self-loop already spends the whole row, so a positive entry
elsewhere would push the row sum past one. -/
theorem FinDTMC.eq_of_absorbing_step (M : FinDTMC S) {x y : S}
    (hx : M.Absorbing x) (hxy : 0 < M.step x y) : y = x := by
  classical
  by_contra hne
  have herase : M.step x y ≤ ∑ s' ∈ Finset.univ.erase x, M.step x s' :=
    Finset.single_le_sum (f := fun s' => M.step x s')
      (fun s' _ => M.step_nonneg x s')
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ y⟩)
  have hsplit : (∑ s' ∈ Finset.univ.erase x, M.step x s') + M.step x x
      = ∑ s', M.step x s' :=
    Finset.sum_erase_add _ _ (Finset.mem_univ x)
  have hx1 : M.step x x = 1 := hx
  have hsum : (∑ s', M.step x s') = 1 := M.step_row_sum x
  linarith

/-- An absorbing set is forward-closed: from inside, the only positive
step is the self-loop. -/
theorem FinDTMC.forwardClosed_of_absorbing (M : FinDTMC S)
    {C : Finset S} (hC : ∀ s ∈ C, M.Absorbing s) : M.ForwardClosed C := by
  intro x hx y hxy
  rw [M.eq_of_absorbing_step (hC x hx) hxy]
  exact hx

/-- At an absorbing state, any set containing it already receives the
whole outgoing row. -/
theorem one_le_row_sum_on (M : FinDTMC S) {s : S} (hs : M.Absorbing s)
    {A : Finset S} (hsA : s ∈ A) :
    1 ≤ ∑ s' ∈ A, M.step s s' := by
  have h : M.step s s ≤ ∑ s' ∈ A, M.step s s' :=
    Finset.single_le_sum (f := fun s' => M.step s s')
      (fun s' _ => M.step_nonneg s s') hsA
  have hs1 : M.step s s = 1 := hs
  rwa [hs1] at h

/-- **Monotone absorption, one step**: the mass on a set of absorbing
states never decreases — the absorbing case of monotone mass on a
forward-closed set. -/
theorem dtmcAbsorb_mass_mono_step (M : FinDTMC S) {C : Finset S}
    (hC : ∀ s ∈ C, M.Absorbing s) (t : ℕ) :
    massOn M t C ≤ massOn M (t + 1) C :=
  dtmc_mass_mono_step_of_forwardClosed M
    (M.forwardClosed_of_absorbing hC) t

/-- **Monotone absorption**: the mass on a set of absorbing states is
monotone in time — the absorbing case of
`dtmc_mass_mono_of_forwardClosed`. -/
theorem dtmcAbsorb_mass_mono (M : FinDTMC S) {C : Finset S}
    (hC : ∀ s ∈ C, M.Absorbing s) {T t' : ℕ} (h : T ≤ t') :
    massOn M T C ≤ massOn M t' C :=
  dtmc_mass_mono_of_forwardClosed M (M.forwardClosed_of_absorbing hC) h

/-! ## The conservation bracket -/

section ConservationBracket

variable [DecidableEq S]

/-- Splitting mass over a subset and its relative complement. -/
theorem massOn_sdiff (M : FinDTMC S) (t : ℕ) {C A : Finset S}
    (hCA : C ⊆ A) :
    massOn M t (A \ C) + massOn M t C = massOn M t A :=
  Finset.sum_sdiff hCA

/-- **The conservation bracket**: for a class `C` inside a set `Abs`
of absorbing states, every mass at or after horizon `T` lies in
`[mass_T(C), mass_T(C) + (1 - mass_T(Abs))]`.  The lower endpoint is
monotone absorption; the upper endpoint is conservation — the
complement `Abs \ C` is itself a set of absorbing states, so its mass
is also monotone, and the class can only gain what was not yet
absorbed at `T`. -/
theorem dtmcAbsorbBracket_sound (M : FinDTMC S) {C Abs : Finset S}
    (hAbs : ∀ s ∈ Abs, M.Absorbing s) (hCA : C ⊆ Abs)
    {T t' : ℕ} (h : T ≤ t') :
    massOn M T C ≤ massOn M t' C ∧
      massOn M t' C ≤ massOn M T C + (1 - massOn M T Abs) := by
  have hC : ∀ s ∈ C, M.Absorbing s := fun s hs => hAbs s (hCA hs)
  have hD : ∀ s ∈ Abs \ C, M.Absorbing s := fun s hs =>
    hAbs s (Finset.mem_sdiff.mp hs).1
  refine ⟨dtmcAbsorb_mass_mono M hC h, ?_⟩
  have hsplitT := massOn_sdiff M T hCA
  have hsplitt' := massOn_sdiff M t' hCA
  have hmonoD := dtmcAbsorb_mass_mono M hD h
  have hle1 := massOn_le_one M t' Abs
  linarith

/-- **The composed bracket, in the claim shape the species checks**:
endpoints verified against the horizon-`T` masses — `lo` below the
class mass, `hi` above the class mass plus the not-yet-absorbed
residual — bracket the class mass at *every* horizon `t' ≥ T`.

Stated universally rather than as a supremum on purpose: over `ℚ` the
supremum of the (monotone, bounded) mass sequence need not exist as a
rational, and the universally quantified form is the citable content —
any eventual absorption measure defined as a supremum or limit of the
sequence, in any completion, inherits `[lo, hi]` from this form. -/
theorem dtmcAbsorb_eventual_bracket (M : FinDTMC S) {C Abs : Finset S}
    (hAbs : ∀ s ∈ Abs, M.Absorbing s) (hCA : C ⊆ Abs)
    {T : ℕ} {lo hi : ℚ}
    (hlo : lo ≤ massOn M T C)
    (hhi : massOn M T C + (1 - massOn M T Abs) ≤ hi) :
    ∀ t', T ≤ t' → lo ≤ massOn M t' C ∧ massOn M t' C ≤ hi := by
  intro t' h
  obtain ⟨h1, h2⟩ := dtmcAbsorbBracket_sound M hAbs hCA h
  exact ⟨le_trans hlo h1, le_trans h2 hhi⟩

end ConservationBracket

/-! ## Reachability and the sharpened residual

The conservation bracket charges the whole not-yet-absorbed residual
`1 - mass_T(Abs)` to every class.  But mass can only arrive in `C`
along positive-probability steps, so mass sitting at `T` on states
that cannot *reach* `C` is dead to the class forever: the non-reachers
form a forward-closed set (a step out of it would witness reaching),
their mass is monotone, and what is left over for `C` at any `t' ≥ T`
is at most the horizon-`T` mass of the reachers.  The sharpened upper
endpoint `mass_T(C) + mass_T(reach(C) \ C)` needs **no absorbing
hypothesis at all** — it holds for every class of every finite chain —
and it never loosens the incumbent's (`dtmcAbsorb_reach_residual_le`):
when every state of `Abs ⊇ C` is absorbing, a reacher outside `C` is
never in `Abs` (an absorbing state that reaches `C` is in `C`), so the
reach-residual sits inside `1 - mass_T(Abs)`. -/

/-- Reachability into a class along positive-probability steps of the
chain: reflexive on the class, closed under prepending a step of
positive probability. -/
inductive FinDTMC.Reaches (M : FinDTMC S) (C : Finset S) : S → Prop
  | base {x : S} (hx : x ∈ C) : FinDTMC.Reaches M C x
  | step {x y : S} (hxy : 0 < M.step x y)
      (hy : FinDTMC.Reaches M C y) : FinDTMC.Reaches M C x

open Classical in
/-- The set of states from which the class is reachable.  Reachability
is used here at the proof layer only, so classical decidability
suffices; the certificate checker recomputes reachability by chase
saturation, which is its native operation. -/
noncomputable def FinDTMC.reachSet (M : FinDTMC S) (C : Finset S) :
    Finset S :=
  Finset.univ.filter (M.Reaches C)

theorem FinDTMC.mem_reachSet {M : FinDTMC S} {C : Finset S} {x : S} :
    x ∈ M.reachSet C ↔ M.Reaches C x := by
  simp only [FinDTMC.reachSet, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- The class reaches itself. -/
theorem FinDTMC.subset_reachSet (M : FinDTMC S) (C : Finset S) :
    C ⊆ M.reachSet C :=
  fun _ hx => FinDTMC.mem_reachSet.mpr (.base hx)

/-- An absorbing state that reaches the class is in the class: its
only positive step is the self-loop, so the reaching path never
leaves it. -/
theorem FinDTMC.Reaches.mem_of_absorbing {M : FinDTMC S}
    {C : Finset S} {s : S} (hr : M.Reaches C s) :
    M.Absorbing s → s ∈ C := by
  induction hr with
  | base hx => exact fun _ => hx
  | @step x y hxy _ ih =>
    intro hxabs
    have hyx : y = x := M.eq_of_absorbing_step hxabs hxy
    rw [hyx] at ih
    exact ih hxabs

section ReachabilitySharpening

variable [DecidableEq S]

/-- Membership in the sharpened residual set, spelled out: the
reachers outside the class. -/
theorem FinDTMC.mem_reachSet_sdiff {M : FinDTMC S} {C : Finset S}
    {x : S} :
    x ∈ M.reachSet C \ C ↔ M.Reaches C x ∧ x ∉ C := by
  rw [Finset.mem_sdiff, FinDTMC.mem_reachSet]

/-- The non-reachers form a forward-closed set: a positive step from a
non-reacher to a reacher would make the source a reacher. -/
theorem FinDTMC.forwardClosed_compl_reachSet (M : FinDTMC S)
    (C : Finset S) :
    M.ForwardClosed (Finset.univ \ M.reachSet C) := by
  intro x hx y hxy
  rcases Finset.mem_sdiff.mp hx with ⟨-, hxr⟩
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyr => ?_⟩
  exact hxr (FinDTMC.mem_reachSet.mpr
    (.step hxy (FinDTMC.mem_reachSet.mp hyr)))

/-- **The reachability-sharpened upper bound** — no hypotheses on the
class at all: at every `t' ≥ T`, the class mass is at most the
horizon-`T` class mass plus the horizon-`T` mass of the states that
can still reach the class.  Mass on non-reachers is trapped there
(their set is forward-closed), so only the reachers' mass at `T` is
ever available to the class. -/
theorem dtmcAbsorb_mass_le_reach (M : FinDTMC S) {C : Finset S}
    {T t' : ℕ} (h : T ≤ t') :
    massOn M t' C ≤ massOn M T C + massOn M T (M.reachSet C \ C) := by
  have hCR : C ⊆ M.reachSet C := M.subset_reachSet C
  have h1 : massOn M t' C ≤ massOn M t' (M.reachSet C) :=
    massOn_le_of_subset M t' hCR
  have hmono : massOn M T (Finset.univ \ M.reachSet C) ≤
      massOn M t' (Finset.univ \ M.reachSet C) :=
    dtmc_mass_mono_of_forwardClosed M
      (M.forwardClosed_compl_reachSet C) h
  have hsplitT : massOn M T (M.reachSet C \ C) + massOn M T C =
      massOn M T (M.reachSet C) :=
    massOn_sdiff M T hCR
  have huT : massOn M T (Finset.univ \ M.reachSet C) +
      massOn M T (M.reachSet C) = 1 := by
    rw [massOn_sdiff M T (Finset.subset_univ _), massOn_univ]
  have hut' : massOn M t' (Finset.univ \ M.reachSet C) +
      massOn M t' (M.reachSet C) = 1 := by
    rw [massOn_sdiff M t' (Finset.subset_univ _), massOn_univ]
  linarith

/-- **The reachability-sharpened conservation bracket**: under the
incumbent's hypotheses (`C` inside a set `Abs` of absorbing states),
every mass at or after horizon `T` lies in
`[mass_T(C), mass_T(C) + mass_T(reach(C) \ C)]`.  The lower endpoint
is monotone absorption; the upper endpoint is the sharpened residual,
which by `dtmcAbsorb_reach_residual_le` never exceeds the incumbent's
`1 - mass_T(Abs)`. -/
theorem dtmcAbsorbBracket_reach_sound (M : FinDTMC S)
    {C Abs : Finset S} (hAbs : ∀ s ∈ Abs, M.Absorbing s)
    (hCA : C ⊆ Abs) {T t' : ℕ} (h : T ≤ t') :
    massOn M T C ≤ massOn M t' C ∧
      massOn M t' C ≤ massOn M T C + massOn M T (M.reachSet C \ C) :=
  ⟨dtmcAbsorb_mass_mono M (fun s hs => hAbs s (hCA hs)) h,
    dtmcAbsorb_mass_le_reach M h⟩

/-- **Subsumption**: the sharpened residual never exceeds the
incumbent's.  A reacher outside the class is never in `Abs` — an
absorbing state that reaches the class is in the class — so the
reach-residual set sits inside the complement of `Abs`, whose mass is
`1 - mass_T(Abs)`.  Sharpened certificates therefore never loosen
existing ones: any bracket the incumbent rule admits, the sharpened
rule admits.  (`C ⊆ Abs` is not needed: every set of absorbing states
`Abs` bounds the reach-residual of every class.) -/
theorem dtmcAbsorb_reach_residual_le (M : FinDTMC S)
    {C Abs : Finset S} (hAbs : ∀ s ∈ Abs, M.Absorbing s) (T : ℕ) :
    massOn M T (M.reachSet C \ C) ≤ 1 - massOn M T Abs := by
  have hsub : M.reachSet C \ C ⊆ Finset.univ \ Abs := by
    intro s hs
    rcases Finset.mem_sdiff.mp hs with ⟨hsr, hsc⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, fun hsAbs => ?_⟩
    exact hsc
      ((FinDTMC.mem_reachSet.mp hsr).mem_of_absorbing (hAbs s hsAbs))
  have hu : massOn M T (Finset.univ \ Abs) + massOn M T Abs = 1 := by
    rw [massOn_sdiff M T (Finset.subset_univ Abs), massOn_univ]
  have := massOn_le_of_subset M T hsub
  linarith

/-- **The sharpened bracket, in the claim shape the species checks**:
endpoints verified against the horizon-`T` masses — `lo` below the
class mass, `hi` above the class mass plus the reach-residual —
bracket the class mass at *every* horizon `t' ≥ T`.  Universally
quantified for the same reason as `dtmcAbsorb_eventual_bracket`: over
`ℚ` the supremum of the mass sequence need not exist as a rational,
and any completion-valued eventual reading inherits `[lo, hi]` from
this form. -/
theorem dtmcAbsorb_eventual_bracket_reach (M : FinDTMC S)
    {C Abs : Finset S} (hAbs : ∀ s ∈ Abs, M.Absorbing s)
    (hCA : C ⊆ Abs) {T : ℕ} {lo hi : ℚ}
    (hlo : lo ≤ massOn M T C)
    (hhi : massOn M T C + massOn M T (M.reachSet C \ C) ≤ hi) :
    ∀ t', T ≤ t' → lo ≤ massOn M t' C ∧ massOn M t' C ≤ hi := by
  intro t' h
  obtain ⟨h1, h2⟩ := dtmcAbsorbBracket_reach_sound M hAbs hCA h
  exact ⟨le_trans hlo h1, le_trans h2 hhi⟩

end ReachabilitySharpening

/-! ## The correlated-ratio (posterior) bracket -/

/-- **The correlated-ratio bracket** — pure algebra, no chain in
sight.  Given per-class lower bounds `N c` on true masses `Mv c`
sharing one slack budget `R` (the residual: total underestimation
across all classes at most `R`), with positive total evidence
`S = Σ N`, every normalized ratio is bracketed:
`Mv c / Σ Mv ∈ [N c / (S + R), (N c + R) / (S + R)]`.

The correlation is the content: numerator and denominator draw their
errors from the same budget, so both endpoints use the single
normalizer `S + R` rather than the looser interval quotient. -/
theorem dtmcPosteriorBracket_sound {ι : Type} [Fintype ι]
    (N Mv : ι → ℚ) (R : ℚ) (hR : 0 ≤ R)
    (hN : ∀ c, 0 ≤ N c)
    (hS : 0 < ∑ c', N c')
    (hle : ∀ c, N c ≤ Mv c)
    (hgap : (∑ c', (Mv c' - N c')) ≤ R) (c : ι) :
    N c / ((∑ c', N c') + R) ≤ Mv c / (∑ c', Mv c') ∧
      Mv c / (∑ c', Mv c') ≤ (N c + R) / ((∑ c', N c') + R) := by
  set SN := ∑ c', N c' with hSN
  set SM := ∑ c', Mv c' with hSM
  have hMv_nonneg : ∀ c', 0 ≤ Mv c' := fun c' =>
    le_trans (hN c') (hle c')
  have hSN_le_SM : SN ≤ SM := Finset.sum_le_sum fun c' _ => hle c'
  have hgap' : SM - SN ≤ R := by
    rwa [Finset.sum_sub_distrib] at hgap
  have hSM_pos : 0 < SM := lt_of_lt_of_le hS hSN_le_SM
  have hSNR_pos : 0 < SN + R := by linarith
  have hNc_le_SN : N c ≤ SN :=
    Finset.single_le_sum (fun c' _ => hN c') (Finset.mem_univ c)
  have hMc_gap : Mv c - N c ≤ SM - SN := by
    have h1 : Mv c - N c ≤ ∑ c', (Mv c' - N c') :=
      Finset.single_le_sum (fun c' _ => sub_nonneg.mpr (hle c'))
        (Finset.mem_univ c)
    rwa [Finset.sum_sub_distrib] at h1
  constructor
  · rw [div_le_div_iff₀ hSNR_pos hSM_pos]
    have h1 : N c * SM ≤ Mv c * SM :=
      mul_le_mul_of_nonneg_right (hle c) (le_of_lt hSM_pos)
    have h2 : Mv c * SM ≤ Mv c * (SN + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (hMv_nonneg c)
    linarith
  · rw [div_le_div_iff₀ hSM_pos hSNR_pos]
    have hkey : 0 ≤ (SN - N c) * ((SN + R) - SM) :=
      mul_nonneg (by linarith) (by linarith)
    have hM_ub : Mv c * (SN + R) ≤ (N c + (SM - SN)) * (SN + R) :=
      mul_le_mul_of_nonneg_right (by linarith [hMc_gap])
        (le_of_lt hSNR_pos)
    nlinarith [hM_ub, hkey]

/-! ## Transfer contraction

The core induction of the generator-form strengthening: a one-step
transfer that contracts a nonnegative observable by a factor `c` on
the whole space decays its expectation geometrically.  A regional
contraction reduces to this global form by passing to the observable
supported on the region (under the no-re-entry hypothesis the
strengthened species carries); that regional packaging is staged with
the species itself.  The `c = 1` case subsumes the supermartingale
consumption of the generator form. -/

/-- **Transfer contraction**: if the one-step transfer of the
observable is bounded by `c` times the observable at every state, the
expectation against the evolving mass decays as `cᵗ`. -/
theorem massAt_expect_le_of_contraction (M : FinDTMC S)
    (V : S → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ s, (∑ s', M.step s s' * V s') ≤ c * V s) (t : ℕ) :
    (∑ s, massAt M t s * V s) ≤ c ^ t * ∑ s, massAt M 0 s * V s := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : (∑ s', massAt M (t + 1) s' * V s') ≤
        c * ∑ s, massAt M t s * V s := by
      rw [massAt_expect_succ, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      calc massAt M t s * ∑ s', M.step s s' * V s'
          ≤ massAt M t s * (c * V s) :=
            mul_le_mul_of_nonneg_left (hcontr s) (massAt_nonneg M t s)
        _ = c * (massAt M t s * V s) := by ring
    calc (∑ s', massAt M (t + 1) s' * V s')
        ≤ c * ∑ s, massAt M t s * V s := hstep
      _ ≤ c * (c ^ t * ∑ s, massAt M 0 s * V s) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (t + 1) * ∑ s, massAt M 0 s * V s := by ring

section Subsumption

variable [DecidableEq S]

/-- **Subsumption at `c = 1`**: a nonpositive generator form is
exactly a `c = 1` transfer contraction, and through the duality bridge
the conclusion is the statement shape of the path-law supermartingale
consumption (`rowsLaw_expect_le_of_nonpos`), re-derived here for the
compiled rows from the forward evolution. -/
theorem pathLaw_expect_le_of_genRow_nonpos (M : FinDTMC S)
    (V : S → ℚ) (hg : ∀ s, genRow (compile M) V s ≤ 0) (t : ℕ) :
    expectQ (M.pathLaw t) (atLast V) ≤
      expectQ (M.pathLaw 0) (atLast V) := by
  rw [← massAt_dual M t V, ← massAt_dual M 0 V]
  have hcontr : ∀ s, (∑ s', M.step s s' * V s') ≤ 1 * V s := by
    intro s
    have h := hg s
    rw [genRow_compile] at h
    linarith
  have h := massAt_expect_le_of_contraction M V zero_le_one hcontr t
  simpa using h

end Subsumption

/-! ## The strict-improvement witness

The regression tooth for the sharpening's revision event, in
miniature (the beauquier-3 shape: a class unreachable from the alive
mass): the two-state identity chain, all initial mass on `false`,
class `C = Abs = {true}`.  The incumbent residual `1 - mass_T(Abs)`
is `1` at every horizon — the incumbent bracket is `[0, 1]`, width
`1` — while the reach-residual is `0` (nothing outside the class
reaches it), so the sharpened bracket is `[0, 0]`: width `0`, pinning
the class mass exactly.  Kernel-checked strict improvement at matched
hypotheses. -/

section SharpWitness

/-- The two-state identity chain: every state self-loops with
probability one; all initial mass on `false`. -/
def idBool : FinDTMC Bool where
  step b b' := if b' = b then 1 else 0
  init b := if b then 0 else 1
  step_nonneg b b' := by split <;> norm_num
  step_row_sum b := by rw [Fintype.sum_bool]; cases b <;> norm_num
  init_nonneg b := by split <;> norm_num
  init_sum := by rw [Fintype.sum_bool]; norm_num

@[simp] theorem idBool_step (b b' : Bool) :
    idBool.step b b' = if b' = b then 1 else 0 := rfl

@[simp] theorem idBool_init (b : Bool) :
    idBool.init b = if b then 0 else 1 := rfl

/-- The identity chain never moves: the distribution at every time is
the initial one. -/
theorem idBool_massAt (t : ℕ) : massAt idBool t = idBool.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext b'
    rw [massAt_succ, Fintype.sum_bool, ih]
    cases b' <;> norm_num

/-- In the identity chain, only the class itself reaches the class:
every positive step is a self-loop. -/
theorem idBool_reaches_true_iff (b : Bool) :
    idBool.Reaches {true} b ↔ b = true := by
  constructor
  · intro hb
    induction hb with
    | base hx => exact Finset.mem_singleton.mp hx
    | @step x y hxy _ ih =>
      have hyx : y = x := by
        by_contra hne
        rw [idBool_step, if_neg hne] at hxy
        exact lt_irrefl 0 hxy
      rw [← hyx]
      exact ih
  · intro hb
    exact .base (Finset.mem_singleton.mpr hb)

theorem idBool_reachSet_eq : idBool.reachSet {true} = {true} := by
  ext b
  rw [FinDTMC.mem_reachSet, idBool_reaches_true_iff,
    Finset.mem_singleton]

theorem idBool_absorbing : ∀ s ∈ ({true} : Finset Bool),
    idBool.Absorbing s := by
  intro s hs
  rw [Finset.mem_singleton] at hs
  subst hs
  show idBool.step true true = 1
  norm_num

/-- The class mass at every horizon is zero (directly: the chain never
moves and the class starts empty). -/
theorem idBool_massOn_true (t : ℕ) : massOn idBool t {true} = 0 := by
  unfold massOn
  rw [Finset.sum_singleton, idBool_massAt]
  norm_num

/-- **The incumbent residual is total**: `1 - mass_T(Abs) = 1` at
every horizon — the incumbent bracket on the class is `[0, 1]`. -/
theorem idBool_incumbent_residual (T : ℕ) :
    1 - massOn idBool T {true} = 1 := by
  rw [idBool_massOn_true]; ring

/-- **The sharpened residual is zero**: no state outside the class
reaches it, so the reach-residual set is empty. -/
theorem idBool_sharp_residual (T : ℕ) :
    massOn idBool T (idBool.reachSet {true} \ {true}) = 0 := by
  rw [idBool_reachSet_eq, Finset.sdiff_self]
  simp [massOn]

/-- **Strict improvement, end to end**: the sharpened bracket — used
as the certificate rule would use it, through
`dtmcAbsorbBracket_reach_sound` with `C = Abs = {true}` — pins the
class mass to exactly `0` at every horizon, where the incumbent
bracket's upper endpoint is `1` (`idBool_incumbent_residual`): width
`0` against width `1` at matched hypotheses. -/
theorem idBool_strict_improvement {T t' : ℕ} (h : T ≤ t') :
    massOn idBool t' {true} = 0 := by
  have h2 := (dtmcAbsorbBracket_reach_sound idBool idBool_absorbing
    (Finset.Subset.refl {true}) h).2
  rw [idBool_massOn_true T, idBool_sharp_residual T] at h2
  have h0 := massOn_nonneg idBool t' {true}
  linarith

end SharpWitness

end Adequacy
end SuFunctor
