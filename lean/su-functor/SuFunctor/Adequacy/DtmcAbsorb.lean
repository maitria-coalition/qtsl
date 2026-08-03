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
  `rowsLaw_expect_le_of_nonpos` on compiled rows. -/

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

theorem massOn_le_one (M : FinDTMC S) (t : ℕ) (A : Finset S) :
    massOn M t A ≤ 1 := by
  calc massOn M t A
      ≤ ∑ s, massAt M t s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          fun s _ _ => massAt_nonneg M t s
    _ = 1 := massAt_sum M t

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

/-! ## Absorbing states and monotone absorption -/

/-- A state is absorbing when its self-loop carries the whole row. -/
def FinDTMC.Absorbing (M : FinDTMC S) (s : S) : Prop := M.step s s = 1

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
states never decreases.  The next mass sums every state's contribution
`m_t(s) · K(s, C)`; keeping only the states of `C` and reading the
whole row at each already returns today's mass. -/
theorem dtmcAbsorb_mass_mono_step (M : FinDTMC S) {C : Finset S}
    (hC : ∀ s ∈ C, M.Absorbing s) (t : ℕ) :
    massOn M t C ≤ massOn M (t + 1) C := by
  have hswap : massOn M (t + 1) C =
      ∑ s, massAt M t s * ∑ s' ∈ C, M.step s s' := by
    unfold massOn
    calc (∑ s' ∈ C, massAt M (t + 1) s')
        = ∑ s' ∈ C, ∑ s, massAt M t s * M.step s s' :=
          Finset.sum_congr rfl fun s' _ => massAt_succ M t s'
      _ = ∑ s, ∑ s' ∈ C, massAt M t s * M.step s s' := Finset.sum_comm
      _ = ∑ s, massAt M t s * ∑ s' ∈ C, M.step s s' :=
          Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
  rw [hswap]
  calc massOn M t C
      = ∑ s ∈ C, massAt M t s := rfl
    _ ≤ ∑ s ∈ C, massAt M t s * ∑ s' ∈ C, M.step s s' :=
        Finset.sum_le_sum fun s hs =>
          le_mul_of_one_le_right (massAt_nonneg M t s)
            (one_le_row_sum_on M (hC s hs) hs)
    _ ≤ ∑ s, massAt M t s * ∑ s' ∈ C, M.step s s' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          fun s _ _ => mul_nonneg (massAt_nonneg M t s)
            (Finset.sum_nonneg fun s' _ => M.step_nonneg s s')

/-- **Monotone absorption**: the mass on a set of absorbing states is
monotone in time. -/
theorem dtmcAbsorb_mass_mono (M : FinDTMC S) {C : Finset S}
    (hC : ∀ s ∈ C, M.Absorbing s) {T t' : ℕ} (h : T ≤ t') :
    massOn M T C ≤ massOn M t' C := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (dtmcAbsorb_mass_mono_step M hC n)

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

end Adequacy
end SuFunctor
