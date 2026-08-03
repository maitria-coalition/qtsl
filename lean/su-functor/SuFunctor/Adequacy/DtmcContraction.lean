import SuFunctor.Adequacy.DtmcAbsorb

/-! # Weighted transfer contraction for the discrete row grain

The species packaging of the generator-form contraction: the transfer
of `SuFunctor.Adequacy.DtmcAbsorb` generalized from stochastic kernels
to arbitrary nonnegative weight matrices, with the regional form, exit
domination, and the geometric-series tail and first-moment assemblies.

The carrier deliberately stays a bare weight matrix `W : S → S → ℚ`
with nonnegativity as an explicit hypothesis: a score-carrying row set
`s(x)·K(x,y)`, a sub-probability row set, and a stochastic kernel are
all instances of one nonnegative matrix, so one induction serves every
face.  The score-factored spelling ships as a corollary
(`wmassAt_expect_le_of_contraction_scored`), never a second induction.

* `wmassAt` — the weighted forward evolution: the `massAt` recursion
  over an arbitrary weight matrix; `massAt_eq_wmassAt` is the
  stochastic instance tie.
* `wmassAt_expect_le_of_contraction` — the weighted core: a one-step
  transfer bounded by `c` times the observable at every state decays
  the observable's expectation as `cᵗ`.  V-nonnegativity dropped, as
  in the stochastic core it generalizes.
* `massAt_expect_le_of_contraction_of_weighted` — the subsumption
  instance: the exact statement of the proven stochastic core,
  re-derived from the weighted lemma at score `≡ 1`.  Deliberate
  restatement — this is the mechanized implication from the
  strengthened rule's premise-form to the old, which chains with
  `pathLaw_expect_le_of_genRow_nonpos` (the `c = 1` face) down to the
  incumbent generator-form consumption, so every certificate admitted
  under the incumbent stays valid under the strengthening.
* `wmassAt_expect_on_le_of_contraction_on` — the regional packaging:
  contraction checked only on a region, plus no-re-entry from its
  complement, via the global lemma at the region-supported observable.
* `wmassAt_exit_le_of_contraction` — exit domination: an exit-weight
  observable dominated by `κ·V` on every state inherits the geometric
  decay, per step.
* `wmassAt_exit_tail_le` / `wmassAt_exit_moment_tail_le` — the tail
  assemblies, as universally quantified partial-sum bounds over
  `Finset.Ico T T'` (over `ℚ` the limit need not exist; any
  completion-valued limit inherits the bound): total exit weight after
  `T` is at most `κ·cᵀ·⟨m₀,V⟩/(1-c)`, and time-weighted exit weight at
  most `κ·⟨m₀,V⟩·cᵀ·(T(1-c)+c)/(1-c)²` — the geometric and
  arithmetico-geometric series bounds (`sum_Ico_pow_le`,
  `sum_Ico_mul_pow_le`) applied through the per-step domination.
  Higher moments (`k ≥ 2`) are deliberately absent from this module:
  they ride the same per-term reduction with `∑ tᵏcᵗ` closed forms,
  and belong to the species leg that first needs them. -/

namespace SuFunctor
namespace Adequacy

open Finset

variable {S : Type} [Fintype S]

/-! ## The weighted forward evolution -/

/-- The weighted mass vector at time `t`: the `massAt` recursion over
an arbitrary weight matrix — `m_t = m_0 Wᵗ` in exact rational
arithmetic, with no stochasticity assumed.  Sub-probability and
score-carrying row sets evolve by exactly this map. -/
def wmassAt (init : S → ℚ) (W : S → S → ℚ) : ℕ → S → ℚ
  | 0 => init
  | t + 1 => fun s' => ∑ s, wmassAt init W t s * W s s'

@[simp] theorem wmassAt_zero (init : S → ℚ) (W : S → S → ℚ) :
    wmassAt init W 0 = init := rfl

theorem wmassAt_succ (init : S → ℚ) (W : S → S → ℚ) (t : ℕ) (s' : S) :
    wmassAt init W (t + 1) s' = ∑ s, wmassAt init W t s * W s s' := rfl

theorem wmassAt_nonneg {init : S → ℚ} {W : S → S → ℚ}
    (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s') (t : ℕ) (s : S) :
    0 ≤ wmassAt init W t s := by
  induction t generalizing s with
  | zero => exact hinit s
  | succ t ih =>
    rw [wmassAt_succ]
    exact Finset.sum_nonneg fun s' _ =>
      mul_nonneg (ih s') (hW s' s)

/-- The stochastic instance tie: the chain evolution of the absorption
module is the weighted evolution at the chain's own kernel. -/
theorem massAt_eq_wmassAt (M : FinDTMC S) (t : ℕ) :
    massAt M t = wmassAt M.init M.step t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext s'
    rw [massAt_succ, wmassAt_succ, ih]

/-- One weighted step, in expectation form. -/
theorem wmassAt_expect_succ (init : S → ℚ) (W : S → S → ℚ)
    (V : S → ℚ) (t : ℕ) :
    (∑ s', wmassAt init W (t + 1) s' * V s') =
      ∑ s, wmassAt init W t s * ∑ s', W s s' * V s' := by
  calc (∑ s', wmassAt init W (t + 1) s' * V s')
      = ∑ s', (∑ s, wmassAt init W t s * W s s') * V s' :=
        Finset.sum_congr rfl fun s' _ => by rw [wmassAt_succ]
    _ = ∑ s', ∑ s, wmassAt init W t s * W s s' * V s' :=
        Finset.sum_congr rfl fun s' _ => by rw [Finset.sum_mul]
    _ = ∑ s, ∑ s', wmassAt init W t s * W s s' * V s' := Finset.sum_comm
    _ = ∑ s, wmassAt init W t s * ∑ s', W s s' * V s' := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s' _ => by ring

/-! ## The weighted contraction core -/

/-- **Weighted transfer contraction**: over any nonnegative weight
matrix and nonnegative initial mass, a one-step transfer of the
observable bounded by `c` times the observable at every state decays
the expectation as `cᵗ`.  No row-mass hypothesis and no sign
hypothesis on `V`. -/
theorem wmassAt_expect_le_of_contraction {init : S → ℚ} {W : S → S → ℚ}
    (V : S → ℚ) (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s')
    {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ s, (∑ s', W s s' * V s') ≤ c * V s) (t : ℕ) :
    (∑ s, wmassAt init W t s * V s) ≤ c ^ t * ∑ s, init s * V s := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : (∑ s', wmassAt init W (t + 1) s' * V s') ≤
        c * ∑ s, wmassAt init W t s * V s := by
      rw [wmassAt_expect_succ, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      calc wmassAt init W t s * ∑ s', W s s' * V s'
          ≤ wmassAt init W t s * (c * V s) :=
            mul_le_mul_of_nonneg_left (hcontr s)
              (wmassAt_nonneg hinit hW t s)
        _ = c * (wmassAt init W t s * V s) := by ring
    calc (∑ s', wmassAt init W (t + 1) s' * V s')
        ≤ c * ∑ s, wmassAt init W t s * V s := hstep
      _ ≤ c * (c ^ t * ∑ s, init s * V s) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (t + 1) * ∑ s, init s * V s := by ring

/-- The score face: a score-carrying row set `s(x)·K(x,y)` contracting
in the factored spelling is an instance of the weighted core. -/
theorem wmassAt_expect_le_of_contraction_scored {init : S → ℚ}
    {score : S → ℚ} {K : S → S → ℚ} (V : S → ℚ)
    (hinit : ∀ s, 0 ≤ init s) (hscore : ∀ s, 0 ≤ score s)
    (hK : ∀ s s', 0 ≤ K s s') {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ x, score x * (∑ y, K x y * V y) ≤ c * V x) (t : ℕ) :
    (∑ s, wmassAt init (fun x y => score x * K x y) t s * V s) ≤
      c ^ t * ∑ s, init s * V s := by
  refine wmassAt_expect_le_of_contraction V hinit
    (fun s s' => mul_nonneg (hscore s) (hK s s')) hc (fun x => ?_) t
  calc (∑ y, score x * K x y * V y)
      = score x * ∑ y, K x y * V y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ c * V x := hcontr x

/-- **Subsumption instance**: the proven stochastic core's exact
statement, re-derived from the weighted lemma (score `≡ 1` on a
stochastic kernel).  Deliberate restatement of
`massAt_expect_le_of_contraction`: the strengthened rule's premise-form
implies the old rule's conclusion, and the chain continues through the
`c = 1` face (`pathLaw_expect_le_of_genRow_nonpos`) to the incumbent
generator-form consumption — certificates admitted under the incumbent
stay valid under the strengthening, mechanically. -/
theorem massAt_expect_le_of_contraction_of_weighted (M : FinDTMC S)
    (V : S → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ s, (∑ s', M.step s s' * V s') ≤ c * V s) (t : ℕ) :
    (∑ s, massAt M t s * V s) ≤ c ^ t * ∑ s, massAt M 0 s * V s := by
  simpa [massAt_eq_wmassAt] using
    wmassAt_expect_le_of_contraction V M.init_nonneg M.step_nonneg
      hc hcontr t

/-- **The composed subsumption theorem** (the `generalize:` obligation
in one statement): from the INCUMBENT premise — a recomputed
nonpositive generator form on the compiled rows (C-SYS-GENFORM-DTMC) —
the strengthened rule's engine, instantiated at score `≡ 1`, `c = 1`,
region = the whole space, derives exactly the incumbent consumption's
conclusion on the path law.  Derived through the weighted engine and
the duality bridge, never by citing the incumbent's own proof: every
certificate admitted under the incumbent discharges under the
strengthened rule with an unchanged conclusion. -/
theorem qGenFormContraction_subsumes_genform [DecidableEq S]
    (M : FinDTMC S) (V : S → ℚ)
    (hg : ∀ s, genRow (compile M) V s ≤ 0) (t : ℕ) :
    expectQ (M.pathLaw t) (atLast V) ≤
      expectQ (M.pathLaw 0) (atLast V) := by
  rw [← massAt_dual M t V, ← massAt_dual M 0 V]
  have hcontr : ∀ s, (∑ s', M.step s s' * V s') ≤ 1 * V s := by
    intro s
    have h := hg s
    rw [genRow_compile] at h
    linarith
  simpa using
    massAt_expect_le_of_contraction_of_weighted M V zero_le_one hcontr t

/-! ## Regional packaging -/

section Regional

variable [DecidableEq S]

/-- The region-supported observable: `V` on `A`, zero elsewhere. -/
def indicatorOn (A : Finset S) (V : S → ℚ) : S → ℚ :=
  fun s => if s ∈ A then V s else 0

omit [Fintype S] in
theorem indicatorOn_of_mem {A : Finset S} {V : S → ℚ} {s : S}
    (hs : s ∈ A) : indicatorOn A V s = V s := if_pos hs

omit [Fintype S] in
theorem indicatorOn_of_not_mem {A : Finset S} {V : S → ℚ} {s : S}
    (hs : s ∉ A) : indicatorOn A V s = 0 := if_neg hs

/-- Weighting against the region-supported observable restricts the
sum to the region. -/
theorem sum_mul_indicatorOn (A : Finset S) (w V : S → ℚ) :
    (∑ s, w s * indicatorOn A V s) = ∑ s ∈ A, w s * V s := by
  simp only [indicatorOn, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Regional transfer contraction**: contraction checked only on the
region `A` (and only against destinations in `A`), plus no re-entry
from the complement, give the geometric decay of the observable's
expectation restricted to `A` — the global core at the
region-supported observable. -/
theorem wmassAt_expect_on_le_of_contraction_on {init : S → ℚ}
    {W : S → S → ℚ} (A : Finset S) (V : S → ℚ)
    (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s')
    {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ x ∈ A, (∑ y ∈ A, W x y * V y) ≤ c * V x)
    (hnoreentry : ∀ x ∉ A, ∀ y ∈ A, W x y = 0) (t : ℕ) :
    (∑ s ∈ A, wmassAt init W t s * V s) ≤
      c ^ t * ∑ s ∈ A, init s * V s := by
  have h := wmassAt_expect_le_of_contraction (indicatorOn A V) hinit hW
    hc (fun x => ?_) t
  · rw [sum_mul_indicatorOn, sum_mul_indicatorOn] at h
    exact h
  · by_cases hx : x ∈ A
    · rw [sum_mul_indicatorOn, indicatorOn_of_mem hx]
      exact hcontr x hx
    · rw [sum_mul_indicatorOn, indicatorOn_of_not_mem hx, mul_zero]
      have hzero : (∑ y ∈ A, W x y * V y) = 0 :=
        Finset.sum_eq_zero fun y hy => by
          rw [hnoreentry x hx y hy, zero_mul]
      rw [hzero]

end Regional

/-! ## Exit domination -/

/-- **Exit domination, per step**: an exit-weight observable dominated
by `κ·V` at every state inherits the contraction's geometric decay. -/
theorem wmassAt_exit_le_of_contraction {init : S → ℚ} {W : S → S → ℚ}
    (V e : S → ℚ) (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s')
    {c : ℚ} (hc : 0 ≤ c)
    (hcontr : ∀ s, (∑ s', W s s' * V s') ≤ c * V s)
    {κ : ℚ} (hκ : 0 ≤ κ) (hexit : ∀ s, e s ≤ κ * V s) (t : ℕ) :
    (∑ s, wmassAt init W t s * e s) ≤
      κ * c ^ t * ∑ s, init s * V s := by
  calc (∑ s, wmassAt init W t s * e s)
      ≤ ∑ s, wmassAt init W t s * (κ * V s) :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hexit s)
            (wmassAt_nonneg hinit hW t s)
    _ = κ * ∑ s, wmassAt init W t s * V s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ κ * (c ^ t * ∑ s, init s * V s) :=
        mul_le_mul_of_nonneg_left
          (wmassAt_expect_le_of_contraction V hinit hW hc hcontr t) hκ
    _ = κ * c ^ t * ∑ s, init s * V s := by ring

/-! ## Series bounds

Pure exact-rational series facts, stated as partial-sum bounds:
the geometric tail and the arithmetico-geometric tail. -/

/-- The arithmetico-geometric partial sum, exactly, in the
denominator-cleared form (an identity, so no hypotheses on `c`). -/
theorem sum_range_mul_pow_mul_eq (c : ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℚ) * c ^ i) * (1 - c) ^ 2 =
      c - (n : ℚ) * c ^ n + ((n : ℚ) - 1) * c ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    push_cast
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- The geometric partial sum is bounded by `1/(1-c)`. -/
theorem sum_range_pow_le {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, c ^ i) ≤ 1 / (1 - c) := by
  have h1c : (0 : ℚ) < 1 - c := by linarith
  rw [le_div_iff₀ h1c]
  have hmul : (∑ i ∈ Finset.range n, c ^ i) * (1 - c) = 1 - c ^ n := by
    have := geom_sum_mul c n
    -- `(c - 1) * ∑ = c ^ n - 1`; negate both sides.
    nlinarith [this]
  rw [hmul]
  have := pow_nonneg hc n
  linarith

/-- The arithmetico-geometric partial sum is bounded by `c/(1-c)²`. -/
theorem sum_range_mul_pow_le {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1)
    (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℚ) * c ^ i) ≤ c / (1 - c) ^ 2 := by
  have hsq : (0 : ℚ) < (1 - c) ^ 2 := by positivity
  rw [le_div_iff₀ hsq, sum_range_mul_pow_mul_eq]
  have hpow : (0 : ℚ) ≤ c ^ n := pow_nonneg hc n
  have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  have hps : c ^ (n + 1) = c ^ n * c := pow_succ c n
  nlinarith [mul_nonneg hpow (mul_nonneg hn (by linarith : (0 : ℚ) ≤ 1 - c)),
    mul_nonneg hpow hc]

/-- The geometric tail: `∑_{T ≤ t < T'} cᵗ ≤ cᵀ/(1-c)`. -/
theorem sum_Ico_pow_le {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1) (T T' : ℕ) :
    (∑ t ∈ Finset.Ico T T', c ^ t) ≤ c ^ T / (1 - c) := by
  have h1c : (0 : ℚ) < 1 - c := by linarith
  have hT : (0 : ℚ) ≤ c ^ T := pow_nonneg hc T
  rcases le_or_gt T T' with h | h
  · rw [Finset.sum_Ico_eq_sum_range]
    have hsplit : (∑ i ∈ Finset.range (T' - T), c ^ (T + i)) =
        c ^ T * ∑ i ∈ Finset.range (T' - T), c ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => pow_add c T i
    rw [hsplit, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (sum_range_pow_le hc hc1 _) hT
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- The arithmetico-geometric tail:
`∑_{T ≤ t < T'} t·cᵗ ≤ cᵀ·(T(1-c)+c)/(1-c)²`. -/
theorem sum_Ico_mul_pow_le {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1)
    (T T' : ℕ) :
    (∑ t ∈ Finset.Ico T T', (t : ℚ) * c ^ t) ≤
      c ^ T * ((T : ℚ) * (1 - c) + c) / (1 - c) ^ 2 := by
  have h1c : (0 : ℚ) < 1 - c := by linarith
  have hT : (0 : ℚ) ≤ c ^ T := pow_nonneg hc T
  have hTn : (0 : ℚ) ≤ (T : ℚ) := Nat.cast_nonneg T
  rcases le_or_gt T T' with h | h
  · rw [Finset.sum_Ico_eq_sum_range]
    calc (∑ i ∈ Finset.range (T' - T), ((T + i : ℕ) : ℚ) * c ^ (T + i))
        = ∑ i ∈ Finset.range (T' - T),
            (c ^ T * (T : ℚ) * c ^ i + c ^ T * ((i : ℚ) * c ^ i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_add]
          push_cast
          ring
      _ = c ^ T * (T : ℚ) * (∑ i ∈ Finset.range (T' - T), c ^ i) +
            c ^ T * ∑ i ∈ Finset.range (T' - T), (i : ℚ) * c ^ i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ c ^ T * (T : ℚ) * (1 / (1 - c)) + c ^ T * (c / (1 - c) ^ 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (sum_range_pow_le hc hc1 _)
              (mul_nonneg hT hTn))
            (mul_le_mul_of_nonneg_left (sum_range_mul_pow_le hc hc1 _) hT)
      _ = c ^ T * ((T : ℚ) * (1 - c) + c) / (1 - c) ^ 2 := by
          field_simp
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have hnum : (0 : ℚ) ≤ (T : ℚ) * (1 - c) + c :=
      add_nonneg (mul_nonneg hTn (by linarith)) hc
    exact div_nonneg (mul_nonneg hT hnum) (by positivity)

/-! ## Tail assemblies -/

/-- **Geometric tail assembly** (the `Z - Z_T` bound): under strict
contraction, the total exit weight over any window `[T, T')` is at
most `κ·cᵀ·⟨m₀,V⟩/(1-c)`.  The sign condition is the weakest usable
one — nonnegativity of the initial expectation `⟨m₀,V⟩`, implied by
`V ≥ 0` (a certificate component's usual posture) but not requiring
it. -/
theorem wmassAt_exit_tail_le {init : S → ℚ} {W : S → S → ℚ}
    (V e : S → ℚ) (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s')
    {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ s, (∑ s', W s s' * V s') ≤ c * V s)
    {κ : ℚ} (hκ : 0 ≤ κ) (hexit : ∀ s, e s ≤ κ * V s)
    (hIV : 0 ≤ ∑ s, init s * V s) (T T' : ℕ) :
    (∑ t ∈ Finset.Ico T T', ∑ s, wmassAt init W t s * e s) ≤
      κ * c ^ T * (∑ s, init s * V s) / (1 - c) := by
  have hκIV : (0 : ℚ) ≤ κ * ∑ s, init s * V s := mul_nonneg hκ hIV
  calc (∑ t ∈ Finset.Ico T T', ∑ s, wmassAt init W t s * e s)
      ≤ ∑ t ∈ Finset.Ico T T', κ * c ^ t * ∑ s, init s * V s :=
        Finset.sum_le_sum fun t _ =>
          wmassAt_exit_le_of_contraction V e hinit hW hc hcontr hκ
            hexit t
    _ = (κ * ∑ s, init s * V s) * ∑ t ∈ Finset.Ico T T', c ^ t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ (κ * ∑ s, init s * V s) * (c ^ T / (1 - c)) :=
        mul_le_mul_of_nonneg_left (sum_Ico_pow_le hc hc1 T T') hκIV
    _ = κ * c ^ T * (∑ s, init s * V s) / (1 - c) := by ring

/-- **First-moment tail assembly**: under strict contraction, the
time-weighted exit weight over any window `[T, T')` is at most
`κ·⟨m₀,V⟩·cᵀ·(T(1-c)+c)/(1-c)²` — the arithmetico-geometric bound
through the per-step domination.  Together with a finite-horizon
evaluation below `T` this brackets first-moment (expected-value)
readings of exit-stamped quantities; higher moments ride the same
reduction with `∑ tᵏcᵗ` closed forms and are deliberately left to the
species leg that first needs them. -/
theorem wmassAt_exit_moment_tail_le {init : S → ℚ} {W : S → S → ℚ}
    (V e : S → ℚ) (hinit : ∀ s, 0 ≤ init s) (hW : ∀ s s', 0 ≤ W s s')
    {c : ℚ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ s, (∑ s', W s s' * V s') ≤ c * V s)
    {κ : ℚ} (hκ : 0 ≤ κ) (hexit : ∀ s, e s ≤ κ * V s)
    (hIV : 0 ≤ ∑ s, init s * V s) (T T' : ℕ) :
    (∑ t ∈ Finset.Ico T T', (t : ℚ) * ∑ s, wmassAt init W t s * e s) ≤
      κ * (∑ s, init s * V s) * c ^ T * ((T : ℚ) * (1 - c) + c) /
        (1 - c) ^ 2 := by
  have hκIV : (0 : ℚ) ≤ κ * ∑ s, init s * V s := mul_nonneg hκ hIV
  calc (∑ t ∈ Finset.Ico T T', (t : ℚ) * ∑ s, wmassAt init W t s * e s)
      ≤ ∑ t ∈ Finset.Ico T T', (t : ℚ) * (κ * c ^ t * ∑ s, init s * V s) :=
        Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left
            (wmassAt_exit_le_of_contraction V e hinit hW hc hcontr hκ
              hexit t)
            (Nat.cast_nonneg t)
    _ = (κ * ∑ s, init s * V s) * ∑ t ∈ Finset.Ico T T', (t : ℚ) * c ^ t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ (κ * ∑ s, init s * V s) *
          (c ^ T * ((T : ℚ) * (1 - c) + c) / (1 - c) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_Ico_mul_pow_le hc hc1 T T') hκIV
    _ = κ * (∑ s, init s * V s) * c ^ T * ((T : ℚ) * (1 - c) + c) /
          (1 - c) ^ 2 := by ring

end Adequacy
end SuFunctor
