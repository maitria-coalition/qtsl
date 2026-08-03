import QtslAux.Imprecise.Credal
import Mathlib.Logic.Function.Iterate

/-! # Soundness of the Bellman-gap rule

Finite-carrier, exact-ℚ soundness for the `SRegretLE` Bellman-gap rule,
following the rule's design memo (cited below as "the memo", by its section
numbers). The statements were preregistered — committed before any of these
proofs was attempted. Everything is finitary — no fixpoint existence, no limits, no
measure theory: the theorems bound the difference of `N`-step iterates for
every `N`, which is the form a certificate checker consumes.

## The model, and where the §8.5 fence lives

`RobustMDP S A W`: finite state carrier `S`, finite action set `A` at the
hole, finite residual demonic seat `W` (weather), transition rows as
`FinPMF S` (exact-ℚ), reward gate `r : S → A → W → ℚ` (the reward may read
the firing's weather), discount `γ ≥ 0`. The one-step per-state robust value

  `QVal M V s a = min_w [ r s a w + γ · E_{P s a w}[V] ]`

takes its weather minimum **inside** the one-step operator, so every theorem
below about iterates of `Tpol`/`Topt` is a theorem about values whose demonic
residue is re-quantified per firing — the memo's soundness fence ("per-firing
weather = the operator's min re-quantified per application") is encoded in
the definition the theorems quantify over. The once-drawn alternative (the
weather minimum outside the recursion) genuinely breaks the benchmark side:
`QtslAux.Imprecise.BellmanGapCrystal.once_drawn_rule_false`.

## Premise rows (per state / per state-action, exact-ℚ)

* **(U)** super-solution residual: `QVal M V s a ≤ V s + ε` — feeds the
  benchmark side (`claimA`);
* **(L)** sub-solution residual: `V s − ε ≤ QVal M V s (π s)` — feeds the
  achieved side (`claimB'`);
* **(G)** greediness: `QVal M V s a ≤ QVal M V s (π s)`;
* **(Gδ)** δ-greediness: `Topt M V s − δ ≤ QVal M V s (π s)`.

## Main results

* `claimA` [(U)]: every filler's `(n+1)`-step value is
  `≤ Topt V + gsum γ n · ε`;
* `claimB'` [(L)]: the pure achieved-side telescope, anchored at `Tpol π V`;
* `claimB` [(L)+(G)]: the achieved side anchored at `Topt V`;
* `regret_le` [(U)+(L)+(G)]: regret at every horizon `≤ 2 · gsum γ n · ε`,
  hence (`regret_le_const`, `γ < 1`, `ε ≥ 0`) `≤ 2γε/(1−γ)` — the memo's
  headline constant, confirmed at exactly this premise shape;
* `regret_le_graded` [(U)+(L)+(Gδ)]: `≤ 2 · gsum γ n · ε + δ`, hence
  (`regret_le_graded_const`) `≤ 2γε/(1−γ) + δ`. **Tighter than the memo's
  §8.2 `+ δ/(1−γ)`**: δ enters once at the anchor and is never fed back
  through the operator, so it takes no `1/(1−γ)` inflation (the memo's
  constant follows a fortiori, `bound_graded_le_memo`);
* `eps_zero_exact` [ε = 0]: exact optimality at every horizon — the
  "optimal, exactly" claim class;
* `regret_zero_terminal`: the zero-terminal form with the
  `2γ^(n+1)·‖V‖∞`-class tail — the memo §8.6's checker-consumable shape;
* `bound_mono_bracket`: monotonicity of `x ↦ 2xε/(1−x)` on `(-∞, 1)`, the
  lemma the §8.4 rational-bracket schema (`c ≥ e^{−θ}`) leans on (stated
  without the prereg's `0 ≤ γ` hypothesis — it is not needed);
* `fh_claimA`/`fh_claimB`/`fh_regret`/`fh_exact`: the finite-horizon
  telescope (memo §8.3) — time-indexed tables, conclusion `2·Σ ε_t` at γ = 1
  (`fh_regret_sum`), exact optimality by finite induction at `ε ≡ 0`.
  Note (prereg'd): the greediness rows are *not* load-bearing for the
  finite-horizon constant — both sides anchor at `V`; greediness buys only
  the discounted form's γ-numerator (anchor at `Topt V`).
-/

namespace Qtsl.Imprecise
namespace BellmanGap

open Finset

/-! ## Lattice-fold helpers over `univ` -/

section Helpers

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem infu_le (f : ι → ℚ) (i : ι) :
    univ.inf' univ_nonempty f ≤ f i :=
  Finset.inf'_le f (mem_univ i)

theorem le_infu {f : ι → ℚ} {a : ℚ} (h : ∀ i, a ≤ f i) :
    a ≤ univ.inf' univ_nonempty f :=
  Finset.le_inf' univ_nonempty f fun i _ => h i

theorem le_supu (f : ι → ℚ) (i : ι) :
    f i ≤ univ.sup' univ_nonempty f :=
  Finset.le_sup' f (mem_univ i)

theorem supu_le {f : ι → ℚ} {a : ℚ} (h : ∀ i, f i ≤ a) :
    univ.sup' univ_nonempty f ≤ a :=
  Finset.sup'_le univ_nonempty f fun i _ => h i

theorem infu_mono {f g : ι → ℚ} (h : ∀ i, f i ≤ g i) :
    univ.inf' univ_nonempty f ≤ univ.inf' univ_nonempty g :=
  le_infu fun i => le_trans (infu_le f i) (h i)

theorem supu_mono {f g : ι → ℚ} (h : ∀ i, f i ≤ g i) :
    univ.sup' univ_nonempty f ≤ univ.sup' univ_nonempty g :=
  supu_le fun i => le_trans (h i) (le_supu g i)

theorem infu_add_const (f : ι → ℚ) (c : ℚ) :
    univ.inf' univ_nonempty (fun i => f i + c) =
      univ.inf' univ_nonempty f + c := by
  apply le_antisymm
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' univ_nonempty f
    calc univ.inf' univ_nonempty (fun i => f i + c) ≤ f i + c :=
          infu_le (fun i => f i + c) i
      _ = univ.inf' univ_nonempty f + c := by rw [hi]
  · exact le_infu fun i => add_le_add (infu_le f i) (le_refl c)

theorem supu_add_const (f : ι → ℚ) (c : ℚ) :
    univ.sup' univ_nonempty (fun i => f i + c) =
      univ.sup' univ_nonempty f + c := by
  apply le_antisymm
  · exact supu_le fun i => add_le_add (le_supu f i) (le_refl c)
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' univ_nonempty f
    calc univ.sup' univ_nonempty f + c = f i + c := by rw [hi]
      _ ≤ univ.sup' univ_nonempty (fun i => f i + c) :=
          le_supu (fun i => f i + c) i

end Helpers

/-- Expectation of a constant shift (specialization of `FinPMF.exp_add` +
`FinPMF.exp_const`). -/
theorem exp_add_const {X : Type*} [Fintype X] (p : FinPMF X) (f : X → ℚ)
    (c : ℚ) : p.exp (fun x => f x + c) = p.exp f + c := by
  have h := p.exp_add f (fun _ => c)
  rw [p.exp_const c] at h
  exact h

/-! ## The error ladders -/

/-- `gsum γ n = γ + γ² + ⋯ + γⁿ`, by the recursion the telescopes actually
use: `gsum γ 0 = 0`, `gsum γ (n+1) = γ + γ · gsum γ n`. -/
def gsum (γ : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => γ + γ * gsum γ n

theorem gsum_eq_sum (γ : ℚ) : ∀ n, gsum γ n = ∑ k ∈ Finset.range n, γ ^ (k + 1)
  | 0 => by simp [gsum]
  | n + 1 => by
    show γ + γ * gsum γ n = _
    rw [gsum_eq_sum γ n, Finset.mul_sum, Finset.sum_range_succ']
    simp only [← pow_succ', zero_add, pow_one]
    ring

theorem gsum_nonneg {γ : ℚ} (hγ : 0 ≤ γ) : ∀ n, 0 ≤ gsum γ n
  | 0 => le_refl 0
  | n + 1 => by
    have h1 := gsum_nonneg hγ n
    have h2 := mul_nonneg hγ h1
    simp only [gsum]
    linarith

/-- The division-free geometric bound: `gsum γ n · (1 − γ) ≤ γ`. -/
theorem gsum_bound {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ n, gsum γ n * (1 - γ) ≤ γ
  | 0 => by simpa [gsum] using hγ0
  | n + 1 => by
    have ih := gsum_bound hγ0 hγ1 n
    have h := mul_le_mul_of_nonneg_left ih hγ0
    simp only [gsum]
    nlinarith

/-- Monotonicity of `x ↦ 2xε/(1−x)` below 1 — the lemma the §8.4
rational-bracket schema (`e^{−θ} ≤ c < 1`, conclude at `c`) leans on. -/
theorem bound_mono_bracket {γ c ε : ℚ} (hgc : γ ≤ c) (hc : c < 1)
    (hε : 0 ≤ ε) :
    2 * γ * ε / (1 - γ) ≤ 2 * c * ε / (1 - c) := by
  have h1γ : (0 : ℚ) < 1 - γ := by linarith
  have h1c : (0 : ℚ) < 1 - c := by linarith
  rw [div_le_div_iff₀ h1γ h1c]
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hgc)]

/-- The finite-horizon error ladder: `errF γ ε 0 = 0`,
`errF γ ε (n+1) = ε n + γ · errF γ ε n` (at γ = 1: `Σ_{k<n} ε k`). -/
def errF (γ : ℚ) (ε : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ε n + γ * errF γ ε n

theorem errF_one (ε : ℕ → ℚ) : ∀ n, errF 1 ε n = ∑ k ∈ Finset.range n, ε k
  | 0 => by simp [errF]
  | n + 1 => by
    show ε n + 1 * errF 1 ε n = _
    rw [errF_one ε n, Finset.sum_range_succ, one_mul]
    ring

theorem errF_zero (γ : ℚ) : ∀ n, errF γ (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by
    show (fun _ => (0 : ℚ)) n + γ * errF γ (fun _ => 0) n = 0
    rw [errF_zero γ n]
    ring

/-! ## The model -/

/-- A finite MDP with a residual demonic weather seat: transitions and
rewards read the firing's weather `w : W`; `P s a w` is an exact-ℚ
probability row. The discount `γ` is a plain rational — when the
discount arises from a rate (`γ = e^{−θ}`, not rational) this `γ` plays
the §8.4 rational bracket witness `c ≥ e^{−θ}`. -/
structure RobustMDP (S A W : Type*) [Fintype S] [Fintype A] [Fintype W] where
  /-- Transition law: state, action, weather ↦ next-state distribution. -/
  P : S → A → W → FinPMF S
  /-- Reward gate; may read the firing's weather. -/
  r : S → A → W → ℚ
  /-- Discount factor (the §8.4 bracket `c` in the rate-θ setting). -/
  γ : ℚ
  γ_nonneg : 0 ≤ γ

namespace RobustMDP

variable {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
variable [Nonempty W]
variable (M : RobustMDP S A W)

/-- Per-state robust action value: the weather minimum is INSIDE the
one-step operator — per-firing (adaptive) weather, the §8.5 fence. -/
def QVal (V : S → ℚ) (s : S) (a : A) : ℚ :=
  univ.inf' univ_nonempty fun w => M.r s a w + M.γ * (M.P s a w).exp V

/-- The policy (achieved-side) Bellman operator `T_π`. -/
def Tpol (π : S → A) (V : S → ℚ) (s : S) : ℚ :=
  M.QVal V s (π s)

/-! ### Monotonicity and constant-shift laws -/

theorem QVal_mono {V V' : S → ℚ} (h : ∀ x, V x ≤ V' x) (s : S) (a : A) :
    M.QVal V s a ≤ M.QVal V' s a := by
  unfold QVal
  apply infu_mono
  intro w
  have hexp := (M.P s a w).exp_mono h
  have hmul := mul_le_mul_of_nonneg_left hexp M.γ_nonneg
  linarith

theorem QVal_add_const (V : S → ℚ) (c : ℚ) (s : S) (a : A) :
    M.QVal (fun x => V x + c) s a = M.QVal V s a + M.γ * c := by
  unfold QVal
  have hfg : (fun w => M.r s a w + M.γ * (M.P s a w).exp (fun x => V x + c))
      = fun w => (M.r s a w + M.γ * (M.P s a w).exp V) + M.γ * c := by
    funext w
    rw [exp_add_const]
    ring
  rw [hfg]
  exact infu_add_const _ _

theorem QVal_sub_const (V : S → ℚ) (c : ℚ) (s : S) (a : A) :
    M.QVal (fun x => V x - c) s a = M.QVal V s a - M.γ * c := by
  have h := M.QVal_add_const V (-c) s a
  simpa [sub_eq_add_neg, mul_neg] using h

theorem Tpol_mono (π : S → A) {V V' : S → ℚ} (h : ∀ x, V x ≤ V' x) (s : S) :
    M.Tpol π V s ≤ M.Tpol π V' s :=
  M.QVal_mono h s (π s)

theorem Tpol_add_const (π : S → A) (V : S → ℚ) (c : ℚ) (s : S) :
    M.Tpol π (fun x => V x + c) s = M.Tpol π V s + M.γ * c :=
  M.QVal_add_const V c s (π s)

theorem Tpol_sub_const (π : S → A) (V : S → ℚ) (c : ℚ) (s : S) :
    M.Tpol π (fun x => V x - c) s = M.Tpol π V s - M.γ * c :=
  M.QVal_sub_const V c s (π s)

/-! ### Iterate laws -/

theorem iter_Tpol_mono (π : S → A) {V V' : S → ℚ} (h : ∀ x, V x ≤ V' x) :
    ∀ n s, (M.Tpol π)^[n] V s ≤ (M.Tpol π)^[n] V' s := by
  intro n
  induction n with
  | zero => intro s; simpa using h s
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact M.Tpol_mono π (fun x => ih x) s

theorem iter_Tpol_add_const (π : S → A) (V : S → ℚ) (c : ℚ) :
    ∀ n s, (M.Tpol π)^[n] (fun x => V x + c) s =
      (M.Tpol π)^[n] V s + M.γ ^ n * c := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfun : (M.Tpol π)^[n] (fun x => V x + c) =
        fun x => (M.Tpol π)^[n] V x + M.γ ^ n * c :=
      funext fun x => ih x
    rw [hfun, M.Tpol_add_const]
    ring

theorem iter_Tpol_sub_const (π : S → A) (V : S → ℚ) (c : ℚ) (n : ℕ) (s : S) :
    (M.Tpol π)^[n] (fun x => V x - c) s =
      (M.Tpol π)^[n] V s - M.γ ^ n * c := by
  have h := M.iter_Tpol_add_const π V (-c) n s
  simpa [sub_eq_add_neg, mul_neg] using h

/-! ### Claim B′ — the pure achieved-side telescope [(L) only] -/

/-- **Claim B′** (the pure telescope). From the sub-solution rows (L) alone,
the certified policy's `(n+1)`-step value stays within `gsum γ n · ε` of its
one-step anchor `Tpol π V`. -/
theorem claimB' {V : S → ℚ} {ε : ℚ} {π : S → A}
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s)) :
    ∀ n s, M.Tpol π V s - gsum M.γ n * ε ≤ (M.Tpol π)^[n + 1] V s := by
  intro n
  induction n with
  | zero =>
    intro s
    have h1 : (M.Tpol π)^[0 + 1] V s = M.Tpol π V s := by simp
    rw [h1]
    simp only [gsum]
    linarith
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply']
    have hL' : ∀ x, V x - ε ≤ M.Tpol π V x := fun x => hL x
    calc M.Tpol π V s - gsum M.γ (n + 1) * ε
        = (M.Tpol π V s - M.γ * ε) - M.γ * (gsum M.γ n * ε) := by
          simp only [gsum]
          ring
      _ = M.Tpol π (fun x => V x - ε) s - M.γ * (gsum M.γ n * ε) := by
          rw [M.Tpol_sub_const]
      _ ≤ M.Tpol π (M.Tpol π V) s - M.γ * (gsum M.γ n * ε) := by
          have h2 := M.Tpol_mono π hL' s
          linarith
      _ = M.Tpol π (fun x => M.Tpol π V x - gsum M.γ n * ε) s := by
          rw [M.Tpol_sub_const]
      _ ≤ M.Tpol π ((M.Tpol π)^[n + 1] V) s :=
          M.Tpol_mono π (fun x => ih x) s

/-! ### The finite-horizon telescope (memo §8.3)

Time-indexed tables `V k` (`k` = steps remaining), per-stage residuals
`ε k`, policy sequences `σ k`; backward-induction values with the SHARED
terminal `V 0`. No contraction, no limit — pure telescoping; at `ε ≡ 0`,
exact optimality by finite induction. This is the schema that the
"optimal, exactly" certificate instances instantiate (`retChanSum`,
step-limit truncation, γ = 1).

Prereg'd observation: the greediness rows (G_t) are NOT load-bearing for
the memo's finite-horizon constant `Σ 2ε_t` — both sides anchor at `V`. -/

/-- `n`-step backward-induction value of policy sequence `σ` with terminal
`VT`; `σ k` acts with `k+1` steps remaining. Per-firing weather: each stage
takes the robust one-step `QVal`. -/
def valF (σ : ℕ → S → A) (VT : S → ℚ) : ℕ → S → ℚ
  | 0 => VT
  | n + 1 => fun s => M.QVal (valF σ VT n) s (σ n s)

/-- Finite-horizon Claim A [(U_k) only]: every filler sequence's value is
bounded by the table plus the accumulated residuals. -/
theorem fh_claimA (V : ℕ → S → ℚ) (ε : ℕ → ℚ)
    (hU : ∀ k s a, M.QVal (V k) s a ≤ V (k + 1) s + ε k) (σ' : ℕ → S → A) :
    ∀ n s, M.valF σ' (V 0) n s ≤ V n s + errF M.γ ε n := by
  intro n
  induction n with
  | zero => intro s; simp [valF, errF]
  | succ n ih =>
    intro s
    calc M.valF σ' (V 0) (n + 1) s
        = M.QVal (M.valF σ' (V 0) n) s (σ' n s) := by simp [valF]
      _ ≤ M.QVal (fun x => V n x + errF M.γ ε n) s (σ' n s) :=
          M.QVal_mono (fun x => ih x) s (σ' n s)
      _ = M.QVal (V n) s (σ' n s) + M.γ * errF M.γ ε n :=
          M.QVal_add_const (V n) (errF M.γ ε n) s (σ' n s)
      _ ≤ V (n + 1) s + ε n + M.γ * errF M.γ ε n := by
          have h := hU n s (σ' n s)
          linarith
      _ = V (n + 1) s + errF M.γ ε (n + 1) := by
          simp only [errF]
          ring

/-- Finite-horizon Claim B [(L_k) only]. -/
theorem fh_claimB (V : ℕ → S → ℚ) (ε : ℕ → ℚ) (π : ℕ → S → A)
    (hL : ∀ k s, V (k + 1) s - ε k ≤ M.QVal (V k) s (π k s)) :
    ∀ n s, V n s - errF M.γ ε n ≤ M.valF π (V 0) n s := by
  intro n
  induction n with
  | zero => intro s; simp [valF, errF]
  | succ n ih =>
    intro s
    calc V (n + 1) s - errF M.γ ε (n + 1)
        = (V (n + 1) s - ε n) - M.γ * errF M.γ ε n := by
          simp only [errF]
          ring
      _ ≤ M.QVal (V n) s (π n s) - M.γ * errF M.γ ε n := by
          have h := hL n s
          linarith
      _ = M.QVal (fun x => V n x - errF M.γ ε n) s (π n s) :=
          (M.QVal_sub_const (V n) (errF M.γ ε n) s (π n s)).symm
      _ ≤ M.QVal (M.valF π (V 0) n) s (π n s) :=
          M.QVal_mono (fun x => ih x) s (π n s)
      _ = M.valF π (V 0) (n + 1) s := by simp [valF]

/-- The finite-horizon rule: regret `≤ 2 · errF γ ε n` (at γ = 1:
`Σ_{t<n} 2ε_t`, the memo §8.3's conclusion). -/
theorem fh_regret (V : ℕ → S → ℚ) (ε : ℕ → ℚ) (π : ℕ → S → A)
    (hU : ∀ k s a, M.QVal (V k) s a ≤ V (k + 1) s + ε k)
    (hL : ∀ k s, V (k + 1) s - ε k ≤ M.QVal (V k) s (π k s))
    (σ' : ℕ → S → A) (n : ℕ) (s : S) :
    M.valF σ' (V 0) n s - M.valF π (V 0) n s ≤ 2 * errF M.γ ε n := by
  have hA := M.fh_claimA V ε hU σ' n s
  have hB := M.fh_claimB V ε π hL n s
  linarith

/-- The γ = 1 (undiscounted, `retChanSum`) reading: regret `≤ 2 Σ ε_t`. -/
theorem fh_regret_sum (V : ℕ → S → ℚ) (ε : ℕ → ℚ) (π : ℕ → S → A)
    (hγ : M.γ = 1)
    (hU : ∀ k s a, M.QVal (V k) s a ≤ V (k + 1) s + ε k)
    (hL : ∀ k s, V (k + 1) s - ε k ≤ M.QVal (V k) s (π k s))
    (σ' : ℕ → S → A) (n : ℕ) (s : S) :
    M.valF σ' (V 0) n s - M.valF π (V 0) n s ≤
      2 * ∑ k ∈ Finset.range n, ε k := by
  have h := M.fh_regret V ε π hU hL σ' n s
  rw [hγ, errF_one] at h
  exact h

/-- ε ≡ 0: the "optimal, exactly" schema — exact optimality by finite
induction; the exact-DP tables are the entire certificate. -/
theorem fh_exact (V : ℕ → S → ℚ) (π : ℕ → S → A)
    (hU : ∀ k s a, M.QVal (V k) s a ≤ V (k + 1) s)
    (hL : ∀ k s, V (k + 1) s ≤ M.QVal (V k) s (π k s))
    (σ' : ℕ → S → A) (n : ℕ) (s : S) :
    M.valF σ' (V 0) n s ≤ M.valF π (V 0) n s := by
  have hU0 : ∀ k s a, M.QVal (V k) s a ≤ V (k + 1) s + (fun _ => (0 : ℚ)) k := by
    simpa using hU
  have hL0 : ∀ k s, V (k + 1) s - (fun _ => (0 : ℚ)) k ≤
      M.QVal (V k) s (π k s) := by
    simpa using hL
  have h := M.fh_regret V (fun _ => 0) π hU0 hL0 σ' n s
  rw [errF_zero] at h
  linarith

/-! ### The benchmark operator (needs a nonempty action seat) -/

variable [Nonempty A]

/-- The optimal (benchmark-side) Bellman operator `T`. -/
def Topt (V : S → ℚ) (s : S) : ℚ :=
  univ.sup' univ_nonempty fun a => M.QVal V s a

theorem Topt_mono {V V' : S → ℚ} (h : ∀ x, V x ≤ V' x) (s : S) :
    M.Topt V s ≤ M.Topt V' s :=
  supu_mono fun a => M.QVal_mono h s a

theorem Topt_add_const (V : S → ℚ) (c : ℚ) (s : S) :
    M.Topt (fun x => V x + c) s = M.Topt V s + M.γ * c := by
  unfold Topt
  have hfg : (fun a => M.QVal (fun x => V x + c) s a)
      = fun a => M.QVal V s a + M.γ * c := by
    funext a
    exact M.QVal_add_const V c s a
  rw [hfg]
  exact supu_add_const _ _

theorem Tpol_le_Topt (π : S → A) (V : S → ℚ) (s : S) :
    M.Tpol π V s ≤ M.Topt V s :=
  le_supu (fun a => M.QVal V s a) (π s)

/-- Greediness ((G) rows) makes the two operators agree at `V`. -/
theorem Tpol_eq_Topt {V : S → ℚ} {π : S → A}
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s)) (s : S) :
    M.Tpol π V s = M.Topt V s :=
  le_antisymm (M.Tpol_le_Topt π V s) (supu_le fun a => hG s a)

/-! ### Claim A — the benchmark telescope [(U) only] -/

/-- **Claim A** (memo §8.2). From the super-solution rows (U), every
type-correct filler's `(n+1)`-step value from terminal `V` is bounded by
`Topt V + gsum γ n · ε` — the benchmark side anchored at `Topt V`. The
standard argument's one direction: no minimax interchange, no
rectangularity, per-filler operator bounded by `Topt` pointwise plus
monotone induction. -/
theorem claimA {V : S → ℚ} {ε : ℚ}
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε) (π' : S → A) :
    ∀ n s, (M.Tpol π')^[n + 1] V s ≤ M.Topt V s + gsum M.γ n * ε := by
  intro n
  induction n with
  | zero =>
    intro s
    have h1 : (M.Tpol π')^[0 + 1] V s = M.Tpol π' V s := by simp
    rw [h1]
    have h2 := M.Tpol_le_Topt π' V s
    simp only [gsum]
    linarith
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply']
    have hTopt_le : ∀ x, M.Topt V x ≤ V x + ε :=
      fun x => supu_le fun a => hU x a
    calc M.Tpol π' ((M.Tpol π')^[n + 1] V) s
        ≤ M.Tpol π' (fun x => M.Topt V x + gsum M.γ n * ε) s :=
          M.Tpol_mono π' (fun x => ih x) s
      _ = M.Tpol π' (M.Topt V) s + M.γ * (gsum M.γ n * ε) :=
          M.Tpol_add_const π' (M.Topt V) (gsum M.γ n * ε) s
      _ ≤ M.Topt (M.Topt V) s + M.γ * (gsum M.γ n * ε) := by
          have h3 := M.Tpol_le_Topt π' (M.Topt V) s
          linarith
      _ ≤ M.Topt (fun x => V x + ε) s + M.γ * (gsum M.γ n * ε) := by
          have h4 := M.Topt_mono hTopt_le s
          linarith
      _ = M.Topt V s + M.γ * ε + M.γ * (gsum M.γ n * ε) := by
          rw [M.Topt_add_const]
      _ = M.Topt V s + gsum M.γ (n + 1) * ε := by
          simp only [gsum]
          ring

/-- **Claim B** [(L)+(G)]: the achieved side anchored at `Topt V` — the
anchor agreement that purchases the γ in the rule's numerator. -/
theorem claimB {V : S → ℚ} {ε : ℚ} {π : S → A}
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s)) :
    ∀ n s, M.Topt V s - gsum M.γ n * ε ≤ (M.Tpol π)^[n + 1] V s := by
  intro n s
  have h := M.claimB' hL n s
  rw [M.Tpol_eq_Topt hG s] at h
  exact h

/-! ### The rule: regret bounds at every horizon -/

/-- **The Bellman-gap rule, strong form** [(U)+(L)+(G)]: at every horizon,
every filler's value exceeds the certified policy's by at most
`2 · gsum γ n · ε` — both telescopes anchored at `Topt V`. -/
theorem regret_le {V : S → ℚ} {ε : ℚ} {π : S → A}
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε)
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] V s - (M.Tpol π)^[n + 1] V s ≤
      2 * gsum M.γ n * ε := by
  have hA := M.claimA hU π' n s
  have hB := M.claimB hL hG n s
  linarith

/-- **The graded (δ-greedy) form** [(U)+(L)+(Gδ)]: regret
`≤ 2 · gsum γ n · ε + δ`. Tighter than the memo §8.2's
`2γε/(1−γ) + δ/(1−γ)`: δ enters once at the anchor (`Tpol π V ≥ Topt V − δ`)
and is never fed back through the operator, so it takes no `1/(1−γ)`
inflation. -/
theorem regret_le_graded {V : S → ℚ} {ε δ : ℚ} {π : S → A}
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε)
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hGd : ∀ s, M.Topt V s - δ ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] V s - (M.Tpol π)^[n + 1] V s ≤
      2 * gsum M.γ n * ε + δ := by
  have hA := M.claimA hU π' n s
  have hB' := M.claimB' hL n s
  have hAnchor : M.Topt V s - δ ≤ M.Tpol π V s := hGd s
  linarith

/-- The charter's constant, confirmed: with `γ < 1` and `ε ≥ 0`, regret
`≤ 2γε/(1−γ)` at every horizon, under exactly the (U)+(L)+(G) premise
shape. -/
theorem regret_le_const {V : S → ℚ} {ε : ℚ} {π : S → A}
    (hγ1 : M.γ < 1) (hε : 0 ≤ ε)
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε)
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] V s - (M.Tpol π)^[n + 1] V s ≤
      2 * M.γ * ε / (1 - M.γ) := by
  have h1γ : (0 : ℚ) < 1 - M.γ := by linarith
  have h := M.regret_le hU hL hG π' n s
  have hb := gsum_bound M.γ_nonneg hγ1 n
  rw [le_div_iff₀ h1γ]
  have k1 : ((M.Tpol π')^[n + 1] V s - (M.Tpol π)^[n + 1] V s) * (1 - M.γ) ≤
      (2 * gsum M.γ n * ε) * (1 - M.γ) :=
    mul_le_mul_of_nonneg_right h (le_of_lt h1γ)
  have k2 : gsum M.γ n * (1 - M.γ) * (2 * ε) ≤ M.γ * (2 * ε) :=
    mul_le_mul_of_nonneg_right hb (mul_nonneg (by norm_num) hε)
  nlinarith [k1, k2]

/-- Graded closed-form twin: `≤ 2γε/(1−γ) + δ`. -/
theorem regret_le_graded_const {V : S → ℚ} {ε δ : ℚ} {π : S → A}
    (hγ1 : M.γ < 1) (hε : 0 ≤ ε)
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε)
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hGd : ∀ s, M.Topt V s - δ ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] V s - (M.Tpol π)^[n + 1] V s ≤
      2 * M.γ * ε / (1 - M.γ) + δ := by
  have h1γ : (0 : ℚ) < 1 - M.γ := by linarith
  have h := M.regret_le_graded hU hL hGd π' n s
  have hb := gsum_bound M.γ_nonneg hγ1 n
  have hgs : 2 * gsum M.γ n * ε ≤ 2 * M.γ * ε / (1 - M.γ) := by
    rw [le_div_iff₀ h1γ]
    have k2 : gsum M.γ n * (1 - M.γ) * (2 * ε) ≤ M.γ * (2 * ε) :=
      mul_le_mul_of_nonneg_right hb (mul_nonneg (by norm_num) hε)
    nlinarith [k2]
  linarith

/-- The memo §8.2's stated graded constant follows a fortiori from the
tighter one: `B + δ ≤ B + δ/(1−γ)` for `0 ≤ δ`, `0 ≤ γ < 1`. -/
theorem bound_graded_le_memo {γ δ B : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hδ : 0 ≤ δ) : B + δ ≤ B + δ / (1 - γ) := by
  have h1γ : (0 : ℚ) < 1 - γ := by linarith
  have hd : δ ≤ δ / (1 - γ) := by
    rw [le_div_iff₀ h1γ]
    nlinarith
  linarith

/-- ε = 0 (the "optimal, exactly" class): the certified policy is
exactly optimal at every horizon. -/
theorem eps_zero_exact {V : S → ℚ} {π : S → A}
    (hU : ∀ s a, M.QVal V s a ≤ V s)
    (hL : ∀ s, V s ≤ M.QVal V s (π s))
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] V s ≤ (M.Tpol π)^[n + 1] V s := by
  have hU0 : ∀ s a, M.QVal V s a ≤ V s + 0 := by simpa using hU
  have hL0 : ∀ s, V s - 0 ≤ M.QVal V s (π s) := by simpa using hL
  have h := M.regret_le hU0 hL0 hG π' n s
  have hz : 2 * gsum M.γ n * 0 = 0 := by ring
  linarith

/-- The zero-terminal (checker-consumable) form: regret between zero-terminal
`(n+1)`-step returns `≤ 2·gsum γ n·ε + 2·γ^(n+1)·b` where `b` bounds `‖V‖∞` —
the memo §8.6's `2γε/(1−γ) + 2γ^N‖V‖∞`-class tail bound, division-free. -/
theorem regret_zero_terminal {V : S → ℚ} {ε b : ℚ} {π : S → A}
    (hb : ∀ x, |V x| ≤ b)
    (hU : ∀ s a, M.QVal V s a ≤ V s + ε)
    (hL : ∀ s, V s - ε ≤ M.QVal V s (π s))
    (hG : ∀ s a, M.QVal V s a ≤ M.QVal V s (π s))
    (π' : S → A) (n : ℕ) (s : S) :
    (M.Tpol π')^[n + 1] (fun _ => 0) s - (M.Tpol π)^[n + 1] (fun _ => 0) s ≤
      2 * gsum M.γ n * ε + 2 * M.γ ^ (n + 1) * b := by
  have hup : ∀ x, (fun _ => (0 : ℚ)) x ≤ V x + b := fun x => by
    have h := (abs_le.mp (hb x)).1
    show (0 : ℚ) ≤ V x + b
    linarith
  have hlo : ∀ x, V x - b ≤ (fun _ => (0 : ℚ)) x := fun x => by
    have h := (abs_le.mp (hb x)).2
    show V x - b ≤ (0 : ℚ)
    linarith
  have h1 := M.iter_Tpol_mono π' hup (n + 1) s
  have h2 := M.iter_Tpol_add_const π' V b (n + 1) s
  have h3 := M.claimA hU π' n s
  have h4 := M.iter_Tpol_mono π hlo (n + 1) s
  have h5 := M.iter_Tpol_sub_const π V b (n + 1) s
  have h6 := M.claimB hL hG n s
  linarith

end RobustMDP

end BellmanGap
end Qtsl.Imprecise
