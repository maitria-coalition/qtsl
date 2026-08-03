import QtslAux.Imprecise.BellmanGapRule
import Mathlib.Tactic.FinCases

/-! # The crystal counterexample: the §8.5 fence is load-bearing

Negative witnesses for the Bellman-gap rule, companions to
`QtslAux.Imprecise.BellmanGapRule` (whose header introduces the design memo
cited here by its section numbers; these statements were likewise
preregistered before the proofs). Two sorry-free disproofs:

## 1. Once-drawn weather breaks the benchmark side (`once_drawn_rule_false`)

The rule's per-state premises price an **adaptive** weather — the robust
`QVal`'s min is re-quantified at every firing (per-firing weather, the memo
§8.5's fence). Where a demonic element is **once-drawn and
trajectory-consistent** ("one crystal, one draw"), a filler that learns the
crystal mid-run can beat the robust benchmark, and the rule as stated is
unsound — not conservative.

The witness (`crystalM`): start → (weather `w`) → state `h_w` (the crystal
revealed) → one matching round: reward 1 iff the action equals the firing's
weather. With `V ≡ 0` the premise rows (U), (L), (G) all hold **exactly**
(ε = 0): per-firing, the round-2 adversary re-draws the weather against the
chosen action, so every robust action value is 0. Yet with the crystal
drawn once:

* the learner `σ*` (play `a_i` at `h_i`) scores 1 against **every** crystal
  (`crystal_once_learner`) — it reads the draw off the state;
* the certified constant policy guarantees 0 (`crystal_once_pi`);

so the premises hold at ε = 0 while the once-drawn regret is 1 > 0: the
benchmark side (Claim A) fails, exactly as the memo says — and per-firing
the same comparison is sound (`crystal_perfiring_verdict`, an instance of
the main `fh_regret`). Repair, per the memo: augment the crystal into the
state carrier; over the augmented carrier the rule applies verbatim.

(A note on where the failure lands, since the guess is tempting the other
way: one might expect the dropped fence to break the achieved side, Claim B;
the memo §8.5 and this witness locate the failure on the benchmark side —
Claim A — with the combined regret conclusion failing in consequence.)

## 2. Greediness purchases the numerator's γ (`greediness_load_bearing`)

A one-state model where (U) and (L) hold at ε = 1, γ = 1/2, but π is NOT
greedy: the horizon-2 regret is 3, strictly above the strong constant
`2γε/(1−γ) = 2`. So the (G) rows cannot be dropped from `regret_le_const` —
the memo §8.2's "the γ in the numerator is purchased exactly by the
greediness premise," witnessed (the honest constant without (G) is
`2ε/(1−γ) = 4`, respected here: 3 < 4).
-/

namespace Qtsl.Imprecise
namespace BellmanGapCrystal

open Finset
open BellmanGap
open BellmanGap.RobustMDP

/-! ## Small-universe fold helpers -/

theorem inf'_fin_one (h : (univ : Finset (Fin 1)).Nonempty) (f : Fin 1 → ℚ) :
    (univ : Finset (Fin 1)).inf' h f = f 0 := by
  apply le_antisymm
  · exact Finset.inf'_le f (mem_univ 0)
  · apply Finset.le_inf'
    intro i _
    fin_cases i
    exact le_refl _

theorem inf'_fin_two (h : (univ : Finset (Fin 2)).Nonempty) (f : Fin 2 → ℚ) :
    (univ : Finset (Fin 2)).inf' h f = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le f (mem_univ 0))
      (Finset.inf'_le f (mem_univ 1))
  · apply Finset.le_inf'
    intro i _
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _

/-! ## Deterministic transition rows -/

/-- The Dirac row: all mass on `x`. -/
def detPMF {X : Type*} [Fintype X] [DecidableEq X] (x : X) : FinPMF X where
  prob := fun y => if y = x then 1 else 0
  nonneg := fun y => by by_cases h : y = x <;> simp [h]
  total := by simp [Finset.sum_ite_eq']

theorem detPMF_exp {X : Type*} [Fintype X] [DecidableEq X] (x : X)
    (f : X → ℚ) : (detPMF x).exp f = f x := by
  simp [detPMF, FinPMF.exp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']

/-! ## Once-drawn semantics (the fence's other side)

`valFixed` clamps the weather to a single draw `w` through the whole run;
`valOnce` takes the demonic minimum ONCE, outside the recursion — the
one-crystal-one-draw reading. Contrast `RobustMDP.valF`, whose `QVal`
re-quantifies the minimum at every firing. -/

/-- `n`-step value of policy sequence `σ` with the weather clamped to the
single draw `w` throughout. -/
def valFixed {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    (M : RobustMDP S A W) (w : W) (σ : ℕ → S → A) (VT : S → ℚ) :
    ℕ → S → ℚ
  | 0 => VT
  | n + 1 => fun s =>
      M.r s (σ n s) w + M.γ * (M.P s (σ n s) w).exp (valFixed M w σ VT n)

/-- Once-drawn (trajectory-consistent) demonic value: the weather minimum
taken once, over whole-run draws. -/
def valOnce {S A W : Type*} [Fintype S] [Fintype A] [Fintype W] [Nonempty W]
    (M : RobustMDP S A W) (σ : ℕ → S → A) (VT : S → ℚ) (n : ℕ) (s : S) : ℚ :=
  (univ : Finset W).inf' univ_nonempty fun w => valFixed M w σ VT n s

/-! ## The crystal model -/

/-- Transition targets: from `start` (state 0) the weather routes to `h_w`
(state 1 for w = 0, state 2 for w = 1); everything else falls to `done`
(state 3). Actions never move the state — only the reward round reads
them. -/
def next : Fin 4 → Fin 2 → Fin 4 := fun s w =>
  if s = 0 then (if w = 0 then 1 else 2) else 3

/-- The crystal comb, closed: reward 1 at the matching round (`h_i`, either
i) iff the action equals the FIRING's weather; γ = 1, horizon 2 (the memo
§8.3 finite-horizon instance). -/
def crystalM : RobustMDP (Fin 4) (Fin 2) (Fin 2) where
  P := fun s _a w => detPMF (next s w)
  r := fun s a w => if (s = 1 ∨ s = 2) ∧ a = w then 1 else 0
  γ := 1
  γ_nonneg := by norm_num

/-- The zero table (all stages). -/
def Vz : ℕ → Fin 4 → ℚ := fun _ _ => 0

/-- Zero per-stage residuals. -/
def εz : ℕ → ℚ := fun _ => 0

/-- The certified (constant) policy: always `a0`. -/
def piC : ℕ → Fin 4 → Fin 2 := fun _ _ => 0

/-- The crystal-learner: at `h_1` play `a1`, everywhere else `a0` — reads
the once-drawn crystal off the state that revealed it. -/
def sigmaStar : ℕ → Fin 4 → Fin 2 := fun _ s => if s = 2 then 1 else 0

/-- Per-firing robust action values all vanish on the zero table: the
round-2 adversary re-draws the weather against whatever action is chosen. -/
theorem crystal_QVal_zero (k : ℕ) (s : Fin 4) (a : Fin 2) :
    crystalM.QVal (Vz k) s a = 0 := by
  show crystalM.QVal (fun _ => 0) s a = 0
  unfold RobustMDP.QVal
  simp only [inf'_fin_two]
  fin_cases s <;> fin_cases a <;>
    norm_num [crystalM, next, detPMF_exp, min_def] <;> decide

/-- The premise rows (U_k), (L_k), (G_k) all hold EXACTLY (ε = 0) for the
constant policy on the zero table. -/
theorem crystal_premises :
    (∀ k (s : Fin 4) (a : Fin 2),
        crystalM.QVal (Vz k) s a ≤ Vz (k + 1) s + εz k) ∧
    (∀ k (s : Fin 4),
        Vz (k + 1) s - εz k ≤ crystalM.QVal (Vz k) s (piC k s)) ∧
    (∀ k (s : Fin 4) (a : Fin 2),
        crystalM.QVal (Vz k) s a ≤ crystalM.QVal (Vz k) s (piC k s)) := by
  refine ⟨fun k s a => ?_, fun k s => ?_, fun k s a => ?_⟩
  · rw [crystal_QVal_zero]
    show (0 : ℚ) ≤ 0 + 0
    norm_num
  · rw [crystal_QVal_zero]
    show (0 : ℚ) - 0 ≤ 0
    norm_num
  · rw [crystal_QVal_zero, crystal_QVal_zero]

/-- Per-firing, the learner gains nothing: its robust two-step value from
`start` is 0. -/
theorem crystal_perfiring_learner :
    crystalM.valF sigmaStar (Vz 0) 2 0 = 0 := by
  have h1 : ∀ s : Fin 4, crystalM.valF sigmaStar (Vz 0) 1 s = 0 := by
    intro s
    show crystalM.QVal (crystalM.valF sigmaStar (Vz 0) 0) s (sigmaStar 0 s) = 0
    exact crystal_QVal_zero 0 s (sigmaStar 0 s)
  show crystalM.QVal (crystalM.valF sigmaStar (Vz 0) 1) 0 (sigmaStar 1 0) = 0
  have hV : crystalM.valF sigmaStar (Vz 0) 1 = Vz 0 := funext h1
  rw [hV]
  exact crystal_QVal_zero 0 0 (sigmaStar 1 0)

/-- The per-firing verdict, as an instance of the MAIN theorem: with the
`crystal_premises` rows, `fh_regret` certifies the learner cannot beat the
constant policy — the rule is sound in exactly the semantics its operator
defines. -/
theorem crystal_perfiring_verdict :
    crystalM.valF sigmaStar (Vz 0) 2 0 ≤
      crystalM.valF piC (Vz 0) 2 0 + 2 * errF crystalM.γ εz 2 := by
  obtain ⟨hU, hL, -⟩ := crystal_premises
  have h := crystalM.fh_regret Vz εz piC hU hL sigmaStar 2 0
  linarith

/-- The learner's once-drawn two-step value is 1 against EITHER crystal:
the first firing reveals the draw, the second exploits it. -/
theorem crystal_fixed_learner (w : Fin 2) :
    valFixed crystalM w sigmaStar (Vz 0) 2 0 = 1 := by
  show crystalM.r 0 (sigmaStar 1 0) w +
      crystalM.γ * (crystalM.P 0 (sigmaStar 1 0) w).exp
        (valFixed crystalM w sigmaStar (Vz 0) 1) = 1
  rw [show crystalM.P 0 (sigmaStar 1 0) w = detPMF (next 0 w) from rfl,
    detPMF_exp]
  show crystalM.r 0 (sigmaStar 1 0) w + crystalM.γ *
      (crystalM.r (next 0 w) (sigmaStar 0 (next 0 w)) w + crystalM.γ *
        (crystalM.P (next 0 w) (sigmaStar 0 (next 0 w)) w).exp (Vz 0)) = 1
  fin_cases w <;>
    norm_num [crystalM, sigmaStar, next, Vz, detPMF_exp] <;> decide

theorem crystal_once_learner :
    valOnce crystalM sigmaStar (Vz 0) 2 0 = 1 := by
  unfold valOnce
  simp only [inf'_fin_two]
  rw [crystal_fixed_learner 0, crystal_fixed_learner 1]
  norm_num

/-- Against the crystal `w`, the constant policy scores 1 iff `w = 0`. -/
theorem crystal_fixed_pi (w : Fin 2) :
    valFixed crystalM w piC (Vz 0) 2 0 = if w = 0 then 1 else 0 := by
  show crystalM.r 0 (piC 1 0) w +
      crystalM.γ * (crystalM.P 0 (piC 1 0) w).exp
        (valFixed crystalM w piC (Vz 0) 1) = if w = 0 then 1 else 0
  rw [show crystalM.P 0 (piC 1 0) w = detPMF (next 0 w) from rfl, detPMF_exp]
  show crystalM.r 0 (piC 1 0) w + crystalM.γ *
      (crystalM.r (next 0 w) (piC 0 (next 0 w)) w + crystalM.γ *
        (crystalM.P (next 0 w) (piC 0 (next 0 w)) w).exp (Vz 0)) =
      if w = 0 then 1 else 0
  fin_cases w <;>
    norm_num +decide [crystalM, piC, next, Vz, detPMF_exp]

/-- Once-drawn, the constant policy guarantees nothing: the crystal `w = 1`
defeats it. -/
theorem crystal_once_pi :
    valOnce crystalM piC (Vz 0) 2 0 = 0 := by
  unfold valOnce
  simp only [inf'_fin_two]
  rw [crystal_fixed_pi 0, crystal_fixed_pi 1]
  norm_num

/-- **The fence, load-bearing** (memo §8.5): the premise rows hold at ε = 0,
yet under once-drawn weather the rule's conclusion is FALSE — the learner
beats the certified policy by 1 where the rule concluded regret ≤ 0. The
per-state premises are sound only where residual demonic freedom is
per-firing; a one-crystal-one-draw element must be augmented into the state
carrier (after which the rule applies verbatim over the augmented
carrier). -/
theorem once_drawn_rule_false :
    ((∀ k (s : Fin 4) (a : Fin 2),
        crystalM.QVal (Vz k) s a ≤ Vz (k + 1) s + εz k) ∧
     (∀ k (s : Fin 4),
        Vz (k + 1) s - εz k ≤ crystalM.QVal (Vz k) s (piC k s)) ∧
     (∀ k (s : Fin 4) (a : Fin 2),
        crystalM.QVal (Vz k) s a ≤ crystalM.QVal (Vz k) s (piC k s))) ∧
    ¬ (valOnce crystalM sigmaStar (Vz 0) 2 0 -
        valOnce crystalM piC (Vz 0) 2 0 ≤ 2 * errF crystalM.γ εz 2) := by
  refine ⟨crystal_premises, ?_⟩
  rw [crystal_once_learner, crystal_once_pi]
  have hz : errF crystalM.γ εz 2 = 0 := errF_zero crystalM.γ 2
  rw [hz]
  norm_num

/-! ## Greediness purchases the γ in the numerator -/

/-- One state, two actions, no weather: `r(a0) = 0`, `r(a1) = 2`,
γ = 1/2. -/
def greedyM : RobustMDP (Fin 1) (Fin 2) (Fin 1) where
  P := fun _ _ _ => detPMF 0
  r := fun _ a _ => if a = 1 then 2 else 0
  γ := 1 / 2
  γ_nonneg := by norm_num

/-- One-step values in the greediness model, in closed form. -/
theorem greedy_QVal (V : Fin 1 → ℚ) (s : Fin 1) (a : Fin 2) :
    greedyM.QVal V s a = (if a = 1 then 2 else 0) + 1 / 2 * V 0 := by
  unfold RobustMDP.QVal
  simp only [inf'_fin_one]
  simp [greedyM, detPMF_exp]

/-- **(G) cannot be dropped from the strong constant** (memo §8.2): with
`V ≡ 2`, ε = 1, the rows (U) and (L) hold but π = const `a0` is not greedy,
and the horizon-2 regret is 3 > 2 = `2γε/(1−γ)`. The γ in the numerator is
purchased exactly by the greediness rows. -/
theorem greediness_load_bearing :
    (∀ (s : Fin 1) (a : Fin 2),
        greedyM.QVal (fun _ => 2) s a ≤ (fun _ : Fin 1 => (2 : ℚ)) s + 1) ∧
    (∀ s : Fin 1,
        (fun _ : Fin 1 => (2 : ℚ)) s - 1 ≤
          greedyM.QVal (fun _ => 2) s ((fun _ : Fin 1 => (0 : Fin 2)) s)) ∧
    2 * greedyM.γ * 1 / (1 - greedyM.γ) <
      (greedyM.Tpol (fun _ => 1))^[1 + 1] (fun _ => 2) 0 -
        (greedyM.Tpol (fun _ => 0))^[1 + 1] (fun _ => 2) 0 := by
  refine ⟨fun s a => ?_, fun s => ?_, ?_⟩
  · rw [greedy_QVal]
    fin_cases a <;> norm_num
  · rw [greedy_QVal]
    norm_num
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    have hT1 : greedyM.Tpol (fun _ => 1) (fun _ => 2) 0 = 3 := by
      show greedyM.QVal (fun _ => 2) 0 1 = 3
      rw [greedy_QVal]
      norm_num
    have hT0 : greedyM.Tpol (fun _ => 0) (fun _ => 2) 0 = 1 := by
      show greedyM.QVal (fun _ => 2) 0 0 = 1
      rw [greedy_QVal]
      norm_num
    have hTT1 : greedyM.Tpol (fun _ => 1)
        (greedyM.Tpol (fun _ => 1) (fun _ => 2)) 0 = 2 + 1 / 2 * 3 := by
      show greedyM.QVal (greedyM.Tpol (fun _ => 1) (fun _ => 2)) 0 1 = _
      rw [greedy_QVal, hT1]
      norm_num
    have hTT0 : greedyM.Tpol (fun _ => 0)
        (greedyM.Tpol (fun _ => 0) (fun _ => 2)) 0 = 0 + 1 / 2 * 1 := by
      show greedyM.QVal (greedyM.Tpol (fun _ => 0) (fun _ => 2)) 0 0 = _
      rw [greedy_QVal, hT0]
      norm_num
    rw [hTT1, hTT0]
    show 2 * greedyM.γ * 1 / (1 - greedyM.γ) < 2 + 1 / 2 * 3 - (0 + 1 / 2 * 1)
    norm_num [greedyM]

end BellmanGapCrystal
end Qtsl.Imprecise
