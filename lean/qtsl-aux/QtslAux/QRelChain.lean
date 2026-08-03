import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! # Finite Markov chains: lumping, drift, absorption, and relational bounds

This module develops finite-state Markov chains concretely as row-stochastic
matrices and proves the ingredients for relational (two-chain) certificates:
exact lumping, supermartingale drift bounds, absorption analysis, and
total-variation / expectation-gap soundness theorems for product couplings.

Principal declarations:

* `IsMarkov`, `IsDist`, `step`, `law`, `push`: row-stochastic kernels,
  distributions, one-step evolution, the `n`-step law, and pushforward along
  a state map; `isDist_law`, `isDist_push` preserve distributionhood.
* `PushKernel π K Q` with `push_step` and `push_law`: exact lumping commutes
  with the dynamics at every horizon.
* `expect_step_le`, `expect_law_le`: a drift function `V` with
  `∑ t, K s t * V t ≤ V s` has non-increasing expectation along the chain.
* `finalMass K μ₀ a`: the limiting mass in an absorbing state `a`
  (`K a a = 1`), with monotone convergence `tendsto_law_finalMass`;
  `finalExpect_le` bounds terminal expectations by the initial drift value.
* `exists_uniform_reach`, `absorbed_decay`, `tendsto_absorbedMass_one`: if
  from every state some finite horizon reaches the absorbing set with
  positive probability, the absorbed mass tends to `1` geometrically.
* `tvDist` and `tvDist_push_le_disagree`: the total-variation distance between
  two labelings of a coupled final law is at most the disagreement mass.
* Product-chain machinery (`sum_finalMass_snd_eq`, `sum_finalMass_fst_eq`,
  `finalLaw`, `push_finalLaw_fst`, `push_finalLaw_snd`): a coupling chain `K`
  on `σ₁ × σ₂` lumping to marginals `K₁, K₂` has final-law marginals equal to
  the marginal final laws.
* `sound_QRelTV` / `sound_QRelTV_of_reach`: soundness of the relational
  total-variation certificate — a coupling drift function `V` that is `≥ 1`
  wherever the two output labels disagree bounds the TV distance between the
  pushed terminal laws by the initial expectation bound `b`.
* `sound_QRelExpGap` / `sound_QRelExpGap_of_reach`: the analogous bound
  `|E₁ - E₂| ≤ b` for the gap between terminal expectations of `v₁, v₂` when
  `V` dominates `|v₁ - v₂|` on the absorbing rectangle.
-/

namespace Qtsl

namespace QRelChain

open Finset Filter Topology

noncomputable section

variable {α β L : Type*}

structure IsMarkov [Fintype α] (K : α → α → ℝ) : Prop where
  nonneg : ∀ s t, 0 ≤ K s t
  rowSum : ∀ s, ∑ t, K s t = 1

structure IsDist [Fintype α] (μ : α → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ μ s
  total : ∑ s, μ s = 1

def step [Fintype α] (K : α → α → ℝ) (μ : α → ℝ) : α → ℝ :=
  fun t => ∑ s, μ s * K s t

def law [Fintype α] (K : α → α → ℝ) (μ₀ : α → ℝ) : ℕ → α → ℝ
  | 0 => μ₀
  | n + 1 => step K (law K μ₀ n)

def push [Fintype α] [DecidableEq β] (π : α → β) (μ : α → ℝ) : β → ℝ :=
  fun b => ∑ s ∈ univ.filter fun s => π s = b, μ s

section Basic

variable [Fintype α] {K : α → α → ℝ} {μ₀ μ : α → ℝ}

@[simp] theorem law_zero : law K μ₀ 0 = μ₀ := rfl

@[simp] theorem law_succ (n : ℕ) : law K μ₀ (n + 1) = step K (law K μ₀ n) := rfl

theorem step_nonneg (hK : ∀ s t, 0 ≤ K s t) (hμ : ∀ s, 0 ≤ μ s) (t : α) :
    0 ≤ step K μ t :=
  sum_nonneg fun s _ => mul_nonneg (hμ s) (hK s t)

theorem law_nonneg (hK : ∀ s t, 0 ≤ K s t) (hμ₀ : ∀ s, 0 ≤ μ₀ s) :
    ∀ n s, 0 ≤ law K μ₀ n s
  | 0, s => hμ₀ s
  | n + 1, t => step_nonneg hK (law_nonneg hK hμ₀ n) t

theorem sum_step (hrow : ∀ s, ∑ t, K s t = 1) : ∑ t, step K μ t = ∑ s, μ s := by
  unfold step
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow, mul_one]

theorem sum_law (hrow : ∀ s, ∑ t, K s t = 1) :
    ∀ n, ∑ s, law K μ₀ n s = ∑ s, μ₀ s
  | 0 => rfl
  | n + 1 => by rw [law_succ, sum_step hrow, sum_law hrow n]

theorem isDist_law (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (n : ℕ) :
    IsDist (law K μ₀ n) :=
  ⟨law_nonneg hK.nonneg hμ₀.nonneg n,
    by rw [sum_law hK.rowSum n, hμ₀.total]⟩

theorem law_le_one (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (n : ℕ) (s : α) :
    law K μ₀ n s ≤ 1 := by
  have h := single_le_sum (f := law K μ₀ n)
    (fun t _ => (isDist_law hK hμ₀ n).nonneg t) (mem_univ s)
  exact h.trans_eq (isDist_law hK hμ₀ n).total

end Basic

section Push

variable [Fintype α] [DecidableEq β]

theorem push_nonneg {π : α → β} {μ : α → ℝ} (hμ : ∀ s, 0 ≤ μ s) (b : β) :
    0 ≤ push π μ b :=
  sum_nonneg fun s _ => hμ s

theorem sum_push [Fintype β] (π : α → β) (μ : α → ℝ) :
    ∑ b, push π μ b = ∑ s, μ s := by
  unfold push
  exact Finset.sum_fiberwise univ π μ

theorem isDist_push [Fintype β] {π : α → β} {μ : α → ℝ} (hμ : IsDist μ) :
    IsDist (push π μ) :=
  ⟨push_nonneg hμ.nonneg, by rw [sum_push, hμ.total]⟩

def PushKernel (π : α → β) (K : α → α → ℝ) (Q : β → β → ℝ) : Prop :=
  ∀ s, push π (K s) = Q (π s)

theorem push_step [Fintype β] {π : α → β} {K : α → α → ℝ} {Q : β → β → ℝ}
    (h : PushKernel π K Q) (μ : α → ℝ) :
    push π (step K μ) = step Q (push π μ) := by
  funext b
  have key : ∀ s : α, (∑ t ∈ univ.filter fun t => π t = b, K s t) = Q (π s) b :=
    fun s => congrFun (h s) b
  show (∑ t ∈ univ.filter fun t => π t = b, ∑ s, μ s * K s t)
      = ∑ c, push π μ c * Q c b
  rw [Finset.sum_comm]
  have h1 : ∀ s : α, (∑ t ∈ univ.filter (fun t => π t = b), μ s * K s t)
      = μ s * Q (π s) b := fun s => by rw [← Finset.mul_sum, key s]
  rw [Finset.sum_congr rfl fun s _ => h1 s,
    ← Finset.sum_fiberwise univ π fun s => μ s * Q (π s) b]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (∑ s ∈ univ.filter fun s => π s = c, μ s * Q (π s) b)
      = ∑ s ∈ univ.filter fun s => π s = c, μ s * Q c b from
    Finset.sum_congr rfl fun s hs => by rw [(mem_filter.1 hs).2], ← Finset.sum_mul]
  rfl

theorem push_law [Fintype β] {π : α → β} {K : α → α → ℝ} {Q : β → β → ℝ}
    (h : PushKernel π K Q) (μ₀ : α → ℝ) :
    ∀ n, push π (law K μ₀ n) = law Q (push π μ₀) n
  | 0 => rfl
  | n + 1 => by rw [law_succ, push_step h, push_law h μ₀ n, law_succ]

end Push

section Drift

variable [Fintype α] {K : α → α → ℝ} {V μ₀ μ : α → ℝ}

theorem expect_step_le (hμ : ∀ s, 0 ≤ μ s)
    (hdrift : ∀ s, ∑ t, K s t * V t ≤ V s) :
    ∑ t, step K μ t * V t ≤ ∑ s, μ s * V s := by
  have expand : (∑ t, step K μ t * V t) = ∑ s, μ s * ∑ t, K s t * V t := by
    unfold step
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [expand]
  exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hdrift s) (hμ s)

theorem expect_law_le (hK : ∀ s t, 0 ≤ K s t) (hμ₀ : ∀ s, 0 ≤ μ₀ s)
    (hdrift : ∀ s, ∑ t, K s t * V t ≤ V s) :
    ∀ n, ∑ s, law K μ₀ n s * V s ≤ ∑ s, μ₀ s * V s
  | 0 => le_rfl
  | n + 1 =>
    (expect_step_le (law_nonneg hK hμ₀ n) hdrift).trans
      (expect_law_le hK hμ₀ hdrift n)

end Drift

section Absorb

variable [Fintype α] {K : α → α → ℝ} {μ₀ : α → ℝ}

theorem law_mono_absorbing (hK : ∀ s t, 0 ≤ K s t) (hμ₀ : ∀ s, 0 ≤ μ₀ s)
    {a : α} (haa : K a a = 1) :
    Monotone fun n => law K μ₀ n a := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h := single_le_sum (f := fun s => law K μ₀ n s * K s a)
    (fun s _ => mul_nonneg (law_nonneg hK hμ₀ n s) (hK s a)) (mem_univ a)
  rw [haa, mul_one] at h
  exact h

def finalMass (K : α → α → ℝ) (μ₀ : α → ℝ) (a : α) : ℝ :=
  ⨆ n, law K μ₀ n a

theorem bddAbove_range_law (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (a : α) :
    BddAbove (Set.range fun n => law K μ₀ n a) := by
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  exact law_le_one hK hμ₀ n a

theorem finalMass_nonneg (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (a : α) :
    0 ≤ finalMass K μ₀ a :=
  (law_nonneg hK.nonneg hμ₀.nonneg 0 a).trans
    (le_ciSup (bddAbove_range_law hK hμ₀ a) 0)

theorem tendsto_law_finalMass (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    {a : α} (haa : K a a = 1) :
    Tendsto (fun n => law K μ₀ n a) atTop (𝓝 (finalMass K μ₀ a)) :=
  tendsto_atTop_ciSup (law_mono_absorbing hK.nonneg hμ₀.nonneg haa)
    (bddAbove_range_law hK hμ₀ a)

theorem sum_finalMass_eq_one {A : Finset α} (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    (hfr : ∀ a ∈ A, K a a = 1)
    (habs : Tendsto (fun n => ∑ a ∈ A, law K μ₀ n a) atTop (𝓝 1)) :
    ∑ a ∈ A, finalMass K μ₀ a = 1 :=
  tendsto_nhds_unique
    (tendsto_finsetSum A fun a ha => tendsto_law_finalMass hK hμ₀ (hfr a ha))
    habs

theorem finalExpect_le {V gv : α → ℝ} {A : Finset α} {b : ℝ}
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hfr : ∀ a ∈ A, K a a = 1)
    (hgV : ∀ a ∈ A, gv a ≤ V a) (hV0 : ∀ s, 0 ≤ V s)
    (hdrift : ∀ s, ∑ t, K s t * V t ≤ V s) (hb : ∑ s, μ₀ s * V s ≤ b) :
    ∑ a ∈ A, finalMass K μ₀ a * gv a ≤ b := by
  have hn : ∀ n, (∑ a ∈ A, law K μ₀ n a * gv a) ≤ b := by
    intro n
    have h1 : (∑ a ∈ A, law K μ₀ n a * gv a) ≤ ∑ a ∈ A, law K μ₀ n a * V a :=
      sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hgV a ha)
        (law_nonneg hK.nonneg hμ₀.nonneg n a)
    have h2 : (∑ a ∈ A, law K μ₀ n a * V a) ≤ ∑ s, law K μ₀ n s * V s :=
      sum_le_sum_of_subset_of_nonneg (subset_univ A) fun s _ _ =>
        mul_nonneg (law_nonneg hK.nonneg hμ₀.nonneg n s) (hV0 s)
    exact h1.trans (h2.trans
      ((expect_law_le hK.nonneg hμ₀.nonneg hdrift n).trans hb))
  have hlim : Tendsto (fun n => ∑ a ∈ A, law K μ₀ n a * gv a) atTop
      (𝓝 (∑ a ∈ A, finalMass K μ₀ a * gv a)) :=
    tendsto_finsetSum A fun a ha =>
      (tendsto_law_finalMass hK hμ₀ (hfr a ha)).mul_const (gv a)
  exact le_of_tendsto hlim (Eventually.of_forall hn)

end Absorb

section Reach

variable [Fintype α] [DecidableEq α] {K : α → α → ℝ} {μ₀ : α → ℝ} {A : Finset α}

omit [Fintype α] in

def pointMass (s : α) : α → ℝ := fun t => if t = s then 1 else 0

omit [Fintype α] in
theorem pointMass_nonneg (s t : α) : 0 ≤ pointMass s t := by
  unfold pointMass
  split
  · exact zero_le_one
  · exact le_rfl

theorem isDist_pointMass (s : α) : IsDist (pointMass s) := by
  refine ⟨pointMass_nonneg s, ?_⟩
  unfold pointMass
  simp

theorem absorbing_row (hK : IsMarkov K) {a : α} (haa : K a a = 1) :
    ∀ t, K a t = pointMass a t := by
  intro t
  unfold pointMass
  by_cases ht : t = a
  · rw [if_pos ht, ht, haa]
  · rw [if_neg ht]
    have hsplit : K a a + ∑ u ∈ univ.erase a, K a u = ∑ u, K a u :=
      Finset.add_sum_erase univ (K a) (mem_univ a)
    have hzero : ∑ u ∈ univ.erase a, K a u = 0 := by
      rw [hK.rowSum a] at hsplit
      linarith [haa ▸ hsplit]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun u _ => hK.nonneg a u).1 hzero t
      (Finset.mem_erase.2 ⟨ht, mem_univ t⟩)

theorem step_pointMass (K : α → α → ℝ) (a : α) :
    step K (pointMass a) = K a := by
  funext t
  unfold step pointMass
  simp

theorem law_pointMass_absorbing (hK : IsMarkov K) {a : α} (haa : K a a = 1) :
    ∀ n, law K (pointMass a) n = pointMass a
  | 0 => rfl
  | n + 1 => by
    rw [law_succ, law_pointMass_absorbing hK haa n, step_pointMass]
    exact funext (absorbing_row hK haa)

omit [DecidableEq α] in

theorem law_add (K : α → α → ℝ) (μ₀ : α → ℝ) (m : ℕ) :
    ∀ n, law K μ₀ (m + n) = law K (law K μ₀ m) n
  | 0 => rfl
  | n + 1 => by
    show law K μ₀ ((m + n) + 1) = law K (law K μ₀ m) (n + 1)
    rw [law_succ, law_add K μ₀ m n, law_succ]

theorem law_eq_sum_pointMass :
    ∀ n t, law K μ₀ n t = ∑ s, μ₀ s * law K (pointMass s) n t
  | 0, t => by
    show μ₀ t = _
    unfold pointMass
    simp [mul_ite]
  | n + 1, t => by
    show step K (law K μ₀ n) t = _
    unfold step
    simp_rw [law_eq_sum_pointMass n, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rfl

omit [DecidableEq α] in
theorem absorbedMass_mono (hK : ∀ s t, 0 ≤ K s t) (hμ₀ : ∀ s, 0 ≤ μ₀ s)
    (hfr : ∀ a ∈ A, K a a = 1) :
    Monotone fun n => ∑ a ∈ A, law K μ₀ n a := fun _ _ hmn =>
  sum_le_sum fun a ha => law_mono_absorbing hK hμ₀ (hfr a ha) hmn

omit [DecidableEq α] in
theorem absorbedMass_le_one (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (n : ℕ) :
    ∑ a ∈ A, law K μ₀ n a ≤ 1 := by
  have h : (∑ a ∈ A, law K μ₀ n a) ≤ ∑ s, law K μ₀ n s :=
    sum_le_sum_of_subset_of_nonneg (subset_univ A) fun s _ _ =>
      law_nonneg hK.nonneg hμ₀.nonneg n s
  exact h.trans_eq (isDist_law hK hμ₀ n).total

theorem exists_uniform_reach (hK : IsMarkov K) (hfr : ∀ a ∈ A, K a a = 1)
    (hreach : ∀ s, ∃ k, 0 < ∑ a ∈ A, law K (pointMass s) k a) :
    ∃ N ε, 0 < ε ∧ 1 ≤ N ∧ ∀ s, ε ≤ ∑ a ∈ A, law K (pointMass s) N a := by
  classical
  by_cases hα : Nonempty α
  · choose k hk using hreach
    haveI := hα
    set N := max 1 (Finset.univ.sup k) with hN
    have hN1 : 1 ≤ N := le_max_left _ _
    have hmono : ∀ s : α, Monotone fun n => ∑ a ∈ A, law K (pointMass s) n a :=
      fun s => absorbedMass_mono hK.nonneg (pointMass_nonneg s) hfr
    have hks : ∀ s : α, k s ≤ N := fun s =>
      le_max_of_le_right (Finset.le_sup (mem_univ s))
    have hpos : ∀ s : α, 0 < ∑ a ∈ A, law K (pointMass s) N a := fun s =>
      lt_of_lt_of_le (hk s) (hmono s (hks s))
    obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image univ
      (fun s => ∑ a ∈ A, law K (pointMass s) N a) Finset.univ_nonempty
    exact ⟨N, _, hpos s₀, hN1, fun s => hs₀ s (mem_univ s)⟩
  · exact ⟨1, 1, one_pos, le_rfl, fun s => absurd ⟨s⟩ hα⟩

theorem absorbed_decay {μ : α → ℝ} (hK : IsMarkov K) (hμ : IsDist μ)
    (hfr : ∀ a ∈ A, K a a = 1) {N : ℕ} {ε : ℝ}
    (hε : ∀ s, ε ≤ ∑ a ∈ A, law K (pointMass s) N a) :
    1 - ∑ a ∈ A, law K μ N a ≤
      (1 - ε) * (1 - ∑ s ∈ A, μ s) := by
  classical
  set R : α → ℝ := fun s => ∑ a ∈ A, law K (pointMass s) N a with hR
  have hswap : (∑ a ∈ A, law K μ N a) = ∑ s, μ s * R s := by
    simp_rw [hR, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => law_eq_sum_pointMass N a
  have hRabs : ∀ s ∈ A, R s = 1 := by
    intro s hs
    show (∑ a ∈ A, law K (pointMass s) N a) = 1
    rw [law_pointMass_absorbing hK (hfr s hs) N]
    unfold pointMass
    simp [hs]
  have hsplit : (∑ s ∈ A, μ s * R s) + ∑ s ∈ Aᶜ, μ s * R s
      = ∑ s, μ s * R s := Finset.sum_add_sum_compl A _
  have hsplitμ : (∑ s ∈ A, μ s) + ∑ s ∈ Aᶜ, μ s = 1 := by
    rw [Finset.sum_add_sum_compl, hμ.total]
  have hA : (∑ s ∈ A, μ s * R s) = ∑ s ∈ A, μ s := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hRabs s hs, mul_one]
  have hAc : ε * (∑ s ∈ Aᶜ, μ s) ≤ ∑ s ∈ Aᶜ, μ s * R s := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun s _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hε s) (hμ.nonneg s)
  have hkey : (∑ s ∈ A, μ s) + ε * (1 - ∑ s ∈ A, μ s) ≤ ∑ a ∈ A, law K μ N a := by
    rw [hswap, ← hsplit, hA]
    have h1 : (∑ s ∈ Aᶜ, μ s) = 1 - ∑ s ∈ A, μ s := by linarith
    rw [← h1]
    linarith [hAc]
  have hring : 1 - ((∑ s ∈ A, μ s) + ε * (1 - ∑ s ∈ A, μ s))
      = (1 - ε) * (1 - ∑ s ∈ A, μ s) := by ring
  linarith [hkey, hring]

theorem tendsto_absorbedMass_one (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    (hfr : ∀ a ∈ A, K a a = 1)
    (hreach : ∀ s, ∃ k, 0 < ∑ a ∈ A, law K (pointMass s) k a) :
    Tendsto (fun n => ∑ a ∈ A, law K μ₀ n a) atTop (𝓝 1) := by
  classical
  have hne : Nonempty α := by
    by_contra h
    have : (∑ s, μ₀ s) = 0 := by
      haveI := not_nonempty_iff.1 h
      simp
    rw [hμ₀.total] at this
    exact one_ne_zero this
  obtain ⟨N, ε, hε0, hN1, hε⟩ := exists_uniform_reach hK hfr hreach
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := hne
    exact (hε s).trans (absorbedMass_le_one hK (isDist_pointMass s) N)
  have hmono := absorbedMass_mono (μ₀ := μ₀) hK.nonneg hμ₀.nonneg hfr
  have hbdd : BddAbove (Set.range fun n => ∑ a ∈ A, law K μ₀ n a) := by
    refine ⟨1, ?_⟩
    rintro x ⟨n, rfl⟩
    exact absorbedMass_le_one hK hμ₀ n
  have hlim : Tendsto (fun n => ∑ a ∈ A, law K μ₀ n a) atTop
      (𝓝 (⨆ n, ∑ a ∈ A, law K μ₀ n a)) := tendsto_atTop_ciSup hmono hbdd
  have hsub : ∀ m : ℕ, 1 - (1 - ε) ^ m ≤ ∑ a ∈ A, law K μ₀ (m * N) a := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, sub_self, Nat.zero_mul]
      exact sum_nonneg fun a _ => law_nonneg hK.nonneg hμ₀.nonneg 0 a
    | succ m ih =>
      have hdist : IsDist (law K μ₀ (m * N)) := isDist_law hK hμ₀ _
      have hdecay := absorbed_decay hK hdist hfr hε
      have hstep : (∑ a ∈ A, law K μ₀ ((m + 1) * N) a)
          = ∑ a ∈ A, law K (law K μ₀ (m * N)) N a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [show (m + 1) * N = m * N + N by ring, law_add]
      have hgeom : (1 - ε) * (1 - ∑ s ∈ A, law K μ₀ (m * N) s)
          ≤ (1 - ε) * (1 - ε) ^ m := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith [ih]
      rw [hstep]
      have := hdecay.trans hgeom
      have hpow : (1 - ε) * (1 - ε) ^ m = (1 - ε) ^ (m + 1) := by ring
      linarith [hpow ▸ this]
  have hgeo : Tendsto (fun m : ℕ => 1 - (1 - ε) ^ m) atTop (𝓝 1) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by linarith : (0:ℝ) ≤ 1 - ε) (by linarith : 1 - ε < 1)
    simpa using tendsto_const_nhds.sub h
  have hNmono : StrictMono fun m : ℕ => m * N := fun a b h =>
    (Nat.mul_lt_mul_right (lt_of_lt_of_le one_pos hN1)).mpr h
  have hsubseq : Tendsto (fun m : ℕ => ∑ a ∈ A, law K μ₀ (m * N) a) atTop
      (𝓝 (⨆ n, ∑ a ∈ A, law K μ₀ n a)) := hlim.comp hNmono.tendsto_atTop
  have hone : Tendsto (fun m : ℕ => ∑ a ∈ A, law K μ₀ (m * N) a) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hgeo tendsto_const_nhds hsub
      fun m => absorbedMass_le_one hK hμ₀ (m * N)
  have hsup : (⨆ n, ∑ a ∈ A, law K μ₀ n a) = 1 :=
    tendsto_nhds_unique hsubseq hone
  exact hsup ▸ hlim

end Reach

def tvDist [Fintype L] (p q : L → ℝ) : ℝ := (∑ l, |p l - q l|) / 2

theorem tvDist_push_le_disagree {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂]
    [Fintype L] [DecidableEq L] (γ : σ₁ × σ₂ → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (f : σ₁ → L) (g : σ₂ → L) :
    tvDist (push (fun p : σ₁ × σ₂ => f p.1) γ) (push (fun p : σ₁ × σ₂ => g p.2) γ) ≤
      ∑ p ∈ univ.filter fun p : σ₁ × σ₂ => f p.1 ≠ g p.2, γ p := by
  classical
  set D : Finset (σ₁ × σ₂) := univ.filter fun p => f p.1 ≠ g p.2 with hD
  have key : ∀ l, |push (fun p : σ₁ × σ₂ => f p.1) γ l -
        push (fun p : σ₁ × σ₂ => g p.2) γ l| ≤
      (∑ p ∈ D.filter fun p => f p.1 = l, γ p) +
        ∑ p ∈ D.filter fun p => g p.2 = l, γ p := by
    intro l
    have hagree : (univ.filter fun p : σ₁ × σ₂ => g p.2 = l ∧ f p.1 = g p.2)
        = univ.filter fun p : σ₁ × σ₂ => f p.1 = l ∧ f p.1 = g p.2 :=
      filter_congr fun p _ => by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2.trans h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2.symm.trans h1, h2⟩
    have hsplit₁ : push (fun p : σ₁ × σ₂ => f p.1) γ l =
        (∑ p ∈ univ.filter fun p : σ₁ × σ₂ => f p.1 = l ∧ f p.1 = g p.2, γ p) +
          ∑ p ∈ univ.filter fun p : σ₁ × σ₂ => f p.1 = l ∧ ¬f p.1 = g p.2, γ p := by
      unfold push
      rw [← sum_filter_add_sum_filter_not
        (univ.filter fun p : σ₁ × σ₂ => f p.1 = l) (fun p => f p.1 = g p.2) γ,
        filter_filter, filter_filter]
    have hsplit₂ : push (fun p : σ₁ × σ₂ => g p.2) γ l =
        (∑ p ∈ univ.filter fun p : σ₁ × σ₂ => f p.1 = l ∧ f p.1 = g p.2, γ p) +
          ∑ p ∈ univ.filter fun p : σ₁ × σ₂ => g p.2 = l ∧ ¬f p.1 = g p.2, γ p := by
      unfold push
      rw [← sum_filter_add_sum_filter_not
        (univ.filter fun p : σ₁ × σ₂ => g p.2 = l) (fun p => f p.1 = g p.2) γ,
        filter_filter, filter_filter, hagree]
    have hd1 : (univ.filter fun p : σ₁ × σ₂ => f p.1 = l ∧ ¬f p.1 = g p.2)
        = D.filter fun p => f p.1 = l := by
      rw [hD, filter_filter]
      exact filter_congr fun p _ => and_comm
    have hd2 : (univ.filter fun p : σ₁ × σ₂ => g p.2 = l ∧ ¬f p.1 = g p.2)
        = D.filter fun p => g p.2 = l := by
      rw [hD, filter_filter]
      exact filter_congr fun p _ => and_comm
    have h1 : 0 ≤ ∑ p ∈ D.filter fun p => f p.1 = l, γ p :=
      sum_nonneg fun p _ => hγ p
    have h2 : 0 ≤ ∑ p ∈ D.filter fun p => g p.2 = l, γ p :=
      sum_nonneg fun p _ => hγ p
    rw [hsplit₁, hsplit₂, hd1, hd2, add_sub_add_left_eq_sub]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hsum : (∑ l, ((∑ p ∈ D.filter fun p => f p.1 = l, γ p) +
      ∑ p ∈ D.filter fun p => g p.2 = l, γ p)) = 2 * ∑ p ∈ D, γ p := by
    rw [Finset.sum_add_distrib, Finset.sum_fiberwise D (fun p => f p.1) γ,
      Finset.sum_fiberwise D (fun p => g p.2) γ]
    ring
  have hle : (∑ l, |push (fun p : σ₁ × σ₂ => f p.1) γ l -
      push (fun p : σ₁ × σ₂ => g p.2) γ l|) ≤ 2 * ∑ p ∈ D, γ p :=
    (sum_le_sum fun l _ => key l).trans_eq hsum
  unfold tvDist
  linarith

section Product

variable {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
variable {K : σ₁ × σ₂ → σ₁ × σ₂ → ℝ} {K₁ : σ₁ → σ₁ → ℝ} {K₂ : σ₂ → σ₂ → ℝ}
variable {μ₀ : σ₁ × σ₂ → ℝ} {A₁ : Finset σ₁} {A₂ : Finset σ₂}

omit [DecidableEq σ₂] in
theorem push_fst_apply (μ : σ₁ × σ₂ → ℝ) (a : σ₁) :
    push Prod.fst μ a = ∑ s₂, μ (a, s₂) := by
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp

omit [DecidableEq σ₁] in
theorem push_snd_apply (μ : σ₁ × σ₂ → ℝ) (a : σ₂) :
    push Prod.snd μ a = ∑ s₁, μ (s₁, a) := by
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

theorem sum_finalMass_snd_eq (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1) (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1)
    (habs₂ : Tendsto (fun n => ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)
      atTop (𝓝 1))
    {a₁ : σ₁} (ha₁ : a₁ ∈ A₁) :
    ∑ a₂ ∈ A₂, finalMass K μ₀ (a₁, a₂) = finalMass K₁ (push Prod.fst μ₀) a₁ := by
  have hν₁ : IsDist (push Prod.fst μ₀) := isDist_push hμ₀
  have hν₂ : IsDist (push Prod.snd μ₀) := isDist_push hμ₀
  set S : ℕ → ℝ := fun n => ∑ a₂ ∈ A₂, law K μ₀ n (a₁, a₂) with hS
  set T : ℕ → ℝ := fun n => law K₁ (push Prod.fst μ₀) n a₁ with hT
  have hTfull : ∀ n, T n = ∑ s₂, law K μ₀ n (a₁, s₂) := by
    intro n
    show law K₁ (push Prod.fst μ₀) n a₁ = _
    rw [← push_law hm₁ μ₀ n, push_fst_apply]
  have hlimS : Tendsto S atTop (𝓝 (∑ a₂ ∈ A₂, finalMass K μ₀ (a₁, a₂))) :=
    tendsto_finsetSum A₂ fun a₂ ha₂ =>
      tendsto_law_finalMass hK hμ₀ (hfreeze (a₁, a₂) (mem_product.2 ⟨ha₁, ha₂⟩))
  have hlimT : Tendsto T atTop (𝓝 (finalMass K₁ (push Prod.fst μ₀) a₁)) :=
    tendsto_law_finalMass hK₁ hν₁ (hfr₁ a₁ ha₁)
  have hST : ∀ n, S n ≤ T n := by
    intro n
    rw [hTfull n, hS]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ A₂) fun s₂ _ _ =>
      law_nonneg hK.nonneg hμ₀.nonneg n (a₁, s₂)
  have hTS : ∀ n,
      T n - (1 - ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a) ≤ S n := by
    intro n
    have hsplit : (∑ s₂ ∈ A₂, law K μ₀ n (a₁, s₂)) +
        ∑ s₂ ∈ A₂ᶜ, law K μ₀ n (a₁, s₂) = ∑ s₂, law K μ₀ n (a₁, s₂) :=
      Finset.sum_add_sum_compl A₂ _
    have hcompl : (∑ s₂ ∈ A₂ᶜ, law K μ₀ n (a₁, s₂)) ≤
        ∑ s₂ ∈ A₂ᶜ, law K₂ (push Prod.snd μ₀) n s₂ := by
      refine sum_le_sum fun s₂ _ => ?_
      rw [← push_law hm₂ μ₀ n, push_snd_apply]
      exact single_le_sum (f := fun s₁ => law K μ₀ n (s₁, s₂))
        (fun s₁ _ => law_nonneg hK.nonneg hμ₀.nonneg n (s₁, s₂)) (mem_univ a₁)
    have htot₂ : (∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a) +
        ∑ s₂ ∈ A₂ᶜ, law K₂ (push Prod.snd μ₀) n s₂ = 1 := by
      rw [Finset.sum_add_sum_compl, sum_law hK₂.rowSum, hν₂.total]
    have hTn := hTfull n
    rw [hS]
    linarith
  have hsq : Tendsto S atTop (𝓝 (finalMass K₁ (push Prod.fst μ₀) a₁)) := by
    have hlow : Tendsto
        (fun n => T n - (1 - ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)) atTop
        (𝓝 (finalMass K₁ (push Prod.fst μ₀) a₁ - (1 - 1))) :=
      hlimT.sub (tendsto_const_nhds.sub habs₂)
    rw [sub_self, sub_zero] at hlow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hlimT hTS hST
  exact tendsto_nhds_unique hlimS hsq

theorem sum_finalMass_fst_eq (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (habs₁ : Tendsto (fun n => ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)
      atTop (𝓝 1))
    {a₂ : σ₂} (ha₂ : a₂ ∈ A₂) :
    ∑ a₁ ∈ A₁, finalMass K μ₀ (a₁, a₂) = finalMass K₂ (push Prod.snd μ₀) a₂ := by
  have hν₁ : IsDist (push Prod.fst μ₀) := isDist_push hμ₀
  have hν₂ : IsDist (push Prod.snd μ₀) := isDist_push hμ₀
  set S : ℕ → ℝ := fun n => ∑ a₁ ∈ A₁, law K μ₀ n (a₁, a₂) with hS
  set T : ℕ → ℝ := fun n => law K₂ (push Prod.snd μ₀) n a₂ with hT
  have hTfull : ∀ n, T n = ∑ s₁, law K μ₀ n (s₁, a₂) := by
    intro n
    show law K₂ (push Prod.snd μ₀) n a₂ = _
    rw [← push_law hm₂ μ₀ n, push_snd_apply]
  have hlimS : Tendsto S atTop (𝓝 (∑ a₁ ∈ A₁, finalMass K μ₀ (a₁, a₂))) :=
    tendsto_finsetSum A₁ fun a₁ ha₁ =>
      tendsto_law_finalMass hK hμ₀ (hfreeze (a₁, a₂) (mem_product.2 ⟨ha₁, ha₂⟩))
  have hlimT : Tendsto T atTop (𝓝 (finalMass K₂ (push Prod.snd μ₀) a₂)) :=
    tendsto_law_finalMass hK₂ hν₂ (hfr₂ a₂ ha₂)
  have hST : ∀ n, S n ≤ T n := by
    intro n
    rw [hTfull n, hS]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ A₁) fun s₁ _ _ =>
      law_nonneg hK.nonneg hμ₀.nonneg n (s₁, a₂)
  have hTS : ∀ n,
      T n - (1 - ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a) ≤ S n := by
    intro n
    have hsplit : (∑ s₁ ∈ A₁, law K μ₀ n (s₁, a₂)) +
        ∑ s₁ ∈ A₁ᶜ, law K μ₀ n (s₁, a₂) = ∑ s₁, law K μ₀ n (s₁, a₂) :=
      Finset.sum_add_sum_compl A₁ _
    have hcompl : (∑ s₁ ∈ A₁ᶜ, law K μ₀ n (s₁, a₂)) ≤
        ∑ s₁ ∈ A₁ᶜ, law K₁ (push Prod.fst μ₀) n s₁ := by
      refine sum_le_sum fun s₁ _ => ?_
      rw [← push_law hm₁ μ₀ n, push_fst_apply]
      exact single_le_sum (f := fun s₂ => law K μ₀ n (s₁, s₂))
        (fun s₂ _ => law_nonneg hK.nonneg hμ₀.nonneg n (s₁, s₂)) (mem_univ a₂)
    have htot₁ : (∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a) +
        ∑ s₁ ∈ A₁ᶜ, law K₁ (push Prod.fst μ₀) n s₁ = 1 := by
      rw [Finset.sum_add_sum_compl, sum_law hK₁.rowSum, hν₁.total]
    have hTn := hTfull n
    rw [hS]
    linarith
  have hsq : Tendsto S atTop (𝓝 (finalMass K₂ (push Prod.snd μ₀) a₂)) := by
    have hlow : Tendsto
        (fun n => T n - (1 - ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)) atTop
        (𝓝 (finalMass K₂ (push Prod.snd μ₀) a₂ - (1 - 1))) :=
      hlimT.sub (tendsto_const_nhds.sub habs₁)
    rw [sub_self, sub_zero] at hlow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hlimT hTS hST
  exact tendsto_nhds_unique hlimS hsq

theorem sum_finalMass_prod_eq_one (hK : IsMarkov K) (hμ₀ : IsDist μ₀)
    (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1) (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1)
    (habs₁ : Tendsto (fun n => ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)
      atTop (𝓝 1))
    (habs₂ : Tendsto (fun n => ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)
      atTop (𝓝 1)) :
    ∑ p ∈ A₁ ×ˢ A₂, finalMass K μ₀ p = 1 := by
  rw [Finset.sum_product]
  have h : ∀ a₁ ∈ A₁, (∑ a₂ ∈ A₂, finalMass K μ₀ (a₁, a₂))
      = finalMass K₁ (push Prod.fst μ₀) a₁ := fun a₁ ha₁ =>
    sum_finalMass_snd_eq hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ habs₂ ha₁
  rw [Finset.sum_congr rfl h]
  exact sum_finalMass_eq_one hK₁ (isDist_push hμ₀) hfr₁ habs₁

def finalLaw {α : Type*} [Fintype α] [DecidableEq α] (K : α → α → ℝ)
    (μ₀ : α → ℝ) (A : Finset α) : α → ℝ :=
  fun s => if s ∈ A then finalMass K μ₀ s else 0

theorem finalLaw_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {K : α → α → ℝ} {μ₀ : α → ℝ}
    {A : Finset α} (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (s : α) :
    0 ≤ finalLaw K μ₀ A s := by
  unfold finalLaw
  split
  · exact finalMass_nonneg hK hμ₀ s
  · exact le_rfl

theorem push_finalLaw_fst [Fintype L] [DecidableEq L]
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1) (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1)
    (habs₂ : Tendsto (fun n => ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)
      atTop (𝓝 1))
    (f : σ₁ → L) :
    push (fun p : σ₁ × σ₂ => f p.1) (finalLaw K μ₀ (A₁ ×ˢ A₂)) =
      push f (finalLaw K₁ (push Prod.fst μ₀) A₁) := by
  funext l
  unfold push finalLaw
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  by_cases hfa : f a₁ = l
  · rw [if_pos hfa, Finset.sum_congr rfl fun (s₂ : σ₂) _ => if_pos hfa]
    by_cases ha₁ : a₁ ∈ A₁
    · have hcollapse : (∑ s₂ : σ₂, if (a₁, s₂) ∈ A₁ ×ˢ A₂
          then finalMass K μ₀ (a₁, s₂) else 0)
          = ∑ s₂ ∈ A₂, finalMass K μ₀ (a₁, s₂) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext s₂
        simp [Finset.mem_product, ha₁]
      rw [hcollapse,
        sum_finalMass_snd_eq hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ habs₂ ha₁,
        if_pos ha₁]
      rfl
    · rw [if_neg ha₁]
      refine Finset.sum_eq_zero fun s₂ _ => ?_
      rw [if_neg]
      simp [Finset.mem_product, ha₁]
  · rw [if_neg hfa]
    exact Finset.sum_eq_zero fun s₂ _ => if_neg hfa

theorem push_finalLaw_snd [Fintype L] [DecidableEq L]
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (habs₁ : Tendsto (fun n => ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)
      atTop (𝓝 1))
    (g : σ₂ → L) :
    push (fun p : σ₁ × σ₂ => g p.2) (finalLaw K μ₀ (A₁ ×ˢ A₂)) =
      push g (finalLaw K₂ (push Prod.snd μ₀) A₂) := by
  funext l
  unfold push finalLaw
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  by_cases hga : g a₂ = l
  · rw [if_pos hga, Finset.sum_congr rfl fun (s₁ : σ₁) _ => if_pos hga]
    by_cases ha₂ : a₂ ∈ A₂
    · have hcollapse : (∑ s₁ : σ₁, if (s₁, a₂) ∈ A₁ ×ˢ A₂
          then finalMass K μ₀ (s₁, a₂) else 0)
          = ∑ s₁ ∈ A₁, finalMass K μ₀ (s₁, a₂) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext s₁
        simp [Finset.mem_product, ha₂]
      rw [hcollapse,
        sum_finalMass_fst_eq hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₂ habs₁ ha₂,
        if_pos ha₂]
      rfl
    · rw [if_neg ha₂]
      refine Finset.sum_eq_zero fun s₁ _ => ?_
      rw [if_neg]
      simp [Finset.mem_product, ha₂]
  · rw [if_neg hga]
    exact Finset.sum_eq_zero fun s₁ _ => if_neg hga

theorem sound_QRelTV [Fintype L] [DecidableEq L] {f : σ₁ → L} {g : σ₂ → L}
    {V : σ₁ × σ₂ → ℝ} {b : ℝ}
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1)
    (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (habs₁ : Tendsto (fun n => ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)
      atTop (𝓝 1))
    (habs₂ : Tendsto (fun n => ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)
      atTop (𝓝 1))
    (hV0 : ∀ p, 0 ≤ V p) (hdrift : ∀ p, ∑ q, K p q * V q ≤ V p)
    (hterm : ∀ p ∈ A₁ ×ˢ A₂, f p.1 ≠ g p.2 → 1 ≤ V p)
    (hb : ∑ p, μ₀ p * V p ≤ b) :
    tvDist (push f (finalLaw K₁ (push Prod.fst μ₀) A₁))
      (push g (finalLaw K₂ (push Prod.snd μ₀) A₂)) ≤ b := by
  classical
  rw [← push_finalLaw_fst hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ habs₂ f,
    ← push_finalLaw_snd hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₂ habs₁ g]
  refine (tvDist_push_le_disagree (finalLaw K μ₀ (A₁ ×ˢ A₂))
    (finalLaw_nonneg hK hμ₀) f g).trans ?_
  set gv : σ₁ × σ₂ → ℝ := fun p => if f p.1 ≠ g p.2 then 1 else 0 with hgv
  have step1 : (∑ p ∈ univ.filter fun p : σ₁ × σ₂ => f p.1 ≠ g p.2,
      finalLaw K μ₀ (A₁ ×ˢ A₂) p) =
      ∑ p ∈ A₁ ×ˢ A₂, finalMass K μ₀ p * gv p := by
    rw [Finset.sum_filter]
    rw [show (∑ p ∈ A₁ ×ˢ A₂, finalMass K μ₀ p * gv p)
        = ∑ p : σ₁ × σ₂, if p ∈ A₁ ×ˢ A₂ then finalMass K μ₀ p * gv p else 0 by
      rw [Finset.sum_ite_mem, univ_inter]]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold finalLaw
    by_cases h1 : f p.1 ≠ g p.2 <;> by_cases h2 : p ∈ A₁ ×ˢ A₂ <;>
      simp [hgv, h1, h2]
  rw [step1]
  refine finalExpect_le hK hμ₀ hfreeze ?_ hV0 hdrift hb
  intro p hp
  rw [hgv]
  dsimp only
  split
  · next h => exact hterm p hp h
  · exact hV0 p

theorem sound_QRelExpGap {v₁ : σ₁ → ℝ} {v₂ : σ₂ → ℝ} {V : σ₁ × σ₂ → ℝ} {b : ℝ}
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1)
    (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (habs₁ : Tendsto (fun n => ∑ a ∈ A₁, law K₁ (push Prod.fst μ₀) n a)
      atTop (𝓝 1))
    (habs₂ : Tendsto (fun n => ∑ a ∈ A₂, law K₂ (push Prod.snd μ₀) n a)
      atTop (𝓝 1))
    (hV0 : ∀ p, 0 ≤ V p) (hdrift : ∀ p, ∑ q, K p q * V q ≤ V p)
    (hterm : ∀ p ∈ A₁ ×ˢ A₂, |v₁ p.1 - v₂ p.2| ≤ V p)
    (hb : ∑ p, μ₀ p * V p ≤ b) :
    |(∑ a₁ ∈ A₁, finalMass K₁ (push Prod.fst μ₀) a₁ * v₁ a₁) -
      ∑ a₂ ∈ A₂, finalMass K₂ (push Prod.snd μ₀) a₂ * v₂ a₂| ≤ b := by
  have hE₁ : (∑ a₁ ∈ A₁, finalMass K₁ (push Prod.fst μ₀) a₁ * v₁ a₁)
      = ∑ p ∈ A₁ ×ˢ A₂, finalMass K μ₀ p * v₁ p.1 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a₁ ha₁ => ?_
    rw [← sum_finalMass_snd_eq hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ habs₂ ha₁,
      Finset.sum_mul]
  have hE₂ : (∑ a₂ ∈ A₂, finalMass K₂ (push Prod.snd μ₀) a₂ * v₂ a₂)
      = ∑ p ∈ A₁ ×ˢ A₂, finalMass K μ₀ p * v₂ p.2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a₂ ha₂ => ?_
    rw [← sum_finalMass_fst_eq hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₂ habs₁ ha₂,
      Finset.sum_mul]
  rw [hE₁, hE₂, ← Finset.sum_sub_distrib]
  have hfactor : ∀ p : σ₁ × σ₂,
      finalMass K μ₀ p * v₁ p.1 - finalMass K μ₀ p * v₂ p.2
      = finalMass K μ₀ p * (v₁ p.1 - v₂ p.2) := fun p => by ring
  simp_rw [hfactor]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have habs' : ∀ p ∈ A₁ ×ˢ A₂, |finalMass K μ₀ p * (v₁ p.1 - v₂ p.2)|
      = finalMass K μ₀ p * |v₁ p.1 - v₂ p.2| := fun p _ => by
    rw [abs_mul, abs_of_nonneg (finalMass_nonneg hK hμ₀ p)]
  rw [Finset.sum_congr rfl habs']
  exact finalExpect_le hK hμ₀ hfreeze hterm hV0 hdrift hb

theorem sound_QRelTV_of_reach [Fintype L] [DecidableEq L] {f : σ₁ → L}
    {g : σ₂ → L} {V : σ₁ × σ₂ → ℝ} {b : ℝ}
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1)
    (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (hreach₁ : ∀ s, ∃ k, 0 < ∑ a ∈ A₁, law K₁ (pointMass s) k a)
    (hreach₂ : ∀ s, ∃ k, 0 < ∑ a ∈ A₂, law K₂ (pointMass s) k a)
    (hV0 : ∀ p, 0 ≤ V p) (hdrift : ∀ p, ∑ q, K p q * V q ≤ V p)
    (hterm : ∀ p ∈ A₁ ×ˢ A₂, f p.1 ≠ g p.2 → 1 ≤ V p)
    (hb : ∑ p, μ₀ p * V p ≤ b) :
    tvDist (push f (finalLaw K₁ (push Prod.fst μ₀) A₁))
      (push g (finalLaw K₂ (push Prod.snd μ₀) A₂)) ≤ b :=
  sound_QRelTV hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ hfr₂
    (tendsto_absorbedMass_one hK₁ (isDist_push hμ₀) hfr₁ hreach₁)
    (tendsto_absorbedMass_one hK₂ (isDist_push hμ₀) hfr₂ hreach₂)
    hV0 hdrift hterm hb

theorem sound_QRelExpGap_of_reach {v₁ : σ₁ → ℝ} {v₂ : σ₂ → ℝ}
    {V : σ₁ × σ₂ → ℝ} {b : ℝ}
    (hK : IsMarkov K) (hμ₀ : IsDist μ₀) (hK₁ : IsMarkov K₁) (hK₂ : IsMarkov K₂)
    (hm₁ : PushKernel Prod.fst K K₁) (hm₂ : PushKernel Prod.snd K K₂)
    (hfreeze : ∀ p ∈ A₁ ×ˢ A₂, K p p = 1)
    (hfr₁ : ∀ a ∈ A₁, K₁ a a = 1) (hfr₂ : ∀ a ∈ A₂, K₂ a a = 1)
    (hreach₁ : ∀ s, ∃ k, 0 < ∑ a ∈ A₁, law K₁ (pointMass s) k a)
    (hreach₂ : ∀ s, ∃ k, 0 < ∑ a ∈ A₂, law K₂ (pointMass s) k a)
    (hV0 : ∀ p, 0 ≤ V p) (hdrift : ∀ p, ∑ q, K p q * V q ≤ V p)
    (hterm : ∀ p ∈ A₁ ×ˢ A₂, |v₁ p.1 - v₂ p.2| ≤ V p)
    (hb : ∑ p, μ₀ p * V p ≤ b) :
    |(∑ a₁ ∈ A₁, finalMass K₁ (push Prod.fst μ₀) a₁ * v₁ a₁) -
      ∑ a₂ ∈ A₂, finalMass K₂ (push Prod.snd μ₀) a₂ * v₂ a₂| ≤ b :=
  sound_QRelExpGap hK hμ₀ hK₁ hK₂ hm₁ hm₂ hfreeze hfr₁ hfr₂
    (tendsto_absorbedMass_one hK₁ (isDist_push hμ₀) hfr₁ hreach₁)
    (tendsto_absorbedMass_one hK₂ (isDist_push hμ₀) hfr₂ hreach₂)
    hV0 hdrift hterm hb

end Product

end

end QRelChain

end Qtsl
