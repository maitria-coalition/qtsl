import QtslAux.QRelChain

/-! # Total-variation transport across approximate lumpings

This module bounds the total-variation error incurred when a finite Markov
chain is abstracted along a state map `π : α → β` that commutes with the
dynamics only approximately.

Principal declarations:

* `tvDist_nonneg`, `tvDist_triangle`, `eq_of_tvDist_le_zero`: metric facts
  for the total-variation distance `tvDist` on finitely supported signed
  vectors.
* `tvDist_push_le`: pushing forward along any map is a TV contraction.
* `tvDist_step_le`: one step of a Markov kernel is a TV contraction.
* `EpsPushKernel π K Q ε`: approximate lumping — for every state `s`, the
  pushforward of the row `K s` is within TV distance `ε` of `Q (π s)`.
* `push_step_defect`: under an `ε`-lumping, pushing a distribution forward
  and stepping commute up to TV error `ε`.
* `sound_QDistTransport_eps`: the main transport bound — after `n` steps the
  pushforward of the concrete law and the abstract law differ by at most
  `n * ε` in total variation, by a telescoping triangle-inequality argument.
* `epsPushKernel_comp`: errors add under composition of lumpings.
* `pushKernel_iff_eps_zero`, `strict_cell_exact`: the `ε = 0` case coincides
  with exact lumping (`PushKernel`), giving equality of laws at every horizon.
-/

namespace Qtsl

namespace QDistTransport

open Finset
open Qtsl.QRelChain

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem tvDist_nonneg {L : Type*} [Fintype L] (p q : L → ℝ) : 0 ≤ tvDist p q :=
  div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) two_pos.le

theorem tvDist_triangle {L : Type*} [Fintype L] (p q r : L → ℝ) :
    tvDist p r ≤ tvDist p q + tvDist q r := by
  have h : ∑ l, |p l - r l| ≤ (∑ l, |p l - q l|) + ∑ l, |q l - r l| := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun l _ => abs_sub_le (p l) (q l) (r l)
  simp only [tvDist]
  linarith

theorem eq_of_tvDist_le_zero {L : Type*} [Fintype L] {p q : L → ℝ}
    (h : tvDist p q ≤ 0) : p = q := by
  have hnn : 0 ≤ ∑ l, |p l - q l| := sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∑ l, |p l - q l| ≤ 0 := by
    simp only [tvDist] at h
    linarith
  have hz := (sum_eq_zero_iff_of_nonneg fun l _ => abs_nonneg _).mp
    (le_antisymm hle hnn)
  funext l
  have := abs_eq_zero.mp (hz l (mem_univ l))
  linarith

theorem tvDist_push_le [DecidableEq β] (π : α → β) (p q : α → ℝ) :
    tvDist (push π p) (push π q) ≤ tvDist p q := by
  have h : ∑ b, |push π p b - push π q b| ≤ ∑ s, |p s - q s| := by
    calc ∑ b, |push π p b - push π q b|
        ≤ ∑ b, ∑ s ∈ univ.filter fun s => π s = b, |p s - q s| := by
          refine sum_le_sum fun b _ => ?_
          simp only [push]
          rw [← sum_sub_distrib]
          exact abs_sum_le_sum_abs _ _
      _ = ∑ s, |p s - q s| :=
          sum_fiberwise_of_maps_to (fun s _ => mem_univ (π s)) _
  simp only [tvDist]
  linarith

theorem sound_QDistSelfTransport [DecidableEq β] (π : α → β)
    {μ ν : α → ℝ} {ε : ℝ} (h : tvDist μ ν ≤ ε) :
    tvDist (push π μ) (push π ν) ≤ ε :=
  (tvDist_push_le π μ ν).trans h

theorem push_comp [DecidableEq β] [DecidableEq γ] (π₁ : α → β) (π₂ : β → γ)
    (μ : α → ℝ) : push (π₂ ∘ π₁) μ = push π₂ (push π₁ μ) := by
  funext c
  simp only [push]
  rw [eq_comm, sum_fiberwise_eq_sum_filter univ (univ.filter fun b => π₂ b = c) π₁ μ]
  exact sum_congr (filter_congr fun s _ => by simp [Function.comp]) fun _ _ => rfl

theorem tvDist_step_le {K : α → α → ℝ} (hK : IsMarkov K) (p q : α → ℝ) :
    tvDist (step K p) (step K q) ≤ tvDist p q := by
  have h : ∑ t, |step K p t - step K q t| ≤ ∑ s, |p s - q s| := by
    calc ∑ t, |step K p t - step K q t|
        ≤ ∑ t, ∑ s, |p s - q s| * K s t := by
          refine sum_le_sum fun t _ => ?_
          simp only [step]
          rw [← sum_sub_distrib]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
          rw [← sub_mul, abs_mul, abs_of_nonneg (hK.nonneg s t)]
      _ = ∑ s, |p s - q s| := by
          rw [sum_comm]
          exact sum_congr rfl fun s _ => by
            rw [← mul_sum, hK.rowSum s, mul_one]
  simp only [tvDist]
  linarith

def EpsPushKernel [DecidableEq β] (π : α → β) (K : α → α → ℝ)
    (Q : β → β → ℝ) (ε : ℝ) : Prop :=
  ∀ s, tvDist (push π (K s)) (Q (π s)) ≤ ε

theorem push_step_defect [DecidableEq β] {π : α → β} {K : α → α → ℝ}
    {Q : β → β → ℝ} {ε : ℝ} {μ : α → ℝ} (hμ : IsDist μ)
    (h : EpsPushKernel π K Q ε) :
    tvDist (push π (step K μ)) (step Q (push π μ)) ≤ ε := by

  have h1 : ∀ b, push π (step K μ) b = ∑ s, μ s * push π (K s) b := by
    intro b
    simp only [push, step]
    rw [sum_comm]
    exact sum_congr rfl fun s _ => by rw [← mul_sum]
  have h2 : ∀ b, step Q (push π μ) b = ∑ s, μ s * Q (π s) b := by
    intro b
    simp only [step, push]
    calc ∑ b', (∑ s ∈ univ.filter fun s => π s = b', μ s) * Q b' b
        = ∑ b', ∑ s ∈ univ.filter fun s => π s = b', μ s * Q (π s) b := by
          refine sum_congr rfl fun b' _ => ?_
          rw [sum_mul]
          exact sum_congr rfl fun s hs => by
            rw [(mem_filter.mp hs).2]
      _ = ∑ s, μ s * Q (π s) b :=
          sum_fiberwise_of_maps_to (fun s _ => mem_univ (π s)) _

  have hmix : ∑ b, |push π (step K μ) b - step Q (push π μ) b| ≤ 2 * ε := by
    calc ∑ b, |push π (step K μ) b - step Q (push π μ) b|
        = ∑ b, |∑ s, μ s * (push π (K s) b - Q (π s) b)| := by
          refine sum_congr rfl fun b _ => ?_
          rw [h1 b, h2 b, ← sum_sub_distrib]
          exact congrArg abs (sum_congr rfl fun s _ => by ring)
      _ ≤ ∑ b, ∑ s, μ s * |push π (K s) b - Q (π s) b| := by
          refine sum_le_sum fun b _ => ?_
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ.nonneg s)]
      _ = ∑ s, μ s * ∑ b, |push π (K s) b - Q (π s) b| := by
          rw [sum_comm]
          exact sum_congr rfl fun s _ => (mul_sum _ _ _).symm
      _ ≤ ∑ s, μ s * (2 * ε) := by
          refine sum_le_sum fun s _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hμ.nonneg s)
          have := h s
          simp only [tvDist] at this
          linarith
      _ = 2 * ε := by rw [← sum_mul, hμ.total, one_mul]
  simp only [tvDist]
  linarith

theorem sound_QDistTransport_eps [DecidableEq β] {π : α → β}
    {K : α → α → ℝ} {Q : β → β → ℝ} {ε : ℝ} {μ₀ : α → ℝ}
    (hK : IsMarkov K) (hQ : IsMarkov Q) (hμ₀ : IsDist μ₀)
    (h : EpsPushKernel π K Q ε) (n : ℕ) :
    tvDist (push π (law K μ₀ n)) (law Q (push π μ₀) n) ≤ n * ε := by
  induction n with
  | zero => simp [tvDist, law]
  | succ n ih =>
      have hstep := push_step_defect (isDist_law hK hμ₀ n) h
      have hcontract := tvDist_step_le hQ (push π (law K μ₀ n)) (law Q (push π μ₀) n)
      have htri := tvDist_triangle (push π (step K (law K μ₀ n)))
        (step Q (push π (law K μ₀ n))) (step Q (law Q (push π μ₀) n))
      simp only [law_succ]
      push_cast
      linarith

theorem epsPushKernel_comp [DecidableEq β] [DecidableEq γ]
    {π₁ : α → β} {π₂ : β → γ} {K₁ : α → α → ℝ} {K₂ : β → β → ℝ}
    {K₃ : γ → γ → ℝ} {ε₁ ε₂ : ℝ}
    (h₁ : EpsPushKernel π₁ K₁ K₂ ε₁) (h₂ : EpsPushKernel π₂ K₂ K₃ ε₂) :
    EpsPushKernel (π₂ ∘ π₁) K₁ K₃ (ε₁ + ε₂) := by
  intro s
  have hsplit := tvDist_triangle (push (π₂ ∘ π₁) (K₁ s))
    (push π₂ (K₂ (π₁ s))) (K₃ (π₂ (π₁ s)))
  have hleft : tvDist (push (π₂ ∘ π₁) (K₁ s)) (push π₂ (K₂ (π₁ s))) ≤ ε₁ := by
    rw [push_comp]
    exact (tvDist_push_le π₂ _ _).trans (h₁ s)
  have hright := h₂ (π₁ s)
  simp only [Function.comp_apply] at *
  linarith

theorem pushKernel_iff_eps_zero [DecidableEq β] {π : α → β}
    {K : α → α → ℝ} {Q : β → β → ℝ} :
    PushKernel π K Q ↔ EpsPushKernel π K Q 0 := by
  constructor
  · intro h s
    rw [h s]
    simp [tvDist]
  · intro h s
    exact eq_of_tvDist_le_zero (h s)

theorem strict_cell_exact [DecidableEq β] {π : α → β} {K : α → α → ℝ}
    {Q : β → β → ℝ} (h : PushKernel π K Q) (μ₀ : α → ℝ) (n : ℕ) :
    push π (law K μ₀ n) = law Q (push π μ₀) n :=
  push_law h μ₀ n

end QDistTransport

end Qtsl

