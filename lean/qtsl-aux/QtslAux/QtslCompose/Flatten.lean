import QtslAux.QRelChain

/-! # Parallel composition of finite-state chains

This module defines the parallel (product) composition of finite-state
Markov chains represented as row-stochastic matrices, and proves that the
product construction is compatible with every piece of the chain machinery.

* `prodKernel K₁ K₂`, `prodDist μ₁ μ₂`: the product transition kernel and
  product initial distribution on `α × β`, defined entrywise by
  multiplication.
* `isMarkov_prodKernel`, `isDist_prodDist`: the product of Markov kernels is
  Markov, and the product of distributions is a distribution.
* `step_prodKernel`, `law_prodKernel`: one-step evolution and hence the full
  `n`-step law factor through the product — the components of a parallel
  composition evolve independently.
* `pushKernel_fst`, `pushKernel_snd`, `push_fst_prodDist`: the coordinate
  projections are simulation maps from the product chain to its components,
  and marginalize the initial distribution accordingly.
-/

namespace Qtsl.QtslCompose

open Finset
open Qtsl.QRelChain

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The product transition kernel on `α × β`: components transition
independently, so the transition weight is the product of the component
weights. -/
def prodKernel (K₁ : α → α → ℝ) (K₂ : β → β → ℝ) :
    α × β → α × β → ℝ :=
  fun p q => K₁ p.1 q.1 * K₂ p.2 q.2

/-- The product distribution on `α × β`, assigning to each pair the product
of the component probabilities. -/
def prodDist (μ₁ : α → ℝ) (μ₂ : β → ℝ) : α × β → ℝ :=
  fun p => μ₁ p.1 * μ₂ p.2

/-- The product of two Markov kernels is a Markov kernel: entries are
nonnegative and each row sums to `1`. -/
theorem isMarkov_prodKernel {K₁ : α → α → ℝ} {K₂ : β → β → ℝ}
    (h₁ : IsMarkov K₁) (h₂ : IsMarkov K₂) :
    IsMarkov (prodKernel K₁ K₂) where
  nonneg := fun p q => mul_nonneg (h₁.nonneg p.1 q.1) (h₂.nonneg p.2 q.2)
  rowSum := fun p => by
    unfold prodKernel
    rw [Fintype.sum_prod_type]
    calc ∑ a, ∑ b, K₁ p.1 a * K₂ p.2 b
        = ∑ a, K₁ p.1 a * ∑ b, K₂ p.2 b := by
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by
          simp_rw [h₂.rowSum p.2, mul_one]
          exact h₁.rowSum p.1

/-- The product of two probability distributions is a probability
distribution. -/
theorem isDist_prodDist {μ₁ : α → ℝ} {μ₂ : β → ℝ}
    (h₁ : IsDist μ₁) (h₂ : IsDist μ₂) : IsDist (prodDist μ₁ μ₂) where
  nonneg := fun p => mul_nonneg (h₁.nonneg p.1) (h₂.nonneg p.2)
  total := by
    unfold prodDist
    rw [Fintype.sum_prod_type]
    calc ∑ a, ∑ b, μ₁ a * μ₂ b
        = ∑ a, μ₁ a * ∑ b, μ₂ b := by
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [h₂.total]; simp_rw [mul_one]; exact h₁.total

/-- One-step evolution factors through the product: stepping the product
distribution by the product kernel is the product of the stepped component
distributions. -/
theorem step_prodKernel (K₁ : α → α → ℝ) (K₂ : β → β → ℝ)
    (μ₁ : α → ℝ) (μ₂ : β → ℝ) :
    step (prodKernel K₁ K₂) (prodDist μ₁ μ₂)
      = prodDist (step K₁ μ₁) (step K₂ μ₂) := by
  funext q
  unfold step prodKernel prodDist
  rw [Fintype.sum_prod_type]
  calc ∑ a, ∑ b, μ₁ a * μ₂ b * (K₁ a q.1 * K₂ b q.2)
      = ∑ a, ∑ b, (μ₁ a * K₁ a q.1) * (μ₂ b * K₂ b q.2) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = ∑ a, (μ₁ a * K₁ a q.1) * ∑ b, μ₂ b * K₂ b q.2 := by
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ a, μ₁ a * K₁ a q.1) * ∑ b, μ₂ b * K₂ b q.2 :=
        (Finset.sum_mul _ _ _).symm

/-- The `n`-step law of a parallel composition is the product of the
component `n`-step laws, for every `n`. Induction on `n` via
`step_prodKernel`. -/
theorem law_prodKernel (K₁ : α → α → ℝ) (K₂ : β → β → ℝ)
    (μ₁ : α → ℝ) (μ₂ : β → ℝ) :
    ∀ n, law (prodKernel K₁ K₂) (prodDist μ₁ μ₂) n
      = prodDist (law K₁ μ₁ n) (law K₂ μ₂ n)
  | 0 => rfl
  | n + 1 => by
    rw [law_succ, law_prodKernel K₁ K₂ μ₁ μ₂ n, step_prodKernel, law_succ,
      law_succ]

section Projections

variable [DecidableEq α] [DecidableEq β]

/-- The first projection is a simulation map from the product chain to its
first component, provided the second kernel is row-stochastic. -/
theorem pushKernel_fst {K₁ : α → α → ℝ} {K₂ : β → β → ℝ}
    (h₂ : ∀ b, ∑ b', K₂ b b' = 1) :
    PushKernel Prod.fst (prodKernel K₁ K₂) K₁ := by
  intro p
  funext a
  rw [push_fst_apply]
  unfold prodKernel
  calc ∑ b', K₁ p.1 a * K₂ p.2 b'
      = K₁ p.1 a * ∑ b', K₂ p.2 b' := (Finset.mul_sum _ _ _).symm
    _ = K₁ p.1 a := by rw [h₂ p.2, mul_one]

/-- The second projection is a simulation map from the product chain to its
second component, provided the first kernel is row-stochastic. -/
theorem pushKernel_snd {K₁ : α → α → ℝ} {K₂ : β → β → ℝ}
    (h₁ : ∀ a, ∑ a', K₁ a a' = 1) :
    PushKernel Prod.snd (prodKernel K₁ K₂) K₂ := by
  intro p
  funext b
  rw [push_snd_apply]
  unfold prodKernel
  calc ∑ a', K₁ p.1 a' * K₂ p.2 b
      = (∑ a', K₁ p.1 a') * K₂ p.2 b := (Finset.sum_mul _ _ _).symm
    _ = K₂ p.2 b := by rw [h₁ p.1, one_mul]

/-- Marginalizing a product distribution onto the first coordinate recovers
the first factor. -/
theorem push_fst_prodDist {μ₁ : α → ℝ} {μ₂ : β → ℝ} (h₂ : IsDist μ₂) :
    push Prod.fst (prodDist μ₁ μ₂) = μ₁ := by
  funext a
  rw [push_fst_apply]
  unfold prodDist
  calc ∑ b, μ₁ a * μ₂ b = μ₁ a * ∑ b, μ₂ b := (Finset.mul_sum _ _ _).symm
    _ = μ₁ a := by rw [h₂.total, mul_one]

end Projections

end

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.isMarkov_prodKernel
#print axioms Qtsl.QtslCompose.isDist_prodDist
#print axioms Qtsl.QtslCompose.law_prodKernel
#print axioms Qtsl.QtslCompose.pushKernel_fst
#print axioms Qtsl.QtslCompose.pushKernel_snd
#print axioms Qtsl.QtslCompose.push_fst_prodDist
