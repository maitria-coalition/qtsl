import QtslAux.QRelChain

/-! # Specification transport along simulations

This module shows how satisfaction of a specification transports from an
abstract model back to a concrete one along a simulation map, in the
finite-state chain setting.

* `pullback`: the behavioural form — if the observed behaviours `σ '' Beh`
  are contained in the abstract behaviours and the abstract behaviours
  satisfy `spec'`, then the concrete behaviours satisfy the pulled-back
  specification `σ ⁻¹' spec'`.
* `expect_push`: change of variables — the expectation of `g` under a
  pushforward distribution equals the expectation of `g ∘ σ` under the
  original.
* `sim_expect`: if `σ` intertwines the concrete kernel `K` with the
  abstract kernel `Q` (`PushKernel σ K Q`), expectations of lifted
  observables after `n` steps of `K` equal abstract expectations after `n`
  steps of `Q`.
* `sim_expect_bound`: consequently any expectation bound certified on the
  abstract chain transfers verbatim to the concrete chain.
* `sim_region`: support confinement transports — if the abstract `n`-step
  law vanishes outside a region `R'`, the concrete `n`-step law vanishes
  outside `σ ⁻¹' R'`.
-/

namespace Qtsl.QtslCompose

/-- Behavioural pullback: a simulation inclusion `σ '' Beh ⊆ Beh'` together
with abstract satisfaction `Beh' ⊆ spec'` yields concrete satisfaction of
the pulled-back specification, `Beh ⊆ σ ⁻¹' spec'`. -/
theorem pullback {Ω Ω' : Type*} {σ : Ω → Ω'} {Beh : Set Ω} {Beh' : Set Ω'}
    {spec' : Set Ω'} (hsim : σ '' Beh ⊆ Beh') (hsat : Beh' ⊆ spec') :
    Beh ⊆ σ ⁻¹' spec' :=
  fun ω hω => hsat (hsim ⟨ω, hω, rfl⟩)

open Finset
open Qtsl.QRelChain

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Change of variables for finite expectations: summing `g` against the
pushforward `push σ μ` equals summing `g ∘ σ` against `μ`. -/
theorem expect_push (σ : α → β) (μ : α → ℝ) (g : β → ℝ) :
    ∑ b, push σ μ b * g b = ∑ s, μ s * g (σ s) := by
  unfold push
  calc ∑ b, (∑ s ∈ univ.filter fun s => σ s = b, μ s) * g b
      = ∑ b, ∑ s ∈ univ.filter fun s => σ s = b, μ s * g (σ s) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s hs => by
          rw [(Finset.mem_filter.1 hs).2]
    _ = ∑ s, μ s * g (σ s) := Finset.sum_fiberwise univ σ fun s => μ s * g (σ s)

/-- Expectation transport along a simulation: if `σ` intertwines `K` with
`Q`, the expectation of the lifted observable `g ∘ σ` after `n` steps of the
concrete chain equals the expectation of `g` after `n` steps of the abstract
chain started from the pushforward initial distribution. -/
theorem sim_expect {σ : α → β} {K : α → α → ℝ} {Q : β → β → ℝ}
    (hσ : PushKernel σ K Q) (μ₀ : α → ℝ) (g : β → ℝ) (n : ℕ) :
    ∑ s, law K μ₀ n s * g (σ s) = ∑ b, law Q (push σ μ₀) n b * g b := by
  rw [← push_law hσ μ₀ n, expect_push]

/-- Bound transport: an expectation bound certified on the abstract chain
holds verbatim for the lifted observable on the concrete chain. -/
theorem sim_expect_bound {σ : α → β} {K : α → α → ℝ} {Q : β → β → ℝ}
    (hσ : PushKernel σ K Q) (μ₀ : α → ℝ) (g : β → ℝ) {n : ℕ} {b₀ : ℝ}
    (hb : ∑ b, law Q (push σ μ₀) n b * g b ≤ b₀) :
    ∑ s, law K μ₀ n s * g (σ s) ≤ b₀ := by
  rw [sim_expect hσ μ₀ g n]; exact hb

/-- Region transport: if the abstract `n`-step law is supported in `R'`,
the concrete `n`-step law is supported in `σ ⁻¹' R'` — each concrete mass
is dominated by the abstract mass of its observation fibre. -/
theorem sim_region {σ : α → β} {K : α → α → ℝ} {Q : β → β → ℝ}
    (hσ : PushKernel σ K Q) {μ₀ : α → ℝ}
    (hK : ∀ s t, 0 ≤ K s t) (hμ₀ : ∀ s, 0 ≤ μ₀ s) {n : ℕ} {R' : Set β}
    (hR' : ∀ b, b ∉ R' → law Q (push σ μ₀) n b = 0) :
    ∀ s, σ s ∉ R' → law K μ₀ n s = 0 := by
  intro s hs
  have hnn : ∀ t, 0 ≤ law K μ₀ n t := law_nonneg hK hμ₀ n
  have hle : law K μ₀ n s ≤ push σ (law K μ₀ n) (σ s) := by
    unfold push
    exact Finset.single_le_sum (f := fun t => law K μ₀ n t)
      (fun t _ => hnn t)
      (Finset.mem_filter.2 ⟨Finset.mem_univ s, rfl⟩)
  have hzero : push σ (law K μ₀ n) (σ s) = 0 := by
    rw [push_law hσ μ₀ n]
    exact hR' (σ s) hs
  exact le_antisymm (hzero ▸ hle) (hnn s)

end

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.pullback
#print axioms Qtsl.QtslCompose.expect_push
#print axioms Qtsl.QtslCompose.sim_expect
#print axioms Qtsl.QtslCompose.sim_expect_bound
#print axioms Qtsl.QtslCompose.sim_region
