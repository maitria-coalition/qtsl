import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Composition.CompMap
import QtslAux.QtslCompose.SimTransport

/-! # Specification transport along simulations, measure-theoretic version

This module develops the measure-theoretic counterpart of
`QtslAux.QtslCompose.SimTransport`: transporting expectations,
bounds, and support confinement along a simulation map between Markov
kernels on general measurable spaces.

* `PushKernel σ K Q`: the exact intertwining condition
  `(K s).map σ = Q (σ s)` — one concrete step observed through `σ` is one
  abstract step.
* `law K μ n`: the `n`-step law of the chain, iterating `Measure.bind`.
* `map_bind`, `bind_map`: commutation of `Measure.map` with `Measure.bind`
  in the two required orientations.
* `push_law`: the fundamental transport identity — for a measurable
  simulation, `(law K μ n).map σ = law Q (μ.map σ) n` for every `n`.
* `sim_expect_lintegral`, `sim_expect_integral`: expectations (lower
  Lebesgue and Bochner) of lifted observables under the concrete law equal
  abstract expectations.
* `sim_expect_bound`: abstract expectation bounds transfer to the concrete
  chain.
* `sim_region`: if the abstract `n`-step law vanishes outside a measurable
  region `R'`, the concrete law vanishes outside `σ ⁻¹' R'`.
* `pushKernel_iff_comp`: `PushKernel σ K Q` is equivalent to commutation
  of the kernels with the deterministic kernel of `σ`:
  `deterministic σ ∘ₖ K = Q ∘ₖ deterministic σ`.
-/

namespace Qtsl.QtslCompose.Meas

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `σ` is a simulation map from the kernel `K` to the kernel `Q`: one step
of `K` observed through `σ` is exactly one step of `Q`,
`(K s).map σ = Q (σ s)` for every state `s`. -/
def PushKernel (σ : α → β) (K : Kernel α α) (Q : Kernel β β) : Prop :=
  ∀ s, (K s).map σ = Q (σ s)

/-- The `n`-step law of the Markov chain with kernel `K` and initial
measure `μ`: `law K μ 0 = μ`, and each further step binds the current law
through `K`. -/
noncomputable def law (K : Kernel α α) (μ : Measure α) : ℕ → Measure α
  | 0 => μ
  | n + 1 => (law K μ n).bind K

@[simp] theorem law_zero (K : Kernel α α) (μ : Measure α) : law K μ 0 = μ := rfl

theorem law_succ (K : Kernel α α) (μ : Measure α) (n : ℕ) :
    law K μ (n + 1) = (law K μ n).bind K := rfl

theorem map_bind (μ : Measure α) (K : Kernel α α) {σ : α → β}
    (hσ : Measurable σ) :
    (μ.bind K).map σ = μ.bind fun s => (K s).map σ := by
  have hf : AEMeasurable (fun s => (K s).map σ) μ :=
    ((Measure.measurable_map σ hσ).comp K.measurable).aemeasurable
  ext t ht
  rw [Measure.map_apply hσ ht, Measure.bind_apply (hσ ht) K.aemeasurable,
    Measure.bind_apply ht hf]
  exact lintegral_congr fun s => (Measure.map_apply hσ ht).symm

theorem bind_map (μ : Measure α) (Q : Kernel β β) {σ : α → β}
    (hσ : Measurable σ) :
    (μ.map σ).bind Q = μ.bind fun s => Q (σ s) := by
  have hf : AEMeasurable (fun s => Q (σ s)) μ :=
    (Q.measurable.comp hσ).aemeasurable
  ext t ht
  rw [Measure.bind_apply ht Q.aemeasurable, Measure.bind_apply ht hf,
    lintegral_map (Q.measurable_coe ht) hσ]

/-- The fundamental transport identity: for a measurable simulation `σ`
from `K` to `Q`, observing the concrete `n`-step law through `σ` gives the
abstract `n`-step law started from `μ.map σ`, for every `n`. -/
theorem push_law {σ : α → β} {K : Kernel α α} {Q : Kernel β β}
    (hσ : Measurable σ) (h : PushKernel σ K Q) (μ : Measure α) :
    ∀ n, (law K μ n).map σ = law Q (μ.map σ) n
  | 0 => rfl
  | n + 1 => by
    rw [law_succ, map_bind _ _ hσ, funext h, ← bind_map _ _ hσ,
      push_law hσ h μ n, law_succ]

/-- Expectation transport (lower Lebesgue integral): the expectation of a
lifted observable `g ∘ σ` under the concrete `n`-step law equals the
abstract expectation of `g`. -/
theorem sim_expect_lintegral {σ : α → β} {K : Kernel α α} {Q : Kernel β β}
    (hσ : Measurable σ) (h : PushKernel σ K Q) (μ : Measure α)
    {g : β → ℝ≥0∞} (hg : Measurable g) (n : ℕ) :
    ∫⁻ s, g (σ s) ∂law K μ n = ∫⁻ b, g b ∂law Q (μ.map σ) n := by
  rw [← push_law hσ h μ n, lintegral_map hg hσ]

/-- Expectation transport (Bochner integral), for a vector-valued
observable that is almost-everywhere strongly measurable with respect to
the abstract law. -/
theorem sim_expect_integral {σ : α → β} {K : Kernel α α} {Q : Kernel β β}
    (hσ : Measurable σ) (h : PushKernel σ K Q) (μ : Measure α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : β → E} {n : ℕ}
    (hg : AEStronglyMeasurable g (law Q (μ.map σ) n)) :
    ∫ s, g (σ s) ∂law K μ n = ∫ b, g b ∂law Q (μ.map σ) n := by
  rw [← push_law hσ h μ n] at hg ⊢
  exact (integral_map hσ.aemeasurable hg).symm

/-- Bound transport: an expectation bound certified on the abstract chain
holds verbatim for the lifted observable on the concrete chain. -/
theorem sim_expect_bound {σ : α → β} {K : Kernel α α} {Q : Kernel β β}
    (hσ : Measurable σ) (h : PushKernel σ K Q) (μ : Measure α)
    {g : β → ℝ≥0∞} (hg : Measurable g) {n : ℕ} {b₀ : ℝ≥0∞}
    (hb : ∫⁻ b, g b ∂law Q (μ.map σ) n ≤ b₀) :
    ∫⁻ s, g (σ s) ∂law K μ n ≤ b₀ := by
  rw [sim_expect_lintegral hσ h μ hg n]; exact hb

/-- Region transport: if the abstract `n`-step law assigns zero mass to the
complement of a measurable region `R'`, the concrete `n`-step law assigns
zero mass to the complement of `σ ⁻¹' R'`. -/
theorem sim_region {σ : α → β} {K : Kernel α α} {Q : Kernel β β}
    (hσ : Measurable σ) (h : PushKernel σ K Q) (μ : Measure α)
    {R' : Set β} (hR' : MeasurableSet R') {n : ℕ}
    (hz : law Q (μ.map σ) n R'ᶜ = 0) :
    law K μ n (σ ⁻¹' R')ᶜ = 0 := by
  rw [← Set.preimage_compl, ← Measure.map_apply hσ hR'.compl,
    push_law hσ h μ n]
  exact hz

/-- The simulation condition is a commutation square: `PushKernel σ K Q`
holds if and only if the deterministic kernel of `σ` intertwines `K` and
`Q` under kernel composition. -/
theorem pushKernel_iff_comp {σ : α → β} (hσ : Measurable σ)
    {K : Kernel α α} {Q : Kernel β β} :
    PushKernel σ K Q ↔
      Kernel.deterministic σ hσ ∘ₖ K = Q ∘ₖ Kernel.deterministic σ hσ := by
  rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap,
    Kernel.ext_iff]
  exact forall_congr' fun s => by
    rw [Kernel.map_apply _ hσ, Kernel.comap_apply]

end Qtsl.QtslCompose.Meas

#print axioms Qtsl.QtslCompose.Meas.map_bind
#print axioms Qtsl.QtslCompose.Meas.bind_map
#print axioms Qtsl.QtslCompose.Meas.push_law
#print axioms Qtsl.QtslCompose.Meas.sim_expect_lintegral
#print axioms Qtsl.QtslCompose.Meas.sim_expect_integral
#print axioms Qtsl.QtslCompose.Meas.sim_expect_bound
#print axioms Qtsl.QtslCompose.Meas.sim_region
#print axioms Qtsl.QtslCompose.Meas.pushKernel_iff_comp
