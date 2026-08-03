import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.Lemmas
import QtslAux.QtslCompose.SimTransportMeas
import QtslAux.QtslCompose.StochCoherence

/-! # Parallel composition, measure-theoretic version

This module carries the parallel-composition facts of
`QtslAux.QtslCompose.Flatten` from finite-state chains to general
Markov kernels, using mathlib's parallel composition `K ∥ₖ Q` and the
`n`-step law `law K μ n` (iterated `Measure.bind`).

* `sfinite_law`, `isProbabilityMeasure_law`: the `n`-step law inherits
  s-finiteness from an s-finite start and kernel, and is a probability
  measure when the kernel is Markov and the start is a probability measure.
* `bind_parallelComp`: one step of `K ∥ₖ Q` from a product measure is the
  product of the component steps.
* `law_parallelComp`: hence the `n`-step law of a parallel composition
  started from a product measure is the product of the component laws.
* `pushKernel_fst`, `pushKernel_snd`: the coordinate projections intertwine
  the parallel composition with its components.
* `sim_expect_fst`, `sim_expect_snd`: expectations of coordinatewise
  observables under the product law reduce to expectations under the
  corresponding component law.
* `pushKernel_iff_stochSim`: the intertwining property used here coincides
  (up to the orientation of the defining equation) with `StochSim`.
-/

namespace Qtsl.QtslCompose.Meas

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The `n`-step law of an s-finite kernel from an s-finite initial measure
is s-finite. -/
instance sfinite_law (K : Kernel α α) [IsSFiniteKernel K]
    (μ : Measure α) [SFinite μ] : ∀ n, SFinite (law K μ n)
  | 0 => inferInstanceAs (SFinite μ)
  | n + 1 => by
    have := sfinite_law K μ n
    exact inferInstanceAs (SFinite ((law K μ n).bind K))

/-- The `n`-step law of a Markov kernel from a probability measure is a
probability measure. -/
instance isProbabilityMeasure_law (K : Kernel α α) [IsMarkovKernel K]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    ∀ n, IsProbabilityMeasure (law K μ n)
  | 0 => inferInstanceAs (IsProbabilityMeasure μ)
  | n + 1 => by
    have := isProbabilityMeasure_law K μ n
    exact inferInstanceAs (IsProbabilityMeasure ((law K μ n).bind K))

/-- One step of a parallel composition from a product measure is the
product of the component steps:
`(μ.prod ν).bind (K ∥ₖ Q) = (μ.bind K).prod (ν.bind Q)`. -/
theorem bind_parallelComp (μ : Measure α) (ν : Measure β)
    (K : Kernel α α) (Q : Kernel β β)
    [SFinite μ] [SFinite ν] [IsSFiniteKernel K] [IsSFiniteKernel Q] :
    (μ.prod ν).bind (K ∥ₖ Q) = (μ.bind K).prod (ν.bind Q) := by
  calc (μ.prod ν).bind (K ∥ₖ Q)
      = ((K ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ Q)) ∘ₘ (μ.prod ν) := by
        rw [Kernel.parallelComp_comp_parallelComp, Kernel.comp_id,
          Kernel.id_comp]
    _ = (K ∥ₖ Kernel.id) ∘ₘ ((Kernel.id ∥ₖ Q) ∘ₘ (μ.prod ν)) :=
        Measure.comp_assoc.symm
    _ = (K ∥ₖ Kernel.id) ∘ₘ (μ.prod (Q ∘ₘ ν)) := by
        rw [Measure.prod_comp_right]
    _ = (μ.bind K).prod (ν.bind Q) := by
        rw [← Measure.prod_comp_left]

/-- The `n`-step law of a parallel composition started from a product
measure is the product of the component `n`-step laws, for every `n`. -/
theorem law_parallelComp (μ : Measure α) (ν : Measure β)
    (K : Kernel α α) (Q : Kernel β β)
    [SFinite μ] [SFinite ν] [IsSFiniteKernel K] [IsSFiniteKernel Q] :
    ∀ n, law (K ∥ₖ Q) (μ.prod ν) n = (law K μ n).prod (law Q ν n)
  | 0 => rfl
  | n + 1 => by
    rw [law_succ, law_parallelComp μ ν K Q n, bind_parallelComp,
      ← law_succ, ← law_succ]

/-- The first projection intertwines the parallel composition `K ∥ₖ Q`
with `K` (when `Q` is Markov): marginalizing a transition onto the first
coordinate gives a transition of the first component. -/
theorem pushKernel_fst {K : Kernel α α} {Q : Kernel β β}
    [IsSFiniteKernel K] [IsMarkovKernel Q] :
    PushKernel Prod.fst (K ∥ₖ Q) K := by
  intro p
  rw [Kernel.parallelComp_apply, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- The second projection intertwines the parallel composition `K ∥ₖ Q`
with `Q` (when `K` is Markov). -/
theorem pushKernel_snd {K : Kernel α α} {Q : Kernel β β}
    [IsMarkovKernel K] [IsSFiniteKernel Q] :
    PushKernel Prod.snd (K ∥ₖ Q) Q := by
  intro p
  rw [Kernel.parallelComp_apply, Measure.map_snd_prod, measure_univ,
    one_smul]

/-- Expectations of first-coordinate observables under the product law
reduce to the first component:
`∫⁻ p, g p.1 ∂law (K ∥ₖ Q) (μ.prod ν) n = ∫⁻ a, g a ∂law K μ n`. -/
theorem sim_expect_fst {K : Kernel α α} {Q : Kernel β β}
    [IsSFiniteKernel K] [IsMarkovKernel Q]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν]
    {g : α → ℝ≥0∞} (hg : Measurable g) (n : ℕ) :
    ∫⁻ p, g p.1 ∂law (K ∥ₖ Q) (μ.prod ν) n = ∫⁻ a, g a ∂law K μ n := by
  have h := sim_expect_lintegral measurable_fst
    (pushKernel_fst (K := K) (Q := Q)) (μ.prod ν) hg n
  rwa [measurePreserving_fst.map_eq] at h

/-- Expectations of second-coordinate observables under the product law
reduce to the second component. -/
theorem sim_expect_snd {K : Kernel α α} {Q : Kernel β β}
    [IsMarkovKernel K] [IsSFiniteKernel Q]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν]
    {g : β → ℝ≥0∞} (hg : Measurable g) (n : ℕ) :
    ∫⁻ p, g p.2 ∂law (K ∥ₖ Q) (μ.prod ν) n = ∫⁻ b, g b ∂law Q ν n := by
  have h := sim_expect_lintegral measurable_snd
    (pushKernel_snd (K := K) (Q := Q)) (μ.prod ν) hg n
  rwa [measurePreserving_snd.map_eq] at h

/-- `PushKernel` and `StochSim` state the same intertwining condition, with
the two sides of the defining equation swapped. -/
theorem pushKernel_iff_stochSim {σ : α → β} {K : Kernel α α}
    {Q : Kernel β β} : PushKernel σ K Q ↔ StochSim σ K Q :=
  forall_congr' fun _ => eq_comm

end Qtsl.QtslCompose.Meas

#print axioms Qtsl.QtslCompose.Meas.sfinite_law
#print axioms Qtsl.QtslCompose.Meas.isProbabilityMeasure_law
#print axioms Qtsl.QtslCompose.Meas.bind_parallelComp
#print axioms Qtsl.QtslCompose.Meas.law_parallelComp
#print axioms Qtsl.QtslCompose.Meas.pushKernel_fst
#print axioms Qtsl.QtslCompose.Meas.pushKernel_snd
#print axioms Qtsl.QtslCompose.Meas.sim_expect_fst
#print axioms Qtsl.QtslCompose.Meas.sim_expect_snd
#print axioms Qtsl.QtslCompose.Meas.pushKernel_iff_stochSim
