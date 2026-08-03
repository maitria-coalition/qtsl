import QtslAux.QtslCompose.Coherence
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Stochastic coherence laws

This module proves the coherence of stochastic simulation with parallel
composition and product flattening, for Markov kernels on general
measurable spaces — the measure-theoretic counterpart of the interchange
and flattening sections of `QtslAux.QtslCompose.Coherence`.

* `StochSim σ κ η`: `σ` is a stochastic simulation from `κ` to `η`, i.e.
  `η (σ x) = (κ x).map σ` for every state `x`.
* `stoch_interchange_law`, `stoch_pushKernel_prodMap`, `stoch_interchange`:
  simulations compose in parallel — `Prod.map σ₁ σ₂` is a stochastic
  simulation from `κ₁ ∥ₖ κ₂` to `η₁ ∥ₖ η₂`, and initial product laws map
  accordingly.
* `stoch_flatten_law`, `stoch_flattenNest_kernel`: the product-associativity
  equivalence flattens nested parallel compositions, at the level of both
  initial laws and kernels.
* `stoch_integral_transport`, `stoch_driftCert_transport`: expectations of
  an abstract certificate `V` against the abstract kernel compute on the
  concrete side, so a supermartingale drift certificate established for the
  concrete kernel (through `σ`) transports to the abstract kernel along the
  range of `σ`.
-/

namespace Qtsl.QtslCompose

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

section StochInterchange

variable {X₁ X₂ Y₁ Y₂ : Type*}
  [MeasurableSpace X₁] [MeasurableSpace X₂]
  [MeasurableSpace Y₁] [MeasurableSpace Y₂]

/-- Interchange at the level of initial laws: mapping componentwise and
then taking the product agrees with taking the product and mapping along
`Prod.map σ₁ σ₂`. -/
theorem stoch_interchange_law {σ₁ : X₁ → Y₁} {σ₂ : X₂ → Y₂}
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂]
    (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂) :
    (μ₁.map σ₁).prod (μ₂.map σ₂) = (μ₁.prod μ₂).map (Prod.map σ₁ σ₂) :=
  Measure.map_prod_map μ₁ μ₂ hσ₁ hσ₂

/-- `σ` is a stochastic simulation from the kernel `κ` to the kernel `η`:
the abstract transition at an observed state is the observation of the
concrete transition, `η (σ x) = (κ x).map σ`. -/
def StochSim (σ : X₁ → Y₁) (κ : Kernel X₁ X₁) (η : Kernel Y₁ Y₁) : Prop :=
  ∀ x, η (σ x) = (κ x).map σ

/-- A parallel composition of stochastic simulations is a stochastic
simulation of the parallel composition: `Prod.map σ₁ σ₂` carries
`κ₁ ∥ₖ κ₂` to `η₁ ∥ₖ η₂` (stated pointwise). -/
theorem stoch_pushKernel_prodMap {σ₁ : X₁ → Y₁} {σ₂ : X₂ → Y₂}
    (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂)
    {κ₁ : Kernel X₁ X₁} {κ₂ : Kernel X₂ X₂}
    {η₁ : Kernel Y₁ Y₁} {η₂ : Kernel Y₂ Y₂}
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂]
    [IsSFiniteKernel η₁] [IsSFiniteKernel η₂]
    (h₁ : StochSim σ₁ κ₁ η₁) (h₂ : StochSim σ₂ κ₂ η₂) :
    ∀ p : X₁ × X₂,
      (η₁ ∥ₖ η₂) (Prod.map σ₁ σ₂ p)
        = ((κ₁ ∥ₖ κ₂) p).map (Prod.map σ₁ σ₂) := by
  intro p
  rw [Kernel.parallelComp_apply, Kernel.parallelComp_apply]
  show (η₁ (σ₁ p.1)).prod (η₂ (σ₂ p.2)) = _
  rw [h₁ p.1, h₂ p.2]
  exact Measure.map_prod_map _ _ hσ₁ hσ₂

/-- The stochastic interchange law, bundled: parallel composition of
simulations is a simulation, and initial product laws transport
componentwise. -/
theorem stoch_interchange {σ₁ : X₁ → Y₁} {σ₂ : X₂ → Y₂}
    (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂)
    {κ₁ : Kernel X₁ X₁} {κ₂ : Kernel X₂ X₂}
    {η₁ : Kernel Y₁ Y₁} {η₂ : Kernel Y₂ Y₂}
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂]
    [IsSFiniteKernel η₁] [IsSFiniteKernel η₂]
    (h₁ : StochSim σ₁ κ₁ η₁) (h₂ : StochSim σ₂ κ₂ η₂)
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂] :
    StochSim (Prod.map σ₁ σ₂) (κ₁ ∥ₖ κ₂) (η₁ ∥ₖ η₂)
      ∧ (μ₁.map σ₁).prod (μ₂.map σ₂)
          = (μ₁.prod μ₂).map (Prod.map σ₁ σ₂) :=
  ⟨stoch_pushKernel_prodMap hσ₁ hσ₂ h₁ h₂,
   stoch_interchange_law μ₁ μ₂ hσ₁ hσ₂⟩

end StochInterchange

section StochFlatten

variable {Z₁ Z₂ Z₃ : Type*}
  [MeasurableSpace Z₁] [MeasurableSpace Z₂] [MeasurableSpace Z₃]

/-- Flattening a nested product of initial laws along the associativity
equivalence. -/
theorem stoch_flatten_law
    (μ₁ : Measure Z₁) (μ₂ : Measure Z₂) (μ₃ : Measure Z₃)
    [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] :
    ((μ₁.prod μ₂).prod μ₃).map (MeasurableEquiv.prodAssoc)
      = μ₁.prod (μ₂.prod μ₃) :=
  Measure.prodAssoc_prod

/-- The associativity equivalence is a stochastic simulation from the
nested parallel composition `(κ₁ ∥ₖ κ₂) ∥ₖ κ₃` to the flattened
`κ₁ ∥ₖ (κ₂ ∥ₖ κ₃)`. -/
theorem stoch_flattenNest_kernel
    (κ₁ : Kernel Z₁ Z₁) (κ₂ : Kernel Z₂ Z₂) (κ₃ : Kernel Z₃ Z₃)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel κ₃] :
    StochSim (MeasurableEquiv.prodAssoc (α := Z₁) (β := Z₂) (γ := Z₃))
      ((κ₁ ∥ₖ κ₂) ∥ₖ κ₃) (κ₁ ∥ₖ (κ₂ ∥ₖ κ₃)) := by
  intro p
  obtain ⟨⟨a, b⟩, c⟩ := p
  simp only [Kernel.parallelComp_apply]
  exact (Measure.prodAssoc_prod).symm

end StochFlatten

section StochCert

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Certificate integrals transport along a stochastic simulation: the
abstract one-step expectation of `V` at an observed state equals the
concrete one-step expectation of `V ∘ σ`. -/
theorem stoch_integral_transport {σ : X → Y}
    (hσ : Measurable σ) {κ : Kernel X X} {η : Kernel Y Y}
    (h : StochSim σ κ η) {V : Y → ℝ} (hV : Measurable V) (x : X) :
    ∫ y, V y ∂(η (σ x)) = ∫ z, V (σ z) ∂(κ x) := by
  rw [h x]
  exact integral_map hσ.aemeasurable hV.aestronglyMeasurable

/-- Drift certificate transport: if the lifted certificate `V ∘ σ`
satisfies the supermartingale drift condition for the concrete kernel `κ`,
then `V` satisfies it for the abstract kernel `η` at every observed
state. -/
theorem stoch_driftCert_transport {σ : X → Y}
    (hσ : Measurable σ) {κ : Kernel X X} {η : Kernel Y Y}
    (h : StochSim σ κ η) {V : Y → ℝ} (hV : Measurable V)
    (hdrift : ∀ x, ∫ z, V (σ z) ∂(κ x) ≤ V (σ x)) :
    ∀ x, ∫ y, V y ∂(η (σ x)) ≤ V (σ x) := by
  intro x
  rw [stoch_integral_transport hσ h hV x]
  exact hdrift x

end StochCert

#print axioms stoch_interchange_law
#print axioms stoch_pushKernel_prodMap
#print axioms stoch_interchange
#print axioms stoch_flatten_law
#print axioms stoch_flattenNest_kernel
#print axioms stoch_integral_transport
#print axioms stoch_driftCert_transport

end Qtsl.QtslCompose
