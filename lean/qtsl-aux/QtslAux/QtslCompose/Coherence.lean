import QtslAux.QtslCompose.AGCompose
import QtslAux.QtslCompose.Flatten
import Mathlib.MeasureTheory.Measure.Map

/-! # Coherence of composition and abstraction

This module proves the interchange (coherence) laws relating assume-guarantee
composition, abstraction along an observation map, and parallel product —
the statements that make the composition operations commute, so certificates
may be discharged in whichever order is convenient.

Behavioural interchange (events on an outcome space):

* `interchange_row_pullback`, `interchange_wiring_pullback`: preimages under
  an observation map `σ : Ω → Ω'` preserve conjunction rows and wiring
  conditions.
* `interchange_behavioral`: composing abstract contracts and then pulling
  back agrees with pulling back and then composing — an almost-everywhere
  assume-guarantee conclusion on the abstract space transports to the
  concrete space.
* `interchange_conclusion_transport`: the transported conclusion can be
  restated under the pushforward measure `μ.map σ`.

Kernel interchange (finite-state chains, as in `Flatten`):

* `push_prodMap`, `pushKernel_prodMap`: pushforward along `Prod.map σ₁ σ₂`
  commutes with product distributions and product kernels, so a product of
  simulations is a simulation of the product.
* `interchange_kernel`, `interchange_kernel'`: abstracting a product chain
  componentwise and taking `n`-step laws commute — the pushforward of the
  product law is the product of the pushforward laws.

Flattening of nested products:

* `prodKernel_assoc`, `prodDist_assoc`, `flattenNest_pushKernel`,
  `flattenNest_law`: reassociating a nested product `(K₁ × K₂) × K₃` along
  `Equiv.prodAssoc` is a simulation, and the corresponding `n`-step laws
  agree.
-/

namespace Qtsl.QtslCompose

open MeasureTheory

section InterchangeBehavioral

variable {n : ℕ} {Ω Ω' : Type*}

theorem interchange_row_pullback (σ : Ω → Ω') (conformExt' : Set Ω')
    (sat' : Fin n → Set Ω') :
    σ ⁻¹' (conformExt' ∩ ⋂ j, sat' j)
      = (σ ⁻¹' conformExt') ∩ ⋂ j, σ ⁻¹' (sat' j) := by
  simp [Set.preimage_iInter]

theorem interchange_wiring_pullback (S : System n) (σ : Ω → Ω')
    {conformExt' : Set Ω'} {conform' sat' : Fin n → Set Ω'}
    (hw' : ∀ j, conformExt' ∩ (⋂ i ∈ S.upstream j, sat' i) ⊆ conform' j) :
    ∀ j, (σ ⁻¹' conformExt') ∩ (⋂ i ∈ S.upstream j, σ ⁻¹' (sat' i))
      ⊆ σ ⁻¹' (conform' j) := by
  intro j ω hω
  exact hw' j ⟨hω.1, Set.mem_iInter₂.2 fun i hi =>
    Set.mem_iInter₂.1 hω.2 i hi⟩

/-- Behavioural interchange: assume-guarantee contracts stated on the
abstract space `Ω'` and satisfied almost everywhere by the observed process
`σ ∘ ·` yield the composed conclusion on the concrete space — pulling back
along `σ` commutes with composition. -/
theorem interchange_behavioral [MeasurableSpace Ω] {μ : Measure Ω}
    (S : System n) (σ : Ω → Ω') (conformExt' : Set Ω')
    (conform' sat' : Fin n → Set Ω') {satOut' : Set Ω'}
    (hw' : ∀ j, conformExt' ∩ (⋂ i ∈ S.upstream j, sat' i) ⊆ conform' j)
    (h : ∀ j, ∀ᵐ ω ∂μ, σ ω ∈ conform' j → σ ω ∈ sat' j)
    (hout' : conformExt' ∩ (⋂ j, sat' j) ⊆ satOut') :
    ∀ᵐ ω ∂μ, ω ∈ σ ⁻¹' conformExt' → ω ∈ σ ⁻¹' satOut' :=
  qualitative S (σ ⁻¹' conformExt') (fun j => σ ⁻¹' (conform' j))
    (fun j => σ ⁻¹' (sat' j))
    (interchange_wiring_pullback S σ hw') h
    (by rw [← interchange_row_pullback]; exact Set.preimage_mono hout')

/-- The composed conclusion holds almost everywhere for the pushforward
measure `μ.map σ` if and only if it holds almost everywhere for `μ` about
the observed outcome `σ ω`. -/
theorem interchange_conclusion_transport [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} {σ : Ω → Ω'}
    (hσ : AEMeasurable σ μ) {conformExt' satOut' : Set Ω'}
    (hm : MeasurableSet {ω' : Ω' | ω' ∈ conformExt' → ω' ∈ satOut'}) :
    (∀ᵐ ω' ∂(μ.map σ), ω' ∈ conformExt' → ω' ∈ satOut')
      ↔ ∀ᵐ ω ∂μ, σ ω ∈ conformExt' → σ ω ∈ satOut' :=
  ae_map_iff hσ hm

end InterchangeBehavioral

section InterchangeKernel

open Finset
open Qtsl.QRelChain

noncomputable section

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁]
  [Fintype β₂] [DecidableEq β₁] [DecidableEq β₂]

omit [Fintype β₁] [Fintype β₂] in

/-- Pushforward along `Prod.map σ₁ σ₂` sends a product distribution to the
product of the pushforwards. -/
theorem push_prodMap (σ₁ : α₁ → β₁) (σ₂ : α₂ → β₂) (μ₁ : α₁ → ℝ)
    (μ₂ : α₂ → ℝ) :
    push (Prod.map σ₁ σ₂) (prodDist μ₁ μ₂)
      = prodDist (push σ₁ μ₁) (push σ₂ μ₂) := by
  funext b
  unfold push prodDist
  have hfil : (univ.filter fun s : α₁ × α₂ => Prod.map σ₁ σ₂ s = b)
      = (univ.filter fun s₁ => σ₁ s₁ = b.1)
          ×ˢ (univ.filter fun s₂ => σ₂ s₂ = b.2) := by
    ext s
    simp [Finset.mem_product, Prod.ext_iff, Prod.map]
  rw [hfil, Finset.sum_product, Finset.sum_mul_sum]

omit [Fintype β₁] [Fintype β₂] in

/-- A product of simulations is a simulation of the product: if `σ₁`
intertwines `K₁` with `Q₁` and `σ₂` intertwines `K₂` with `Q₂`, then
`Prod.map σ₁ σ₂` intertwines the product kernels. -/
theorem pushKernel_prodMap {σ₁ : α₁ → β₁} {σ₂ : α₂ → β₂}
    {K₁ : α₁ → α₁ → ℝ} {K₂ : α₂ → α₂ → ℝ}
    {Q₁ : β₁ → β₁ → ℝ} {Q₂ : β₂ → β₂ → ℝ}
    (h₁ : PushKernel σ₁ K₁ Q₁) (h₂ : PushKernel σ₂ K₂ Q₂) :
    PushKernel (Prod.map σ₁ σ₂) (prodKernel K₁ K₂) (prodKernel Q₁ Q₂) := by
  intro p
  have hrow : prodKernel K₁ K₂ p = prodDist (K₁ p.1) (K₂ p.2) := rfl
  rw [hrow, push_prodMap, h₁ p.1, h₂ p.2]
  rfl

/-- Kernel interchange: abstracting the product chain along
`Prod.map σ₁ σ₂` after `n` steps gives the product of the abstract `n`-step
laws started from the pushforward initial distributions. -/
theorem interchange_kernel {σ₁ : α₁ → β₁} {σ₂ : α₂ → β₂}
    {K₁ : α₁ → α₁ → ℝ} {K₂ : α₂ → α₂ → ℝ}
    {Q₁ : β₁ → β₁ → ℝ} {Q₂ : β₂ → β₂ → ℝ}
    (h₁ : PushKernel σ₁ K₁ Q₁) (h₂ : PushKernel σ₂ K₂ Q₂)
    (μ₁ : α₁ → ℝ) (μ₂ : α₂ → ℝ) (n : ℕ) :
    push (Prod.map σ₁ σ₂) (law (prodKernel K₁ K₂) (prodDist μ₁ μ₂) n)
      = prodDist (law Q₁ (push σ₁ μ₁) n) (law Q₂ (push σ₂ μ₂) n) := by
  rw [push_law (pushKernel_prodMap h₁ h₂), push_prodMap,
    law_prodKernel Q₁ Q₂ (push σ₁ μ₁) (push σ₂ μ₂) n]

/-- Variant of `interchange_kernel` with the abstraction applied after the
concrete evolution: the pushforward of the product law is the product of the
pushforwards of the component laws. -/
theorem interchange_kernel' {σ₁ : α₁ → β₁} {σ₂ : α₂ → β₂}
    {K₁ : α₁ → α₁ → ℝ} {K₂ : α₂ → α₂ → ℝ}
    {Q₁ : β₁ → β₁ → ℝ} {Q₂ : β₂ → β₂ → ℝ}
    (h₁ : PushKernel σ₁ K₁ Q₁) (h₂ : PushKernel σ₂ K₂ Q₂)
    (μ₁ : α₁ → ℝ) (μ₂ : α₂ → ℝ) (n : ℕ) :
    push (Prod.map σ₁ σ₂) (law (prodKernel K₁ K₂) (prodDist μ₁ μ₂) n)
      = prodDist (push σ₁ (law K₁ μ₁ n)) (push σ₂ (law K₂ μ₂ n)) := by
  rw [interchange_kernel h₁ h₂ μ₁ μ₂ n, push_law h₁, push_law h₂]

end

end InterchangeKernel

section FlattenNest

open Finset
open Qtsl.QRelChain

noncomputable section

variable {γ₁ γ₂ γ₃ : Type*} [Fintype γ₁] [Fintype γ₂] [Fintype γ₃]
  [DecidableEq γ₁] [DecidableEq γ₂] [DecidableEq γ₃]

theorem push_equiv {α β : Type*} [Fintype α] [DecidableEq β] (e : α ≃ β)
    (μ : α → ℝ) : push (⇑e) μ = fun b => μ (e.symm b) := by
  funext b
  unfold push
  have hfil : (univ.filter fun s => e s = b) = {e.symm b} := by
    ext s
    simp [Equiv.eq_symm_apply]
  rw [hfil, Finset.sum_singleton]

omit [Fintype γ₁] [Fintype γ₂] [Fintype γ₃] [DecidableEq γ₁] [DecidableEq γ₂]
  [DecidableEq γ₃] in

theorem prodKernel_assoc (K₁ : γ₁ → γ₁ → ℝ) (K₂ : γ₂ → γ₂ → ℝ)
    (K₃ : γ₃ → γ₃ → ℝ) (p q : (γ₁ × γ₂) × γ₃) :
    prodKernel (prodKernel K₁ K₂) K₃ p q
      = prodKernel K₁ (prodKernel K₂ K₃)
          (Equiv.prodAssoc γ₁ γ₂ γ₃ p) (Equiv.prodAssoc γ₁ γ₂ γ₃ q) := by
  simp only [prodKernel, Equiv.prodAssoc, Equiv.coe_fn_mk]
  ring

omit [Fintype γ₁] [Fintype γ₂] [Fintype γ₃] [DecidableEq γ₁] [DecidableEq γ₂]
  [DecidableEq γ₃] in

theorem prodDist_assoc (μ₁ : γ₁ → ℝ) (μ₂ : γ₂ → ℝ) (μ₃ : γ₃ → ℝ)
    (p : (γ₁ × γ₂) × γ₃) :
    prodDist (prodDist μ₁ μ₂) μ₃ p
      = prodDist μ₁ (prodDist μ₂ μ₃) (Equiv.prodAssoc γ₁ γ₂ γ₃ p) := by
  simp only [prodDist, Equiv.prodAssoc, Equiv.coe_fn_mk]
  ring

/-- Reassociation is a simulation: `Equiv.prodAssoc` intertwines the nested
product kernel `(K₁ × K₂) × K₃` with the flattened `K₁ × (K₂ × K₃)`. -/
theorem flattenNest_pushKernel (K₁ : γ₁ → γ₁ → ℝ) (K₂ : γ₂ → γ₂ → ℝ)
    (K₃ : γ₃ → γ₃ → ℝ) :
    PushKernel (⇑(Equiv.prodAssoc γ₁ γ₂ γ₃))
      (prodKernel (prodKernel K₁ K₂) K₃)
      (prodKernel K₁ (prodKernel K₂ K₃)) := by
  intro p
  funext q
  have h1 : push (⇑(Equiv.prodAssoc γ₁ γ₂ γ₃))
        (prodKernel (prodKernel K₁ K₂) K₃ p) q
      = prodKernel (prodKernel K₁ K₂) K₃ p
          ((Equiv.prodAssoc γ₁ γ₂ γ₃).symm q) :=
    congrFun (push_equiv (Equiv.prodAssoc γ₁ γ₂ γ₃)
      (prodKernel (prodKernel K₁ K₂) K₃ p)) q
  rw [h1, prodKernel_assoc K₁ K₂ K₃ p ((Equiv.prodAssoc γ₁ γ₂ γ₃).symm q),
    Equiv.apply_symm_apply]

/-- Flattening coherence at the level of laws: transporting the `n`-step
law of the nested product along `Equiv.prodAssoc` gives exactly the `n`-step
law of the flattened product with the correspondingly flattened initial
distribution. -/
theorem flattenNest_law (K₁ : γ₁ → γ₁ → ℝ) (K₂ : γ₂ → γ₂ → ℝ)
    (K₃ : γ₃ → γ₃ → ℝ) (μ₁ : γ₁ → ℝ) (μ₂ : γ₂ → ℝ) (μ₃ : γ₃ → ℝ)
    (n : ℕ) :
    push (⇑(Equiv.prodAssoc γ₁ γ₂ γ₃))
        (law (prodKernel (prodKernel K₁ K₂) K₃)
          (prodDist (prodDist μ₁ μ₂) μ₃) n)
      = law (prodKernel K₁ (prodKernel K₂ K₃))
          (prodDist μ₁ (prodDist μ₂ μ₃)) n := by
  rw [push_law (flattenNest_pushKernel K₁ K₂ K₃)]
  congr 1
  funext b
  have h1 : push (⇑(Equiv.prodAssoc γ₁ γ₂ γ₃))
        (prodDist (prodDist μ₁ μ₂) μ₃) b
      = prodDist (prodDist μ₁ μ₂) μ₃
          ((Equiv.prodAssoc γ₁ γ₂ γ₃).symm b) :=
    congrFun (push_equiv (Equiv.prodAssoc γ₁ γ₂ γ₃)
      (prodDist (prodDist μ₁ μ₂) μ₃)) b
  rw [h1, prodDist_assoc μ₁ μ₂ μ₃ ((Equiv.prodAssoc γ₁ γ₂ γ₃).symm b),
    Equiv.apply_symm_apply]

end

end FlattenNest

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.interchange_row_pullback
#print axioms Qtsl.QtslCompose.interchange_wiring_pullback
#print axioms Qtsl.QtslCompose.interchange_behavioral
#print axioms Qtsl.QtslCompose.interchange_conclusion_transport
#print axioms Qtsl.QtslCompose.push_prodMap
#print axioms Qtsl.QtslCompose.pushKernel_prodMap
#print axioms Qtsl.QtslCompose.interchange_kernel
#print axioms Qtsl.QtslCompose.interchange_kernel'
#print axioms Qtsl.QtslCompose.push_equiv
#print axioms Qtsl.QtslCompose.prodKernel_assoc
#print axioms Qtsl.QtslCompose.prodDist_assoc
#print axioms Qtsl.QtslCompose.flattenNest_pushKernel
#print axioms Qtsl.QtslCompose.flattenNest_law
