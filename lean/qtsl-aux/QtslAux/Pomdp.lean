import QtslAux.QtslCompose.StochCoherence
import Mathlib.Probability.Kernel.Composition.CompProd

/-! # POMDPs with Moore policies as Markov kernels

This module builds partially observable Markov decision processes over
measurable spaces and closes the loop with memory-carrying policies, so that
the joint state–memory process is an ordinary Markov kernel amenable to the
kernel-level simulation machinery (`StochSim`).

Principal declarations:

* `KPomdp S A Ω`: a transition kernel `trans : Kernel (S × A) S` (Markov)
  together with a measurable deterministic observation map `obs : S → Ω`.
* `MoorePolicy M A Ω`: a Markov memory-update kernel `step : Kernel (M × Ω) M`
  with a measurable action readout `act : M → A` (Moore-style: the action
  depends on memory only).
* `closedLoop P π : Kernel (S × M) (S × M)`: the closed-loop kernel, formed
  by composing the state leg (transition under the policy's action) with the
  memory leg (update on the new observation) via `Kernel.compProd`; it is
  Markov (`instIsMarkovKernel` instances throughout, including
  `parallelComp.isMarkovKernel` for `κ ∥ₖ η`).
* `KPomdp.par`, `MoorePolicy.par`: componentwise parallel composition of two
  POMDPs and of two policies, using the `middleFour` reshuffle.
* `ClosedLoopParInterchange`: the statement that closing the loop commutes
  with parallel composition, phrased as a `StochSim` along the corresponding
  product reshuffle.
* `PolicySim π π' σ`: a measurable map of memories intertwining actions and
  memory updates; `closedLoop_policySim` shows it induces a stochastic
  simulation `StochSim (Prod.map id σ)` between the closed loops.
* `FilterReduction`: a stochastic simulation from a history chain to a belief
  chain along a filtering map.
-/

namespace Qtsl.Pomdp

open MeasureTheory ProbabilityTheory Qtsl.QtslCompose
open scoped ProbabilityTheory

section ParallelMarkov

variable {X₁ Y₁ X₂ Y₂ : Type*}
  [MeasurableSpace X₁] [MeasurableSpace Y₁]
  [MeasurableSpace X₂] [MeasurableSpace Y₂]

instance parallelComp.isMarkovKernel {κ : Kernel X₁ Y₁} {η : Kernel X₂ Y₂}
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (κ ∥ₖ η) :=
  ⟨fun p => by rw [Kernel.parallelComp_apply]; infer_instance⟩

end ParallelMarkov

variable {S A Ω M M' : Type*}
  [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace Ω]
  [MeasurableSpace M] [MeasurableSpace M']

structure KPomdp (S A Ω : Type*) [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace Ω] where
  trans : Kernel (S × A) S
  obs : S → Ω
  obs_meas : Measurable obs
  trans_markov : IsMarkovKernel trans

attribute [instance] KPomdp.trans_markov

structure MoorePolicy (M A Ω : Type*) [MeasurableSpace M]
    [MeasurableSpace A] [MeasurableSpace Ω] where
  step : Kernel (M × Ω) M
  act : M → A
  act_meas : Measurable act
  step_markov : IsMarkovKernel step

attribute [instance] MoorePolicy.step_markov

section ClosedLoop

variable (P : KPomdp S A Ω) (π : MoorePolicy M A Ω)

noncomputable def stateLeg : Kernel (S × M) S :=
  P.trans.comap (fun p => (p.1, π.act p.2))
    (measurable_fst.prodMk (π.act_meas.comp measurable_snd))

noncomputable def memLeg : Kernel ((S × M) × S) M :=
  π.step.comap (fun q => (q.1.2, P.obs q.2))
    ((measurable_snd.comp measurable_fst).prodMk
      (P.obs_meas.comp measurable_snd))

instance : IsMarkovKernel (stateLeg P π) := by
  unfold stateLeg; infer_instance

instance : IsMarkovKernel (memLeg P π) := by
  unfold memLeg; infer_instance

noncomputable def closedLoop : Kernel (S × M) (S × M) :=
  Kernel.compProd (stateLeg P π) (memLeg P π)

instance : IsMarkovKernel (closedLoop P π) := by
  unfold closedLoop; infer_instance

end ClosedLoop

section Par

variable {S₁ A₁ Ω₁ S₂ A₂ Ω₂ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace A₁] [MeasurableSpace Ω₁]
  [MeasurableSpace S₂] [MeasurableSpace A₂] [MeasurableSpace Ω₂]

def middleFour (p : (S₁ × S₂) × (A₁ × A₂)) : (S₁ × A₁) × (S₂ × A₂) :=
  ((p.1.1, p.2.1), (p.1.2, p.2.2))

theorem measurable_middleFour :
    Measurable (middleFour (S₁ := S₁) (S₂ := S₂) (A₁ := A₁) (A₂ := A₂)) :=
  ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))

noncomputable def KPomdp.par (P₁ : KPomdp S₁ A₁ Ω₁)
    (P₂ : KPomdp S₂ A₂ Ω₂) :
    KPomdp (S₁ × S₂) (A₁ × A₂) (Ω₁ × Ω₂) where
  trans := (P₁.trans ∥ₖ P₂.trans).comap middleFour measurable_middleFour
  obs := Prod.map P₁.obs P₂.obs
  obs_meas := (P₁.obs_meas.comp measurable_fst).prodMk
    (P₂.obs_meas.comp measurable_snd)
  trans_markov := inferInstance

noncomputable def MoorePolicy.par {M₁ M₂ : Type*} [MeasurableSpace M₁]
    [MeasurableSpace M₂] (π₁ : MoorePolicy M₁ A₁ Ω₁)
    (π₂ : MoorePolicy M₂ A₂ Ω₂) :
    MoorePolicy (M₁ × M₂) (A₁ × A₂) (Ω₁ × Ω₂) where
  step := (π₁.step ∥ₖ π₂.step).comap middleFour measurable_middleFour
  act := Prod.map π₁.act π₂.act
  act_meas := (π₁.act_meas.comp measurable_fst).prodMk
    (π₂.act_meas.comp measurable_snd)
  step_markov := inferInstance

def ClosedLoopParInterchange (P₁ : KPomdp S₁ A₁ Ω₁) (P₂ : KPomdp S₂ A₂ Ω₂)
    {M₁ M₂ : Type*} [MeasurableSpace M₁] [MeasurableSpace M₂]
    (π₁ : MoorePolicy M₁ A₁ Ω₁) (π₂ : MoorePolicy M₂ A₂ Ω₂) : Prop :=
  StochSim (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    (closedLoop (P₁.par P₂) (π₁.par π₂))
    ((closedLoop P₁ π₁) ∥ₖ (closedLoop P₂ π₂))

end Par

section PolicySim

structure PolicySim (π : MoorePolicy M A Ω) (π' : MoorePolicy M' A Ω)
    (σ : M → M') : Prop where
  meas : Measurable σ
  act_eq : ∀ m, π'.act (σ m) = π.act m
  step_sim : ∀ m ω, π'.step (σ m, ω) = (π.step (m, ω)).map σ

variable (P : KPomdp S A Ω)
variable {π : MoorePolicy M A Ω} {π' : MoorePolicy M' A Ω} {σ : M → M'}

theorem stateLeg_policySim (h : PolicySim π π' σ) (s : S) (m : M) :
    stateLeg P π' (s, σ m) = stateLeg P π (s, m) := by
  simp only [stateLeg, Kernel.comap_apply, h.act_eq]

theorem closedLoop_policySim (h : PolicySim π π' σ) :
    StochSim (Prod.map (id : S → S) σ)
      (closedLoop P π) (closedLoop P π') := by
  intro p
  obtain ⟨s, m⟩ := p
  have hmap : Measurable (Prod.map (id : S → S) σ) :=
    measurable_id.prodMap h.meas
  simp only [Prod.map_apply', id_eq]
  ext t ht
  rw [Measure.map_apply hmap ht]
  simp only [closedLoop]
  rw [Kernel.compProd_apply ht, Kernel.compProd_apply (hmap ht)]
  rw [stateLeg_policySim P h s m]
  refine lintegral_congr fun s' => ?_
  simp only [memLeg, Kernel.comap_apply]
  rw [h.step_sim]
  rw [Measure.map_apply h.meas (measurable_prodMk_left ht)]
  congr 1

end PolicySim

section Filter

def FilterReduction {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (filt : H → B) (κHist : Kernel H H) (κBelief : Kernel B B) : Prop :=
  Measurable filt ∧ StochSim filt κHist κBelief

end Filter

#print axioms parallelComp.isMarkovKernel
#print axioms stateLeg_policySim
#print axioms closedLoop_policySim

end Qtsl.Pomdp
