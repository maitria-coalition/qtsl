import QtslAux.Wasserstein.Coupling
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Gluing couplings and the triangle inequality for `W2edist`

Given a coupling `π₁₂` of `(μ₁, μ₂)` and a coupling `π₂₃` of `(μ₂, μ₃)` on a standard Borel space,
disintegration along the shared marginal (`Measure.condKernel`) glues them into a measure on
`X × X × X` whose outer marginal couples `μ₁` with `μ₃`; Minkowski's inequality then bounds the
cost of the glued coupling.

Main declarations:

* `measure_ext_prod`, `map_compProd_kernelProd_left`, `map_compProd_kernelProd_right`,
  `map_compProd_comap`: marginal computations for composition products of kernels;
* `IsCoupling.compProd_condKernel`: a coupling is recovered as the composition product of its
  first marginal with its conditional kernel;
* `W2edist_le_add_of_couplings`: `W2edist μ₁ μ₃ ≤ cost2 π₁₂ ^ (1/2) + cost2 π₂₃ ^ (1/2)`;
* `W2edist_triangle`: the triangle inequality for the Wasserstein-2 extended distance.
-/

namespace Qtsl

namespace Wasserstein

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

section Plumbing

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem measure_ext_prod {ρ₁ ρ₂ : Measure (α × β)} [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂]
    (h : ∀ ⦃s : Set α⦄ ⦃t : Set β⦄, MeasurableSet s → MeasurableSet t →
      ρ₁ (s ×ˢ t) = ρ₂ (s ×ˢ t)) : ρ₁ = ρ₂ := by
  refine ext_of_generate_finite
    (image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set β | MeasurableSet t})
    generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact h hs ht
  · simpa using h MeasurableSet.univ MeasurableSet.univ

theorem nonempty_of_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    Nonempty α := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have h0 : μ univ = 0 := by
    rw [univ_eq_empty_iff.mpr hemp, measure_empty]
  rw [measure_univ] at h0
  exact one_ne_zero h0

theorem map_compProd_kernelProd_left (m : Measure α) [IsFiniteMeasure m]
    (κ : Kernel α β) (η : Kernel α γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (m ⊗ₘ (κ ×ₖ η)).map (fun p : α × β × γ => (p.1, p.2.1)) = m ⊗ₘ κ := by
  have hmeas : Measurable fun p : α × β × γ => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  refine measure_ext_prod fun s t hs ht => ?_
  have hpre : (fun p : α × β × γ => (p.1, p.2.1)) ⁻¹' (s ×ˢ t)
      = s ×ˢ (t ×ˢ (univ : Set γ)) := by
    ext p
    simp
  rw [Measure.map_apply hmeas (hs.prod ht), hpre,
    Measure.compProd_apply_prod hs (ht.prod MeasurableSet.univ),
    Measure.compProd_apply_prod hs ht]
  refine setLIntegral_congr_fun hs ?_
  intro a _
  simp only [Kernel.prod_apply_prod, measure_univ, mul_one]

theorem map_compProd_kernelProd_right (m : Measure α) [IsFiniteMeasure m]
    (κ : Kernel α β) (η : Kernel α γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (m ⊗ₘ (κ ×ₖ η)).map (fun p : α × β × γ => (p.1, p.2.2)) = m ⊗ₘ η := by
  have hmeas : Measurable fun p : α × β × γ => (p.1, p.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  refine measure_ext_prod fun s t hs ht => ?_
  have hpre : (fun p : α × β × γ => (p.1, p.2.2)) ⁻¹' (s ×ˢ t)
      = s ×ˢ ((univ : Set β) ×ˢ t) := by
    ext p
    simp
  rw [Measure.map_apply hmeas (hs.prod ht), hpre,
    Measure.compProd_apply_prod hs (MeasurableSet.univ.prod ht),
    Measure.compProd_apply_prod hs ht]
  refine setLIntegral_congr_fun hs ?_
  intro a _
  simp only [Kernel.prod_apply_prod, measure_univ, one_mul]

theorem map_compProd_comap (m : Measure β) [IsProbabilityMeasure m]
    {g : β → α} (hg : Measurable g) (κ : Kernel α γ) [IsMarkovKernel κ] :
    (m ⊗ₘ (κ.comap g hg)).map (fun p : β × γ => (g p.1, p.2))
      = (m.map g) ⊗ₘ κ := by
  haveI : IsProbabilityMeasure (m.map g) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hmeas : Measurable fun p : β × γ => (g p.1, p.2) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  refine measure_ext_prod fun s t hs ht => ?_
  have hpre : (fun p : β × γ => (g p.1, p.2)) ⁻¹' (s ×ˢ t) = (g ⁻¹' s) ×ˢ t := by
    ext p
    simp
  rw [Measure.map_apply hmeas (hs.prod ht), hpre,
    Measure.compProd_apply_prod (hg hs) ht, Measure.compProd_apply_prod hs ht,
    setLIntegral_map hs (Kernel.measurable_coe κ ht) hg]
  refine setLIntegral_congr_fun (hg hs) ?_
  intro b _
  simp only [Kernel.comap_apply]

end Plumbing

section Disintegrate

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

theorem IsCoupling.compProd_condKernel {π : Measure (X × X)} {μ ν : Measure X}
    [IsFiniteMeasure π] (h : IsCoupling π μ ν) :
    μ ⊗ₘ π.condKernel = π := by
  have hd := π.disintegrate π.condKernel
  rwa [h.1] at hd

end Disintegrate

section Triangle

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [SecondCountableTopology X] [BorelSpace X] [StandardBorelSpace X]

theorem W2edist_le_add_of_couplings {μ₁ μ₂ μ₃ : Measure X}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]
    {π₁₂ π₂₃ : Measure (X × X)}
    (h₁₂ : IsCoupling π₁₂ μ₁ μ₂) (h₂₃ : IsCoupling π₂₃ μ₂ μ₃) :
    W2edist μ₁ μ₃ ≤ cost2 π₁₂ ^ (1 / 2 : ℝ) + cost2 π₂₃ ^ (1 / 2 : ℝ) := by
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ₂
  haveI hπ₁₂p : IsProbabilityMeasure π₁₂ := h₁₂.isProbabilityMeasure
  haveI hπ₂₃p : IsProbabilityMeasure π₂₃ := h₂₃.isProbabilityMeasure

  set ρ : Measure (X × X) := π₁₂.map Prod.swap with hρ_def
  have hρ : IsCoupling ρ μ₂ μ₁ := h₁₂.swap
  haveI : IsProbabilityMeasure ρ := hρ.isProbabilityMeasure
  set κ₁ : Kernel X X := ρ.condKernel with hκ₁_def
  set κ₃ : Kernel X X := π₂₃.condKernel with hκ₃_def
  have hκ₁ : μ₂ ⊗ₘ κ₁ = ρ := hρ.compProd_condKernel
  have hκ₃ : μ₂ ⊗ₘ κ₃ = π₂₃ := h₂₃.compProd_condKernel

  set γ : Measure (X × X × X) := μ₂ ⊗ₘ (κ₁ ×ₖ κ₃) with hγ_def
  have hγ₁ : γ.map (fun p : X × X × X => (p.1, p.2.1)) = ρ := by
    rw [hγ_def, map_compProd_kernelProd_left, hκ₁]
  have hγ₂ : γ.map (fun p : X × X × X => (p.1, p.2.2)) = π₂₃ := by
    rw [hγ_def, map_compProd_kernelProd_right, hκ₃]

  have hprPair : Measurable fun p : X × X × X => (p.2.1, p.2.2) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  have hpr₁ : Measurable fun p : X × X × X => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hpr₂ : Measurable fun p : X × X × X => (p.1, p.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  set θ : Measure (X × X) := γ.map (fun p : X × X × X => (p.2.1, p.2.2)) with hθ_def
  have hθ : IsCoupling θ μ₁ μ₃ := by
    constructor
    ·
      rw [hθ_def, Measure.fst, Measure.map_map measurable_fst hprPair,
        ← hρ.2, ← hγ₁, Measure.snd, Measure.map_map measurable_snd hpr₁]
      rfl
    ·
      rw [hθ_def, Measure.snd, Measure.map_map measurable_snd hprPair,
        ← h₂₃.2, ← hγ₂, Measure.snd, Measure.map_map measurable_snd hpr₂]
      rfl

  have hedist : Measurable fun p : X × X => edist p.1 p.2 := measurable_edist
  have hF : Measurable fun p : X × X × X => edist p.2.1 p.1 :=
    hedist.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hG : Measurable fun p : X × X × X => edist p.1 p.2.2 :=
    hedist.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hsq2 : Measurable fun q : X × X => edist q.1 q.2 ^ (2 : ℝ) :=
    ENNReal.continuous_rpow_const.measurable.comp hedist
  have hcostθ : cost2 θ = ∫⁻ p : X × X × X, edist p.2.1 p.2.2 ^ (2 : ℝ) ∂γ := by
    rw [cost2, hθ_def]
    exact lintegral_map hsq2 hprPair
  have hptwise : ∀ p : X × X × X, edist p.2.1 p.2.2 ^ (2 : ℝ)
      ≤ (edist p.2.1 p.1 + edist p.1 p.2.2) ^ (2 : ℝ) := fun p =>
    ENNReal.rpow_le_rpow (edist_triangle _ _ _) (by norm_num)
  have hmink := ENNReal.lintegral_Lp_add_le (μ := γ)
    hF.aemeasurable hG.aemeasurable (by norm_num : (1:ℝ) ≤ 2)
  have hFcost : (∫⁻ p : X × X × X, edist p.2.1 p.1 ^ (2 : ℝ) ∂γ) = cost2 π₁₂ := by
    have hsq_swap : Measurable fun q : X × X => edist q.2 q.1 ^ (2 : ℝ) :=
      ENNReal.continuous_rpow_const.measurable.comp
        (hedist.comp (measurable_snd.prodMk measurable_fst))
    have h1 : (∫⁻ p : X × X × X, edist p.2.1 p.1 ^ (2 : ℝ) ∂γ)
        = ∫⁻ q : X × X, edist q.2 q.1 ^ (2 : ℝ) ∂ρ := by
      rw [← hγ₁]
      exact (lintegral_map hsq_swap hpr₁).symm
    have h2 : (∫⁻ q : X × X, edist q.2 q.1 ^ (2 : ℝ) ∂ρ) = cost2 π₁₂ := by
      rw [hρ_def]
      have hswap : (Prod.swap : X × X → X × X)
          = ⇑(MeasurableEquiv.prodComm (α := X) (β := X)) := rfl
      rw [hswap, lintegral_map_equiv]
      rfl
    rw [h1, h2]
  have hGcost : (∫⁻ p : X × X × X, edist p.1 p.2.2 ^ (2 : ℝ) ∂γ) = cost2 π₂₃ := by
    rw [cost2, ← hγ₂]
    exact (lintegral_map hsq2 hpr₂).symm
  calc W2edist μ₁ μ₃ ≤ cost2 θ ^ (1 / 2 : ℝ) := W2edist_le_cost hθ
    _ ≤ (∫⁻ p, (edist p.2.1 p.1 + edist p.1 p.2.2) ^ (2 : ℝ) ∂γ) ^ (1 / 2 : ℝ) := by
        rw [hcostθ]
        exact ENNReal.rpow_le_rpow (lintegral_mono hptwise) (by norm_num)
    _ ≤ (∫⁻ p, edist p.2.1 p.1 ^ (2 : ℝ) ∂γ) ^ (1 / 2 : ℝ)
        + (∫⁻ p, edist p.1 p.2.2 ^ (2 : ℝ) ∂γ) ^ (1 / 2 : ℝ) := hmink
    _ = cost2 π₁₂ ^ (1 / 2 : ℝ) + cost2 π₂₃ ^ (1 / 2 : ℝ) := by
        rw [hFcost, hGcost]

theorem W2edist_triangle {μ₁ μ₂ μ₃ : Measure X}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃] :
    W2edist μ₁ μ₃ ≤ W2edist μ₁ μ₂ + W2edist μ₂ μ₃ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  have h12 : W2edist μ₁ μ₂ ≠ ∞ := (ne_of_lt (lt_of_le_of_lt le_self_add hfin))
  have h23 : W2edist μ₂ μ₃ ≠ ∞ := (ne_of_lt (lt_of_le_of_lt le_add_self hfin))
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.ofNat_ne_top,
      or_false]
    exact_mod_cast hε.ne'
  obtain ⟨π₁₂, hc₁₂, hlt₁⟩ := exists_coupling_of_lt
    (ENNReal.lt_add_right h12 hε2)
  obtain ⟨π₂₃, hc₂₃, hlt₂⟩ := exists_coupling_of_lt
    (ENNReal.lt_add_right h23 hε2)
  calc W2edist μ₁ μ₃
      ≤ cost2 π₁₂ ^ (1 / 2 : ℝ) + cost2 π₂₃ ^ (1 / 2 : ℝ) :=
        W2edist_le_add_of_couplings hc₁₂ hc₂₃
    _ ≤ (W2edist μ₁ μ₂ + ε / 2) + (W2edist μ₂ μ₃ + ε / 2) :=
        add_le_add hlt₁.le hlt₂.le
    _ = W2edist μ₁ μ₂ + W2edist μ₂ μ₃ + ε := by
        rw [add_add_add_comm, ENNReal.add_halves]

end Triangle

end Wasserstein

end Qtsl
