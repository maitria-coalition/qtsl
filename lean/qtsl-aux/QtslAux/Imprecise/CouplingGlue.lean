import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Couplings concentrated on agreement of pushforwards

This module proves `exists_coupling_of_map_eq`: if two probability measures
`μ₁` on `Ω₁` and `μ₂` on `Ω₂` (standard Borel spaces) have equal pushforwards
along measurable maps `r : Ω₁ → Y` and `s : Ω₂ → Y`, then there is a coupling
`ν` on `Ω₁ × Ω₂` — a probability measure with first marginal `μ₁` and second
marginal `μ₂` — that gives full measure to the agreement set
`{p | r p.1 = s p.2}`.

The construction disintegrates each graph measure `μᵢ.map (fun a => (rᵢ a, a))`
over the common law `μ₁.map r = μ₂.map s` using conditional kernels
(`Measure.condKernel`), forms the fibrewise product of the two conditional
kernels, and integrates against the common law. The marginal identities and the
almost-sure agreement all follow from the disintegration identities.
-/

open MeasureTheory ProbabilityTheory

namespace Qtsl.Imprecise

variable {Ω₁ Ω₂ Y : Type*}
  [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁]
  [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂]
  [MeasurableSpace Y] [MeasurableEq Y]

theorem exists_coupling_of_map_eq
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {r : Ω₁ → Y} {s : Ω₂ → Y} (hr : Measurable r) (hs : Measurable s)
    (h : μ₁.map r = μ₂.map s) :
    ∃ ν : Measure (Ω₁ × Ω₂), IsProbabilityMeasure ν ∧
      ν.map Prod.fst = μ₁ ∧ ν.map Prod.snd = μ₂ ∧
      ν {p : Ω₁ × Ω₂ | r p.1 = s p.2} = 1 := by

  haveI : Nonempty Ω₁ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : μ₁ Set.univ = 0 := by
      simp [Set.univ_eq_empty_iff.mpr hne]
    rw [measure_univ] at h0
    exact one_ne_zero h0
  haveI : Nonempty Ω₂ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : μ₂ Set.univ = 0 := by
      simp [Set.univ_eq_empty_iff.mpr hne]
    rw [measure_univ] at h0
    exact one_ne_zero h0

  have hg₁ : Measurable fun a : Ω₁ => (r a, a) := hr.prodMk measurable_id
  have hg₂ : Measurable fun a : Ω₂ => (s a, a) := hs.prodMk measurable_id
  haveI : IsProbabilityMeasure (μ₁.map fun a => (r a, a)) :=
    Measure.isProbabilityMeasure_map hg₁.aemeasurable
  haveI : IsProbabilityMeasure (μ₂.map fun a => (s a, a)) :=
    Measure.isProbabilityMeasure_map hg₂.aemeasurable

  set lam : Measure Y := μ₁.map r with hlam
  haveI : IsProbabilityMeasure lam :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  have hρ₁fst : (μ₁.map fun a => (r a, a)).fst = lam :=
    Measure.fst_map_prodMk measurable_id
  have hρ₂fst' : (μ₂.map fun a => (s a, a)).fst = μ₂.map s :=
    Measure.fst_map_prodMk measurable_id
  have hρ₂fst : (μ₂.map fun a => (s a, a)).fst = lam :=
    hρ₂fst'.trans h.symm

  set κ₁ := (μ₁.map fun a => (r a, a)).condKernel with hκ₁def
  set κ₂ := (μ₂.map fun a => (s a, a)).condKernel with hκ₂def
  have hd₁ : lam ⊗ₘ κ₁ = μ₁.map fun a => (r a, a) := by
    rw [hκ₁def, ← hρ₁fst]
    exact (μ₁.map fun a => (r a, a)).disintegrate _
  have hd₂ : lam ⊗ₘ κ₂ = μ₂.map fun a => (s a, a) := by
    rw [hκ₂def, ← hρ₂fst]
    exact (μ₂.map fun a => (s a, a)).disintegrate _

  haveI hMk : IsMarkovKernel (κ₁ ×ₖ κ₂) := inferInstance
  set ν' : Measure (Y × Ω₁ × Ω₂) := lam ⊗ₘ (κ₁ ×ₖ κ₂) with hν'def
  haveI : IsProbabilityMeasure ν' := by
    rw [hν'def]; infer_instance
  refine ⟨ν'.map Prod.snd, Measure.isProbabilityMeasure_map
    measurable_snd.aemeasurable, ?_, ?_, ?_⟩

  · rw [Measure.map_map measurable_fst measurable_snd]
    ext B hB
    have hpre : MeasurableSet ((Prod.fst ∘ Prod.snd : Y × Ω₁ × Ω₂ → Ω₁)
        ⁻¹' B) := (measurable_fst.comp measurable_snd) hB
    rw [Measure.map_apply (measurable_fst.comp measurable_snd) hB,
      hν'def, Measure.compProd_apply hpre]
    have hcalc : ∀ y : Y, (κ₁ ×ₖ κ₂) y
        (Prod.mk y ⁻¹' ((Prod.fst ∘ Prod.snd) ⁻¹' B)) = κ₁ y B := by
      intro y
      have hsec : (Prod.mk y ⁻¹' ((Prod.fst ∘ Prod.snd) ⁻¹' B)
          : Set (Ω₁ × Ω₂)) = B ×ˢ Set.univ := by
        ext ⟨u, w⟩; simp
      rw [hsec, Kernel.prod_apply, Measure.prod_prod, measure_univ,
        mul_one]
    simp_rw [hcalc]
    have hup : ∫⁻ y, κ₁ y B ∂lam
        = (lam ⊗ₘ κ₁) (Set.univ ×ˢ B) := by
      rw [Measure.compProd_apply (MeasurableSet.univ.prod hB)]
      congr 1
      ext y
      congr 1
      ext u; simp
    rw [hup, hd₁,
      Measure.map_apply hg₁ (MeasurableSet.univ.prod hB)]
    congr 1
    ext a; simp

  · rw [Measure.map_map measurable_snd measurable_snd]
    ext B hB
    have hpre : MeasurableSet ((Prod.snd ∘ Prod.snd : Y × Ω₁ × Ω₂ → Ω₂)
        ⁻¹' B) := (measurable_snd.comp measurable_snd) hB
    rw [Measure.map_apply (measurable_snd.comp measurable_snd) hB,
      hν'def, Measure.compProd_apply hpre]
    have hcalc : ∀ y : Y, (κ₁ ×ₖ κ₂) y
        (Prod.mk y ⁻¹' ((Prod.snd ∘ Prod.snd) ⁻¹' B)) = κ₂ y B := by
      intro y
      have hsec : (Prod.mk y ⁻¹' ((Prod.snd ∘ Prod.snd) ⁻¹' B)
          : Set (Ω₁ × Ω₂)) = Set.univ ×ˢ B := by
        ext ⟨u, w⟩; simp
      rw [hsec, Kernel.prod_apply, Measure.prod_prod, measure_univ,
        one_mul]
    simp_rw [hcalc]
    have hup : ∫⁻ y, κ₂ y B ∂lam
        = (lam ⊗ₘ κ₂) (Set.univ ×ˢ B) := by
      rw [Measure.compProd_apply (MeasurableSet.univ.prod hB)]
      congr 1
      ext y
      congr 1
      ext u; simp
    rw [hup, hd₂,
      Measure.map_apply hg₂ (MeasurableSet.univ.prod hB)]
    congr 1
    ext a; simp

  · have hGmeas : MeasurableSet {p : Ω₁ × Ω₂ | r p.1 = s p.2} :=
      measurableSet_eq_fun (hr.comp measurable_fst)
        (hs.comp measurable_snd)
    rw [Measure.map_apply measurable_snd hGmeas]

    have hB₁meas : MeasurableSet {q : Y × Ω₁ × Ω₂ | ¬ r q.2.1 = q.1} :=
      (measurableSet_eq_fun
        (hr.comp (measurable_fst.comp measurable_snd))
        measurable_fst).compl
    have hB₂meas : MeasurableSet {q : Y × Ω₁ × Ω₂ | ¬ s q.2.2 = q.1} :=
      (measurableSet_eq_fun
        (hs.comp (measurable_snd.comp measurable_snd))
        measurable_fst).compl
    have hsub : (Prod.snd ⁻¹' {p : Ω₁ × Ω₂ | r p.1 = s p.2}ᶜ
        : Set (Y × Ω₁ × Ω₂)) ⊆
        {q | ¬ r q.2.1 = q.1} ∪ {q | ¬ s q.2.2 = q.1} := by
      rintro ⟨y, u, w⟩ hq
      simp only [Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_setOf_eq] at hq
      by_cases h1 : r u = y
      · right
        simp only [Set.mem_setOf_eq]
        intro h2
        exact hq (h1.trans h2.symm)
      · left
        simpa using h1

    have hoff₁ : ν' {q : Y × Ω₁ × Ω₂ | ¬ r q.2.1 = q.1} = 0 := by
      rw [hν'def, Measure.compProd_apply hB₁meas]
      have hcalc : ∀ y : Y, (κ₁ ×ₖ κ₂) y
          (Prod.mk y ⁻¹' {q : Y × Ω₁ × Ω₂ | ¬ r q.2.1 = q.1})
            = κ₁ y {u | ¬ r u = y} := by
        intro y
        have hsec : (Prod.mk y ⁻¹'
            {q : Y × Ω₁ × Ω₂ | ¬ r q.2.1 = q.1} : Set (Ω₁ × Ω₂))
              = {u | ¬ r u = y} ×ˢ Set.univ := by
          ext ⟨u, w⟩; simp
        rw [hsec, Kernel.prod_apply, Measure.prod_prod, measure_univ,
          mul_one]
      simp_rw [hcalc]
      have hqmeas : MeasurableSet {q : Y × Ω₁ | ¬ r q.2 = q.1} :=
        (measurableSet_eq_fun (hr.comp measurable_snd)
          measurable_fst).compl
      have hup : ∫⁻ y, κ₁ y {u | ¬ r u = y} ∂lam
          = (lam ⊗ₘ κ₁) {q : Y × Ω₁ | ¬ r q.2 = q.1} :=
        (Measure.compProd_apply hqmeas).symm
      rw [hup, hd₁, Measure.map_apply hg₁ hqmeas]
      have hempty : ((fun a : Ω₁ => (r a, a)) ⁻¹'
          {q : Y × Ω₁ | ¬ r q.2 = q.1}) = (∅ : Set Ω₁) := by
        ext a; simp
      rw [hempty, measure_empty]

    have hoff₂ : ν' {q : Y × Ω₁ × Ω₂ | ¬ s q.2.2 = q.1} = 0 := by
      rw [hν'def, Measure.compProd_apply hB₂meas]
      have hcalc : ∀ y : Y, (κ₁ ×ₖ κ₂) y
          (Prod.mk y ⁻¹' {q : Y × Ω₁ × Ω₂ | ¬ s q.2.2 = q.1})
            = κ₂ y {w | ¬ s w = y} := by
        intro y
        have hsec : (Prod.mk y ⁻¹'
            {q : Y × Ω₁ × Ω₂ | ¬ s q.2.2 = q.1} : Set (Ω₁ × Ω₂))
              = Set.univ ×ˢ {w | ¬ s w = y} := by
          ext ⟨u, w⟩; simp
        rw [hsec, Kernel.prod_apply, Measure.prod_prod, measure_univ,
          one_mul]
      simp_rw [hcalc]
      have hqmeas : MeasurableSet {q : Y × Ω₂ | ¬ s q.2 = q.1} :=
        (measurableSet_eq_fun (hs.comp measurable_snd)
          measurable_fst).compl
      have hup : ∫⁻ y, κ₂ y {w | ¬ s w = y} ∂lam
          = (lam ⊗ₘ κ₂) {q : Y × Ω₂ | ¬ s q.2 = q.1} :=
        (Measure.compProd_apply hqmeas).symm
      rw [hup, hd₂, Measure.map_apply hg₂ hqmeas]
      have hempty : ((fun a : Ω₂ => (s a, a)) ⁻¹'
          {q : Y × Ω₂ | ¬ s q.2 = q.1}) = (∅ : Set Ω₂) := by
        ext a; simp
      rw [hempty, measure_empty]

    have hcompl : ν' (Prod.snd ⁻¹' {p : Ω₁ × Ω₂ | r p.1 = s p.2}ᶜ) = 0 :=
      le_zero_iff.mp
        (le_trans (measure_mono hsub)
          (le_trans (measure_union_le _ _)
            (by rw [hoff₁, hoff₂, add_zero])))
    have hpre : MeasurableSet
        (Prod.snd ⁻¹' {p : Ω₁ × Ω₂ | r p.1 = s p.2}
          : Set (Y × Ω₁ × Ω₂)) := measurable_snd hGmeas
    rw [Set.preimage_compl] at hcompl
    exact (prob_compl_eq_zero_iff hpre).mp hcompl

end Qtsl.Imprecise
