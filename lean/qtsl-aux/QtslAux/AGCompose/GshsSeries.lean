import QtslAux.Ville
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Series assume-guarantee composition of supermartingale certificates

This module composes two certified components in series: the first component's
conformance and satisfaction (`conform₁ ∩ sat₁`) establishes the second
component's assumption (`conform₂`), and joint satisfaction implies the output
specification `satOut`.

Main results:

* `qualitative`: almost-sure guarantees chain through the series connection.
* `fail_subset` and `fail_bound`: the failure event of the composition is
  covered by the two component failure events, so failure probabilities add.
* `fail_bound_of_ae_conform`: the same bound on the unconditional failure
  probability when the first assumption holds almost everywhere.
* `tower_step` and `tower`: lower bounds on success probability via the tower
  rule — a conditional-probability floor `p₂` on a sub-σ-algebra-measurable
  success event multiplies an unconditional floor `p₁`.
* `certified`: the quantitative series composition where each component's
  failure is witnessed by reaching a bad set and bounded by Ville's
  inequality applied to its nonnegative supermartingale certificate.
-/

open scoped NNReal ENNReal

open MeasureTheory

namespace Qtsl.AGCompose.Series

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {conform₁ sat₁ conform₂ sat₂ satOut : Set Ω}

theorem qualitative
    (h₁ : ∀ᵐ ω ∂μ, ω ∈ conform₁ → ω ∈ sat₁)
    (hw : conform₁ ∩ sat₁ ⊆ conform₂)
    (h₂ : ∀ᵐ ω ∂μ, ω ∈ conform₂ → ω ∈ sat₂)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut) :
    ∀ᵐ ω ∂μ, ω ∈ conform₁ → ω ∈ satOut := by
  filter_upwards [h₁, h₂] with ω h₁ω h₂ω hIn
  have hs₁ : ω ∈ sat₁ := h₁ω hIn
  exact hout ⟨⟨hIn, hs₁⟩, h₂ω (hw ⟨hIn, hs₁⟩)⟩

theorem fail_subset
    (hw : conform₁ ∩ sat₁ ⊆ conform₂)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut) :
    conform₁ ∩ satOutᶜ ⊆ (conform₁ ∩ sat₁ᶜ) ∪ (conform₂ ∩ sat₂ᶜ) := by
  rintro ω ⟨hIn, hnout⟩
  by_cases hs₁ : ω ∈ sat₁
  · by_cases hs₂ : ω ∈ sat₂
    · exact absurd (hout ⟨⟨hIn, hs₁⟩, hs₂⟩) hnout
    · exact Or.inr ⟨hw ⟨hIn, hs₁⟩, hs₂⟩
  · exact Or.inl ⟨hIn, hs₁⟩

theorem fail_bound {ε₁ ε₂ : ℝ≥0∞}
    (hw : conform₁ ∩ sat₁ ⊆ conform₂)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut)
    (h₁ : μ (conform₁ ∩ sat₁ᶜ) ≤ ε₁)
    (h₂ : μ (conform₂ ∩ sat₂ᶜ) ≤ ε₂) :
    μ (conform₁ ∩ satOutᶜ) ≤ ε₁ + ε₂ :=
  (measure_mono (fail_subset hw hout)).trans
    ((measure_union_le _ _).trans (add_le_add h₁ h₂))

theorem fail_bound_of_ae_conform {ε₁ ε₂ : ℝ≥0∞} (hIn : μ conform₁ᶜ = 0)
    (hw : conform₁ ∩ sat₁ ⊆ conform₂)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut)
    (h₁ : μ (conform₁ ∩ sat₁ᶜ) ≤ ε₁)
    (h₂ : μ (conform₂ ∩ sat₂ᶜ) ≤ ε₂) :
    μ satOutᶜ ≤ ε₁ + ε₂ := by
  have hsplit : satOutᶜ ⊆ (conform₁ ∩ satOutᶜ) ∪ conform₁ᶜ := by
    intro ω hω
    by_cases h : ω ∈ conform₁
    · exact Or.inl ⟨h, hω⟩
    · exact Or.inr h
  calc μ satOutᶜ ≤ μ ((conform₁ ∩ satOutᶜ) ∪ conform₁ᶜ) := measure_mono hsplit
    _ ≤ μ (conform₁ ∩ satOutᶜ) + μ conform₁ᶜ := measure_union_le _ _
    _ = μ (conform₁ ∩ satOutᶜ) := by rw [hIn, add_zero]
    _ ≤ ε₁ + ε₂ := fail_bound hw hout h₁ h₂

theorem tower_step [IsFiniteMeasure μ] {mG : MeasurableSpace Ω} (hG : mG ≤ m0)
    {S : Set Ω} (hS : MeasurableSet[mG] S) {E : Set Ω} (hE : MeasurableSet[m0] E)
    {p : ℝ}
    (hcond : ∀ᵐ ω ∂μ, ω ∈ S → p ≤ (μ[E.indicator (fun _ => (1 : ℝ)) | mG]) ω) :
    ENNReal.ofReal p * μ S ≤ μ (S ∩ E) := by
  rcases le_or_gt p 0 with hp | hp
  · rw [ENNReal.ofReal_eq_zero.2 hp, zero_mul]
    exact zero_le
  · have hSm : MeasurableSet[m0] S := hG S hS
    have hf : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hE

    have key : ∫ ω in S, (μ[E.indicator (fun _ => (1 : ℝ)) | mG]) ω ∂μ
        = μ.real (S ∩ E) := by
      rw [setIntegral_condExp hG hf hS, setIntegral_indicator hE, setIntegral_const,
        smul_eq_mul, mul_one]

    have lower : p * μ.real S ≤ ∫ ω in S, (μ[E.indicator (fun _ => (1 : ℝ)) | mG]) ω ∂μ := by
      have hae : ∀ᵐ ω ∂μ.restrict S,
          p ≤ (μ[E.indicator (fun _ => (1 : ℝ)) | mG]) ω :=
        (ae_restrict_iff' hSm).2 hcond
      calc p * μ.real S = ∫ _ω in S, p ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ ∫ ω in S, (μ[E.indicator (fun _ => (1 : ℝ)) | mG]) ω ∂μ :=
          integral_mono_ae (integrable_const p) integrable_condExp.restrict hae
    have h : p * μ.real S ≤ μ.real (S ∩ E) := key ▸ lower
    calc ENNReal.ofReal p * μ S
        = ENNReal.ofReal p * ENNReal.ofReal (μ.real S) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ S)]
      _ = ENNReal.ofReal (p * μ.real S) := (ENNReal.ofReal_mul hp.le).symm
      _ ≤ ENNReal.ofReal (μ.real (S ∩ E)) := ENNReal.ofReal_le_ofReal h
      _ = μ (S ∩ E) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ (S ∩ E))]

theorem tower [IsFiniteMeasure μ] {mG : MeasurableSpace Ω} (hG : mG ≤ m0)
    (hS : MeasurableSet[mG] (conform₁ ∩ sat₁)) (hE : MeasurableSet[m0] sat₂)
    {p₁ p₂ : ℝ} (hp₂ : 0 ≤ p₂)
    (h₁ : ENNReal.ofReal p₁ ≤ μ (conform₁ ∩ sat₁))
    (hcond : ∀ᵐ ω ∂μ, ω ∈ conform₁ ∩ sat₁ →
      p₂ ≤ (μ[sat₂.indicator (fun _ => (1 : ℝ)) | mG]) ω)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut) :
    ENNReal.ofReal (p₂ * p₁) ≤ μ satOut := by
  calc ENNReal.ofReal (p₂ * p₁)
      = ENNReal.ofReal p₂ * ENNReal.ofReal p₁ := ENNReal.ofReal_mul hp₂
    _ ≤ ENNReal.ofReal p₂ * μ (conform₁ ∩ sat₁) := mul_le_mul_right h₁ _
    _ ≤ μ (conform₁ ∩ sat₁ ∩ sat₂) := tower_step hG hS hE hcond
    _ ≤ μ satOut := measure_mono hout

section Certified

variable {S₁ S₂ : Type*} {𝒢 : Filtration ℕ m0}

theorem certified [IsFiniteMeasure μ]
    {Y₁ Y₂ : ℕ → Ω → ℝ} {X₁ : ℕ → Ω → S₁} {X₂ : ℕ → Ω → S₂}
    {B₁ : Set S₁} {B₂ : Set S₂} {a₁ a₂ : ℝ}

    (hY₁ : Supermartingale Y₁ 𝒢 μ) (hY₁0 : 0 ≤ Y₁)
    (hY₂ : Supermartingale Y₂ 𝒢 μ) (hY₂0 : 0 ≤ Y₂)

    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hbar₁ : ∀ n ω, X₁ n ω ∈ B₁ → a₁ ≤ Y₁ n ω)
    (hbar₂ : ∀ n ω, X₂ n ω ∈ B₂ → a₂ ≤ Y₂ n ω)

    (hwit₁ : conform₁ ∩ sat₁ᶜ ⊆ {ω | ∃ n, X₁ n ω ∈ B₁})
    (hwit₂ : conform₂ ∩ sat₂ᶜ ⊆ {ω | ∃ n, X₂ n ω ∈ B₂})

    (hw : conform₁ ∩ sat₁ ⊆ conform₂)
    (hout : conform₁ ∩ sat₁ ∩ sat₂ ⊆ satOut) :
    μ (conform₁ ∩ satOutᶜ) ≤
      ENNReal.ofReal (∫ ω, Y₁ 0 ω ∂μ) / ENNReal.ofReal a₁ +
      ENNReal.ofReal (∫ ω, Y₂ 0 ω ∂μ) / ENNReal.ofReal a₂ :=
  fail_bound hw hout
    ((measure_mono hwit₁).trans
      (Qtsl.Ville.reach_avoid_div hY₁ hY₁0 ha₁ hbar₁))
    ((measure_mono hwit₂).trans
      (Qtsl.Ville.reach_avoid_div hY₂ hY₂0 ha₂ hbar₂))

end Certified

#print axioms Qtsl.AGCompose.Series.qualitative
#print axioms Qtsl.AGCompose.Series.fail_bound
#print axioms Qtsl.AGCompose.Series.fail_bound_of_ae_conform
#print axioms Qtsl.AGCompose.Series.tower_step
#print axioms Qtsl.AGCompose.Series.tower
#print axioms Qtsl.AGCompose.Series.certified

end Qtsl.AGCompose.Series
