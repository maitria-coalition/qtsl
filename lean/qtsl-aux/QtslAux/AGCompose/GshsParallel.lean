import QtslAux.Ville

/-! # Parallel assume-guarantee composition of supermartingale certificates

This module composes finitely many safety certificates that run in parallel
over a common probability space and filtration.

Main results:

* `supermartingale_weighted_sum`: a nonnegative-weighted finite sum of
  supermartingales is a supermartingale.
* `certified`: given nonnegative supermartingales `Y i`, weights `lam i`, and
  barrier conditions (`X n ω ∈ Bad i` forces `a ≤ lam i * Y i n ω`), the
  probability of ever entering the union `⋃ i, Bad i` is bounded by
  `(∑ i, lam i * ∫ Y i 0) / a`, via Ville's inequality applied to the
  weighted-sum supermartingale.
* `certified_pair`: the two-component special case.
* `qualitative`: almost-sure guarantees combine across a finite conjunction.
* `fail_bound`: failure probabilities of the components add (union bound)
  to bound the failure probability of any consequence of the conjunction.
-/

open scoped NNReal ENNReal

open MeasureTheory Finset

namespace Qtsl.AGCompose.Parallel

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

theorem supermartingale_weighted_sum {ι : Type*} (s : Finset ι) [IsFiniteMeasure μ]
    {Y : ι → ℕ → Ω → ℝ} {lam : ι → ℝ}
    (hY : ∀ i ∈ s, Supermartingale (Y i) 𝒢 μ) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    Supermartingale (fun n ω => ∑ i ∈ s, lam i * Y i n ω) 𝒢 μ := by
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : (fun n ω => ∑ i ∈ (∅ : Finset ι), lam i * Y i n ω)
        = fun _ _ => (0 : ℝ) := by
      funext n ω; simp
    exact h0 ▸ (martingale_const 𝒢 μ (0 : ℝ)).supermartingale
  | cons a s ha ih =>
    have h₁ : Supermartingale (lam a • Y a) 𝒢 μ :=
      Supermartingale.smul_nonneg (hlam a (Finset.mem_cons_self a s))
        (hY a (Finset.mem_cons_self a s))
    have h₂ : Supermartingale (fun n ω => ∑ i ∈ s, lam i * Y i n ω) 𝒢 μ :=
      ih (fun i hi => hY i (Finset.mem_cons.2 (Or.inr hi)))
        (fun i hi => hlam i (Finset.mem_cons.2 (Or.inr hi)))
    have hfe : (fun n ω => ∑ i ∈ Finset.cons a s ha, lam i * Y i n ω)
        = lam a • Y a + fun n ω => ∑ i ∈ s, lam i * Y i n ω := by
      funext n ω
      simp [Finset.sum_cons, smul_eq_mul]
    exact hfe ▸ h₁.add h₂

section Certified

variable {ι St : Type*}

theorem certified (s : Finset ι) [IsFiniteMeasure μ]
    {Y : ι → ℕ → Ω → ℝ} {lam : ι → ℝ} {X : ℕ → Ω → St} {Bad : ι → Set St} {a : ℝ}
    (hY : ∀ i ∈ s, Supermartingale (Y i) 𝒢 μ)
    (hY0 : ∀ i ∈ s, 0 ≤ Y i)
    (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hbar : ∀ i ∈ s, ∀ n ω, X n ω ∈ Bad i → a ≤ lam i * Y i n ω) :
    ENNReal.ofReal a * μ {ω | ∃ n, X n ω ∈ ⋃ i ∈ s, Bad i} ≤
      ENNReal.ofReal (∑ i ∈ s, lam i * ∫ ω, Y i 0 ω ∂μ) := by
  have hW : Supermartingale (fun n ω => ∑ i ∈ s, lam i * Y i n ω) 𝒢 μ :=
    supermartingale_weighted_sum s hY hlam
  have hW0 : (0 : ℕ → Ω → ℝ) ≤ fun n ω => ∑ i ∈ s, lam i * Y i n ω := fun n ω =>
    Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi) (hY0 i hi n ω)
  have hbarW : ∀ n ω, X n ω ∈ ⋃ i ∈ s, Bad i →
      a ≤ ∑ i ∈ s, lam i * Y i n ω := by
    intro n ω hmem
    obtain ⟨i, hi, hBi⟩ := Set.mem_iUnion₂.1 hmem
    exact (hbar i hi n ω hBi).trans
      (Finset.single_le_sum
        (f := fun j => lam j * Y j n ω)
        (fun j hj => mul_nonneg (hlam j hj) (hY0 j hj n ω)) hi)
  have hK1 := Qtsl.Ville.reach_avoid (X := X) (B := ⋃ i ∈ s, Bad i)
    hW hW0 hbarW
  have hint : ∫ ω, (∑ i ∈ s, lam i * Y i 0 ω) ∂μ
      = ∑ i ∈ s, lam i * ∫ ω, Y i 0 ω ∂μ := by
    rw [integral_finsetSum s
      (fun i hi => ((hY i hi).integrable 0).const_mul (lam i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  exact hint ▸ hK1

theorem certified_pair [IsFiniteMeasure μ]
    {Y₁ Y₂ : ℕ → Ω → ℝ} {X : ℕ → Ω → St} {B₁ B₂ : Set St} {lam a : ℝ}
    (hY₁ : Supermartingale Y₁ 𝒢 μ) (hY₁0 : 0 ≤ Y₁)
    (hY₂ : Supermartingale Y₂ 𝒢 μ) (hY₂0 : 0 ≤ Y₂) (hlam : 0 ≤ lam)
    (hbar₁ : ∀ n ω, X n ω ∈ B₁ → a ≤ Y₁ n ω)
    (hbar₂ : ∀ n ω, X n ω ∈ B₂ → a ≤ lam * Y₂ n ω) :
    ENNReal.ofReal a * μ {ω | ∃ n, X n ω ∈ B₁ ∪ B₂} ≤
      ENNReal.ofReal (∫ ω, Y₁ 0 ω ∂μ + lam * ∫ ω, Y₂ 0 ω ∂μ) := by
  have hW : Supermartingale (Y₁ + lam • Y₂) 𝒢 μ :=
    hY₁.add (Supermartingale.smul_nonneg hlam hY₂)
  have hW0 : (0 : ℕ → Ω → ℝ) ≤ Y₁ + lam • Y₂ := fun n ω =>
    add_nonneg (hY₁0 n ω) (mul_nonneg hlam (hY₂0 n ω))
  have hbarW : ∀ n ω, X n ω ∈ B₁ ∪ B₂ → a ≤ (Y₁ + lam • Y₂) n ω := by
    intro n ω hmem
    rcases hmem with h₁ | h₂
    · exact le_add_of_le_of_nonneg (hbar₁ n ω h₁) (mul_nonneg hlam (hY₂0 n ω))
    · exact le_add_of_nonneg_of_le (hY₁0 n ω) (hbar₂ n ω h₂)
  have hK1 := Qtsl.Ville.reach_avoid (X := X) (B := B₁ ∪ B₂) hW hW0 hbarW
  have hint : ∫ ω, (Y₁ + lam • Y₂) 0 ω ∂μ
      = ∫ ω, Y₁ 0 ω ∂μ + lam * ∫ ω, Y₂ 0 ω ∂μ := by
    have h₂ : Integrable (fun ω => lam * Y₂ 0 ω) μ :=
      (hY₂.integrable 0).const_mul lam
    calc ∫ ω, (Y₁ + lam • Y₂) 0 ω ∂μ
        = ∫ ω, (Y₁ 0 ω + lam * Y₂ 0 ω) ∂μ := rfl
      _ = ∫ ω, Y₁ 0 ω ∂μ + ∫ ω, lam * Y₂ 0 ω ∂μ :=
          integral_add (hY₁.integrable 0) h₂
      _ = ∫ ω, Y₁ 0 ω ∂μ + lam * ∫ ω, Y₂ 0 ω ∂μ := by
          rw [integral_const_mul]
  exact hint ▸ hK1

end Certified

theorem qualitative {ι : Type*} (s : Finset ι) {sat : ι → Set Ω} {satOut : Set Ω}
    (h : ∀ i ∈ s, ∀ᵐ ω ∂μ, ω ∈ sat i)
    (hout : (⋂ i ∈ s, sat i) ⊆ satOut) :
    ∀ᵐ ω ∂μ, ω ∈ satOut := by
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, ω ∈ sat i :=
    (ae_ball_iff s.countable_toSet).2 h
  filter_upwards [hall] with ω hω
  exact hout (Set.mem_iInter₂.2 hω)

theorem fail_bound {ι : Type*} (s : Finset ι) {sat : ι → Set Ω} {satOut : Set Ω}
    {ε : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, μ (sat i)ᶜ ≤ ε i)
    (hout : (⋂ i ∈ s, sat i) ⊆ satOut) :
    μ satOutᶜ ≤ ∑ i ∈ s, ε i := by
  have hsub : satOutᶜ ⊆ ⋃ i ∈ s, (sat i)ᶜ := by
    rw [← Set.compl_iInter₂]
    exact Set.compl_subset_compl.2 hout
  calc μ satOutᶜ ≤ μ (⋃ i ∈ s, (sat i)ᶜ) := measure_mono hsub
    _ ≤ ∑ i ∈ s, μ (sat i)ᶜ := measure_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, ε i := Finset.sum_le_sum h

#print axioms Qtsl.AGCompose.Parallel.supermartingale_weighted_sum
#print axioms Qtsl.AGCompose.Parallel.certified
#print axioms Qtsl.AGCompose.Parallel.certified_pair
#print axioms Qtsl.AGCompose.Parallel.qualitative
#print axioms Qtsl.AGCompose.Parallel.fail_bound

end Qtsl.AGCompose.Parallel
