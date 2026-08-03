import QtslAux.Ville

/-! # Feedback composition of skeleton certificates, sum form

This module composes two supermartingale-style certificates for the
discrete-time skeleton of a general stochastic hybrid system (GSHS) whose
components are interconnected in feedback, by a sum-form small-gain argument.

* `SkeletonCertificate`: a certificate along a filtration `𝒢` — an adapted
  nonnegative process `val`, a pre-jump value `preVal`, a nonnegative supply
  integrand `alphaInt` and a demand integrand `sigmaInt` — satisfying a
  conditional Dynkin inequality (`dynkin`) and nonexpansiveness of jumps
  (`jump_nonexpansive`). `SkeletonCertificate.step` merges the two axioms into
  a single one-step drift inequality for `val`.
* `SumFormFeedback`: two such certificates together with a weight
  `lambda ≥ 0` and a margin fraction `theta ≥ 0` such that each certificate's
  demand is covered by a `(1 - theta)` fraction of the other's (scaled) supply
  (`mem₁`, `mem₂`) — the small-gain condition.
* `SumFormFeedback.W`, the composite certificate `val₁ + lambda • val₂`, and
  `SumFormFeedback.margin`, the retained supply margin. The drift inequality
  `SumFormFeedback.drift` shows the margin is paid on every step, and over a
  finite measure `SumFormFeedback.supermartingale` makes `W` a supermartingale.
* `SumFormFeedback.avoid_bound` / `debut_avoid_bound`: Ville-type reachability
  bounds — `ENNReal.ofReal a * μ {∃ k, X k ∈ B} ≤ ENNReal.ofReal (∫ W 0)`
  whenever `W ≥ a` on the event that the adapted state process is in `B`.
* `SumFormFeedback.compensated` and `margin_budget`: adding the accumulated
  margins back yields a supermartingale, so the expected total margin collected
  over any horizon is bounded by the initial value `∫ W 0`.
-/

open scoped ENNReal MeasureTheory

namespace Qtsl.AGCompose

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

structure SkeletonCertificate (μ : Measure Ω) (𝒢 : Filtration ℕ m0) where

  val : ℕ → Ω → ℝ

  preVal : ℕ → Ω → ℝ

  alphaInt : ℕ → Ω → ℝ

  sigmaInt : ℕ → Ω → ℝ

  stronglyAdapted : StronglyAdapted 𝒢 val
  integrable_val : ∀ k, Integrable (val k) μ
  integrable_preVal : ∀ k, Integrable (preVal k) μ
  integrable_alphaInt : ∀ k, Integrable (alphaInt k) μ
  integrable_sigmaInt : ∀ k, Integrable (sigmaInt k) μ

  val_nonneg : 0 ≤ val

  alphaInt_nonneg : 0 ≤ alphaInt

  dynkin : ∀ k, μ[preVal (k + 1) + alphaInt k - sigmaInt k | 𝒢 k] ≤ᵐ[μ] val k

  jump_nonexpansive : ∀ k, val (k + 1) ≤ᵐ[μ] preVal (k + 1)

namespace SkeletonCertificate

theorem step (C : SkeletonCertificate μ 𝒢) (k : ℕ) :
    μ[C.val (k + 1) + C.alphaInt k - C.sigmaInt k | 𝒢 k] ≤ᵐ[μ] C.val k := by
  refine (condExp_mono
    (((C.integrable_val (k + 1)).add (C.integrable_alphaInt k)).sub
      (C.integrable_sigmaInt k))
    (((C.integrable_preVal (k + 1)).add (C.integrable_alphaInt k)).sub
      (C.integrable_sigmaInt k))
    ?_).trans (C.dynkin k)
  filter_upwards [C.jump_nonexpansive k] with ω hω
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

end SkeletonCertificate

structure SumFormFeedback (μ : Measure Ω) (𝒢 : Filtration ℕ m0) where
  cert₁ : SkeletonCertificate μ 𝒢
  cert₂ : SkeletonCertificate μ 𝒢
  lambda : ℝ
  theta : ℝ
  lambda_nonneg : 0 ≤ lambda
  theta_nonneg : 0 ≤ theta

  mem₁ : ∀ k, ∀ᵐ ω ∂μ, lambda * cert₂.sigmaInt k ω ≤ (1 - theta) * cert₁.alphaInt k ω

  mem₂ : ∀ k, ∀ᵐ ω ∂μ, cert₁.sigmaInt k ω ≤ lambda * (1 - theta) * cert₂.alphaInt k ω

namespace SumFormFeedback

variable (F : SumFormFeedback μ 𝒢)

def W : ℕ → Ω → ℝ := fun k => F.cert₁.val k + F.lambda • F.cert₂.val k

def margin : ℕ → Ω → ℝ := fun k => F.theta • (F.cert₁.alphaInt k + F.lambda • F.cert₂.alphaInt k)

@[simp] theorem W_apply (k : ℕ) (ω : Ω) :
    F.W k ω = F.cert₁.val k ω + F.lambda * F.cert₂.val k ω := rfl

@[simp] theorem margin_apply (k : ℕ) (ω : Ω) :
    F.margin k ω = F.theta * (F.cert₁.alphaInt k ω + F.lambda * F.cert₂.alphaInt k ω) := rfl

theorem W_stronglyAdapted : StronglyAdapted 𝒢 F.W := fun k =>
  (F.cert₁.stronglyAdapted k).add ((F.cert₂.stronglyAdapted k).const_smul F.lambda)

theorem integrable_W (k : ℕ) : Integrable (F.W k) μ :=
  (F.cert₁.integrable_val k).add ((F.cert₂.integrable_val k).smul F.lambda)

theorem integrable_margin (k : ℕ) : Integrable (F.margin k) μ :=
  (((F.cert₁.integrable_alphaInt k).add
    ((F.cert₂.integrable_alphaInt k).smul F.lambda)).smul F.theta)

theorem W_nonneg : 0 ≤ F.W := fun k ω =>
  add_nonneg (F.cert₁.val_nonneg k ω)
    (mul_nonneg F.lambda_nonneg (F.cert₂.val_nonneg k ω))

theorem margin_nonneg : 0 ≤ F.margin := fun k ω =>
  mul_nonneg F.theta_nonneg
    (add_nonneg (F.cert₁.alphaInt_nonneg k ω)
      (mul_nonneg F.lambda_nonneg (F.cert₂.alphaInt_nonneg k ω)))

theorem drift (k : ℕ) : μ[F.W (k + 1) + F.margin k | 𝒢 k] ≤ᵐ[μ] F.W k := by
  set G₁ : Ω → ℝ :=
    F.cert₁.val (k + 1) + F.cert₁.alphaInt k - F.cert₁.sigmaInt k with hG₁
  set G₂ : Ω → ℝ :=
    F.cert₂.val (k + 1) + F.cert₂.alphaInt k - F.cert₂.sigmaInt k with hG₂
  have hIntG₁ : Integrable G₁ μ :=
    ((F.cert₁.integrable_val (k + 1)).add (F.cert₁.integrable_alphaInt k)).sub
      (F.cert₁.integrable_sigmaInt k)
  have hIntG₂ : Integrable G₂ μ :=
    ((F.cert₂.integrable_val (k + 1)).add (F.cert₂.integrable_alphaInt k)).sub
      (F.cert₂.integrable_sigmaInt k)

  have hpt : F.W (k + 1) + F.margin k ≤ᵐ[μ] G₁ + F.lambda • G₂ := by
    filter_upwards [F.mem₁ k, F.mem₂ k] with ω h₁ h₂
    simp only [hG₁, hG₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      W_apply, margin_apply]
    nlinarith [h₁, h₂]
  calc μ[F.W (k + 1) + F.margin k | 𝒢 k]
      ≤ᵐ[μ] μ[G₁ + F.lambda • G₂ | 𝒢 k] :=
        condExp_mono ((F.integrable_W (k + 1)).add (F.integrable_margin k))
          (hIntG₁.add (hIntG₂.smul F.lambda)) hpt
    _ =ᵐ[μ] μ[G₁ | 𝒢 k] + μ[F.lambda • G₂ | 𝒢 k] :=
        condExp_add hIntG₁ (hIntG₂.smul F.lambda) _
    _ =ᵐ[μ] μ[G₁ | 𝒢 k] + F.lambda • μ[G₂ | 𝒢 k] :=
        Filter.EventuallyEq.add Filter.EventuallyEq.rfl (condExp_smul F.lambda G₂ _)
    _ ≤ᵐ[μ] F.W k := by
        filter_upwards [F.cert₁.step k, F.cert₂.step k] with ω hs₁ hs₂
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, W_apply]
        have h2 := mul_le_mul_of_nonneg_left hs₂ F.lambda_nonneg
        linarith

variable [IsFiniteMeasure μ]

theorem supermartingale : Supermartingale F.W 𝒢 μ := by
  refine supermartingale_nat F.W_stronglyAdapted F.integrable_W fun k => ?_
  refine (condExp_mono (F.integrable_W (k + 1))
    ((F.integrable_W (k + 1)).add (F.integrable_margin k))
    (Filter.Eventually.of_forall fun ω => ?_)).trans (F.drift k)
  have h0 : (0 : ℝ) ≤ F.margin k ω := F.margin_nonneg k ω
  simp only [Pi.add_apply]
  linarith

theorem avoid_bound {S : Type*} {X : ℕ → Ω → S} {B : Set S} {a : ℝ}
    (hbarrier : ∀ k ω, X k ω ∈ B → a ≤ F.W k ω) :
    ENNReal.ofReal a * μ {ω | ∃ k, X k ω ∈ B} ≤ ENNReal.ofReal (∫ ω, F.W 0 ω ∂μ) :=
  Qtsl.Ville.reach_avoid F.supermartingale F.W_nonneg hbarrier

theorem debut_avoid_bound {S : Type*} {X : ℕ → Ω → S} {B : Set S} {a : ℝ}
    (hbarrier : ∀ k ω, X k ω ∈ B → a ≤ F.W k ω) {E : Set Ω}
    (hdebut : E ⊆ {ω | ∃ k, X k ω ∈ B}) :
    ENNReal.ofReal a * μ E ≤ ENNReal.ofReal (∫ ω, F.W 0 ω ∂μ) :=
  le_trans (mul_le_mul' le_rfl (measure_mono hdebut)) (F.avoid_bound hbarrier)

def compensated : ℕ → Ω → ℝ := fun n => F.W n + ∑ j ∈ Finset.range n, F.margin j

omit [IsFiniteMeasure μ] in
@[simp] theorem compensated_zero : F.compensated 0 = F.W 0 := by
  simp [compensated]

omit [IsFiniteMeasure μ] in

theorem margin_stronglyMeasurable_succ
    (hα₁ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₁.alphaInt k))
    (hα₂ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₂.alphaInt k)) (k : ℕ) :
    StronglyMeasurable[𝒢 (k + 1)] (F.margin k) :=
  ((hα₁ k).add ((hα₂ k).const_smul F.lambda)).const_smul F.theta

omit [IsFiniteMeasure μ] in
theorem integrable_marginSum (n : ℕ) :
    Integrable (∑ j ∈ Finset.range n, F.margin j) μ :=
  integrable_finsetSum' _ fun j _ => F.integrable_margin j

theorem compensated_supermartingale
    (hα₁ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₁.alphaInt k))
    (hα₂ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₂.alphaInt k)) :
    Supermartingale F.compensated 𝒢 μ := by
  have hsum_meas : ∀ n, StronglyMeasurable[𝒢 n] (∑ j ∈ Finset.range n, F.margin j) := by
    intro n
    refine Finset.stronglyMeasurable_sum _ fun j hj => ?_
    exact (F.margin_stronglyMeasurable_succ hα₁ hα₂ j).mono
      (𝒢.mono (Finset.mem_range.mp hj))
  refine supermartingale_nat (fun n => (F.W_stronglyAdapted n).add (hsum_meas n))
    (fun n => (F.integrable_W n).add (F.integrable_marginSum n)) fun n => ?_
  have hrw : F.compensated (n + 1) =
      (F.W (n + 1) + F.margin n) + ∑ j ∈ Finset.range n, F.margin j := by
    funext ω
    simp only [compensated, Pi.add_apply, Finset.sum_apply, Finset.sum_range_succ]
    ring
  calc μ[F.compensated (n + 1) | 𝒢 n]
      =ᵐ[μ] μ[F.W (n + 1) + F.margin n | 𝒢 n] +
        μ[∑ j ∈ Finset.range n, F.margin j | 𝒢 n] := by
        rw [hrw]
        exact condExp_add ((F.integrable_W (n + 1)).add (F.integrable_margin n))
          (F.integrable_marginSum n) _
    _ =ᵐ[μ] μ[F.W (n + 1) + F.margin n | 𝒢 n] + ∑ j ∈ Finset.range n, F.margin j := by
        rw [condExp_of_stronglyMeasurable (𝒢.le n) (hsum_meas n) (F.integrable_marginSum n)]
    _ ≤ᵐ[μ] F.W n + ∑ j ∈ Finset.range n, F.margin j := by
        filter_upwards [F.drift n] with ω hω
        simp only [Pi.add_apply] at hω ⊢
        linarith
    _ = F.compensated n := rfl

theorem margin_budget
    (hα₁ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₁.alphaInt k))
    (hα₂ : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (F.cert₂.alphaInt k)) (n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, F.margin j) ω ∂μ ≤ ∫ ω, F.W 0 ω ∂μ := by
  have hM := F.compensated_supermartingale hα₁ hα₂

  have hK2 : ∫ ω, F.compensated n ω ∂μ ≤ ∫ ω, F.compensated 0 ω ∂μ :=
    hM.expected_stoppedValue_antitone (τ := fun _ => ((0 : ℕ) : ℕ∞))
      (π := fun _ => ((n : ℕ) : ℕ∞)) (isStoppingTime_const _ _) (isStoppingTime_const _ _)
      (fun _ => WithTop.coe_le_coe.2 (Nat.zero_le n)) (N := n) fun _ => le_rfl
  rw [compensated_zero] at hK2
  have hsplit : ∫ ω, F.compensated n ω ∂μ =
      (∫ ω, F.W n ω ∂μ) + ∫ ω, (∑ j ∈ Finset.range n, F.margin j) ω ∂μ :=
    integral_add (F.integrable_W n) (F.integrable_marginSum n)
  have hWn : 0 ≤ ∫ ω, F.W n ω ∂μ := integral_nonneg (F.W_nonneg n)
  rw [hsplit] at hK2
  linarith

end SumFormFeedback

end Qtsl.AGCompose

#print axioms Qtsl.AGCompose.SumFormFeedback.drift
#print axioms Qtsl.AGCompose.SumFormFeedback.supermartingale
#print axioms Qtsl.AGCompose.SumFormFeedback.avoid_bound
#print axioms Qtsl.AGCompose.SumFormFeedback.debut_avoid_bound
#print axioms Qtsl.AGCompose.SumFormFeedback.compensated_supermartingale
#print axioms Qtsl.AGCompose.SumFormFeedback.margin_budget
