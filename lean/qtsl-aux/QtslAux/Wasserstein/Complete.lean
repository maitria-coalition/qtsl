import QtslAux.Wasserstein.Space
import QtslAux.QFixBall
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Completeness of the Wasserstein-2 space

This module proves that `P2 X` over a complete, second-countable metric space `X` with its Borel
σ-algebra is a complete metric space, and instantiates the closed-ball fixed-point principle in
it.

Main declarations:

* `chainKernel`, `chainMeasure`: given an initial measure and a sequence of couplings linking
  consecutive laws, the Ionescu-Tulcea construction produces a measure on the path space `ℕ → X`;
  `chainMeasure_marginals` identifies its one-step and adjacent two-step marginals with the
  prescribed laws and couplings;
* `exists_limit_of_summable_chain`: if consecutive couplings have summable square-root costs, the
  sequence has a limit in `P2 X`, with the tail sums as explicit error bounds — paths are almost
  surely Cauchy under the chain measure, and the law of the pointwise limit is the limit point;
* the `CompleteSpace (P2 X)` instance, obtained from the previous result via controlled Cauchy
  sequences with geometric bounds;
* `sound_QFixBall_wasserstein`: for `T` Lipschitz with constant `K < 1` on a closed ball around
  `μ₀` with residual `dist (T μ₀) μ₀ ≤ δ` and `δ + K * r ≤ r`, there is a unique fixed point of
  `T` in that ball — the general fixed-point theorem `QFixBall.sound_QFixBall` applied to the
  Wasserstein-2 space.
-/

namespace Qtsl

namespace Wasserstein

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section Prelim

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem lintegral_le_rpow_two_half [IsProbabilityMeasure P]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂P ≤ (∫⁻ ω, f ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ℝ≥0∞)) hf.aemeasurable aemeasurable_const
  simpa [ENNReal.one_rpow, measure_univ] using h

theorem lintegral_rpow_two_tsum_le {f : ℕ → Ω → ℝ≥0∞}
    (hf : ∀ k, Measurable (f k)) :
    (∫⁻ ω, (∑' k, f k ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
      ≤ ∑' k, (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  have hsm : ∀ m : ℕ, Measurable fun ω => ∑ k ∈ Finset.range m, f k ω :=
    fun m => Finset.measurable_sum _ fun k _ => hf k

  have hfin : ∀ m : ℕ,
      (∫⁻ ω, (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
        ≤ ∑ k ∈ Finset.range m, (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
    intro m
    induction m with
    | zero =>
        simp [ENNReal.zero_rpow_of_pos]
    | succ m ih =>
        calc (∫⁻ ω, (∑ k ∈ Finset.range (m + 1), f k ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
            = (∫⁻ ω, ((∑ k ∈ Finset.range m, f k ω) + f m ω) ^ (2 : ℝ) ∂P)
                ^ (1 / 2 : ℝ) := by
              simp only [Finset.sum_range_succ]
          _ ≤ (∫⁻ ω, (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
              + (∫⁻ ω, f m ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) :=
              ENNReal.lintegral_Lp_add_le (hsm m).aemeasurable
                (hf m).aemeasurable (by norm_num)
          _ ≤ (∑ k ∈ Finset.range m, (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ))
              + (∫⁻ ω, f m ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := add_le_add ih le_rfl
          _ = ∑ k ∈ Finset.range (m + 1),
                (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
              rw [Finset.sum_range_succ]

  have hpt : ∀ ω, (∑' k, f k ω) ^ (2 : ℝ)
      = ⨆ m, (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) := by
    intro ω
    have hmono : Monotone fun m => ∑ k ∈ Finset.range m, f k ω := fun a b hab =>
      Finset.sum_le_sum_of_subset
        (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (hx.trans_le hab))
    have hmono2 : Monotone fun m => (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) :=
      fun a b hab => ENNReal.rpow_le_rpow (hmono hab) (by norm_num)
    have htd : Tendsto (fun m => (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ)) atTop
        (𝓝 ((∑' k, f k ω) ^ (2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.tendsto_nat_tsum _)
    exact tendsto_nhds_unique htd (tendsto_atTop_iSup hmono2)
  have hmct : (∫⁻ ω, (∑' k, f k ω) ^ (2 : ℝ) ∂P)
      = ⨆ m, ∫⁻ ω, (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) ∂P := by
    simp_rw [hpt]
    exact lintegral_iSup
      (fun m => ENNReal.continuous_rpow_const.measurable.comp (hsm m))
      (fun a b hab ω => ENNReal.rpow_le_rpow
        (Finset.sum_le_sum_of_subset
          (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (hx.trans_le hab)))
        (by norm_num))

  have hT : ∀ m, (∫⁻ ω, (∑ k ∈ Finset.range m, f k ω) ^ (2 : ℝ) ∂P)
      ≤ (∑' k, (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    intro m
    have h3 := (hfin m).trans (ENNReal.sum_le_tsum (Finset.range m))
    have h4 := ENNReal.rpow_le_rpow h3 (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, (by norm_num : (1 / 2 : ℝ) * 2 = 1),
      ENNReal.rpow_one] at h4
  have h5 := ENNReal.rpow_le_rpow (hmct ▸ iSup_le hT) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← ENNReal.rpow_mul, (by norm_num : (2 : ℝ) * (1 / 2) = 1),
    ENNReal.rpow_one] at h5

end Prelim

section Chain

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

noncomputable def chainKernel (π : ℕ → Measure (X × X))
    [∀ n, IsFiniteMeasure (π n)] (n : ℕ) : Kernel (Π _ : Iic n, X) X :=
  Kernel.comap (π n).condKernel (fun v => v ⟨n, mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (π : ℕ → Measure (X × X)) [∀ n, IsFiniteMeasure (π n)] (n : ℕ) :
    IsMarkovKernel (chainKernel π n) :=
  inferInstanceAs (IsMarkovKernel (Kernel.comap _ _ _))

noncomputable def chainMeasure (μ0 : Measure X) (π : ℕ → Measure (X × X))
    [∀ n, IsFiniteMeasure (π n)] : Measure (ℕ → X) :=
  Kernel.trajMeasure (X := fun _ => X) μ0 (chainKernel π)

instance (μ0 : Measure X) [IsProbabilityMeasure μ0] (π : ℕ → Measure (X × X))
    [∀ n, IsFiniteMeasure (π n)] : IsProbabilityMeasure (chainMeasure μ0 π) :=
  inferInstanceAs
    (IsProbabilityMeasure (Kernel.trajMeasure (X := fun _ => X) μ0 (chainKernel π)))

theorem chainMeasure_def (μ0 : Measure X) (π : ℕ → Measure (X × X))
    [∀ n, IsFiniteMeasure (π n)] :
    chainMeasure μ0 π = (Kernel.traj (X := fun _ => X) (chainKernel π) 0) ∘ₘ
      (μ0.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm) := rfl

theorem chainMeasure_map_eval_zero (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (π : ℕ → Measure (X × X)) [∀ n, IsFiniteMeasure (π n)] :
    (chainMeasure μ0 π).map (fun ω => ω 0) = μ0 := by
  have hfr0 : (chainMeasure μ0 π).map (frestrictLe 0)
      = μ0.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm := by
    rw [chainMeasure_def, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  calc (chainMeasure μ0 π).map (fun ω => ω 0)
      = ((chainMeasure μ0 π).map (frestrictLe 0)).map
          (fun v : Π _ : Iic 0, X => v ⟨0, mem_Iic.mpr le_rfl⟩) :=
        (Measure.map_map
          (measurable_pi_apply (⟨0, mem_Iic.mpr le_rfl⟩ : Iic 0))
          (measurable_frestrictLe 0)).symm
    _ = (μ0.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm).map
          (fun v : Π _ : Iic 0, X => v ⟨0, mem_Iic.mpr le_rfl⟩) := by rw [hfr0]
    _ = μ0 := by
        refine (Measure.map_map
          (measurable_pi_apply (⟨0, mem_Iic.mpr le_rfl⟩ : Iic 0))
          (MeasurableEquiv.measurable _)).trans ?_
        have h4 : ((fun v : Π _ : Iic 0, X => v ⟨0, mem_Iic.mpr le_rfl⟩)
            ∘ ⇑(MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm) = id := by
          funext x
          show (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm x
              ⟨0, mem_Iic.mpr le_rfl⟩ = x
          have h5 : (⟨0, mem_Iic.mpr le_rfl⟩ : Iic 0)
              = (default : Iic 0) := Unique.eq_default _
          rw [h5]
          exact (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).apply_symm_apply x
        rw [h4, Measure.map_id]

theorem chainMeasure_map_pair (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (π : ℕ → Measure (X × X)) [∀ n, IsProbabilityMeasure (π n)] {n : ℕ}
    (hn : (chainMeasure μ0 π).map (fun ω => ω n) = (π n).fst) :
    (chainMeasure μ0 π).map (fun ω => (ω n, ω (n + 1))) = π n := by
  have hml : ((chainMeasure μ0 π).map (frestrictLe n)) ⊗ₘ chainKernel π n
      = (chainMeasure μ0 π).map (fun ω : ℕ → X => (frestrictLe n ω, ω (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => X) (μ₀ := μ0) (κ := chainKernel π) (a := n)
  have hpm : Measurable fun p : (Π _ : Iic n, X) × X =>
      (p.1 ⟨n, mem_Iic.mpr le_rfl⟩, p.2) :=
    ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
  have hfr : Measurable fun ω : ℕ → X => (frestrictLe n ω, ω (n + 1)) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  have hcomp : (chainMeasure μ0 π).map (fun ω : ℕ → X => (ω n, ω (n + 1)))
      = ((chainMeasure μ0 π).map (fun ω : ℕ → X => (frestrictLe n ω, ω (n + 1)))).map
          (fun p : (Π _ : Iic n, X) × X => (p.1 ⟨n, mem_Iic.mpr le_rfl⟩, p.2)) := by
    rw [Measure.map_map hpm hfr]
    rfl
  haveI : IsProbabilityMeasure ((chainMeasure μ0 π).map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  have h2 : (((chainMeasure μ0 π).map (frestrictLe n)) ⊗ₘ chainKernel π n).map
        (fun p : (Π _ : Iic n, X) × X => (p.1 ⟨n, mem_Iic.mpr le_rfl⟩, p.2))
      = (((chainMeasure μ0 π).map (frestrictLe n)).map
          (fun v : Π _ : Iic n, X => v ⟨n, mem_Iic.mpr le_rfl⟩))
        ⊗ₘ (π n).condKernel :=
    map_compProd_comap _ (measurable_pi_apply _) _
  have h3 : (((chainMeasure μ0 π).map (frestrictLe n)).map
        (fun v : Π _ : Iic n, X => v ⟨n, mem_Iic.mpr le_rfl⟩))
      = (chainMeasure μ0 π).map (fun ω => ω n) :=
    Measure.map_map
      (measurable_pi_apply (⟨n, mem_Iic.mpr le_rfl⟩ : Iic n))
      (measurable_frestrictLe n)
  rw [hcomp, ← hml, h2, h3, hn]
  exact (π n).disintegrate (π n).condKernel

theorem chainMeasure_marginals (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (π : ℕ → Measure (X × X)) [∀ n, IsProbabilityMeasure (π n)]
    (μseq : ℕ → Measure X) (h0 : μseq 0 = μ0)
    (hcoup : ∀ n, IsCoupling (π n) (μseq n) (μseq (n + 1))) :
    (∀ n, (chainMeasure μ0 π).map (fun ω => ω n) = μseq n)
      ∧ ∀ n, (chainMeasure μ0 π).map (fun ω => (ω n, ω (n + 1))) = π n := by
  have heval : ∀ n, (chainMeasure μ0 π).map (fun ω => ω n) = μseq n := by
    intro n
    induction n with
    | zero => rw [chainMeasure_map_eval_zero, h0]
    | succ n ih =>
        have hpair : (chainMeasure μ0 π).map (fun ω => (ω n, ω (n + 1))) = π n :=
          chainMeasure_map_pair μ0 π (by rw [ih, (hcoup n).1])
        have hmm : (chainMeasure μ0 π).map (fun ω : ℕ → X => ω (n + 1))
            = ((chainMeasure μ0 π).map (fun ω : ℕ → X => (ω n, ω (n + 1)))).map
                Prod.snd :=
          (Measure.map_map measurable_snd
            ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))).symm
        rw [hmm, hpair]
        exact (hcoup n).2
  exact ⟨heval, fun n => chainMeasure_map_pair μ0 π (by rw [heval n, (hcoup n).1])⟩

end Chain

section Limit

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X]

theorem exists_limit_of_summable_chain (u : ℕ → P2 X)
    (π : ℕ → Measure (X × X))
    (hcoup : ∀ n, IsCoupling (π n) (u n).toMeasure (u (n + 1)).toMeasure)
    (c : ℕ → ℝ≥0∞) (hc : ∀ n, cost2 (π n) ^ (1 / 2 : ℝ) ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞) :
    ∃ ν : P2 X, ∀ n, edist (u n) ν ≤ ∑' k, c (n + k) := by
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure (u 0).toMeasure
  haveI : ∀ n, IsProbabilityMeasure (π n) := fun n => (hcoup n).isProbabilityMeasure

  set P : Measure (ℕ → X) := chainMeasure (u 0).toMeasure π with hP
  obtain ⟨heval, hpair⟩ := chainMeasure_marginals (u 0).toMeasure π
    (fun n => (u n).toMeasure) rfl hcoup

  set D : ℕ → (ℕ → X) → ℝ≥0∞ := fun n ω => edist (ω n) (ω (n + 1)) with hD
  have hDmeas : ∀ n, Measurable (D n) := fun n =>
    measurable_edist.comp ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
  have hpairmeas : ∀ n, Measurable fun ω : ℕ → X => (ω n, ω (n + 1)) := fun n =>
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))

  have hD2 : ∀ n, (∫⁻ ω, D n ω ^ (2 : ℝ) ∂P) = cost2 (π n) := by
    intro n
    have hsq : Measurable fun q : X × X => edist q.1 q.2 ^ (2 : ℝ) :=
      ENNReal.continuous_rpow_const.measurable.comp measurable_edist
    calc (∫⁻ ω, D n ω ^ (2 : ℝ) ∂P)
        = ∫⁻ q, edist q.1 q.2 ^ (2 : ℝ) ∂(P.map fun ω => (ω n, ω (n + 1))) :=
          (lintegral_map hsq (hpairmeas n)).symm
      _ = cost2 (π n) := by rw [hpair n, cost2]
  have hD1 : ∀ n, (∫⁻ ω, D n ω ∂P) ≤ c n := by
    intro n
    refine (lintegral_le_rpow_two_half (hDmeas n)).trans ?_
    rw [hD2 n]
    exact hc n

  have htsum_meas : Measurable fun ω => ∑' n, D n ω :=
    Measurable.tsum hDmeas
  have htsum_int : (∫⁻ ω, ∑' n, D n ω ∂P) ≠ ∞ := by
    rw [lintegral_tsum fun n => (hDmeas n).aemeasurable]
    exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hD1)
  have hae_sum : ∀ᵐ ω ∂P, (∑' n, D n ω) ≠ ∞ := by
    filter_upwards [ae_lt_top htsum_meas htsum_int] with ω hω
    exact hω.ne

  have hae_ex : ∀ᵐ ω ∂P, ∃ l : X, Tendsto (fun n => ω n) atTop (𝓝 l) := by
    filter_upwards [hae_sum] with ω hω
    have hcau : CauchySeq fun n => ω n :=
      cauchySeq_of_edist_le_of_tsum_ne_top (fun n => D n ω) (fun n => le_rfl) hω
    exact cauchySeq_tendsto_of_complete hcau
  obtain ⟨Zlim, hZmeas, hZtend⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n).aemeasurable)
    hae_ex

  set R : ℕ → (ℕ → X) → ℝ≥0∞ := fun n ω => ∑' k, D (n + k) ω with hR
  have hRmeas : ∀ n, Measurable (R n) := fun n =>
    Measurable.tsum fun k => hDmeas (n + k)
  have hZR : ∀ᵐ ω ∂P, ∀ n, edist (ω n) (Zlim ω) ≤ R n ω := by
    filter_upwards [hZtend] with ω hω
    intro n
    have hd : Tendsto (fun m => edist (ω n) (ω m)) atTop (𝓝 (edist (ω n) (Zlim ω))) :=
      (Filter.Tendsto.edist tendsto_const_nhds hω)
    refine le_of_tendsto hd ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    calc edist (ω n) (ω m)
        ≤ ∑ i ∈ Finset.Ico n m, edist (ω i) (ω (i + 1)) :=
          edist_le_Ico_sum_edist _ hm
      _ = ∑ i ∈ Finset.range (m - n), D (n + i) ω := by
          rw [Finset.sum_Ico_eq_sum_range]
      _ ≤ R n ω := ENNReal.sum_le_tsum _
  have hRL2 : ∀ n, (∫⁻ ω, R n ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ ∑' k, c (n + k) := by
    intro n
    refine (lintegral_rpow_two_tsum_le fun k => hDmeas (n + k)).trans ?_
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [hD2 (n + k)]
    exact hc (n + k)

  set ν : Measure X := P.map Zlim with hν
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hZmeas.aemeasurable

  have hσmeas : ∀ n, Measurable fun ω : ℕ → X => (ω n, Zlim ω) := fun n =>
    (measurable_pi_apply n).prodMk hZmeas
  have hσ : ∀ n, IsCoupling (P.map fun ω => (ω n, Zlim ω)) (u n).toMeasure ν := by
    intro n
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst (hσmeas n), ← heval n]
      rfl
    · rw [Measure.snd, Measure.map_map measurable_snd (hσmeas n), hν]
      rfl
  have hσcost : ∀ n, cost2 (P.map fun ω => (ω n, Zlim ω)) ^ (1 / 2 : ℝ)
      ≤ ∑' k, c (n + k) := by
    intro n
    have hsq : Measurable fun q : X × X => edist q.1 q.2 ^ (2 : ℝ) :=
      ENNReal.continuous_rpow_const.measurable.comp measurable_edist
    have h1 : cost2 (P.map fun ω => (ω n, Zlim ω))
        = ∫⁻ ω, edist (ω n) (Zlim ω) ^ (2 : ℝ) ∂P := by
      rw [cost2]
      exact lintegral_map hsq (hσmeas n)
    have h2 : (∫⁻ ω, edist (ω n) (Zlim ω) ^ (2 : ℝ) ∂P)
        ≤ ∫⁻ ω, R n ω ^ (2 : ℝ) ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [hZR] with ω hω
      exact ENNReal.rpow_le_rpow (hω n) (by norm_num)
    refine le_trans ?_ (hRL2 n)
    rw [h1]
    exact ENNReal.rpow_le_rpow h2 (by norm_num)

  have hm2 : ∀ x₀ : X, m2 ν x₀ ≠ ∞ := by
    intro x₀
    have hb : ∀ ω : ℕ → X, edist (Zlim ω) x₀ ^ (2 : ℝ)
        ≤ 2 * edist (Zlim ω) (ω 0) ^ (2 : ℝ) + 2 * edist (ω 0) x₀ ^ (2 : ℝ) :=
      fun ω => edist_rpow_two_le (Zlim ω) (ω 0) x₀
    have hmz : Measurable fun ω : ℕ → X => edist (Zlim ω) (ω 0) ^ (2 : ℝ) :=
      ENNReal.continuous_rpow_const.measurable.comp
        (measurable_edist.comp (hZmeas.prodMk (measurable_pi_apply 0)))
    have hm0 : Measurable fun ω : ℕ → X => edist (ω 0) x₀ ^ (2 : ℝ) :=
      (measurable_edist_rpow_left x₀).comp (measurable_pi_apply 0)
    have hmoment : m2 ν x₀ = ∫⁻ ω, edist (Zlim ω) x₀ ^ (2 : ℝ) ∂P := by
      rw [m2, hν]
      exact lintegral_map (measurable_edist_rpow_left x₀) hZmeas
    have hint : m2 ν x₀
        ≤ 2 * (∫⁻ ω, edist (Zlim ω) (ω 0) ^ (2 : ℝ) ∂P)
          + 2 * (∫⁻ ω, edist (ω 0) x₀ ^ (2 : ℝ) ∂P) := by
      rw [hmoment]
      refine (lintegral_mono hb).trans_eq ?_
      rw [lintegral_add_left (hmz.const_mul 2), lintegral_const_mul 2 hmz,
        lintegral_const_mul 2 hm0]
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩) hint
    · refine ENNReal.mul_ne_top (by norm_num) ?_

      have h1 : (∫⁻ ω, edist (Zlim ω) (ω 0) ^ (2 : ℝ) ∂P)
          ≤ ∫⁻ ω, R 0 ω ^ (2 : ℝ) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hZR] with ω hω
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [edist_comm]
        exact hω 0
      have h2 : (∫⁻ ω, R 0 ω ^ (2 : ℝ) ∂P) ≤ (∑' k, c k) ^ (2 : ℝ) := by
        have h3 := ENNReal.rpow_le_rpow (hRL2 0) (by norm_num : (0 : ℝ) ≤ 2)
        rw [← ENNReal.rpow_mul, (by norm_num : (1 / 2 : ℝ) * 2 = 1),
          ENNReal.rpow_one] at h3
        simpa using h3
      refine ne_top_of_le_ne_top ?_ (h1.trans h2)
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hsum
    · refine ENNReal.mul_ne_top (by norm_num) ?_
      have h4 : (∫⁻ ω, edist (ω 0) x₀ ^ (2 : ℝ) ∂P) = m2 (u 0).toMeasure x₀ := by
        rw [m2, ← heval 0]
        exact
          (lintegral_map (measurable_edist_rpow_left x₀) (measurable_pi_apply 0)).symm
      rw [h4]
      exact (u 0).m2_ne_top x₀

  refine ⟨⟨ν, inferInstance, hm2⟩, fun n => ?_⟩
  exact (P2.edist_le_cost (hσ n)).trans (hσcost n)

instance : CompleteSpace (P2 X) := by
  refine Metric.complete_of_convergent_controlled_sequences
    (fun n => (1 / 2 : ℝ) ^ n) (fun n => by positivity) fun u hu => ?_
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure (u 0).toMeasure

  have hconsec : ∀ n, edist (u n) (u (n + 1)) < (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    have h1 := hu n n (n + 1) le_rfl (Nat.le_succ n)
    have h2 : edist (u n) (u (n + 1)) = ENNReal.ofReal (dist (u n) (u (n + 1))) :=
      edist_dist _ _
    have h3 : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      congr 1
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    rw [h2, ← h3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h1

  have hex : ∀ n, ∃ πn : Measure (X × X),
      IsCoupling πn (u n).toMeasure (u (n + 1)).toMeasure
        ∧ cost2 πn ^ (1 / 2 : ℝ) < (2⁻¹ : ℝ≥0∞) ^ n :=
    fun n => exists_coupling_of_lt (hconsec n)
  choose π hπ hπc using hex

  have hgeom : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) = 2 := by
    rw [ENNReal.tsum_geometric]
    norm_num [ENNReal.one_sub_inv_two]
  have hsum : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ≠ ∞ := by
    rw [hgeom]
    norm_num
  obtain ⟨ν, hν⟩ := exists_limit_of_summable_chain u π hπ
    (fun n => (2⁻¹ : ℝ≥0∞) ^ n) (fun n => (hπc n).le) hsum
  refine ⟨ν, ?_⟩

  have htail : ∀ n, (∑' k, (2⁻¹ : ℝ≥0∞) ^ (n + k)) = (2⁻¹ : ℝ≥0∞) ^ n * 2 := by
    intro n
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_left, hgeom]
  have hpow : Tendsto (fun n => (2⁻¹ : ℝ≥0∞) ^ n * 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr ENNReal.ofNat_ne_top)
  rw [EMetric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow.eventually_lt_const hε)
  refine ⟨N, fun n hn => ?_⟩
  calc edist (u n) ν ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ (n + k) := hν n
    _ = (2⁻¹ : ℝ≥0∞) ^ n * 2 := htail n
    _ < ε := hN n hn

end Limit

section Wiring

open Metric Function

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X]

theorem sound_QFixBall_wasserstein {T : P2 X → P2 X} {μ₀ : P2 X} {K : ℝ≥0}
    {δ r : ℝ} (hK : K < 1)
    (hlip : LipschitzOnWith K T (closedBall μ₀ r))
    (hres : dist (T μ₀) μ₀ ≤ δ) (hrad : δ + K * r ≤ r) :
    ∃! ν, ν ∈ closedBall μ₀ r ∧ IsFixedPt T ν :=
  Qtsl.QFixBall.sound_QFixBall hK hlip hres hrad

end Wiring

end Wasserstein

end Qtsl
