import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

/-! # Couplings and the Wasserstein-2 extended distance

Foundations for the Wasserstein-2 distance between measures on a metric space.

Main declarations:

* `IsCoupling π μ ν`: `π` is a measure on `X × X` whose marginals are `μ` and `ν`; with
  `IsCoupling.swap`, the product coupling `isCoupling_prod`, and the diagonal coupling
  `isCoupling_map_diag`;
* `cost2 π`: the quadratic transport cost `∫⁻ p, edist p.1 p.2 ^ 2 ∂π`;
* `W2edist μ ν`: the Wasserstein-2 extended distance, the infimum of `cost2 π ^ (1/2)` over all
  couplings `π` of `μ` and `ν`; with symmetry (`W2edist_comm`), vanishing on the diagonal
  (`W2edist_self`), and selection of near-optimal couplings (`exists_coupling_of_lt`);
* `m2 μ x₀`: the second moment of `μ` about `x₀`, and `W2edist_ne_top`: the distance between
  probability measures with finite second moments is finite (via the pointwise bound
  `edist_rpow_two_le` and the product coupling);
* `measure_eq_of_W2edist_eq_zero`: on a second-countable metric space with its Borel σ-algebra,
  probability measures at `W2edist` zero coincide — proved by comparing each closed set with its
  thickenings (`measure_closed_le_thickening_of_eq_zero`, `measure_closed_le_of_eq_zero`).
-/

namespace Qtsl

namespace Wasserstein

open MeasureTheory Set Metric
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

def IsCoupling (π : Measure (X × X)) (μ ν : Measure X) : Prop :=
  π.fst = μ ∧ π.snd = ν

namespace IsCoupling

variable {π : Measure (X × X)} {μ ν : Measure X}

theorem fst_eq (h : IsCoupling π μ ν) : π.fst = μ := h.1

theorem snd_eq (h : IsCoupling π μ ν) : π.snd = ν := h.2

theorem isProbabilityMeasure [IsProbabilityMeasure μ] (h : IsCoupling π μ ν) :
    IsProbabilityMeasure π :=
  ⟨by rw [← Measure.fst_univ, h.1, measure_univ]⟩

theorem swap (h : IsCoupling π μ ν) : IsCoupling (π.map Prod.swap) ν μ :=
  ⟨by rw [Measure.fst_map_swap, h.2], by rw [Measure.snd_map_swap, h.1]⟩

end IsCoupling

theorem isCoupling_prod (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCoupling (μ.prod ν) μ ν :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

theorem isCoupling_map_diag (μ : Measure X) :
    IsCoupling (μ.map fun x => (x, x)) μ μ := by
  have hd : Measurable fun x : X => (x, x) := measurable_id.prodMk measurable_id
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hd]
    exact Measure.map_id
  · rw [Measure.snd, Measure.map_map measurable_snd hd]
    exact Measure.map_id

section Cost

variable [PseudoEMetricSpace X]

noncomputable def cost2 (π : Measure (X × X)) : ℝ≥0∞ :=
  ∫⁻ p, edist p.1 p.2 ^ (2 : ℝ) ∂π

noncomputable def W2edist (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × X)) (_ : IsCoupling π μ ν), cost2 π ^ (1 / 2 : ℝ)

theorem W2edist_le_cost {π : Measure (X × X)} {μ ν : Measure X}
    (h : IsCoupling π μ ν) : W2edist μ ν ≤ cost2 π ^ (1 / 2 : ℝ) :=
  iInf₂_le π h

theorem cost2_map_swap (π : Measure (X × X)) :
    cost2 (π.map Prod.swap) = cost2 π := by
  have hswap : (Prod.swap : X × X → X × X)
      = ⇑(MeasurableEquiv.prodComm (α := X) (β := X)) := rfl
  rw [cost2, hswap, lintegral_map_equiv]
  refine lintegral_congr fun p => ?_
  show edist p.2 p.1 ^ (2 : ℝ) = edist p.1 p.2 ^ (2 : ℝ)
  rw [edist_comm]

theorem W2edist_comm (μ ν : Measure X) : W2edist μ ν = W2edist ν μ := by
  have key : ∀ a b : Measure X, W2edist a b ≤ W2edist b a := fun a b =>
    le_iInf₂ fun π hπ =>
      (W2edist_le_cost hπ.swap).trans_eq (by rw [cost2_map_swap])
  exact le_antisymm (key μ ν) (key ν μ)

theorem W2edist_self (μ : Measure X) : W2edist μ μ = 0 := by
  have hcost : cost2 (μ.map fun x => (x, x)) = 0 := by
    refine le_antisymm ((lintegral_map_le _ _).trans_eq ?_) zero_le
    have hz : ∀ x : X, edist ((fun x : X => (x, x)) x).1 ((fun x : X => (x, x)) x).2
        ^ (2 : ℝ) = 0 := fun x => by
      simp only [edist_self]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
    simp only [hz, lintegral_zero]
  refine le_antisymm ((W2edist_le_cost (isCoupling_map_diag μ)).trans_eq ?_) zero_le
  rw [hcost]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

theorem exists_coupling_of_lt {μ ν : Measure X} {c : ℝ≥0∞}
    (h : W2edist μ ν < c) :
    ∃ π : Measure (X × X), IsCoupling π μ ν ∧ cost2 π ^ (1 / 2 : ℝ) < c := by
  rw [W2edist] at h
  rw [iInf_lt_iff] at h
  obtain ⟨π, hπ⟩ := h
  rw [iInf_lt_iff] at hπ
  obtain ⟨hc, hπ⟩ := hπ
  exact ⟨π, hc, hπ⟩

theorem exists_coupling_cost2_lt_of_eq_zero {μ ν : Measure X}
    (h : W2edist μ ν = 0) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ π : Measure (X × X), IsCoupling π μ ν ∧ cost2 π < c := by
  have hpos : (0 : ℝ≥0∞) < c ^ (1 / 2 : ℝ) := by
    rcases eq_or_ne c ⊤ with rfl | hct
    · simp
    · exact ENNReal.rpow_pos hc hct
  obtain ⟨π, hπ, hlt⟩ := exists_coupling_of_lt (h ▸ hpos)
  refine ⟨π, hπ, ?_⟩
  have hsq := ENNReal.rpow_lt_rpow hlt (by norm_num : (0:ℝ) < 2)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    (by norm_num : (1 / 2 : ℝ) * 2 = 1), ENNReal.rpow_one, ENNReal.rpow_one] at hsq

end Cost

section MarginalLintegral

theorem lintegral_fst_marginal {f : X → ℝ≥0∞} (hf : Measurable f)
    (π : Measure (X × X)) : ∫⁻ p, f p.1 ∂π = ∫⁻ x, f x ∂π.fst := by
  rw [Measure.fst, lintegral_map hf measurable_fst]

theorem lintegral_snd_marginal {f : X → ℝ≥0∞} (hf : Measurable f)
    (π : Measure (X × X)) : ∫⁻ p, f p.2 ∂π = ∫⁻ x, f x ∂π.snd := by
  rw [Measure.snd, lintegral_map hf measurable_snd]

end MarginalLintegral

section PointwiseBound

variable {Y : Type*} [PseudoEMetricSpace Y]

theorem edist_rpow_two_le (x y z : Y) :
    edist x z ^ (2 : ℝ) ≤ 2 * edist x y ^ (2 : ℝ) + 2 * edist y z ^ (2 : ℝ) := by
  calc edist x z ^ (2 : ℝ)
      ≤ (edist x y + edist y z) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (edist_triangle x y z) (by norm_num)
    _ ≤ 2 ^ ((2 : ℝ) - 1) * (edist x y ^ (2 : ℝ) + edist y z ^ (2 : ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
    _ = 2 * edist x y ^ (2 : ℝ) + 2 * edist y z ^ (2 : ℝ) := by
        rw [(by norm_num : (2 : ℝ) - 1 = 1), ENNReal.rpow_one, mul_add]

end PointwiseBound

section Moment

variable [PseudoEMetricSpace X]

noncomputable def m2 (μ : Measure X) (x₀ : X) : ℝ≥0∞ :=
  ∫⁻ x, edist x x₀ ^ (2 : ℝ) ∂μ

variable [OpensMeasurableSpace X]

theorem measurable_edist_rpow_left (x₀ : X) :
    Measurable fun x : X => edist x x₀ ^ (2 : ℝ) :=
  (ENNReal.continuous_rpow_const).measurable.comp measurable_edist_left

end Moment

section MomentMetric

variable [PseudoMetricSpace X] [OpensMeasurableSpace X]

theorem m2_ne_top_of_ne_top {μ : Measure X} [IsFiniteMeasure μ] {x₀ : X}
    (h : m2 μ x₀ ≠ ∞) (x₁ : X) : m2 μ x₁ ≠ ∞ := by
  have hb : ∀ x : X, edist x x₁ ^ (2 : ℝ)
      ≤ 2 * edist x x₀ ^ (2 : ℝ) + 2 * edist x₀ x₁ ^ (2 : ℝ) :=
    fun x => edist_rpow_two_le x x₀ x₁
  have hint : m2 μ x₁ ≤ 2 * m2 μ x₀ + 2 * edist x₀ x₁ ^ (2 : ℝ) * μ univ := by
    refine (lintegral_mono hb).trans_eq ?_
    rw [lintegral_add_left ((measurable_edist_rpow_left x₀).const_mul 2),
      lintegral_const_mul 2 (measurable_edist_rpow_left x₀), lintegral_const,
      m2, mul_assoc]
  refine ne_top_of_le_ne_top ?_ hint
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) h, ?_⟩
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (edist_ne_top x₀ x₁)))
    (measure_ne_top μ univ)

theorem cost2_le_moments {π : Measure (X × X)} {μ ν : Measure X}
    (h : IsCoupling π μ ν) (x₀ : X) :
    cost2 π ≤ 2 * m2 μ x₀ + 2 * m2 ν x₀ := by
  have hb : ∀ p : X × X, edist p.1 p.2 ^ (2 : ℝ)
      ≤ 2 * edist p.1 x₀ ^ (2 : ℝ) + 2 * edist p.2 x₀ ^ (2 : ℝ) := by
    intro p
    have := edist_rpow_two_le p.1 x₀ p.2
    rwa [edist_comm x₀ p.2] at this
  have h1 : Measurable fun p : X × X => edist p.1 x₀ ^ (2 : ℝ) :=
    (measurable_edist_rpow_left x₀).comp measurable_fst
  have h2 : Measurable fun p : X × X => edist p.2 x₀ ^ (2 : ℝ) :=
    (measurable_edist_rpow_left x₀).comp measurable_snd
  calc cost2 π
      ≤ ∫⁻ p, (2 * edist p.1 x₀ ^ (2 : ℝ) + 2 * edist p.2 x₀ ^ (2 : ℝ)) ∂π :=
        lintegral_mono hb
    _ = 2 * (∫⁻ p, edist p.1 x₀ ^ (2 : ℝ) ∂π)
        + 2 * (∫⁻ p, edist p.2 x₀ ^ (2 : ℝ) ∂π) := by
        rw [lintegral_add_left (h1.const_mul 2), lintegral_const_mul 2 h1,
          lintegral_const_mul 2 h2]
    _ = 2 * m2 μ x₀ + 2 * m2 ν x₀ := by
        rw [lintegral_fst_marginal (measurable_edist_rpow_left x₀),
          lintegral_snd_marginal (measurable_edist_rpow_left x₀), h.1, h.2, m2, m2]

theorem W2edist_ne_top {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {x₀ : X} (hμ : m2 μ x₀ ≠ ∞) (hν : m2 ν x₀ ≠ ∞) :
    W2edist μ ν ≠ ∞ := by
  have hbound := cost2_le_moments (isCoupling_prod μ ν) x₀
  have hfin : (2 * m2 μ x₀ + 2 * m2 ν x₀) ≠ ∞ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num) hμ, ENNReal.mul_ne_top (by norm_num) hν⟩
  refine ne_top_of_le_ne_top ?_
    ((W2edist_le_cost (isCoupling_prod μ ν)).trans
      (ENNReal.rpow_le_rpow hbound (by norm_num)))
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin

end MomentMetric

section Eq

variable [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]

theorem measure_closed_le_thickening_of_eq_zero {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : W2edist μ ν = 0) {F : Set X} (hF : IsClosed F) {δ : ℝ} (hδ : 0 < δ) :
    μ F ≤ ν (thickening δ F) := by
  have hedist : Measurable fun p : X × X => edist p.1 p.2 :=
    measurable_edist
  have hδ0 : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hδt : (ENNReal.ofReal δ) ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hδ2 : (0 : ℝ≥0∞) < (ENNReal.ofReal δ) ^ (2 : ℝ) :=
    ENNReal.rpow_pos hδ0 ENNReal.ofReal_ne_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨π, hπ, hc⟩ := exists_coupling_cost2_lt_of_eq_zero h
    (c := (ENNReal.ofReal δ) ^ (2 : ℝ) * ε)
    (ENNReal.mul_pos hδ2.ne' (by exact_mod_cast hε.ne'))

  have hsub : Prod.fst ⁻¹' F ⊆
      (Prod.snd ⁻¹' thickening δ F) ∪ {p : X × X | ENNReal.ofReal δ ≤ edist p.1 p.2} := by
    intro p hp
    rcases lt_or_ge (edist p.1 p.2) (ENNReal.ofReal δ) with hlt | hge
    · left
      rw [mem_preimage, mem_thickening_iff_exists_edist_lt]
      exact ⟨p.1, hp, by rwa [edist_comm]⟩
    · right
      exact hge
  have hbad : π {p : X × X | ENNReal.ofReal δ ≤ edist p.1 p.2} ≤ ε := by
    have hset : {p : X × X | ENNReal.ofReal δ ≤ edist p.1 p.2}
        = {p : X × X | (ENNReal.ofReal δ) ^ (2 : ℝ) ≤ edist p.1 p.2 ^ (2 : ℝ)} := by
      ext p
      simp only [mem_setOf_eq]
      exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).symm
    have hmarkov := meas_ge_le_lintegral_div
      (μ := π) (f := fun p : X × X => edist p.1 p.2 ^ (2 : ℝ))
      ((ENNReal.continuous_rpow_const).measurable.comp hedist).aemeasurable
      (ε := (ENNReal.ofReal δ) ^ (2 : ℝ)) hδ2.ne' hδt
    rw [hset]
    refine hmarkov.trans ?_
    rw [show (∫⁻ p, edist p.1 p.2 ^ (2 : ℝ) ∂π) = cost2 π from rfl]
    exact ENNReal.div_le_of_le_mul' hc.le
  calc μ F = π.fst F := by rw [hπ.1]
    _ = π (Prod.fst ⁻¹' F) := Measure.fst_apply hF.measurableSet
    _ ≤ π ((Prod.snd ⁻¹' thickening δ F)
        ∪ {p : X × X | ENNReal.ofReal δ ≤ edist p.1 p.2}) := measure_mono hsub
    _ ≤ π (Prod.snd ⁻¹' thickening δ F)
        + π {p : X × X | ENNReal.ofReal δ ≤ edist p.1 p.2} := measure_union_le _ _
    _ ≤ ν (thickening δ F) + ε := by
        refine add_le_add ?_ hbad
        rw [← Measure.snd_apply isOpen_thickening.measurableSet, hπ.2]

theorem measure_closed_le_of_eq_zero {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : W2edist μ ν = 0) {F : Set X} (hF : IsClosed F) : μ F ≤ ν F := by

  have hthick : ∀ n : ℕ, μ F ≤ ν (thickening (1 / (n + 1) : ℝ) F) := fun n =>
    measure_closed_le_thickening_of_eq_zero h hF (by positivity)
  have hinter : ⋂ n : ℕ, thickening (1 / (n + 1) : ℝ) F = F := by
    refine subset_antisymm ?_ (subset_iInter fun n =>
      self_subset_thickening (by positivity) F)
    intro x hx
    rw [mem_iInter] at hx
    have hzero : infEDist x F = 0 := by
      by_contra h0
      rcases eq_or_ne (infEDist x F) ⊤ with htop | hne
      · have := hx 0
        rw [mem_thickening_iff_infEDist_lt, htop] at this
        exact (not_top_lt this).elim
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt
          (ENNReal.toReal_pos h0 hne)
        have hlt := hx n
        rw [mem_thickening_iff_infEDist_lt] at hlt
        have hcontra : infEDist x F < infEDist x F := by
          calc infEDist x F < ENNReal.ofReal (1 / (n + 1) : ℝ) := hlt
            _ ≤ ENNReal.ofReal (infEDist x F).toReal := ENNReal.ofReal_le_ofReal hn.le
            _ = infEDist x F := ENNReal.ofReal_toReal hne
        exact (lt_irrefl _ hcontra).elim
    have hxcl : x ∈ closure F := mem_closure_iff_infEDist_zero.mpr hzero
    rwa [hF.closure_eq] at hxcl
  have hanti : Antitone fun n : ℕ => thickening (1 / (n + 1) : ℝ) F := by
    intro a b hab
    refine thickening_mono ?_ F
    have ha : (0:ℝ) < a + 1 := by positivity
    have hb' : (a:ℝ) + 1 ≤ (b:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hab
    exact one_div_le_one_div_of_le ha hb'
  have hlim := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (isOpen_thickening.measurableSet).nullMeasurableSet) hanti
    ⟨0, measure_ne_top ν _⟩
  rw [hinter] at hlim
  exact ge_of_tendsto' hlim hthick

theorem measure_eq_of_W2edist_eq_zero {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : W2edist μ ν = 0) : μ = ν := by
  have hν : W2edist ν μ = 0 := by rw [W2edist_comm]; exact h
  have hclosed : ∀ F : Set X, IsClosed F → μ F = ν F := fun F hF =>
    le_antisymm (measure_closed_le_of_eq_zero h hF)
      (measure_closed_le_of_eq_zero hν hF)
  refine ext_of_generate_finite {s : Set X | IsClosed s} ?_ isPiSystem_isClosed ?_ ?_
  · rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
  · exact fun s hs => hclosed s hs
  · rw [measure_univ, measure_univ]

end Eq

end Wasserstein

end Qtsl
