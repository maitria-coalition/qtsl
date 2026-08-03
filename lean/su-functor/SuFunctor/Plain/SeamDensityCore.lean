import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import SuFunctor.Plain.GeneralSeam

/-! # Density of finitely supported joints among subprobability measures

Every subprobability Borel measure on a separable pseudometric space is a narrow
(weak) limit of finitely supported subprobability measures: the seam embedding
`SuFunctor.Plain.Joint.toMeas` has dense range in `SuFunctor.Plain.MeasJoint`.
This is the subprobability form of the classical fact that finitely supported
probability measures are weakly dense (Parthasarathy, *Probability measures on
metric spaces*, Theorem II.6.3); mass may sit strictly below one, and the
approximants lose mass rather than renormalize.

The proof quantizes a given subprobability measure `μ` along countable measurable
partitions of vanishing diameter
(`MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le`): truncate to
finitely many cells carrying all but a vanishing tail of the mass, and place a
point mass of weight `μ (cell)` at a representative point of each cell.
Convergence is checked against bounded continuous nonnegative test functions
(`MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`); the
integral of a test function against the quantization is compared with its
integral against `μ` through the cell-wise constant discretization of the test
function along the partition, whose integral converges by dominated convergence,
while the truncation error is controlled by the tail mass.  No completeness is
assumed, and the empty carrier is handled separately.

## Main statements

* `SuFunctor.Plain.Joint.denseRange_toMeas` — density, over a separable
  pseudometric carrier.
* `SuFunctor.Plain.Joint.denseRange_toMeas_of_pseudoMetrizable` — the same
  statement with the metric hypothesis relaxed to pseudo-metrizability of a
  given topology.

Auxiliary constructions live in the `Joint.SeamDensityCore` namespace: the joint
built from a finite family of weighted points with its weighted-point-mass
integral formulas, the cell-wise constant discretization of a function along a
countable partition, the tail estimates, the quantization of a subprobability
measure along a truncated partition, and the analytic core of the convergence
argument.  They are namespaced to this module; general-purpose homes for them
belong to the seam modules.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace Joint

namespace SeamDensityCore

/-! ### Joints from finitely many weighted points -/

section OfFinset

variable {X : Type u} {ι : Type*}

/-- The finitely supported joint carrying weight `w i` at the point `x i`, as `i`
ranges over a finite index set, given that the total weight is a subprobability.
Coinciding points accumulate their weights. -/
def ofFinset (s : Finset ι) (x : ι → X) (w : ι → ℝ≥0) (h : ∑ i ∈ s, w i ≤ 1) :
    Joint X where
  wt := ∑ i ∈ s, Finsupp.single (x i) (w i)
  mass_le_one := by
    classical
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) fun _ _ _ => rfl]
    calc ∑ i ∈ s, (Finsupp.single (x i) (w i)).sum (fun _ v => v)
        = ∑ i ∈ s, w i := Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index rfl
      _ ≤ 1 := h

@[simp] theorem ofFinset_wt (s : Finset ι) (x : ι → X) (w : ι → ℝ≥0)
    (h : ∑ i ∈ s, w i ≤ 1) :
    (ofFinset s x w h).wt = ∑ i ∈ s, Finsupp.single (x i) (w i) := rfl

variable [MeasurableSpace X]

/-- The measure of a joint built from finitely many weighted points is the
corresponding finite combination of point masses. -/
theorem measSum_ofFinset {s : Finset ι} {x : ι → X} {w : ι → ℝ≥0}
    {h : ∑ i ∈ s, w i ≤ 1} :
    measSum (ofFinset s x w h)
      = ∑ i ∈ s, ((w i : ℝ≥0∞) • Measure.dirac (x i) : Measure X) := by
  classical
  show (∑ i ∈ s, Finsupp.single (x i) (w i)).sum
      (fun i v => ((v : ℝ≥0∞) • Measure.dirac i : Measure X)) = _
  rw [← Finsupp.sum_finsetSum_index (fun b => by rw [ENNReal.coe_zero, zero_smul])
    fun b w₁ w₂ => by rw [ENNReal.coe_add, add_smul]]
  exact Finset.sum_congr rfl fun i _ =>
    Finsupp.sum_single_index (by rw [ENNReal.coe_zero, zero_smul])

/-- The lower integral of a measurable function against the measure of a
finitely supported joint is the weighted sum of its values on the support. -/
theorem lintegral_toMeas (ν : Joint X) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂((toMeas ν).1 : Measure X) = ν.wt.sum fun i v => (v : ℝ≥0∞) * g i := by
  rw [toMeas_toMeasure]
  simp only [measSum, Finsupp.sum]
  rw [lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun i _ => by
    rw [lintegral_smul_measure, lintegral_dirac' i hg, smul_eq_mul]

/-- The lower integral of a measurable function against a joint built from
finitely many weighted points. -/
theorem lintegral_toMeas_ofFinset {s : Finset ι} {x : ι → X} {w : ι → ℝ≥0}
    {h : ∑ i ∈ s, w i ≤ 1} {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂((toMeas (ofFinset s x w h)).1 : Measure X)
      = ∑ i ∈ s, (w i : ℝ≥0∞) * g (x i) := by
  rw [toMeas_toMeasure, measSum_ofFinset, lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun i _ => by
    rw [lintegral_smul_measure, lintegral_dirac' _ hg, smul_eq_mul]

end OfFinset

/-! ### Cell-wise constant discretizations along a countable partition -/

section Discretize

variable {X : Type u} {As : ℕ → Set X} {v : ℕ → ℝ≥0∞}

/-- The cell-wise constant function taking the value `v n` on `As n`; zero off
the union.  Intended for pairwise disjoint families. -/
def discretize (As : ℕ → Set X) (v : ℕ → ℝ≥0∞) (a : X) : ℝ≥0∞ :=
  ∑' n, (As n).indicator (fun _ => v n) a

theorem discretize_eq_of_mem (hd : Pairwise fun n n' => Disjoint (As n) (As n'))
    {a : X} {n : ℕ} (ha : a ∈ As n) : discretize As v a = v n := by
  refine (tsum_eq_single n fun j hj => ?_).trans (Set.indicator_of_mem ha _)
  exact Set.indicator_of_notMem (Set.disjoint_right.mp (hd hj) ha) _

variable [MeasurableSpace X]

theorem measurable_discretize (v : ℕ → ℝ≥0∞) (hm : ∀ n, MeasurableSet (As n)) :
    Measurable (discretize As v) :=
  Measurable.tsum fun n => measurable_const.indicator (hm n)

theorem lintegral_discretize (m : Measure X) (v : ℕ → ℝ≥0∞)
    (hm : ∀ n, MeasurableSet (As n)) :
    ∫⁻ a, discretize As v a ∂m = ∑' n, v n * m (As n) := by
  simp only [discretize]
  rw [lintegral_tsum fun n => (measurable_const.indicator (hm n)).aemeasurable]
  exact tsum_congr fun n => lintegral_indicator_const (hm n) _

/-- Truncation estimate: the full series of weighted cell masses exceeds its
truncation at rank `N` by at most a uniform weight bound times the tail mass.
Proved through finite partial sums, on which the disjoint cells give exact
additivity. -/
theorem tsum_le_sum_range_add (m : Measure X) (hm : ∀ n, MeasurableSet (As n))
    (hd : Pairwise fun n n' => Disjoint (As n) (As n')) {c : ℝ≥0∞}
    (hv : ∀ n, v n ≤ c) (N : ℕ) :
    (∑' n, v n * m (As n))
      ≤ (∑ n ∈ Finset.range N, v n * m (As n)) + c * m (⋃ n ≥ N, As n) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← Finset.sum_filter_add_sum_filter_not s fun n => n ∈ Finset.range N]
  refine add_le_add
    (Finset.sum_le_sum_of_subset fun n hn => (Finset.mem_filter.mp hn).2) ?_
  calc ∑ n ∈ s.filter fun n => ¬n ∈ Finset.range N, v n * m (As n)
      ≤ ∑ n ∈ s.filter fun n => ¬n ∈ Finset.range N, c * m (As n) :=
        Finset.sum_le_sum fun n _ => mul_le_mul_left (hv n) _
    _ = c * ∑ n ∈ s.filter fun n => ¬n ∈ Finset.range N, m (As n) := by
        rw [Finset.mul_sum]
    _ = c * m (⋃ n ∈ s.filter fun n => ¬n ∈ Finset.range N, As n) := by
        rw [measure_biUnion_finset (hd.set_pairwise _) fun n _ => hm n]
    _ ≤ c * m (⋃ n ≥ N, As n) := by
        refine mul_le_mul_right (measure_mono ?_) _
        refine Set.iUnion₂_subset fun n hn => ?_
        exact Set.subset_biUnion_of_mem
          (le_of_not_gt fun h => (Finset.mem_filter.mp hn).2 (Finset.mem_range.mpr h))

end Discretize

/-! ### Quantization of a subprobability measure along a truncated partition -/

section Quantize

variable {X : Type u} [MeasurableSpace X]

theorem sum_range_toNNReal_measure_le {ν : FiniteMeasure X} (hν : ν.mass ≤ 1)
    {As : ℕ → Set X} (hm : ∀ n, MeasurableSet (As n))
    (hd : Pairwise fun n n' => Disjoint (As n) (As n')) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((ν : Measure X) (As n)).toNNReal ≤ 1 := by
  have h1 : ((∑ n ∈ Finset.range N, ((ν : Measure X) (As n)).toNNReal : ℝ≥0) : ℝ≥0∞)
      = (ν : Measure X) (⋃ n ∈ Finset.range N, As n) := by
    rw [ENNReal.ofNNReal_finsetSum,
      measure_biUnion_finset (hd.set_pairwise _) fun n _ => hm n]
    exact Finset.sum_congr rfl fun n _ => ENNReal.coe_toNNReal (measure_ne_top _ _)
  have h2 : (ν : Measure X) (⋃ n ∈ Finset.range N, As n) ≤ 1 := by
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    rw [← FiniteMeasure.ennreal_mass]
    exact_mod_cast hν
  exact_mod_cast h1.trans_le h2

/-- The quantization of a subprobability measure along a truncated partition:
the finitely supported joint with weight `ν (As n)` at `rep n` for `n < N`. -/
def quantize (ν : FiniteMeasure X) (hν : ν.mass ≤ 1) {As : ℕ → Set X}
    (hm : ∀ n, MeasurableSet (As n))
    (hd : Pairwise fun n n' => Disjoint (As n) (As n'))
    (rep : ℕ → X) (N : ℕ) : Joint X :=
  ofFinset (Finset.range N) rep (fun n => ((ν : Measure X) (As n)).toNNReal)
    (sum_range_toNNReal_measure_le hν hm hd N)

theorem lintegral_quantize (ν : FiniteMeasure X) (hν : ν.mass ≤ 1) {As : ℕ → Set X}
    (hm : ∀ n, MeasurableSet (As n))
    (hd : Pairwise fun n n' => Disjoint (As n) (As n'))
    (rep : ℕ → X) (N : ℕ) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂((toMeas (quantize ν hν hm hd rep N)).1 : Measure X)
      = ∑ n ∈ Finset.range N, g (rep n) * (ν : Measure X) (As n) := by
  simp only [quantize]
  rw [lintegral_toMeas_ofFinset hg]
  exact Finset.sum_congr rfl fun n _ => by
    rw [ENNReal.coe_toNNReal (measure_ne_top _ _), mul_comm]

end Quantize

/-! ### The analytic core -/

set_option maxHeartbeats 400000 in
/-- The analytic core of the density theorem: along partitions of vanishing
diameter with vanishing tail mass, the quantized sums of a bounded continuous
nonnegative test function converge to its lower integral. -/
theorem tendsto_sum_quantization {X : Type u} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (m : Measure X) [IsFiniteMeasure m]
    (As : ℕ → ℕ → Set X) (hm : ∀ k n, MeasurableSet (As k n))
    (hbdd : ∀ k n, Bornology.IsBounded (As k n))
    (hdiam : ∀ k n, Metric.diam (As k n) ≤ 1 / ((k : ℝ) + 1))
    (hcover : ∀ k, ⋃ n, As k n = Set.univ)
    (hdisj : ∀ k, Pairwise fun n n' => Disjoint (As k n) (As k n'))
    (N : ℕ → ℕ)
    (hN : ∀ k, m (⋃ n ≥ N k, As k n) < ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (rep : ℕ → ℕ → X) (hrep : ∀ k n, (As k n).Nonempty → rep k n ∈ As k n)
    (f : BoundedContinuousFunction X ℝ≥0) (C : ℝ≥0) (hfC : ∀ a, f a ≤ C) :
    Tendsto (fun k => ∑ n ∈ Finset.range (N k), (f (rep k n) : ℝ≥0∞) * m (As k n))
      atTop (𝓝 (∫⁻ a, (f a : ℝ≥0∞) ∂m)) := by
  -- Pointwise convergence of the cell-wise discretizations of `f`: the
  -- representative of the cell of `a` converges to `a` since diameters vanish,
  -- and `f` is continuous at `a`.
  have hlim : ∀ a : X,
      Tendsto (fun k => discretize (As k) (fun n => (f (rep k n) : ℝ≥0∞)) a)
        atTop (𝓝 (f a : ℝ≥0∞)) := by
    intro a
    have hcell : ∀ k, ∃ n, a ∈ As k n := fun k =>
      Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp (hcover k) a)
    choose nx hnx using hcell
    have hdist : Tendsto (fun k => rep k (nx k)) atTop (𝓝 a) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun k => dist_nonneg) fun k => ?_
      exact (Metric.dist_le_diam_of_mem (hbdd k (nx k))
        (hrep k (nx k) ⟨a, hnx k⟩) (hnx k)).trans (hdiam k (nx k))
    have hfa : Tendsto (fun k => ((f (rep k (nx k)) : ℝ≥0) : ℝ≥0∞))
        atTop (𝓝 (f a : ℝ≥0∞)) :=
      ENNReal.tendsto_coe.mpr ((f.continuous.tendsto a).comp hdist)
    exact hfa.congr fun k => (discretize_eq_of_mem (hdisj k) (hnx k)).symm
  -- Uniform bound for the discretizations.
  have hle : ∀ k a, discretize (As k) (fun n => (f (rep k n) : ℝ≥0∞)) a ≤ (C : ℝ≥0∞) := by
    intro k a
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp (hcover k) a)
    rw [discretize_eq_of_mem (hdisj k) hn]
    exact ENNReal.coe_le_coe.mpr (hfC _)
  -- Dominated convergence, with the integrals rewritten as series.
  have hB : Tendsto (fun k => ∑' n, (f (rep k n) : ℝ≥0∞) * m (As k n)) atTop
      (𝓝 (∫⁻ a, (f a : ℝ≥0∞) ∂m)) := by
    refine (tendsto_lintegral_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
      (fun k => measurable_discretize _ (hm k)) (fun k => ae_of_all m (hle k)) ?_
      (ae_of_all m hlim)).congr fun k => lintegral_discretize m _ (hm k)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top m _)
  -- The vanishing tail correction.
  have hc : Tendsto (fun k : ℕ => (C : ℝ≥0∞) * ENNReal.ofReal (1 / ((k : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) h1 (Or.inr ENNReal.coe_ne_top)
  have hlower : Tendsto
      (fun k => (∑' n, (f (rep k n) : ℝ≥0∞) * m (As k n))
        - (C : ℝ≥0∞) * ENNReal.ofReal (1 / ((k : ℝ) + 1)))
      atTop (𝓝 (∫⁻ a, (f a : ℝ≥0∞) ∂m)) := by
    simpa using ENNReal.Tendsto.sub hB hc (Or.inr ENNReal.zero_ne_top)
  -- Squeeze the truncations between the tail-corrected series and the series.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hB (fun k => ?_)
    fun k => ENNReal.sum_le_tsum _
  refine tsub_le_iff_right.mpr ?_
  refine (tsum_le_sum_range_add m (hm k) (hdisj k)
    (fun n => ENNReal.coe_le_coe.mpr (hfC _)) (N k)).trans ?_
  exact add_le_add_right (mul_le_mul_right (hN k).le _) _

end SeamDensityCore

/-- **Density of finitely supported joints.**  Over a separable pseudometric
carrier whose σ-algebra contains the Borel one, every subprobability measure is
a narrow limit of finitely supported subprobability measures: the seam embedding
has dense range in the subprobability carrier. -/
theorem denseRange_toMeas {X : Type u} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] :
    DenseRange (toMeas : Joint X → MeasJoint X) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    -- Over an empty carrier the subprobability carrier is a single point, the
    -- zero measure, which is the image of the zero joint.
    intro μ
    have hμ : μ = toMeas (Joint.zero X) := MeasJoint.ext' (Subsingleton.elim _ _)
    rw [hμ]
    exact subset_closure (Set.mem_range_self _)
  | inr hX =>
    intro μ
    obtain ⟨ν, hν⟩ := μ
    -- Countable measurable partitions of vanishing diameter, one per stage `k`.
    have hpart : ∀ k : ℕ, ∃ As : ℕ → Set X, (∀ n, MeasurableSet (As n)) ∧
        (∀ n, Bornology.IsBounded (As n)) ∧
        (∀ n, Metric.diam (As n) ≤ 1 / ((k : ℝ) + 1)) ∧
        (⋃ n, As n = Set.univ) ∧ Pairwise fun n n' => Disjoint (As n) (As n') :=
      fun k => SeparableSpace.exists_measurable_partition_diam_le X (by positivity)
    choose As As_mble As_bdd As_diam As_cover As_disj using hpart
    -- Truncation ranks: all but a vanishing tail of the mass sits on finitely
    -- many cells of each partition.
    have htail : ∀ k : ℕ, ∃ N : ℕ,
        (ν : Measure X) (⋃ n ≥ N, As k n) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have h0 := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (μ := (ν : Measure X)) (fun n => (As_mble k n).nullMeasurableSet) (As_disj k)
      exact ((tendsto_order.1 h0).2 _ (ENNReal.ofReal_pos.mpr (by positivity))).exists
    choose N hN using htail
    -- A representative point of every nonempty cell.
    have hrep' : ∀ k n : ℕ, ∃ y : X, (As k n).Nonempty → y ∈ As k n := by
      intro k n
      rcases (As k n).eq_empty_or_nonempty with h | h
      · exact ⟨Classical.arbitrary X, fun hne => absurd h hne.ne_empty⟩
      · exact ⟨h.some, fun _ => h.some_mem⟩
    choose rep hrep using hrep'
    -- The quantizations converge narrowly: check against test functions and
    -- reduce to the analytic core.
    have key : Tendsto (fun k =>
        toMeas (SeamDensityCore.quantize ν hν (As_mble k) (As_disj k) (rep k) (N k)))
        atTop (𝓝 (⟨ν, hν⟩ : MeasJoint X)) := by
      refine tendsto_subtype_rng.mpr
        (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f => ?_)
      show Tendsto (fun k => ∫⁻ a, (f a : ℝ≥0∞)
          ∂((toMeas (SeamDensityCore.quantize ν hν (As_mble k) (As_disj k)
            (rep k) (N k))).1 : Measure X))
        atTop (𝓝 (∫⁻ a, (f a : ℝ≥0∞) ∂(ν : Measure X)))
      refine (SeamDensityCore.tendsto_sum_quantization (ν : Measure X) As As_mble
        As_bdd As_diam As_cover As_disj N hN rep hrep f (nndist f 0)
        (fun a => BoundedContinuousFunction.NNReal.upper_bound f a)).congr fun k => ?_
      exact (SeamDensityCore.lintegral_quantize ν hν (As_mble k) (As_disj k) (rep k)
        (N k) f.continuous.measurable.coe_nnreal_ennreal).symm
    exact mem_closure_of_tendsto key
      (Filter.Eventually.of_forall fun k => Set.mem_range_self _)

/-- Density of finitely supported joints, with the metric hypothesis relaxed to
pseudo-metrizability: the topology is fixed, and any compatible pseudometric
witnesses the density.  The measurable structure is untouched, since the
compatible pseudometric induces the given topology on the nose. -/
theorem denseRange_toMeas_of_pseudoMetrizable {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] :
    DenseRange (toMeas : Joint X → MeasJoint X) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact denseRange_toMeas

end Joint

end

end Plain

end SuFunctor
