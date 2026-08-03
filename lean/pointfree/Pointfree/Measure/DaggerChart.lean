import Pointfree.Measure.SubProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Gluing

/-! # The measure-level dagger chart

Subprobability measures on `X` are exactly probability measures on
`X ⊕ Unit`: the missing mass is stored at the added dagger point
`Sum.inr ()`.  This is the classical face of the point-free promotion
chart (`SubProb.promoteEquiv`, `SubProb.promoteHomeomorph`): there the
dagger coordinate is a `Prop` factor adjoined to the frame; here it is
a genuine added point of the space.

Main definitions and results:

* `promoteMeasure` / `restrictMeasure` — the chart's two legs at the
  level of measures, with round trips `restrictMeasure_promoteMeasure`
  and `promoteMeasure_restrictMeasure`.
* `lintegral_promoteMeasure` / `lintegral_comap_inl` — the integral
  calculus of the chart: integrating against the promoted measure
  splits into the `X`-part and a dagger atom; integrating against the
  restricted measure is integration of the zero-extension.  The
  `testAgainstNN` faces are derived.
* `daggerChartMeasure : SubProbabilityMeasure X ≃ₜ ProbabilityMeasure (X ⊕ Unit)`
  — the chart is a homeomorphism for the weak topologies.
* Compactness of `SubProbabilityMeasure X` for compact Hausdorff Borel
  `X`, by **two independent routes**: directly from the compactness of
  mass-bounded sets of finite measures (the instance), and transported
  along the chart from Prokhorov's theorem for probability measures on
  the compact space `X ⊕ Unit` (`compactSpace_of_daggerChartMeasure`).
* `metrizableSpace_subProbabilityMeasure` — metrizability of the weak
  topology on subprobability measures over a metrizable separable
  Borel space, transported along the chart from the Lévy–Prokhorov
  metrization.

The file also provides the measurable/Borel glue for the dagger sum
that mathlib does not currently have: `Sum.inl` as a measurable
embedding, and `OpensMeasurableSpace`/`BorelSpace`/`MetrizableSpace`
instances for `X ⊕ Unit`.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

/-! ## `Sum.inl` as a measurable embedding -/

/-- The left injection into a sum of measurable spaces is a measurable
embedding. -/
theorem measurableEmbedding_inl {β : Type*} [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inl : X → X ⊕ β) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' _ hs := hs.inl_image

/-! ## Borel glue for the dagger sum `X ⊕ Unit` -/

section BorelGlue

variable [TopologicalSpace X]

/-- Opens of the dagger sum are measurable: on the `X` summand this is
the `OpensMeasurableSpace` hypothesis, and on the dagger point
everything is measurable. -/
instance instOpensMeasurableSpaceSumUnit [OpensMeasurableSpace X] :
    OpensMeasurableSpace (X ⊕ Unit) where
  borel_le := MeasurableSpace.generateFrom_le fun s hs => by
    rw [measurableSet_sum_iff]
    exact ⟨(IsOpen.preimage continuous_inl hs).measurableSet,
      MeasurableSpace.measurableSet_top⟩

/-- The image under `Sum.inl` of a measurable set is Borel in the
dagger sum: the collection of sets with Borel image is a σ-algebra
containing the opens (the left injection is an open embedding). -/
theorem measurableSet_borel_inl_image [BorelSpace X] {A : Set X}
    (hA : MeasurableSet A) :
    MeasurableSet[borel (X ⊕ Unit)] (Sum.inl '' A) := by
  have hopen : ∀ {t : Set (X ⊕ Unit)}, IsOpen t →
      MeasurableSet[borel (X ⊕ Unit)] t :=
    fun ht => MeasurableSpace.measurableSet_generateFrom ht
  -- derived before `m'` enters the context: a let-bound `MeasurableSpace X`
  -- would otherwise be picked up by instance resolution
  have hA' : MeasurableSet[borel X] A := BorelSpace.measurable_eq (α := X) ▸ hA
  let m' : MeasurableSpace X :=
    { MeasurableSet' := fun B => MeasurableSet[borel (X ⊕ Unit)] (Sum.inl '' B)
      measurableSet_empty := by simp
      measurableSet_compl := fun B hB => by
        rw [Set.image_compl_eq_range_sdiff_image Sum.inl_injective]
        exact (hopen isOpen_range_inl).diff hB
      measurableSet_iUnion := fun g hg => by
        rw [Set.image_iUnion]
        exact MeasurableSet.iUnion hg }
  have hle : borel X ≤ m' :=
    MeasurableSpace.generateFrom_le fun U hU =>
      hopen (Topology.IsOpenEmbedding.inl.isOpenMap U hU)
  exact hle A hA'

/-- The dagger sum of a Borel space is Borel.  The two directions:
opens are measurable (`instOpensMeasurableSpaceSumUnit`), and every
measurable set of the sum σ-algebra decomposes into an `inl`-image of
a Borel set of `X` (Borel by `measurableSet_borel_inl_image`) and a
subset of the dagger point (empty, or the open `range Sum.inr`). -/
instance instBorelSpaceSumUnit [BorelSpace X] : BorelSpace (X ⊕ Unit) where
  measurable_eq := by
    refine le_antisymm (fun s hs => ?_) OpensMeasurableSpace.borel_le
    obtain ⟨h1, h2⟩ := measurableSet_sum_iff.mp hs
    have hdecomp : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext (x | u)
      · simp
      · constructor
        · exact fun h => Or.inr ⟨u, h, rfl⟩
        · rintro (⟨x, -, hx⟩ | ⟨v, hv, hveq⟩)
          · exact absurd hx (by simp)
          · exact hveq ▸ hv
    rw [hdecomp]
    refine MeasurableSet.union (measurableSet_borel_inl_image h1) ?_
    rcases Set.eq_empty_or_nonempty (Sum.inr ⁻¹' s) with hB | hB
    · rw [hB, Set.image_empty]
      exact (borel (X ⊕ Unit)).measurableSet_empty
    · have hBuniv : Sum.inr ⁻¹' s = Set.univ :=
        Set.eq_univ_of_forall fun u => by
          obtain ⟨v, hv⟩ := hB
          rwa [Subsingleton.elim u v]
      rw [hBuniv, Set.image_univ]
      exact MeasurableSpace.measurableSet_generateFrom isOpen_range_inr

/-- The dagger sum of a metrizable space is metrizable, via the glued
sum metric (whose uniformity is proved in mathlib to coincide with the
disjoint-union uniformity). -/
instance instMetrizableSpaceSumUnit [MetrizableSpace X] :
    MetrizableSpace (X ⊕ Unit) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : MetricSpace (X ⊕ Unit) := Metric.metricSpaceSum
  haveI : PseudoMetrizableSpace (X ⊕ Unit) := inferInstance
  infer_instance

end BorelGlue

/-! ## The chart's two legs -/

/-- **Promotion**: a subprobability measure on `X` becomes a probability
measure on `X ⊕ Unit` by pushing forward along `Sum.inl` and storing
the missing mass `1 - μ(X)` as an atom at the dagger point. -/
noncomputable def promoteMeasure (μ : SubProbabilityMeasure X) :
    ProbabilityMeasure (X ⊕ Unit) :=
  ⟨(μ.1 : Measure X).map Sum.inl
      + (1 - (μ.1 : Measure X) Set.univ) • Measure.dirac (Sum.inr ()),
   ⟨by
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_inl MeasurableSet.univ, Set.preimage_univ,
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact add_tsub_cancel_of_le μ.measure_univ_le_one⟩⟩

@[simp] theorem toMeasure_promoteMeasure (μ : SubProbabilityMeasure X) :
    (promoteMeasure μ : Measure (X ⊕ Unit))
      = (μ.1 : Measure X).map Sum.inl
        + (1 - (μ.1 : Measure X) Set.univ) • Measure.dirac (Sum.inr ()) := rfl

/-- **Restriction**: a probability measure on `X ⊕ Unit` restricts to a
subprobability measure on `X` by pulling back along `Sum.inl` (the
dagger atom's mass is forgotten). -/
noncomputable def restrictMeasure (ν : ProbabilityMeasure (X ⊕ Unit)) :
    SubProbabilityMeasure X :=
  ⟨⟨(ν : Measure (X ⊕ Unit)).comap Sum.inl, inferInstance⟩, by
    have h : ((ν : Measure (X ⊕ Unit)).comap Sum.inl) Set.univ ≤ 1 := by
      rw [measurableEmbedding_inl.comap_apply, Set.image_univ]
      exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have h' : ((FiniteMeasure.mass
        ⟨(ν : Measure (X ⊕ Unit)).comap Sum.inl, inferInstance⟩ : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
      rw [FiniteMeasure.ennreal_mass]
      exact h
    exact_mod_cast h'⟩

@[simp] theorem toMeasure_restrictMeasure (ν : ProbabilityMeasure (X ⊕ Unit)) :
    ((restrictMeasure ν).1 : Measure X)
      = (ν : Measure (X ⊕ Unit)).comap Sum.inl := rfl

/-! ## Round trips -/

/-- Restriction after promotion is the identity: pulling the pushforward
back along the embedding recovers the measure, and the dagger atom is
invisible from `X` (its comap vanishes on `inl`-images). -/
theorem restrictMeasure_promoteMeasure (μ : SubProbabilityMeasure X) :
    restrictMeasure (promoteMeasure μ) = μ := by
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  rw [toMeasure_restrictMeasure, toMeasure_promoteMeasure]
  ext s hs
  have hnot : Sum.inr () ∉ Sum.inl '' s := by simp
  rw [measurableEmbedding_inl.comap_apply, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply measurable_inl hs.inl_image,
    Set.preimage_image_eq s Sum.inl_injective,
    Measure.dirac_apply' _ hs.inl_image, Set.indicator_of_notMem hnot, mul_zero,
    add_zero]

/-- Promotion after restriction is the identity: a probability measure
on the dagger sum decomposes into its restriction to `range Sum.inl`
plus its atom at the dagger point, and the dagger weight is exactly the
mass complement. -/
theorem promoteMeasure_restrictMeasure (ν : ProbabilityMeasure (X ⊕ Unit)) :
    promoteMeasure (restrictMeasure ν) = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [toMeasure_promoteMeasure, toMeasure_restrictMeasure]
  have hrange : (Set.range (Sum.inl : X → X ⊕ Unit))ᶜ = {Sum.inr ()} := by
    rw [isCompl_range_inl_range_inr.compl_eq, Set.range_unique]
  have hw : (1 : ℝ≥0∞) - ((ν : Measure (X ⊕ Unit)).comap Sum.inl) Set.univ
      = (ν : Measure (X ⊕ Unit)) {Sum.inr ()} := by
    rw [measurableEmbedding_inl.comap_apply, Set.image_univ,
      ← measure_univ (μ := (ν : Measure (X ⊕ Unit))),
      ← measure_compl measurableSet_range_inl (measure_ne_top _ _), hrange]
  calc ((ν : Measure (X ⊕ Unit)).comap Sum.inl).map Sum.inl
        + ((1 : ℝ≥0∞) - ((ν : Measure (X ⊕ Unit)).comap Sum.inl) Set.univ)
          • Measure.dirac (Sum.inr ())
      = (ν : Measure (X ⊕ Unit)).restrict (Set.range Sum.inl)
        + (ν : Measure (X ⊕ Unit)) {Sum.inr ()} • Measure.dirac (Sum.inr ()) := by
        rw [measurableEmbedding_inl.map_comap, hw]
    _ = (ν : Measure (X ⊕ Unit)).restrict (Set.range Sum.inl)
        + (ν : Measure (X ⊕ Unit)).restrict {Sum.inr ()} := by
        rw [Measure.restrict_singleton]
    _ = (ν : Measure (X ⊕ Unit)).restrict (Set.range Sum.inl)
        + (ν : Measure (X ⊕ Unit)).restrict (Set.range (Sum.inl : X → X ⊕ Unit))ᶜ := by
        rw [hrange]
    _ = (ν : Measure (X ⊕ Unit)) :=
        Measure.restrict_add_restrict_compl measurableSet_range_inl

/-! ## The integral calculus of the chart -/

section Continuity

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The zero-extension of a bounded continuous nonnegative function on
`X` to the dagger sum: `g` on the `X` summand, `0` at the dagger point. -/
noncomputable def extendZero (g : X →ᵇ ℝ≥0) : (X ⊕ Unit) →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨Sum.elim ⇑g fun _ => 0, g.continuous.sumElim continuous_const⟩
    (dist g 0 + dist g 0)
    (by
      have key : ∀ y : X ⊕ Unit,
          dist (Sum.elim ⇑g (fun _ => (0 : ℝ≥0)) y) (0 : ℝ≥0) ≤ dist g 0 := by
        rintro (x | u)
        · simpa using g.dist_coe_le_dist (g := 0) x
        · simp
      intro x y
      calc dist (Sum.elim ⇑g (fun _ => (0 : ℝ≥0)) x)
            (Sum.elim ⇑g (fun _ => (0 : ℝ≥0)) y)
          ≤ dist (Sum.elim ⇑g (fun _ => (0 : ℝ≥0)) x) (0 : ℝ≥0)
            + dist (0 : ℝ≥0) (Sum.elim ⇑g (fun _ => (0 : ℝ≥0)) y) :=
            dist_triangle _ _ _
        _ ≤ dist g 0 + dist g 0 := by
            rw [dist_comm (0 : ℝ≥0)]
            exact add_le_add (key x) (key y))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
@[simp] theorem extendZero_apply_inl (g : X →ᵇ ℝ≥0) (x : X) :
    extendZero g (Sum.inl x) = g x := rfl

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
@[simp] theorem extendZero_apply_inr (g : X →ᵇ ℝ≥0) (u : Unit) :
    extendZero g (Sum.inr u) = 0 := rfl

/-- Integration against the promoted measure: the `X`-part integrates
the restriction of the test function along `Sum.inl`, and the dagger
atom contributes the mass complement times the value at the dagger
point. -/
theorem lintegral_promoteMeasure (μ : SubProbabilityMeasure X)
    (f : (X ⊕ Unit) →ᵇ ℝ≥0) :
    ∫⁻ y, (f y : ℝ≥0∞) ∂(promoteMeasure μ : Measure (X ⊕ Unit))
      = ∫⁻ x, (f (Sum.inl x) : ℝ≥0∞) ∂(μ.1 : Measure X)
        + (1 - (μ.1 : Measure X) Set.univ) * (f (Sum.inr ()) : ℝ≥0∞) := by
  rw [toMeasure_promoteMeasure, lintegral_add_measure,
    measurableEmbedding_inl.lintegral_map, lintegral_smul_measure,
    lintegral_dirac' _ f.measurable_coe_ennreal_comp, smul_eq_mul]

/-- Integration against the restricted measure is integration of the
zero-extension: the comap seam routes through
`MeasurableEmbedding.map_comap`, and the dagger point contributes
nothing because the extension vanishes there. -/
theorem lintegral_comap_inl (ν : ProbabilityMeasure (X ⊕ Unit)) (g : X →ᵇ ℝ≥0) :
    ∫⁻ x, (g x : ℝ≥0∞) ∂((ν : Measure (X ⊕ Unit)).comap Sum.inl)
      = ∫⁻ y, (extendZero g y : ℝ≥0∞) ∂(ν : Measure (X ⊕ Unit)) := by
  have h1 : ∫⁻ x, (g x : ℝ≥0∞) ∂((ν : Measure (X ⊕ Unit)).comap Sum.inl)
      = ∫⁻ y, (extendZero g y : ℝ≥0∞)
          ∂((ν : Measure (X ⊕ Unit)).restrict (Set.range Sum.inl)) := by
    rw [← measurableEmbedding_inl.map_comap]
    exact (measurableEmbedding_inl.lintegral_map
      (fun y => (extendZero g y : ℝ≥0∞))).symm
  have h2 : ∫⁻ y, (extendZero g y : ℝ≥0∞)
      ∂((ν : Measure (X ⊕ Unit)).restrict (Set.range (Sum.inl : X → X ⊕ Unit))ᶜ)
        = 0 := by
    rw [isCompl_range_inl_range_inr.compl_eq, Set.range_unique,
      Measure.restrict_singleton, lintegral_smul_measure,
      lintegral_dirac' _ (extendZero g).measurable_coe_ennreal_comp]
    simp
  conv_rhs => rw [← Measure.restrict_add_restrict_compl
    (μ := (ν : Measure (X ⊕ Unit))) measurableSet_range_inl]
  rw [lintegral_add_measure, h2, add_zero]
  exact h1

/-- The `testAgainstNN` face of `lintegral_promoteMeasure`. -/
theorem testAgainstNN_promoteMeasure (μ : SubProbabilityMeasure X)
    (f : (X ⊕ Unit) →ᵇ ℝ≥0) :
    (promoteMeasure μ).toFiniteMeasure.testAgainstNN f
      = μ.1.testAgainstNN (f.compContinuous ⟨Sum.inl, continuous_inl⟩)
        + (1 - μ.1.mass) * f (Sum.inr ()) := by
  rw [← ENNReal.coe_inj, ENNReal.coe_add, ENNReal.coe_mul,
    FiniteMeasure.testAgainstNN_coe_eq, FiniteMeasure.testAgainstNN_coe_eq,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    lintegral_promoteMeasure, ENNReal.coe_sub, ENNReal.coe_one,
    FiniteMeasure.ennreal_mass]
  congr 1

/-- The `testAgainstNN` face of `lintegral_comap_inl`. -/
theorem testAgainstNN_restrictMeasure (ν : ProbabilityMeasure (X ⊕ Unit))
    (g : X →ᵇ ℝ≥0) :
    (restrictMeasure ν).1.testAgainstNN g
      = ν.toFiniteMeasure.testAgainstNN (extendZero g) := by
  rw [← ENNReal.coe_inj, FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.testAgainstNN_coe_eq, toMeasure_restrictMeasure,
    lintegral_comap_inl, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]

/-! ## Continuity of the chart -/

/-- Promotion is continuous from the (subspace) weak topology into the
weak topology of probability measures on the dagger sum. -/
theorem continuous_promoteMeasure :
    Continuous (promoteMeasure : SubProbabilityMeasure X → ProbabilityMeasure (X ⊕ Unit)) := by
  refine continuous_iff_continuousAt.mpr fun μ₀ => ?_
  refine (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds _).mpr ?_
  rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  simp only [Function.comp_apply,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    lintegral_promoteMeasure]
  refine Filter.Tendsto.add ?_ ?_
  · exact (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp
      (SubProbabilityMeasure.continuous_toFiniteMeasure.tendsto μ₀))
      (f.compContinuous ⟨Sum.inl, continuous_inl⟩)
  · have hcoe : ∀ μ : SubProbabilityMeasure X,
        (1 - ((μ.1 : Measure X) Set.univ)) * (f (Sum.inr ()) : ℝ≥0∞)
          = (((1 - μ.1.mass) * f (Sum.inr ()) : ℝ≥0) : ℝ≥0∞) := by
      intro μ
      rw [ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_one,
        FiniteMeasure.ennreal_mass]
    simp only [hcoe]
    rw [ENNReal.tendsto_coe]
    have hmass : Continuous fun μ : SubProbabilityMeasure X =>
        (1 - μ.1.mass) * f (Sum.inr ()) := by
      refine Continuous.mul ?_ continuous_const
      have hsub : (fun μ : SubProbabilityMeasure X => 1 - μ.1.mass)
          = fun μ => Real.toNNReal (1 - (μ.1.mass : ℝ)) := by
        funext μ
        rw [NNReal.sub_def, NNReal.coe_one]
      rw [hsub]
      exact continuous_real_toNNReal.comp
        (continuous_const.sub (NNReal.continuous_coe.comp
          (FiniteMeasure.continuous_mass.comp continuous_subtype_val)))
    exact hmass.tendsto μ₀

/-- Restriction is continuous from the weak topology of probability
measures on the dagger sum into the (subspace) weak topology of
subprobability measures. -/
theorem continuous_restrictMeasure :
    Continuous (restrictMeasure : ProbabilityMeasure (X ⊕ Unit) → SubProbabilityMeasure X) := by
  have key : Continuous fun ν : ProbabilityMeasure (X ⊕ Unit) =>
      (restrictMeasure ν).1 := by
    refine continuous_iff_continuousAt.mpr fun ν₀ => ?_
    have h : Filter.Tendsto (fun ν : ProbabilityMeasure (X ⊕ Unit) =>
        (restrictMeasure ν).1) (nhds ν₀) (nhds (restrictMeasure ν₀).1) := by
      rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto]
      intro g
      simp only [toMeasure_restrictMeasure, lintegral_comap_inl]
      have h' := (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp
        (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto ν₀)) (extendZero g)
      simpa only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
        using h'
    exact h
  exact key.subtype_mk fun ν => (restrictMeasure ν).2

/-- **The measure-level dagger chart**: subprobability measures on `X`
are homeomorphic to probability measures on the dagger sum `X ⊕ Unit`,
both carrying their weak topologies.  The classical face of the
point-free `SubProb.promoteHomeomorph`. -/
noncomputable def daggerChartMeasure :
    SubProbabilityMeasure X ≃ₜ ProbabilityMeasure (X ⊕ Unit) where
  toFun := promoteMeasure
  invFun := restrictMeasure
  left_inv := restrictMeasure_promoteMeasure
  right_inv := promoteMeasure_restrictMeasure
  continuous_toFun := continuous_promoteMeasure
  continuous_invFun := continuous_restrictMeasure

/-! ## The compactness dividend, by two independent routes -/

/-- **Prokhorov dividend, direct route**: over a compact Hausdorff
Borel space, the subprobability carrier is compact — it is the
mass-at-most-one set of finite measures. -/
instance instCompactSpaceSubProbabilityMeasure [T2Space X] [BorelSpace X]
    [CompactSpace X] : CompactSpace (SubProbabilityMeasure X) := by
  have h := isCompact_setOf_finiteMeasure_le_of_compactSpace X 1
  exact isCompact_iff_compactSpace.mp h

/-- **Prokhorov dividend, chart route**: the same compactness fact,
proved instead by transporting Prokhorov's theorem for probability
measures on the compact dagger sum `X ⊕ Unit` along
`daggerChartMeasure.symm`.  Stated as a theorem rather than an
instance to avoid an instance diamond with the direct route; the two
proofs are deliberately independent (an artifact pair on one fact). -/
theorem compactSpace_of_daggerChartMeasure [T2Space X] [BorelSpace X]
    [CompactSpace X] : CompactSpace (SubProbabilityMeasure X) :=
  (daggerChartMeasure (X := X)).symm.compactSpace

/-! ## Metrizability transfer -/

/-- Over a metrizable separable Borel space, the weak topology on the
subprobability carrier is metrizable: transported along the dagger
chart from the Lévy–Prokhorov metrization of the weak topology on
probability measures over `X ⊕ Unit`. -/
theorem metrizableSpace_subProbabilityMeasure [MetrizableSpace X]
    [SeparableSpace X] [BorelSpace X] :
    MetrizableSpace (SubProbabilityMeasure X) :=
  (daggerChartMeasure (X := X)).isEmbedding.metrizableSpace

end Continuity

end Pointfree
