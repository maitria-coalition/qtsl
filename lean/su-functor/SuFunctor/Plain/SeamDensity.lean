import SuFunctor.Plain.GeneralSeam

/-! # Density completion across the seam

The transport package for evaluation-level claims across the seam
`Joint.toMeas : Joint X → MeasJoint X` — which claims about penalty
functionals, verified on finitely supported joints, extend to all
subprobability Borel joints once the seam is narrowly dense, and which
provably do not.

The package is stated against an explicit density hypothesis
`DenseRange Joint.toMeas`, so each transport theorem is available at
exactly the carriers where density is established; the direct instance
over `ℕ` is proved here (`Joint.denseRange_toMeas_nat`), by truncation,
with no metric-space machinery consumed.

**What transports.**  For a lower semicontinuous penalty — the standing
membership hypothesis of the penalty universe — sublevel conditions are
closed, so upper bounds verified on a dense seam hold everywhere
(`MeasPen.le_of_seam_le`, against any upper semicontinuous majorant),
and suprema are seam-determined (`MeasPen.iSup_seam_eq`).  Narrowly
continuous penalties agreeing on the seam agree everywhere
(`MeasPen.eq_of_seam_eq`).

**What does not.**  Lower bounds and infima of lower semicontinuous
penalties do *not* transport across density: the drop wall
(`dropWall`) — a two-valued penalty vanishing at a single
infinitely-supported joint and infinite elsewhere — is lower
semicontinuous, is bounded below by `1` on the entire seam, and has
infimum `0` on the full carrier (`not_seam_ge_transport`,
`iInf_seam_ne_iInf`).  Since the seam over `ℕ` *is* dense, this is a
semantic boundary of density completion, not a missing hypothesis
(`dense_seam_inf_gap`).

**The rational sub-stratum.**  Finite support does not mean rational
data; that is a further sub-stratum, and its density step is proved
here too: every finitely supported joint is a narrow limit of joints
with (dyadic) rational weights (`Joint.tendsto_toMeas_ratApprox`), so
wherever the seam is dense, the rational-weight seam is already dense
(`Joint.dense_ratSeam`) — kernel checks at exact rational data reach
the full carrier through the two-step chain, for the claim shapes that
transport.

**Finite carriers.**  Over a finite outcome type the seam is onto
(`Joint.toMeas_surjective`): the exact and general strata literally
coincide, which is the precise sense in which the judgment tier's
finite storey is a special case of both.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal NNRat BoundedContinuousFunction

universe u

/-! ## The Lebesgue integral across the seam -/

section Lintegral

variable {X : Type u} [MeasurableSpace X]

/-- The Lebesgue integral against the seam embedding of a finitely
supported joint is the weighted sum of values. -/
theorem Joint.lintegral_toMeas {f : X → ℝ≥0∞} (hf : Measurable f)
    (ν : Joint X) :
    ∫⁻ x, f x ∂((ν.toMeas).1 : Measure X) =
      ν.wt.sum fun i w => (w : ℝ≥0∞) * f i := by
  rw [Joint.toMeas_toMeasure]
  show ∫⁻ x, f x ∂(Joint.measSum ν) = _
  simp only [Joint.measSum, Finsupp.sum]
  rw [lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun i _ => by
    rw [lintegral_smul_measure, lintegral_dirac' i hf, smul_eq_mul]

/-- Finite sums of singleton masses assemble the measure of a finite
set, over any carrier with measurable singletons. -/
theorem sum_measure_singleton {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) (s : Finset X) :
    ∑ x ∈ s, μ {x} = μ (↑s : Set X) := by
  classical
  have hd : (↑s : Set X).PairwiseDisjoint fun x => ({x} : Set X) := by
    intro x _ y _ hxy
    simpa [Set.disjoint_singleton] using hxy
  have h := measure_biUnion_finset (μ := μ) hd
    fun x _ => measurableSet_singleton x
  have hu : ⋃ x ∈ s, ({x} : Set X) = (↑s : Set X) := by
    ext y; simp
  rw [hu] at h
  exact h.symm

/-- A measure on a countable carrier with measurable singletons is the
sum of its singleton masses on every set. -/
theorem measure_eq_tsum_singleton {X : Type u} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (μ : Measure X)
    (s : Set X) : μ s = ∑' x : s, μ {(x : X)} := by
  have hsu : s = ⋃ x : s, {(x : X)} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      rw [Set.mem_singleton_iff.mp hx]
      exact x.2
  conv_lhs => rw [hsu]
  rw [measure_iUnion ?_ fun x => measurableSet_singleton _]
  intro i j hij
  have hne : (i : X) ≠ (j : X) := Subtype.coe_injective.ne hij
  simpa [Function.onFun, Set.disjoint_singleton] using hne

end Lintegral

/-! ## The transport package -/

section Transport

variable {X : Type u} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- Comparison of a lower semicontinuous penalty against an upper
semicontinuous one is a closed condition on joints. -/
theorem isClosed_le_of_lsc_usc {F G : MeasPen X}
    (hF : LowerSemicontinuous F) (hG : UpperSemicontinuous G) :
    IsClosed {μ : MeasJoint X | F μ ≤ G μ} := by
  rw [← isOpen_compl_iff]
  have h : {μ : MeasJoint X | F μ ≤ G μ}ᶜ =
      ⋃ c : ℝ≥0∞, G ⁻¹' Set.Iio c ∩ F ⁻¹' Set.Ioi c := by
    ext μ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    exact ⟨fun hlt => (exists_between hlt).imp fun c hc => ⟨hc.1, hc.2⟩,
      fun ⟨c, h1, h2⟩ => h1.trans h2⟩
  rw [h]
  exact isOpen_iUnion fun c =>
    (hG.isOpen_preimage c).inter (hF.isOpen_preimage c)

/-- **Density completion, the ≤-half**: an upper bound of a lower
semicontinuous penalty by an upper semicontinuous one, verified on the
(dense) seam of finitely supported joints, holds at every
subprobability joint.  Sublevel conditions of lower semicontinuous
penalties are closed, and a closed set containing a dense set is
everything.  The lower-bound dual is *false* — see
`not_seam_ge_transport`. -/
theorem MeasPen.le_of_seam_le
    (hd : DenseRange (Joint.toMeas : Joint X → MeasJoint X))
    {F G : MeasPen X} (hF : LowerSemicontinuous F)
    (hG : UpperSemicontinuous G)
    (h : ∀ ν : Joint X, F ν.toMeas ≤ G ν.toMeas) : F ≤ G := by
  intro μ
  have hsub : Set.range (Joint.toMeas : Joint X → MeasJoint X) ⊆
      {μ : MeasJoint X | F μ ≤ G μ} := by
    rintro _ ⟨ν, rfl⟩
    exact h ν
  have hcl : closure (Set.range (Joint.toMeas : Joint X → MeasJoint X)) ⊆
      {μ : MeasJoint X | F μ ≤ G μ} :=
    (isClosed_le_of_lsc_usc hF hG).closure_subset_iff.mpr hsub
  exact hcl (by rw [hd.closure_range]; exact Set.mem_univ μ)

/-- **Density completion, equalities**: two narrowly continuous
penalties agreeing on the (dense) seam agree everywhere. -/
theorem MeasPen.eq_of_seam_eq
    (hd : DenseRange (Joint.toMeas : Joint X → MeasJoint X))
    {F G : MeasPen X} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ ν : Joint X, F ν.toMeas = G ν.toMeas) : F = G :=
  Continuous.ext_on hd hF hG (by rintro _ ⟨ν, rfl⟩; exact h ν)

/-- **Density completion, suprema**: the supremum of a lower
semicontinuous penalty over all subprobability joints is computed on
the (dense) seam of finitely supported joints.  The infimum dual is
*false* — see `iInf_seam_ne_iInf`. -/
theorem MeasPen.iSup_seam_eq
    (hd : DenseRange (Joint.toMeas : Joint X → MeasJoint X))
    {F : MeasPen X} (hF : LowerSemicontinuous F) :
    ⨆ ν : Joint X, F ν.toMeas = ⨆ μ : MeasJoint X, F μ := by
  refine le_antisymm (iSup_le fun ν => le_iSup F ν.toMeas)
    (iSup_le fun μ => ?_)
  exact MeasPen.le_of_seam_le hd hF upperSemicontinuous_const
    (fun ν => le_iSup (fun ν' : Joint X => F ν'.toMeas) ν) μ

end Transport

/-! ## The rational sub-stratum -/

section Rational

variable {X : Type u} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- A finitely supported joint has rational weights when every weight
is the cast of a nonnegative rational. -/
def Joint.IsRatWeighted (ν : Joint X) : Prop :=
  ∀ x, ∃ q : ℚ≥0, ν.wt x = (q : ℝ≥0)

/-- Dyadic lower approximation of a nonnegative real weight: the
largest multiple of `2⁻ⁿ` at or below `w`. -/
def dyadicApprox (w : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (Nat.floor (w * 2 ^ n) : ℝ≥0) / 2 ^ n

@[simp] theorem dyadicApprox_zero (n : ℕ) : dyadicApprox 0 n = 0 := by
  simp [dyadicApprox]

theorem dyadicApprox_le (w : ℝ≥0) (n : ℕ) : dyadicApprox w n ≤ w := by
  rw [dyadicApprox, div_le_iff₀ (pow_pos two_pos n)]
  exact Nat.floor_le (by positivity)

theorem le_dyadicApprox_add (w : ℝ≥0) (n : ℕ) :
    w ≤ dyadicApprox w n + (2 ^ n)⁻¹ := by
  rw [dyadicApprox, ← one_div, ← add_div,
    le_div_iff₀ (pow_pos two_pos n)]
  exact_mod_cast (Nat.lt_floor_add_one (w * 2 ^ n)).le

theorem tendsto_dyadicApprox (w : ℝ≥0) :
    Tendsto (fun n => dyadicApprox w n) atTop (𝓝 w) := by
  rw [← NNReal.tendsto_coe]
  have h2 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    simp only [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlow : Tendsto (fun n : ℕ => (w : ℝ) - ((2 : ℝ) ^ n)⁻¹) atTop
      (𝓝 (w : ℝ)) := by
    simpa using tendsto_const_nhds.sub h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => ?_) (fun n => ?_)
  · have hc : (w : ℝ) ≤ (dyadicApprox w n : ℝ) + ((2 : ℝ) ^ n)⁻¹ := by
      exact_mod_cast le_dyadicApprox_add w n
    linarith
  · exact_mod_cast dyadicApprox_le w n

/-- The dyadic approximation of a joint: every weight rounded down to a
multiple of `2⁻ⁿ`.  Mass only drops, and every weight becomes
rational. -/
def Joint.ratApprox (ν : Joint X) (n : ℕ) : Joint X where
  wt := ν.wt.mapRange (fun w => dyadicApprox w n) (dyadicApprox_zero n)
  mass_le_one := by
    refine le_trans ?_ ν.mass_le_one
    rw [Finsupp.sum_mapRange_index fun _ => rfl]
    exact Finset.sum_le_sum fun i _ => dyadicApprox_le (ν.wt i) n

omit [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem Joint.isRatWeighted_ratApprox (ν : Joint X) (n : ℕ) :
    (ν.ratApprox n).IsRatWeighted := by
  intro x
  refine ⟨NNRat.divNat (Nat.floor (ν.wt x * 2 ^ n)) (2 ^ n), ?_⟩
  have hwt : (ν.ratApprox n).wt =
      ν.wt.mapRange (fun w => dyadicApprox w n) (dyadicApprox_zero n) := rfl
  rw [hwt, Finsupp.mapRange_apply, dyadicApprox, NNRat.cast_divNat]
  norm_cast

/-- Weights converge, so the seam embeddings converge narrowly: every
seam point is a narrow limit of rational-weight seam points. -/
theorem Joint.tendsto_toMeas_ratApprox (ν : Joint X) :
    Tendsto (fun n => (ν.ratApprox n).toMeas) atTop (𝓝 ν.toMeas) := by
  have key : ∀ f : X →ᵇ ℝ≥0,
      Tendsto (fun n =>
          ∫⁻ x, (f x : ℝ≥0∞) ∂(((ν.ratApprox n).toMeas).1 : Measure X))
        atTop (𝓝 (∫⁻ x, (f x : ℝ≥0∞) ∂((ν.toMeas).1 : Measure X))) := by
    intro f
    have hf : Measurable fun x => (f x : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp f.continuous).measurable
    simp only [Joint.lintegral_toMeas hf]
    have hsum : ∀ n,
        ((ν.ratApprox n).wt).sum (fun i w => (w : ℝ≥0∞) * f i) =
          ∑ i ∈ ν.wt.support,
            ((dyadicApprox (ν.wt i) n : ℝ≥0∞) * f i) := by
      intro n
      have hwt : (ν.ratApprox n).wt =
          ν.wt.mapRange (fun w => dyadicApprox w n) (dyadicApprox_zero n) :=
        rfl
      rw [hwt, Finsupp.sum_mapRange_index (by simp)]
      rfl
    have htgt : ν.wt.sum (fun i w => (w : ℝ≥0∞) * f i) =
        ∑ i ∈ ν.wt.support, ((ν.wt i : ℝ≥0∞) * f i) := rfl
    simp only [hsum, htgt]
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_coe.mpr (tendsto_dyadicApprox (ν.wt i)))
      (Or.inr ENNReal.coe_ne_top)
  have hFM : Tendsto (fun n => ((ν.ratApprox n).toMeas).1) atTop
      (𝓝 ((ν.toMeas).1)) :=
    FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr key
  exact IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hFM

theorem Joint.toMeas_mem_closure_ratSeam (ν : Joint X) :
    ν.toMeas ∈
      closure (Joint.toMeas '' {ν' : Joint X | ν'.IsRatWeighted}) :=
  mem_closure_of_tendsto (Joint.tendsto_toMeas_ratApprox ν)
    (Eventually.of_forall fun n =>
      Set.mem_image_of_mem _ (Joint.isRatWeighted_ratApprox ν n))

/-- **The rational two-step**: wherever the seam of finitely supported
joints is dense, the seam of *rational-weight* finitely supported
joints is already dense.  Kernel checks at exact rational data reach
the full subprobability carrier through this chain, for every claim
shape of the transport package. -/
theorem Joint.dense_ratSeam
    (hd : DenseRange (Joint.toMeas : Joint X → MeasJoint X)) :
    Dense (Joint.toMeas '' {ν : Joint X | ν.IsRatWeighted}) := by
  intro μ
  have h1 : Set.range (Joint.toMeas : Joint X → MeasJoint X) ⊆
      closure (Joint.toMeas '' {ν : Joint X | ν.IsRatWeighted}) := by
    rintro _ ⟨ν, rfl⟩
    exact Joint.toMeas_mem_closure_ratSeam ν
  have h2 := closure_mono h1
  rw [hd.closure_range, closure_closure] at h2
  exact h2 (Set.mem_univ μ)

end Rational

/-! ## Finite carriers: the strata coincide -/

/-- Measures on a countable carrier with measurable singletons are
determined by their singleton masses. -/
theorem measure_ext_of_singleton {X : Type u} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {μ ν : Measure X}
    (h : ∀ x, μ {x} = ν {x}) : μ = ν :=
  Measure.ext fun s _ => by
    rw [measure_eq_tsum_singleton μ s, measure_eq_tsum_singleton ν s]
    exact tsum_congr fun x => h x

section FiniteCarrier

variable {X : Type u} [MeasurableSpace X] [Finite X]
  [MeasurableSingletonClass X]

/-- Over a finite outcome carrier the seam embedding is onto: every
subprobability Borel joint is finitely supported, so the exact and
general strata literally coincide (with `Joint.toMeas_injective`, the
embedding is a bijection there). -/
theorem Joint.toMeas_surjective :
    Function.Surjective (Joint.toMeas : Joint X → MeasJoint X) := by
  classical
  cases nonempty_fintype X
  intro μ
  have hfin : ∀ x : X, (μ.1 : Measure X) {x} ≠ ∞ :=
    fun x => measure_ne_top _ _
  set w : X →₀ ℝ≥0 :=
    Finsupp.equivFunOnFinite.symm fun x => ((μ.1 : Measure X) {x}).toNNReal
    with hw
  have hwval : ∀ x : X, ((w x : ℝ≥0) : ℝ≥0∞) = (μ.1 : Measure X) {x} := by
    intro x
    rw [hw]
    show ((((μ.1 : Measure X) {x}).toNNReal : ℝ≥0∞)) = _
    exact ENNReal.coe_toNNReal (hfin x)
  have hmass : w.sum (fun _ v => v) ≤ 1 := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl,
      ← ENNReal.coe_le_coe, ENNReal.coe_one, ENNReal.ofNNReal_finsetSum]
    calc ∑ x : X, ((w x : ℝ≥0) : ℝ≥0∞)
        = ∑ x : X, (μ.1 : Measure X) {x} :=
          Finset.sum_congr rfl fun x _ => hwval x
      _ = (μ.1 : Measure X) (↑(Finset.univ : Finset X) : Set X) :=
          sum_measure_singleton _ _
      _ ≤ 1 := by
          rw [Finset.coe_univ, ← FiniteMeasure.ennreal_mass]
          exact_mod_cast μ.2
  refine ⟨⟨w, hmass⟩, ?_⟩
  refine MeasJoint.ext' (measure_ext_of_singleton fun x => ?_)
  rw [Joint.toMeas_singleton]
  exact hwval x

end FiniteCarrier

/-! ## The direct density instance over `ℕ` -/

section NatDensity

/-- Truncation of a subprobability joint over `ℕ` to its first `N`
outcomes, as a finitely supported joint.  Mass only drops. -/
def MeasJoint.truncNat (μ : MeasJoint ℕ) (N : ℕ) : Joint ℕ where
  wt := Finsupp.onFinset (Finset.range N)
    (fun n => if n < N then ((μ.1 : Measure ℕ) {n}).toNNReal else 0)
    (fun n hn => by
      rw [Finset.mem_range]
      by_contra h
      exact hn (if_neg h))
  mass_le_one := by
    classical
    rw [Finsupp.onFinset_sum _ fun _ => rfl,
      ← ENNReal.coe_le_coe, ENNReal.coe_one, ENNReal.ofNNReal_finsetSum]
    calc ∑ n ∈ Finset.range N,
          ((if n < N then ((μ.1 : Measure ℕ) {n}).toNNReal else 0 : ℝ≥0) :
            ℝ≥0∞)
        = ∑ n ∈ Finset.range N, (μ.1 : Measure ℕ) {n} := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [if_pos (Finset.mem_range.mp hn)]
          exact ENNReal.coe_toNNReal (measure_ne_top _ _)
      _ = (μ.1 : Measure ℕ) (↑(Finset.range N) : Set ℕ) :=
          sum_measure_singleton _ _
      _ ≤ (μ.1 : Measure ℕ) Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := by
          rw [← FiniteMeasure.ennreal_mass]
          exact_mod_cast μ.2

theorem MeasJoint.truncNat_wt_of_lt (μ : MeasJoint ℕ) {N n : ℕ}
    (h : n < N) :
    (μ.truncNat N).wt n = ((μ.1 : Measure ℕ) {n}).toNNReal := if_pos h

theorem MeasJoint.truncNat_wt_of_le (μ : MeasJoint ℕ) {N n : ℕ}
    (h : N ≤ n) : (μ.truncNat N).wt n = 0 := if_neg (Nat.not_lt.mpr h)

/-- The truncations converge narrowly: over `ℕ`, the tail mass of the
singleton decomposition vanishes, so every bounded continuous pairing
converges by partial sums. -/
theorem MeasJoint.tendsto_truncNat (μ : MeasJoint ℕ) :
    Tendsto (fun N => (μ.truncNat N).toMeas) atTop (𝓝 μ) := by
  have key : ∀ f : ℕ →ᵇ ℝ≥0,
      Tendsto (fun N =>
          ∫⁻ n, (f n : ℝ≥0∞) ∂(((μ.truncNat N).toMeas).1 : Measure ℕ))
        atTop (𝓝 (∫⁻ n, (f n : ℝ≥0∞) ∂((μ.1 : Measure ℕ)))) := by
    intro f
    have hN : ∀ N,
        ∫⁻ n, (f n : ℝ≥0∞) ∂(((μ.truncNat N).toMeas).1 : Measure ℕ) =
          ∑ n ∈ Finset.range N, (f n : ℝ≥0∞) * (μ.1 : Measure ℕ) {n} := by
      intro N
      rw [lintegral_countable' fun n => (f n : ℝ≥0∞)]
      rw [tsum_eq_sum (s := Finset.range N) fun n hn => by
        rw [Joint.toMeas_singleton,
          μ.truncNat_wt_of_le (Nat.not_lt.mp fun h => hn
            (Finset.mem_range.mpr h)), ENNReal.coe_zero, mul_zero]]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Joint.toMeas_singleton,
        μ.truncNat_wt_of_lt (Finset.mem_range.mp hn),
        ENNReal.coe_toNNReal (measure_ne_top _ _)]
    have htgt : ∫⁻ n, (f n : ℝ≥0∞) ∂((μ.1 : Measure ℕ)) =
        ∑' n, (f n : ℝ≥0∞) * (μ.1 : Measure ℕ) {n} :=
      lintegral_countable' fun n => (f n : ℝ≥0∞)
    simp only [hN, htgt]
    exact ENNReal.tendsto_nat_tsum _
  have hFM : Tendsto (fun N => ((μ.truncNat N).toMeas).1) atTop
      (𝓝 (μ.1)) :=
    FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr key
  exact IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hFM

/-- **Density over `ℕ`, directly**: finitely supported joints are
narrowly dense among subprobability joints over `ℕ` — the truncation
instance of the density-completion theorem, with no metric-space
machinery consumed.  (Also the ground-truth instance for the pins
below: the transport obstructions live at a carrier where density
*holds*.) -/
theorem Joint.denseRange_toMeas_nat :
    DenseRange (Joint.toMeas : Joint ℕ → MeasJoint ℕ) := fun μ =>
  mem_closure_of_tendsto (MeasJoint.tendsto_truncNat μ)
    (Eventually.of_forall fun N => Set.mem_range_self (μ.truncNat N))

end NatDensity

/-! ## The pins: what density cannot complete -/

section Pins

open Classical in
/-- The geometric measure on `ℕ`: mass `2⁻⁽ⁿ⁺¹⁾` at each `n`. -/
def geometricMeasure : Measure ℕ :=
  Measure.sum fun n => ((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) • Measure.dirac n

theorem geometricMeasure_singleton (m : ℕ) :
    geometricMeasure {m} = (2 : ℝ≥0∞)⁻¹ ^ (m + 1) := by
  rw [geometricMeasure, Measure.sum_apply _ (measurableSet_singleton m)]
  have hvanish : ∀ n, n ≠ m →
      (((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) • Measure.dirac n) {m} = 0 := by
    intro n hnm
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' n (measurableSet_singleton m),
      Set.indicator_of_notMem (by simpa using hnm), mul_zero]
  rw [tsum_eq_single m hvanish, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' m (measurableSet_singleton m),
    Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl), Pi.one_apply,
    mul_one]

theorem geometricMeasure_univ : geometricMeasure Set.univ = 1 := by
  rw [geometricMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ n : ℕ,
      (((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) • Measure.dirac n) Set.univ =
        (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    intro n
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' n MeasurableSet.univ,
      Set.indicator_of_mem (Set.mem_univ n), Pi.one_apply, mul_one]
  rw [tsum_congr h, ENNReal.tsum_geometric_add_one,
    ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

instance : IsFiniteMeasure geometricMeasure :=
  ⟨by rw [geometricMeasure_univ]; exact ENNReal.one_lt_top⟩

/-- The geometric joint: total mass one, every singleton charged — a
subprobability joint over `ℕ` that is not finitely supported. -/
def geometricMeasJoint : MeasJoint ℕ :=
  ⟨⟨geometricMeasure, inferInstance⟩, by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, ENNReal.coe_one]
    show geometricMeasure Set.univ ≤ 1
    rw [geometricMeasure_univ]⟩

theorem geometricMeasJoint_singleton (m : ℕ) :
    (geometricMeasJoint.1 : Measure ℕ) {m} = (2 : ℝ≥0∞)⁻¹ ^ (m + 1) :=
  geometricMeasure_singleton m

/-- No finitely supported joint reaches the geometric joint: evaluate
at any point outside the finite support. -/
theorem Joint.toMeas_ne_geometric (ν : Joint ℕ) :
    ν.toMeas ≠ geometricMeasJoint := by
  intro h
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset ν.wt.support
  have h1 : ((ν.toMeas).1 : Measure ℕ) {m} = 0 := by
    rw [Joint.toMeas_singleton, Finsupp.notMem_support_iff.mp hm,
      ENNReal.coe_zero]
  rw [h, geometricMeasJoint_singleton] at h1
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) h1

/-- The singleton indicator, as a bounded continuous test function on
the discrete carrier `ℕ`. -/
def natIndicator (n : ℕ) : ℕ →ᵇ ℝ≥0 :=
  ⟨⟨fun m => if m = n then 1 else 0, continuous_of_discreteTopology⟩, 1,
    fun x y => by
      dsimp only [ContinuousMap.coe_mk]
      have h01 : ∀ a b : ℝ≥0, a ≤ 1 → b ≤ 1 → dist a b ≤ 1 := by
        intro a b ha hb
        have ha' : (a : ℝ) ≤ 1 := by exact_mod_cast ha
        have hb' : (b : ℝ) ≤ 1 := by exact_mod_cast hb
        rw [NNReal.dist_eq, abs_le]
        constructor
        · linarith [NNReal.coe_nonneg a]
        · linarith [NNReal.coe_nonneg b]
      exact h01 _ _ (by split_ifs <;> simp) (by split_ifs <;> simp)⟩

theorem testAgainstNN_natIndicator (μ : FiniteMeasure ℕ) (n : ℕ) :
    μ.testAgainstNN (natIndicator n) = ((μ : Measure ℕ) {n}).toNNReal := by
  have hvanish : ∀ m, m ≠ n →
      ((natIndicator n) m : ℝ≥0∞) * (μ : Measure ℕ) {m} = 0 := by
    intro m hmn
    show ((if m = n then (1 : ℝ≥0) else 0 : ℝ≥0) : ℝ≥0∞) * _ = 0
    rw [if_neg hmn, ENNReal.coe_zero, zero_mul]
  have hint : ∫⁻ m, ((natIndicator n) m : ℝ≥0∞) ∂(μ : Measure ℕ) =
      (μ : Measure ℕ) {n} := by
    rw [lintegral_countable' fun m => ((natIndicator n) m : ℝ≥0∞),
      tsum_eq_single n hvanish]
    show ((if n = n then (1 : ℝ≥0) else 0 : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [if_pos rfl, ENNReal.coe_one, one_mul]
  show (∫⁻ m, ((natIndicator n) m : ℝ≥0∞) ∂(μ : Measure ℕ)).toNNReal = _
  rw [hint]

/-- The geometric joint is a closed point of the subprobability
carrier: the singleton evaluations are narrowly continuous and jointly
separating. -/
theorem isClosed_singleton_geometricMeasJoint :
    IsClosed ({geometricMeasJoint} : Set (MeasJoint ℕ)) := by
  have hset : ({geometricMeasJoint} : Set (MeasJoint ℕ)) =
      ⋂ n : ℕ, {μ : MeasJoint ℕ |
        μ.1.testAgainstNN (natIndicator n) =
          geometricMeasJoint.1.testAgainstNN (natIndicator n)} := by
    apply Set.Subset.antisymm
    · rintro μ hμ
      rw [Set.mem_singleton_iff.mp hμ]
      exact Set.mem_iInter.mpr fun n => rfl
    · intro μ hμ
      rw [Set.mem_singleton_iff]
      refine MeasJoint.ext' (measure_ext_of_singleton fun n => ?_)
      have h := Set.mem_iInter.mp hμ n
      rw [Set.mem_setOf_eq, testAgainstNN_natIndicator,
        testAgainstNN_natIndicator] at h
      have h1 : (μ.1 : Measure ℕ) {n} ≠ ∞ := measure_ne_top _ _
      have h2 : (geometricMeasJoint.1 : Measure ℕ) {n} ≠ ∞ :=
        measure_ne_top _ _
      rw [← ENNReal.coe_toNNReal h1, ← ENNReal.coe_toNNReal h2, h]
  rw [hset]
  exact isClosed_iInter fun n =>
    isClosed_eq
      ((FiniteMeasure.continuous_testAgainstNN_eval (natIndicator n)).comp
        continuous_toFiniteMeasure)
      continuous_const

open Classical in
/-- **The drop wall**: a two-valued penalty vanishing at the geometric
joint and infinite elsewhere.  Lower semicontinuous — its only proper
sublevel set is a closed singleton — so a citizen of the penalty
universe's standing membership class. -/
def dropWall : MeasPen ℕ :=
  fun μ => if μ = geometricMeasJoint then 0 else ⊤

theorem dropWall_geometric : dropWall geometricMeasJoint = 0 := if_pos rfl

theorem dropWall_of_ne {μ : MeasJoint ℕ} (h : μ ≠ geometricMeasJoint) :
    dropWall μ = ⊤ := if_neg h

theorem lowerSemicontinuous_dropWall : LowerSemicontinuous dropWall := by
  intro μ y hy
  by_cases hμ : μ = geometricMeasJoint
  · rw [hμ, dropWall_geometric] at hy
    exact absurd hy (by simp)
  · have hopen : IsOpen ({geometricMeasJoint}ᶜ : Set (MeasJoint ℕ)) :=
      isClosed_singleton_geometricMeasJoint.isOpen_compl
    filter_upwards [hopen.mem_nhds hμ] with ν hν
    rw [dropWall_of_ne hν]
    rw [dropWall_of_ne hμ] at hy
    exact hy

/-- On the entire seam the drop wall is maximal. -/
theorem one_le_dropWall_seam (ν : Joint ℕ) : 1 ≤ dropWall ν.toMeas := by
  rw [dropWall_of_ne (Joint.toMeas_ne_geometric ν)]
  exact le_top

/-- **The ≥-half refutation**: lower bounds of lower semicontinuous
penalties do *not* transport across the dense seam — the dual of
`MeasPen.le_of_seam_le` is false, as a kernel-checked counterexample,
not an undischarged goal. -/
theorem not_seam_ge_transport :
    ¬ ∀ F : MeasPen ℕ, LowerSemicontinuous F →
        (∀ ν : Joint ℕ, 1 ≤ F ν.toMeas) → ∀ μ : MeasJoint ℕ, 1 ≤ F μ := by
  intro h
  have h0 := h dropWall lowerSemicontinuous_dropWall one_le_dropWall_seam
    geometricMeasJoint
  rw [dropWall_geometric] at h0
  exact absurd h0 (by simp)

/-- **Infima are not seam-determined**: the dual of
`MeasPen.iSup_seam_eq` is false. -/
theorem iInf_seam_ne_iInf :
    (⨅ ν : Joint ℕ, dropWall ν.toMeas) ≠ ⨅ μ : MeasJoint ℕ, dropWall μ := by
  have hL : (⨅ ν : Joint ℕ, dropWall ν.toMeas) = ⊤ :=
    iInf_eq_top.mpr fun ν => dropWall_of_ne (Joint.toMeas_ne_geometric ν)
  have hR : (⨅ μ : MeasJoint ℕ, dropWall μ) = 0 :=
    le_antisymm
      (le_of_le_of_eq (iInf_le _ geometricMeasJoint) dropWall_geometric)
      bot_le
  rw [hL, hR]
  simp

/-- The pins, bundled with the density instance: over `ℕ` the seam
*is* dense, and the lower-bound/infimum transport still fails — the
failure is a semantic boundary of density completion, not a missing
hypothesis. -/
theorem dense_seam_inf_gap :
    DenseRange (Joint.toMeas : Joint ℕ → MeasJoint ℕ) ∧
      ∃ F : MeasPen ℕ, LowerSemicontinuous F ∧
        (∀ ν : Joint ℕ, 1 ≤ F ν.toMeas) ∧
        (⨅ ν : Joint ℕ, F ν.toMeas) ≠ ⨅ μ : MeasJoint ℕ, F μ :=
  ⟨Joint.denseRange_toMeas_nat,
    dropWall, lowerSemicontinuous_dropWall, one_le_dropWall_seam,
    iInf_seam_ne_iInf⟩

end Pins

end

end Plain

end SuFunctor
