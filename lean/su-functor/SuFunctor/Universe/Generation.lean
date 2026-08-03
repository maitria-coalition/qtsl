import SuFunctor.Universe.CoupledJudgment

/-! # The generation theorem: rational threshold rows see the whole flat universe

Every lsc penalty on the flat carrier is the pointwise supremum of its
**box-row** minorants — scaled indicators of open boxes with rational
corners and rational heights.  A box row is a finite min of
single-coordinate **threshold rows** (`boxRow_eq_inf`), and the index
family of all candidate rows is countable
(`generation_index_countable`); so, in one sentence:

> every citizen of the flat universe is a countable sup of finite mins
> of single-row atoms with rational data.

Polarity lives on rows: each threshold atom is monotone or antitone in
exactly one coordinate, and the citizen assembled from them need be
neither.  Sums are never needed for generation — `{min, sup}` alone
suffice — so additive presentations are certificate-side convenience,
not ontology.

The proof is the layer-cake construction: below any rational height
under `f` at `μ`, lower semicontinuity yields a metric ball on which
`f` stays above the height; a rational box fits inside the ball around
`μ` (density of `ℚ`), and the height-scaled indicator of that box is a
minorant of `f` attaining the height at `μ`.  Compare
`iSup_tents_eq_self`, the same statement for the subprobability
carrier with degree-2 gambles as the generators: there the generators
are smooth and menu-indexed by real data; here they are crisp rows
with rational data — the certificate normal form. -/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-! ## Threshold atoms and box rows -/

/-- The upward threshold row: height `c` where coordinate `v` exceeds
the rational threshold `a`, and `0` elsewhere.  Monotone in the `v`
mass; the safety-polarity atom orientation. -/
noncomputable def thresholdRowGt (c : ℝ≥0∞) (v : V) (a : ℚ) :
    ProbPenalty V :=
  scaledIndicator c {μ | (a : ℝ) < (μ : V → ℝ) v}

/-- The downward threshold row: height `c` where coordinate `v` is
below the rational threshold `b`.  Antitone in the `v` mass; the
liveness-polarity atom orientation. -/
noncomputable def thresholdRowLt (c : ℝ≥0∞) (v : V) (b : ℚ) :
    ProbPenalty V :=
  scaledIndicator c {μ | (μ : V → ℝ) v < (b : ℝ)}

theorem lowerSemicontinuous_thresholdRowGt (c : ℝ≥0∞) (v : V) (a : ℚ) :
    LowerSemicontinuous (thresholdRowGt c v a) :=
  lowerSemicontinuous_scaledIndicator
    (IsOpen.preimage ((continuous_apply v).comp continuous_subtype_val)
      isOpen_Ioi)

theorem lowerSemicontinuous_thresholdRowLt (c : ℝ≥0∞) (v : V) (b : ℚ) :
    LowerSemicontinuous (thresholdRowLt c v b) :=
  lowerSemicontinuous_scaledIndicator
    (IsOpen.preimage ((continuous_apply v).comp continuous_subtype_val)
      isOpen_Iio)

/-- The open box with rational corners `l, u`, as a set of
distributions. -/
def ratBox (l u : V → ℚ) : Set (ProbState V) :=
  {μ | ∀ v, (l v : ℝ) < (μ : V → ℝ) v ∧ (μ : V → ℝ) v < (u v : ℝ)}

theorem isOpen_ratBox (l u : V → ℚ) : IsOpen (ratBox (V := V) l u) := by
  have : ratBox (V := V) l u
      = ⋂ v, ({μ : ProbState V | (l v : ℝ) < (μ : V → ℝ) v}
          ∩ {μ : ProbState V | (μ : V → ℝ) v < (u v : ℝ)}) := by
    ext μ
    simp [ratBox, forall_and]
  rw [this]
  refine isOpen_iInter_of_finite fun v => IsOpen.inter ?_ ?_
  · exact IsOpen.preimage ((continuous_apply v).comp continuous_subtype_val)
      isOpen_Ioi
  · exact IsOpen.preimage ((continuous_apply v).comp continuous_subtype_val)
      isOpen_Iio

/-- The box row: the rational height `q` on the rational open box, `0`
off it. -/
noncomputable def boxRow (q : ℚ) (l u : V → ℚ) : ProbPenalty V :=
  scaledIndicator (ENNReal.ofReal q) (ratBox l u)

theorem lowerSemicontinuous_boxRow (q : ℚ) (l u : V → ℚ) :
    LowerSemicontinuous (boxRow (V := V) q l u) :=
  lowerSemicontinuous_scaledIndicator (isOpen_ratBox l u)

/-- Scaled indicators turn intersections into pointwise mins. -/
theorem scaledIndicator_inter (c : ℝ≥0∞) (S T : Set (ProbState V)) :
    scaledIndicator c (S ∩ T)
      = scaledIndicator c S ⊓ scaledIndicator c T := by
  funext μ
  by_cases hS : μ ∈ S <;> by_cases hT : μ ∈ T <;>
    simp [scaledIndicator, hS, hT]

/-- **A box row is a finite min of threshold atoms**: one upward and
one downward row per coordinate. -/
theorem boxRow_eq_inf [Nonempty V] (q : ℚ) (l u : V → ℚ) :
    boxRow (V := V) q l u
      = Finset.univ.inf fun v =>
          thresholdRowGt (ENNReal.ofReal q) v (l v)
            ⊓ thresholdRowLt (ENNReal.ofReal q) v (u v) := by
  funext μ
  rw [Finset.inf_apply]
  by_cases hμ : μ ∈ ratBox (V := V) l u
  · rw [boxRow, scaledIndicator_apply_of_mem hμ]
    have hterm : ∀ v ∈ Finset.univ,
        (thresholdRowGt (ENNReal.ofReal q) v (l v)
          ⊓ thresholdRowLt (ENNReal.ofReal q) v (u v)) μ
          = ENNReal.ofReal q := by
      intro v _
      rw [Pi.inf_apply, thresholdRowGt, thresholdRowLt,
        scaledIndicator_apply_of_mem (hμ v).1,
        scaledIndicator_apply_of_mem (hμ v).2, inf_idem]
    rw [Finset.inf_congr rfl hterm, Finset.inf_const Finset.univ_nonempty]
  · rw [boxRow, scaledIndicator_apply_of_not_mem hμ]
    simp only [ratBox, Set.mem_setOf_eq, not_forall] at hμ
    obtain ⟨v₀, hv₀⟩ := hμ
    refine le_antisymm zero_le ?_
    refine le_trans (Finset.inf_le (Finset.mem_univ v₀)) ?_
    rw [Pi.inf_apply, thresholdRowGt, thresholdRowLt]
    rcases not_and_or.mp hv₀ with h | h
    · have h' : μ ∉ {μ : ProbState V | (l v₀ : ℝ) < (μ : V → ℝ) v₀} := h
      rw [scaledIndicator_apply_of_not_mem h']
      exact inf_le_left
    · have h' : μ ∉ {μ : ProbState V | (μ : V → ℝ) v₀ < (u v₀ : ℝ)} := h
      rw [scaledIndicator_apply_of_not_mem h']
      exact inf_le_right

/-- The generating family is indexed by countable data: rational
heights and rational box corners. -/
theorem generation_index_countable :
    Countable (ℚ × (V → ℚ) × (V → ℚ)) :=
  inferInstance

/-! ## The generation theorem -/

/-- **The generation theorem.**  Every lsc penalty on the flat carrier
is the pointwise supremum of its box-row minorants — hence a countable
sup of finite mins of rational threshold atoms
(`boxRow_eq_inf`, `generation_index_countable`). -/
theorem iSup_boxRows_eq_self {f : ProbPenalty V}
    (hf : LowerSemicontinuous f) :
    ⨆ (q : ℚ) (l : V → ℚ) (u : V → ℚ) (_ : 0 < q)
        (_ : ∀ ν, boxRow q l u ν ≤ f ν), boxRow q l u = f := by
  apply le_antisymm
  · exact iSup_le fun q => iSup_le fun l => iSup_le fun u =>
      iSup_le fun _ => iSup_le fun hmin => fun ν => hmin ν
  · intro μ
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt'
    have hcoe : ((Real.toNNReal (q : ℝ)) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := rfl
    rw [hcoe] at h1 h2
    have hq0 : 0 < q := by
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal q := zero_le.trans_lt h1
      exact_mod_cast ENNReal.ofReal_pos.mp hpos
    -- lower semicontinuity: a ball on which `f` stays above the height
    have hev : ∀ᶠ ν in nhds μ, ENNReal.ofReal q < f ν := hf μ _ h2
    obtain ⟨δ, hδ0, hball⟩ := Metric.eventually_nhds_iff.mp hev
    -- a rational box around `μ` inside the ball
    have hlex : ∀ v : V, ∃ lq : ℚ,
        (μ : V → ℝ) v - δ < (lq : ℝ) ∧ (lq : ℝ) < (μ : V → ℝ) v :=
      fun v => exists_rat_btwn (by linarith)
    have huex : ∀ v : V, ∃ uq : ℚ,
        (μ : V → ℝ) v < (uq : ℝ) ∧ (uq : ℝ) < (μ : V → ℝ) v + δ :=
      fun v => exists_rat_btwn (by linarith)
    choose l hl₁ hl₂ using hlex
    choose u hu₁ hu₂ using huex
    have hμbox : μ ∈ ratBox (V := V) l u := fun v => ⟨hl₂ v, hu₁ v⟩
    have hboxball : ∀ ν : ProbState V, ν ∈ ratBox (V := V) l u →
        dist ν μ < δ := by
      intro ν hν
      rw [Subtype.dist_eq, dist_pi_lt_iff hδ0]
      intro v
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor
      · have h₁ := (hν v).2
        have h₂ := hu₂ v
        linarith
      · have h₁ := (hν v).1
        have h₂ := hl₁ v
        linarith
    -- the box row is a minorant of `f`
    have hmin : ∀ ν, boxRow q l u ν ≤ f ν := by
      intro ν
      by_cases hν : ν ∈ ratBox (V := V) l u
      · rw [boxRow, scaledIndicator_apply_of_mem hν]
        exact (hball (hboxball ν hν)).le
      · rw [boxRow, scaledIndicator_apply_of_not_mem hν]
        exact zero_le
    -- the box row attains the height at `μ`, beating the supremum
    have happ : boxRow q l u μ = ENNReal.ofReal q := by
      rw [boxRow, scaledIndicator_apply_of_mem hμbox]
    have hle : boxRow q l u
        ≤ ⨆ (q : ℚ) (l : V → ℚ) (u : V → ℚ) (_ : 0 < q)
            (_ : ∀ ν, boxRow q l u ν ≤ f ν), boxRow q l u := by
      refine le_iSup_of_le q ?_
      refine le_iSup_of_le l ?_
      refine le_iSup_of_le u ?_
      refine le_iSup_of_le hq0 ?_
      exact le_iSup_of_le hmin le_rfl
    have hcontra : ENNReal.ofReal q
        ≤ (⨆ (q : ℚ) (l : V → ℚ) (u : V → ℚ) (_ : 0 < q)
            (_ : ∀ ν, boxRow q l u ν ≤ f ν), boxRow q l u) μ := by
      calc ENNReal.ofReal q = boxRow q l u μ := happ.symm
        _ ≤ _ := hle μ
    exact absurd (lt_of_le_of_lt hcontra h1) (lt_irrefl _)

end SuFunctor.Universe
