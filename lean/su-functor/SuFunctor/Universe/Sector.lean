import SuFunctor.Universe.ImageChar

/-! # The sector lemma: the ∃-face generates the lower Vietoris on radial sets

The escape faces of the judgment — the classes `Hit((compile v)ᶜ)` for
citizens `v` — are a *sub-family* of the lower-Vietoris sub-basis
(hit-classes of arbitrary opens).  This module proves they generate
the same topology on the radial locus (`generateFrom_sectorHit_eq_openHit`).

* **Sectors are the complements of scaled-indicator bodies**
  (`notMem_compile_scaledIndicator_iff`): the body of `c·𝟙_B` is
  missed exactly by the points over `B` scaled past `grade c` — an
  open sector of directions `B` above a threshold.
* **The interpolation** (`exists_sector_of_hit`): a radial set hitting
  an open region `W` away from the origin hits some sector whose
  every *radial* hitter also hits `W`.  The proof pins a **band**
  `{γ·μ : μ near μ₀, |γ − γ₀| small} ⊆ W` around the witness
  `x = γ₀·μ₀` and descends: a radial set protruding past the sector
  threshold owns, by ray-down-closure, a point *inside the band* —
  radiality is load-bearing here, not only in the origin case.  (The
  uncapped sector itself never fits inside a small `W`: it reaches the
  full-mass tips over `B`.  Only its trace on each descending ray
  does, and that is exactly what radial sets see.)
* **The origin case** (`hit_of_zero_mem`): a hit-class through the
  origin traps every radial body, so it is the whole subspace and
  needs no generator.  This is a genuine delta between the radial
  locus and the full hyperspace: no sector contains the origin, so on
  the full hyperspace the sector family could never produce these
  classes.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

variable {V : Type*} [Fintype V]

/-! ## Sectors as complements of scaled-indicator bodies -/

/-- Missing the body of a scaled indicator is exactly: living over the
plateau, scaled past the plateau's grade.  The polar description of
the open sector. -/
theorem notMem_compile_scaledIndicator_iff [Nonempty V] {c : ℝ≥0∞}
    {B : Set (ProbState V)} {x : BelState V} :
    x ∉ compile (scaledIndicator c B)
      ↔ ∃ (μ : ProbState V) (γ : ℝ), 0 < γ ∧ γ ≤ 1 ∧ μ ∈ B
          ∧ grade c < γ ∧ (x : V → ℝ) = γ • (μ : V → ℝ) := by
  constructor
  · intro hx
    rcases BelState.exists_polar x with hx0 | ⟨μ, m, hm0, hm1, hxe⟩
    · exfalso
      obtain ⟨ν⟩ := (inferInstance : Nonempty (ProbState V))
      exact hx ⟨ν, 0, le_rfl, grade_nonneg _, by rw [hx0, zero_smul]⟩
    · have hμB : μ ∈ B := by
        by_contra hμB
        refine hx ⟨μ, m, hm0.le, ?_, hxe⟩
        rw [scaledIndicator_apply_of_not_mem hμB, grade_zero]
        exact hm1
      have hgc : grade c < m := by
        by_contra hle
        exact hx ⟨μ, m, hm0.le, by
          rw [scaledIndicator_apply_of_mem hμB]
          exact not_lt.mp hle, hxe⟩
      exact ⟨μ, m, hm0, hm1, hμB, hgc, hxe⟩
  · rintro ⟨μ, γ, hγ0, -, hμB, hgc, hxe⟩ hx
    have hb := compile_scale_le hx hγ0 hxe
    rw [scaledIndicator_apply_of_mem hμB] at hb
    exact absurd hb (not_le.mpr hgc)

/-! ## The band estimate -/

/-- Scaled points move by at most the direction distance plus the
scale distance, when the first scale is bounded by one. -/
theorem dist_smul_le_of_abs_le_one {γ γ' : ℝ} (hγ : |γ| ≤ 1)
    (μ μ' : ProbState V) :
    dist (γ • (μ : V → ℝ)) (γ' • (μ' : V → ℝ)) ≤ dist μ μ' + |γ - γ'| := by
  refine (dist_pi_le_iff (by positivity)).mpr fun v => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Real.dist_eq]
  have hsplit : γ * (μ : V → ℝ) v - γ' * (μ' : V → ℝ) v
      = γ * ((μ : V → ℝ) v - (μ' : V → ℝ) v) + (γ - γ') * (μ' : V → ℝ) v := by
    ring
  rw [hsplit]
  calc |γ * ((μ : V → ℝ) v - (μ' : V → ℝ) v) + (γ - γ') * (μ' : V → ℝ) v|
      ≤ |γ * ((μ : V → ℝ) v - (μ' : V → ℝ) v)|
          + |(γ - γ') * (μ' : V → ℝ) v| := abs_add_le _ _
    _ ≤ 1 * |(μ : V → ℝ) v - (μ' : V → ℝ) v| + |γ - γ'| * 1 := by
        rw [abs_mul, abs_mul]
        refine add_le_add (mul_le_mul_of_nonneg_right hγ (abs_nonneg _))
          (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        rw [abs_of_nonneg (μ'.nonneg v)]
        exact μ'.apply_le_one v
    _ = |(μ : V → ℝ) v - (μ' : V → ℝ) v| + |γ - γ'| := by ring
    _ ≤ dist μ μ' + |γ - γ'| := by
        refine add_le_add ?_ le_rfl
        rw [Subtype.dist_eq, ← Real.dist_eq]
        exact dist_le_pi_dist _ _ v

/-! ## The interpolation, repaired -/

/-- **The sector interpolation.**  A set hitting an open region `W` at
a point away from the origin hits the sector of a scaled-indicator
citizen whose every radial hitter also hits `W`.  Radial descent is
the engine: the sector reaches the full-mass tips and cannot lie
inside `W`, but a radial hitter descends its own ray into the band
around the witness, and the band is inside `W`. -/
theorem exists_sector_of_hit [Nonempty V] {W : Set (BelState V)}
    (hW : IsOpen W) {K₀ : Set (BelState V)} {x : BelState V}
    (hxK : x ∈ K₀) (hxW : x ∈ W) (hx0 : (x : V → ℝ) ≠ 0) :
    ∃ v : ProbPenalty V, LowerSemicontinuous v
      ∧ (K₀ ∩ (compile v)ᶜ).Nonempty
      ∧ ∀ K : Set (BelState V), IsRadial K →
          (K ∩ (compile v)ᶜ).Nonempty → (K ∩ W).Nonempty := by
  -- polar coordinates of the witness
  rcases BelState.exists_polar x with hzero | ⟨μ₀, γ₀, hγ₀0, hγ₀1, hxe⟩
  · exact absurd hzero hx0
  -- a metric ball inside `W`, and the band radii
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.mp hW x hxW
  set η : ℝ := min (ε / 2) γ₀ with hη
  have hη0 : 0 < η := lt_min (by positivity) hγ₀0
  set t₀ : ℝ := γ₀ - η / 2 with ht₀
  have ht₀pos : 0 < t₀ := by
    have hηγ : η ≤ γ₀ := min_le_right _ _
    have : η / 2 < γ₀ := lt_of_lt_of_le (by linarith) hηγ
    simpa [ht₀] using sub_pos.mpr this
  have ht₀lt : t₀ < γ₀ := by
    have : 0 < η / 2 := by positivity
    simpa [ht₀] using sub_lt_self γ₀ this
  have ht₀le1 : t₀ ≤ 1 := ht₀lt.le.trans hγ₀1
  -- the sector citizen
  refine ⟨scaledIndicator (gradeInv t₀) (Metric.ball μ₀ (ε / 2)),
    lowerSemicontinuous_scaledIndicator Metric.isOpen_ball, ?_, ?_⟩
  · -- the witness itself protrudes past the sector threshold
    refine ⟨x, hxK, ?_⟩
    rw [Set.mem_compl_iff, notMem_compile_scaledIndicator_iff]
    exact ⟨μ₀, γ₀, hγ₀0, hγ₀1, Metric.mem_ball_self (by positivity),
      by rw [grade_gradeInv ht₀pos ht₀le1]; exact ht₀lt, hxe⟩
  · -- radial descent into the band
    rintro K hrad ⟨y, hyK, hy⟩
    rw [Set.mem_compl_iff, notMem_compile_scaledIndicator_iff] at hy
    obtain ⟨μy, γy, hγy0, hγy1, hμyB, hgc, hye⟩ := hy
    rw [grade_gradeInv ht₀pos ht₀le1] at hgc
    -- the descent scale: down the ray to the band height
    set γ' : ℝ := min γy γ₀ with hγ'
    have hγ'0 : 0 < γ' := lt_min hγy0 hγ₀0
    have hγ'γy : γ' ≤ γy := min_le_left _ _
    have ht0 : 0 ≤ γ' / γy := div_nonneg hγ'0.le hγy0.le
    have ht1 : γ' / γy ≤ 1 := (div_le_one hγy0).mpr hγ'γy
    refine ⟨BelState.scale (γ' / γy) ht0 ht1 y, hrad y hyK _ ht0 ht1, ?_⟩
    -- the descended point sits in the band, hence in the ball at `x`
    refine hball ?_
    rw [Metric.mem_ball, Subtype.dist_eq, BelState.coe_scale, hye, hxe,
      smul_smul, div_mul_cancel₀ _ hγy0.ne']
    have hd : dist (γ' • (μy : V → ℝ)) (γ₀ • (μ₀ : V → ℝ))
        ≤ dist μy μ₀ + |γ' - γ₀| := by
      refine dist_smul_le_of_abs_le_one ?_ μy μ₀
      rw [abs_of_nonneg hγ'0.le]
      exact (min_le_right _ _).trans hγ₀1
    have hband : |γ' - γ₀| < η / 2 := by
      have hle : γ' ≤ γ₀ := min_le_right _ _
      have hgt : t₀ < γ' := lt_min hgc ht₀lt
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
      have : γ₀ - γ' < γ₀ - t₀ := by linarith
      simpa [ht₀] using this
    have hμd : dist μy μ₀ < ε / 2 := Metric.mem_ball.mp hμyB
    have hη2 : η / 2 ≤ ε / 4 := by
      have : η ≤ ε / 2 := min_le_left _ _
      linarith
    calc dist (γ' • (μy : V → ℝ)) (γ₀ • (μ₀ : V → ℝ))
        ≤ dist μy μ₀ + |γ' - γ₀| := hd
      _ < ε / 2 + η / 2 := add_lt_add hμd hband
      _ ≤ ε / 2 + ε / 4 := by linarith
      _ < ε := by linarith

/-- Hit-classes through the origin trap every nonempty radial set: on
the radial locus they are the whole subspace. -/
theorem hit_of_zero_mem {W : Set (BelState V)} (hz : BelState.zero V ∈ W)
    {K : Set (BelState V)} (hrad : IsRadial K) (hne : K.Nonempty) :
    (K ∩ W).Nonempty :=
  ⟨BelState.zero V, zero_mem_of_isRadial hrad hne, hz⟩

/-! ## The radial locus as a space, and the generation statement -/

variable (V) in
/-- The radial locus of the hyperspace, as a type: nonempty compact
radial subsets of the subprobability carrier — the system space. -/
abbrev RadialCompacts : Type _ :=
  {K : NonemptyCompacts (BelState V) // IsRadial (K : Set (BelState V))}

variable (V) in
/-- The escape faces of citizens, as a family of subsets of the radial
locus: the ∃-face sub-basis. -/
def sectorHitFamily : Set (Set (RadialCompacts V)) :=
  {A | ∃ v : ProbPenalty V, LowerSemicontinuous v
    ∧ A = {K : RadialCompacts V |
        ((K.1 : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty}}

variable (V) in
/-- The full lower-Vietoris sub-basis on the radial locus: hit-classes
of arbitrary opens. -/
def openHitFamily : Set (Set (RadialCompacts V)) :=
  {A | ∃ W : Set (BelState V), IsOpen W
    ∧ A = {K : RadialCompacts V |
        ((K.1 : Set (BelState V)) ∩ W).Nonempty}}

/-- **The sector lemma**: on the radial locus, the escape faces of
citizens generate the same topology as all hit-classes of opens — the
∃-face family is a sub-basis for the whole lower Vietoris. -/
theorem generateFrom_sectorHit_eq_openHit [Nonempty V] :
    generateFrom (sectorHitFamily V) = generateFrom (openHitFamily V) := by
  refine le_antisymm (le_generateFrom ?_) (le_generateFrom ?_)
  · -- every open-hit class is open for the sector family
    rintro A ⟨W, hW, rfl⟩
    by_cases hz : BelState.zero V ∈ W
    · -- a hit-class through the origin is the whole radial locus
      have huniv : {K : RadialCompacts V |
            ((K.1 : Set (BelState V)) ∩ W).Nonempty} = Set.univ :=
        Set.eq_univ_of_forall fun K =>
          hit_of_zero_mem hz K.2 K.1.nonempty
      rw [huniv]
      exact TopologicalSpace.GenerateOpen.univ
    · -- away from the origin, the interpolation covers the class by
      -- sector-hit generators
      have hdecomp : {K : RadialCompacts V |
            ((K.1 : Set (BelState V)) ∩ W).Nonempty}
          = ⋃ v ∈ {v : ProbPenalty V | LowerSemicontinuous v
                ∧ ∀ K : Set (BelState V), IsRadial K →
                  (K ∩ (compile v)ᶜ).Nonempty → (K ∩ W).Nonempty},
              {K : RadialCompacts V |
                ((K.1 : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty} := by
        ext K
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
        constructor
        · rintro ⟨x, hxK, hxW⟩
          have hx0 : (x : V → ℝ) ≠ 0 := by
            intro hx0
            exact hz (by rwa [show x = BelState.zero V from Subtype.ext hx0]
              at hxW)
          obtain ⟨v, hv, hK₀, hgood⟩ :=
            exists_sector_of_hit hW hxK hxW hx0
          exact ⟨v, ⟨hv, hgood⟩, hK₀⟩
        · rintro ⟨v, ⟨-, hgood⟩, hKhit⟩
          exact hgood _ K.2 hKhit
      rw [hdecomp, ← Set.sUnion_image]
      refine TopologicalSpace.GenerateOpen.sUnion _ ?_
      rintro T ⟨v, hv, rfl⟩
      exact TopologicalSpace.GenerateOpen.basic _ ⟨v, hv.1, rfl⟩
  · -- every sector-hit class is an open-hit class
    rintro A ⟨v, hv, rfl⟩
    exact TopologicalSpace.GenerateOpen.basic _
      ⟨(compile v)ᶜ, (isClosed_compile hv).isOpen_compl, rfl⟩

end SuFunctor.Universe
