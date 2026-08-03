import SuFunctor.Universe.General.Dictionary
import SuFunctor.Universe.ImageChar

/-! # The topological dictionary at the general carrier

The chapter's compile correspondence, topological half, over the
general subprobability carrier: **closedness of the body is exactly
lower semicontinuity of the penalty**, and the nonempty closed radial
sets are exactly the bodies.  This retires the finite-outcome fence:
nothing here assumes the outcome space finite, compact, or metrizable —
the carrier is any topological measurable space, and the only standing
hypothesis is `Nonempty X`, which the bottom-body bookkeeping already
required (the bottom body is `{0}`, never the empty set).

Point-free reading of each leg:

* **`isClosed_compile`** (lsc ⟹ closed): a cluster point of a body is
  a point of it.  The proof is a filter argument on the hyperspace-side
  data the narrow topology actually exposes: the *mass* observation is
  continuous, the *direction* (normalization) is continuous wherever
  mass is bounded away from zero, and the penalty sees the limiting
  direction lower semicontinuously.  The zero measure — where the
  mass–direction chart breaks — is handled by the bottom-body law, not
  smoothed over: at the bottom the body is `{0}` and membership is
  unconditional.  No liminf machinery: the grade side carries the whole
  left-limit content in `le_gradeN_of_forall_lt`, which is pure grade
  algebra.
* **attainment** (`rayGauge_mem_raySet`): rays `[0,1]·μ` are compact
  for *any* carrier — the trace of a closed body on a ray is a closed
  subset of the compact scale interval — so the gauge is attained ray
  by ray, exactly as at the finite stratum.
* **the superlevel identity** (`le_rayGauge_iff`): for a closed radial
  body, `c ≤ gauge` at `μ` is *membership of the scaled point* — the
  gauge's superlevels are preimages of the body along the continuous
  scaling maps.  Lower semicontinuity of the gauge penalty
  (`lowerSemicontinuous_rayPenalty`) and upper semicontinuity of the
  gauge (`upperSemicontinuous_rayGauge`) both read off this one
  identity.
* **reconstruction** (`compile_rayPenalty`) and the **image
  characterization** (`exists_lsc_compile_eq_iff`): every nonempty
  closed radial subset of the carrier is the compile of exactly one
  lower semicontinuous penalty.
* **`isClosed_compile_iff`**: the equivalence itself, both directions.

Deliberately absent: any compactness claim for bodies.  Over a
noncompact outcome space the carrier itself is noncompact
(`SuFunctor.Universe.not_compactSpace_probabilityMeasure_nat` is the
standing witness), so closedness is the honest general statement, and
the finite stratum's `isCompact_compile` has no general analogue.
-/

namespace SuFunctor.Universe.General

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-! ## Bodies of citizens are closed -/

/-- **Bodies of citizens are closed.**  The genuinely-new analytic leg
of the general stratum: lower semicontinuity of the penalty forces
closedness of its body in the narrow topology, over an arbitrary
carrier. -/
theorem isClosed_compile [Nonempty X] {f : Penalty X}
    (hf : LowerSemicontinuous f) : IsClosed (compile f) := by
  rw [isClosed_iff_clusterPt]
  intro ν hν
  haveI hFne : (𝓝 ν ⊓ 𝓟 (compile f)).NeBot := hν
  set F := 𝓝 ν ⊓ 𝓟 (compile f) with hFdef
  rcases eq_or_ne ((ν : FiniteMeasure X).mass) 0 with hm | hm
  · -- the bottom state: membership is the bottom-body law
    rw [(SubProbabilityMeasure.mass_eq_zero_iff ν).mp hm]
    exact zero_mem_compile f
  · -- positive mass: mass–direction chart
    have hν0 : (ν : FiniteMeasure X) ≠ 0 := by
      intro h0
      exact hm (by rw [h0, FiniteMeasure.zero_mass])
    -- the underlying finite measures converge along the approach filter
    have hval : Tendsto
        (fun ρ : SubProbabilityMeasure X => (ρ : FiniteMeasure X)) F
        (𝓝 (ν : FiniteMeasure X)) :=
      (SubProbabilityMeasure.continuous_toFiniteMeasure.tendsto ν).mono_left
        inf_le_left
    -- mass converges (narrow continuity of the mass observation)
    have hmass : Tendsto
        (fun ρ : SubProbabilityMeasure X => (ρ : FiniteMeasure X).mass) F
        (𝓝 ((ν : FiniteMeasure X).mass)) :=
      (FiniteMeasure.continuous_mass.tendsto _).comp hval
    -- eventually the mass is nonzero
    have hevpos : ∀ᶠ ρ : SubProbabilityMeasure X in F,
        (ρ : FiniteMeasure X).mass ≠ 0 :=
      hmass.eventually_ne hm
    -- eventually we are inside the body
    have hmem : ∀ᶠ ρ : SubProbabilityMeasure X in F, ρ ∈ compile f :=
      Filter.le_principal_iff.mp inf_le_right
    -- directions converge (normalization is continuous at nonzero mass)
    have hdir : Tendsto
        (fun ρ : SubProbabilityMeasure X =>
          (ρ : FiniteMeasure X).normalize) F
        (𝓝 ((ν : FiniteMeasure X).normalize)) :=
      FiniteMeasure.tendsto_normalize_of_tendsto hval hν0
    -- the limiting mass is below every grade strictly before the
    -- penalty of the limiting direction
    have hbound : ∀ y, y < f ((ν : FiniteMeasure X).normalize) →
        (ν : FiniteMeasure X).mass ≤ gradeN y := by
      intro y hy
      have hev1 : ∀ᶠ ρ : SubProbabilityMeasure X in F,
          y < f ((ρ : FiniteMeasure X).normalize) :=
        hdir.eventually (hf _ y hy)
      have hev2 : ∀ᶠ ρ : SubProbabilityMeasure X in F,
          (ρ : FiniteMeasure X).mass ≤ gradeN y := by
        filter_upwards [hmem, hevpos, hev1] with ρ hρmem hρpos hρy
        obtain ⟨μρ, γρ, hγle, he⟩ := hρmem
        have hγ0 : γρ ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at he
          exact hρpos (by rw [he, FiniteMeasure.zero_mass])
        have hmassρ : (ρ : FiniteMeasure X).mass = γρ := by
          rw [he, SubProbabilityMeasure.mass_smul,
            ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
        have hnorm : (ρ : FiniteMeasure X).normalize = μρ := by
          rw [he]
          exact SubProbabilityMeasure.normalize_smul_prob hγ0 μρ
        rw [hmassρ]
        rw [hnorm] at hρy
        exact hγle.trans (gradeN_anti hρy.le)
      exact le_of_tendsto hmass hev2
    -- close through the grade's left-limit lemma
    have hmle : (ν : FiniteMeasure X).mass
        ≤ gradeN (f ((ν : FiniteMeasure X).normalize)) :=
      le_gradeN_of_forall_lt ν.mass_le_one hbound
    exact ⟨(ν : FiniteMeasure X).normalize, (ν : FiniteMeasure X).mass,
      hmle, (ν : FiniteMeasure X).self_eq_mass_smul_normalize⟩

/-! ## Rays are compact for any carrier; the gauge is attained -/

/-- For closed `R` the ray trace is compact: a closed subset of the
compact scale interval — for **any** carrier. -/
theorem isCompact_raySet {R : Set (SubProbabilityMeasure X)}
    (hR : IsClosed R) (μ : ProbabilityMeasure X) :
    IsCompact (raySet R μ) := by
  have hval : IsClosed (SubProbabilityMeasure.toFiniteMeasure '' R) :=
    SubProbabilityMeasure.isClosed_image_toFiniteMeasure hR
  have hcont : Continuous fun γ : ℝ≥0 => γ • μ.toFiniteMeasure :=
    SubProbabilityMeasure.continuous_smul_scalar μ.toFiniteMeasure
  have hcl : IsClosed (raySet R μ) := by
    have hrepr : raySet R μ
        = Set.Icc (0 : ℝ≥0) 1 ∩ (fun γ : ℝ≥0 => γ • μ.toFiniteMeasure)
            ⁻¹' (SubProbabilityMeasure.toFiniteMeasure '' R) := rfl
    rw [hrepr]
    exact isClosed_Icc.inter (hval.preimage hcont)
  exact IsCompact.of_isClosed_subset isCompact_Icc hcl fun γ hγ => hγ.1

/-- **Attainment**: for a closed set owning the bottom state, the gauge
is a member of the ray trace — the tip of every ray is a point of the
set. -/
theorem rayGauge_mem_raySet {R : Set (SubProbabilityMeasure X)}
    (hR : IsClosed R) (hz : (0 : SubProbabilityMeasure X) ∈ R)
    (μ : ProbabilityMeasure X) : rayGauge R μ ∈ raySet R μ :=
  (isCompact_raySet hR μ).sSup_mem ⟨0, zero_mem_raySet hz μ⟩

/-! ## The superlevel identity -/

/-- **The superlevel identity**: for a closed radial body, a scale is
below the gauge at `μ` exactly when the correspondingly scaled point
belongs to the body.  Forward: descend the ray from the attained tip;
backward: the scaled point is itself a ray-trace witness. -/
theorem le_rayGauge_iff {R : Set (SubProbabilityMeasure X)}
    (hcl : IsClosed R) (hrad : IsRadial R)
    (hz : (0 : SubProbabilityMeasure X) ∈ R) {c : ℝ≥0} (hc : c ≤ 1)
    (μ : ProbabilityMeasure X) :
    c ≤ rayGauge R μ ↔ SubProbabilityMeasure.scalePoint c hc μ ∈ R := by
  constructor
  · intro h
    have htipmem := rayGauge_mem_raySet hcl hz μ
    have htip : SubProbabilityMeasure.scalePoint (rayGauge R μ)
        htipmem.1.2 μ ∈ R :=
      scalePoint_mem_of_mem_raySet htipmem
    rcases eq_or_ne (rayGauge R μ) 0 with hg | hg
    · have hc0 : c = 0 := le_antisymm (hg ▸ h) zero_le
      have hzero : SubProbabilityMeasure.scalePoint c hc μ
          = (0 : SubProbabilityMeasure X) :=
        SubProbabilityMeasure.ext (by
          rw [SubProbabilityMeasure.coe_scalePoint, hc0, zero_smul,
            SubProbabilityMeasure.coe_zero])
      rw [hzero]
      exact hz
    · have hdiv1 : c / rayGauge R μ ≤ 1 :=
        (div_le_one (pos_iff_ne_zero.mpr hg)).mpr h
      have hstep := hrad _ htip (c / rayGauge R μ) hdiv1
      have he : SubProbabilityMeasure.scale (c / rayGauge R μ) hdiv1
          (SubProbabilityMeasure.scalePoint (rayGauge R μ) htipmem.1.2 μ)
            = SubProbabilityMeasure.scalePoint c hc μ :=
        SubProbabilityMeasure.ext (by
          rw [SubProbabilityMeasure.coe_scale,
            SubProbabilityMeasure.coe_scalePoint,
            SubProbabilityMeasure.coe_scalePoint, smul_smul,
            div_mul_cancel₀ _ hg])
      rwa [he] at hstep
  · intro h
    exact le_rayGauge_of_mem_raySet ⟨⟨zero_le, hc⟩, _, h,
      SubProbabilityMeasure.coe_scalePoint _ _ _⟩

/-! ## The gauge penalty of a closed radial body is a citizen -/

/-- Lower semicontinuity of the gauge penalty of a nonempty closed
radial set: every sublevel of the gauge penalty is the preimage of the
body along a continuous scaling map — the superlevel identity composed
with the grade order dictionary. -/
theorem lowerSemicontinuous_rayPenalty {R : Set (SubProbabilityMeasure X)}
    (hcl : IsClosed R) (hrad : IsRadial R) (hne : R.Nonempty) :
    LowerSemicontinuous (rayPenalty R) := by
  have hz : (0 : SubProbabilityMeasure X) ∈ R :=
    zero_mem_of_isRadial hne hrad
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  have hrepr : rayPenalty R ⁻¹' Set.Iic y
      = (fun μ => SubProbabilityMeasure.scalePoint (gradeN y)
          (gradeN_le_one y) μ) ⁻¹' R := by
    ext μ
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [rayPenalty, gradeInv_le_iff (rayGauge_le_one hz μ),
      le_rayGauge_iff hcl hrad hz (gradeN_le_one y)]
  rw [hrepr]
  exact hcl.preimage
    (SubProbabilityMeasure.continuous_scalePoint _ (gradeN_le_one y))

/-- The ray gauge of a nonempty closed radial set is upper
semicontinuous: the usc-grade face of citizenship, read off the same
superlevel identity. -/
theorem upperSemicontinuous_rayGauge {R : Set (SubProbabilityMeasure X)}
    (hcl : IsClosed R) (hrad : IsRadial R) (hne : R.Nonempty) :
    UpperSemicontinuous (rayGauge R) := by
  have hz : (0 : SubProbabilityMeasure X) ∈ R :=
    zero_mem_of_isRadial hne hrad
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c ≤ 1
  · have hrepr : rayGauge R ⁻¹' Set.Ici c
        = (fun μ => SubProbabilityMeasure.scalePoint c hc μ) ⁻¹' R := by
      ext μ
      simp only [Set.mem_preimage, Set.mem_Ici]
      exact le_rayGauge_iff hcl hrad hz hc μ
    rw [hrepr]
    exact hcl.preimage (SubProbabilityMeasure.continuous_scalePoint _ hc)
  · have hrepr : rayGauge R ⁻¹' Set.Ici c = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro μ hμ
      exact absurd (le_trans hμ (rayGauge_le_one hz μ)) hc
    rw [hrepr]
    exact isClosed_empty

/-! ## Reconstruction, and the image characterization -/

/-- **Reconstruction**: the body of the gauge penalty of a nonempty
closed radial set is the set itself — attainment puts the ray tips in
`R`, radiality fills each ray downward from its tip. -/
theorem compile_rayPenalty [Nonempty X] {R : Set (SubProbabilityMeasure X)}
    (hcl : IsClosed R) (hrad : IsRadial R) (hne : R.Nonempty) :
    compile (rayPenalty R) = R := by
  have hz : (0 : SubProbabilityMeasure X) ∈ R :=
    zero_mem_of_isRadial hne hrad
  have hgg : ∀ μ, gradeN (rayPenalty R μ) = rayGauge R μ := by
    intro μ
    ext
    rw [coe_gradeN, rayPenalty, grade_gradeInv_of_nonneg
      (NNReal.coe_nonneg _) (by exact_mod_cast rayGauge_le_one hz μ)]
  ext ν
  constructor
  · rintro ⟨μ, γ, hle, he⟩
    rw [hgg] at hle
    have hγ1 : γ ≤ 1 := hle.trans (rayGauge_le_one hz μ)
    have hmem : SubProbabilityMeasure.scalePoint γ hγ1 μ ∈ R :=
      (le_rayGauge_iff hcl hrad hz hγ1 μ).mp hle
    have hνe : ν = SubProbabilityMeasure.scalePoint γ hγ1 μ :=
      SubProbabilityMeasure.ext (by
        rw [SubProbabilityMeasure.coe_scalePoint, he])
    rw [hνe]
    exact hmem
  · intro hν
    rcases SubProbabilityMeasure.exists_polar ν with h0 | ⟨μ, m, hm0, hm1, he⟩
    · rw [h0]
      exact zero_mem_compile _
    · have hray : m ∈ raySet R μ := ⟨⟨zero_le, hm1⟩, ν, hν, he⟩
      refine ⟨μ, m, ?_, he⟩
      rw [hgg]
      exact le_rayGauge_of_mem_raySet hray

/-- **The image characterization**: a set of subprobability states is
the body of a citizen iff it is nonempty, closed, and radial — over the
general carrier.  Uniqueness of the citizen is `compile_injective`. -/
theorem exists_lsc_compile_eq_iff [Nonempty X]
    {R : Set (SubProbabilityMeasure X)} :
    (∃ f : Penalty X, LowerSemicontinuous f ∧ compile f = R)
      ↔ R.Nonempty ∧ IsClosed R ∧ IsRadial R := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨_, zero_mem_compile f⟩, isClosed_compile hf, isRadial_compile f⟩
  · rintro ⟨hne, hcl, hrad⟩
    exact ⟨rayPenalty R, lowerSemicontinuous_rayPenalty hcl hrad hne,
      compile_rayPenalty hcl hrad hne⟩

/-- **The dictionary's topological leg, both directions**: the body of
a penalty is closed exactly when the penalty is lower semicontinuous —
the general-carrier theorem that retires the finite-stratum fence. -/
theorem isClosed_compile_iff [Nonempty X] {f : Penalty X} :
    IsClosed (compile f) ↔ LowerSemicontinuous f := by
  constructor
  · intro hcl
    have hlsc := lowerSemicontinuous_rayPenalty hcl (isRadial_compile f)
      ⟨_, zero_mem_compile f⟩
    rwa [rayPenalty_compile] at hlsc
  · exact isClosed_compile

end SuFunctor.Universe.General
