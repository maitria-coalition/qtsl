import SuFunctor.Universe.VietorisStratum

/-! # The image characterization: every closed radial set is a compile

`SuFunctor.Universe.VietorisDictionary` sends penalties to their
epistemic bodies; `SuFunctor.Universe.VietorisStratum` shows the body
of a citizen is nonempty, compact (hence closed), and radial.  This
module closes the circle: **those three properties characterize the
image** (`exists_lsc_compile_eq_iff`) — every nonempty closed
ray-down-closed subset of the subprobability carrier is the body of
exactly one citizen.

* **The ray gauge** (`rayGauge`): the length of a set's ray at each
  probability direction — the supremum of the scales at which the ray
  meets the set.  For closed `R` the trace of `R` on each ray is
  compact, so the gauge is *attained* (`rayGauge_mem_raySet`): the
  tip of every ray is a point of `R`.
* **The gauge penalty** (`rayPenalty`): `−log` of the gauge, via the
  grade inverse of the topological stratum; `grade_rayPenalty` says
  the compile of the gauge penalty spends exactly the gauge on each
  ray.
* **Reconstruction** (`compile_rayPenalty`): for nonempty closed
  radial `R`, the body of the gauge penalty is `R` itself — attainment
  gives the tips, radiality fills the rays downward.  Lower
  semicontinuity of the gauge penalty is then *free*, read off
  `isClosed_compile_iff` — no separate semicontinuity argument.
* **Injectivity** (`compile_injective`): distinct penalties have
  distinct bodies — immediate from antitonicity — so the compile is a
  *bijection* from citizens onto nonempty closed radial sets, with
  inverse `rayPenalty` (`rayPenalty_compile`).  The hyperspace is the
  system space with no gap: nothing radial is left over, and nothing
  is hit twice.
* **The gauge is upper semicontinuous** (`upperSemicontinuous_rayGauge`)
  for nonempty closed radial `R`: the usc-grade face of citizenship,
  recovered from the reconstruction through the grade transport.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-! ## Grade and its inverse, on the closed unit interval -/

/-- The grade inverse is a right inverse of the grade on all of
`[0, 1]`: the endpoint `c = 0` goes through hard violation
(`gradeInv 0 = ⊤`, `grade ⊤ = 0`). -/
theorem grade_gradeInv_of_nonneg {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    grade (gradeInv c) = c := by
  rcases h0.lt_or_eq with hpos | hzero
  · exact grade_gradeInv hpos h1
  · rw [← hzero, gradeInv, if_pos le_rfl, grade_top]

/-! ## Polar decomposition of the carrier -/

/-- Polar decomposition: every distribution is the zero state or a
positive mass times a probability direction. -/
theorem BelState.exists_polar (x : BelState V) :
    (x : V → ℝ) = 0 ∨ ∃ (μ : ProbState V) (m : ℝ), 0 < m ∧ m ≤ 1
      ∧ (x : V → ℝ) = m • (μ : V → ℝ) := by
  rcases (BelState.mass_nonneg x).lt_or_eq with hm | hm
  · refine Or.inr ?_
    have hne : BelState.mass x ≠ 0 := hm.ne'
    refine ⟨⟨fun v => (x : V → ℝ) v / BelState.mass x,
      fun v => div_nonneg (x.nonneg v) hm.le, ?_⟩,
      BelState.mass x, hm, x.mass_le_one, ?_⟩
    · simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hne
    · funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_comm, div_mul_cancel₀ _ hne]
  · refine Or.inl (funext fun v => ?_)
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => x.nonneg v)).mp hm.symm
    exact h v (Finset.mem_univ v)

/-- The zero state belongs to every nonempty radial set. -/
theorem zero_mem_of_isRadial {R : Set (BelState V)} (hrad : IsRadial R)
    (hne : R.Nonempty) : BelState.zero V ∈ R := by
  obtain ⟨x, hx⟩ := hne
  have h := hrad x hx 0 le_rfl zero_le_one
  have he : BelState.scale (0 : ℝ) le_rfl zero_le_one x = BelState.zero V := by
    refine Subtype.ext (funext fun v => ?_)
    simp [BelState.coe_scale]
  rwa [he] at h

/-! ## The ray gauge -/

/-- The trace of a set on the ray at a probability direction: the
scales at which the ray meets the set. -/
def raySet (R : Set (BelState V)) (μ : ProbState V) : Set ℝ :=
  {γ ∈ Set.Icc (0 : ℝ) 1 | γ • (μ : V → ℝ) ∈ Subtype.val '' R}

theorem mem_raySet_iff {R : Set (BelState V)} {μ : ProbState V} {γ : ℝ} :
    γ ∈ raySet R μ
      ↔ (0 ≤ γ ∧ γ ≤ 1) ∧ γ • (μ : V → ℝ) ∈ Subtype.val '' R :=
  Iff.rfl

theorem zero_mem_raySet {R : Set (BelState V)} (hz : BelState.zero V ∈ R)
    (μ : ProbState V) : (0 : ℝ) ∈ raySet R μ := by
  refine ⟨⟨le_rfl, zero_le_one⟩, BelState.zero V, hz, funext fun v => ?_⟩
  simp

theorem bddAbove_raySet (R : Set (BelState V)) (μ : ProbState V) :
    BddAbove (raySet R μ) :=
  ⟨1, fun _ hγ => hγ.1.2⟩

/-- For closed `R` the ray trace is compact: a closed subset of the
scale interval. -/
theorem isCompact_raySet {R : Set (BelState V)} (hR : IsClosed R)
    (μ : ProbState V) : IsCompact (raySet R μ) := by
  have hval : IsClosed (Subtype.val '' R) :=
    (hR.isCompact.image continuous_subtype_val).isClosed
  have hcont : Continuous fun γ : ℝ => γ • (μ : V → ℝ) := by
    refine continuous_pi fun v => ?_
    show Continuous fun γ : ℝ => γ * (μ : V → ℝ) v
    exact continuous_id.mul continuous_const
  have hcl : IsClosed (raySet R μ) := by
    have : raySet R μ
        = Set.Icc (0 : ℝ) 1 ∩ (fun γ : ℝ => γ • (μ : V → ℝ)) ⁻¹'
            (Subtype.val '' R) := by
      ext γ
      exact Iff.rfl
    rw [this]
    exact isClosed_Icc.inter (hval.preimage hcont)
  exact IsCompact.of_isClosed_subset isCompact_Icc hcl fun γ hγ => hγ.1

/-- The ray gauge: the length of the set's ray at each direction. -/
noncomputable def rayGauge (R : Set (BelState V)) (μ : ProbState V) : ℝ :=
  sSup (raySet R μ)

/-- **Attainment**: for closed `R` with the zero state, the gauge is a
member of the ray trace — the tip of the ray is a point of `R`. -/
theorem rayGauge_mem_raySet {R : Set (BelState V)} (hR : IsClosed R)
    (hz : BelState.zero V ∈ R) (μ : ProbState V) :
    rayGauge R μ ∈ raySet R μ :=
  (isCompact_raySet hR μ).sSup_mem ⟨0, zero_mem_raySet hz μ⟩

theorem rayGauge_nonneg {R : Set (BelState V)} (hz : BelState.zero V ∈ R)
    (μ : ProbState V) : 0 ≤ rayGauge R μ :=
  le_csSup (bddAbove_raySet R μ) (zero_mem_raySet hz μ)

theorem rayGauge_le_one {R : Set (BelState V)} (hz : BelState.zero V ∈ R)
    (μ : ProbState V) : rayGauge R μ ≤ 1 :=
  csSup_le ⟨0, zero_mem_raySet hz μ⟩ fun _ hγ => hγ.1.2

theorem le_rayGauge_of_mem_raySet {R : Set (BelState V)} {μ : ProbState V}
    {γ : ℝ} (hγ : γ ∈ raySet R μ) : γ ≤ rayGauge R μ :=
  le_csSup (bddAbove_raySet R μ) hγ

/-! ## The gauge penalty, and reconstruction -/

/-- The gauge penalty of a set: `−log` of its ray gauge. -/
noncomputable def rayPenalty (R : Set (BelState V)) : ProbPenalty V :=
  fun μ => gradeInv (rayGauge R μ)

/-- The compile of the gauge penalty spends exactly the gauge on each
ray. -/
theorem grade_rayPenalty {R : Set (BelState V)} (hz : BelState.zero V ∈ R)
    (μ : ProbState V) : grade (rayPenalty R μ) = rayGauge R μ :=
  grade_gradeInv_of_nonneg (rayGauge_nonneg hz μ) (rayGauge_le_one hz μ)

/-- **Reconstruction**: the body of the gauge penalty of a nonempty
closed radial set is the set itself.  Attainment puts the ray tips in
`R`; radiality fills each ray downward from its tip. -/
theorem compile_rayPenalty [Nonempty V] {R : Set (BelState V)}
    (hcl : IsClosed R) (hrad : IsRadial R) (hne : R.Nonempty) :
    compile (rayPenalty R) = R := by
  have hz : BelState.zero V ∈ R := zero_mem_of_isRadial hrad hne
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    rw [grade_rayPenalty hz] at hle
    obtain ⟨-, y, hyR, hy⟩ := rayGauge_mem_raySet hcl hz μ
    rcases (rayGauge_nonneg hz μ).lt_or_eq with hg | hg
    · -- positive gauge: descend the ray from the attained tip
      have ht0 : 0 ≤ γ / rayGauge R μ := div_nonneg h0 hg.le
      have ht1 : γ / rayGauge R μ ≤ 1 := (div_le_one hg).mpr hle
      have hxy : x = BelState.scale (γ / rayGauge R μ) ht0 ht1 y := by
        refine Subtype.ext ?_
        rw [BelState.coe_scale, hy, he, smul_smul, div_mul_cancel₀ _ hg.ne']
      rw [hxy]
      exact hrad y hyR _ ht0 ht1
    · -- zero gauge: the point is the attained tip itself
      have hγ0 : γ = 0 := le_antisymm (hle.trans hg.ge) h0
      have hxy : x = y := by
        refine Subtype.ext ?_
        rw [he, hy, ← hg, hγ0]
      rw [hxy]
      exact hyR
  · intro hx
    rcases BelState.exists_polar x with hx0 | ⟨μ, m, hm0, hm1, hxe⟩
    · obtain ⟨μ⟩ := (inferInstance : Nonempty (ProbState V))
      exact ⟨μ, 0, le_rfl, grade_nonneg _, by rw [hx0, zero_smul]⟩
    · have hmem : m ∈ raySet R μ := ⟨⟨hm0.le, hm1⟩, x, hx, hxe⟩
      exact ⟨μ, m, hm0.le, by
        rw [grade_rayPenalty hz]
        exact le_rayGauge_of_mem_raySet hmem, hxe⟩

/-- **The image characterization**: a set of distributions is the body
of a citizen iff it is nonempty, closed, and radial.  Lower
semicontinuity of the reconstructing penalty is free, read off the
topological face of citizenship. -/
theorem exists_lsc_compile_eq_iff [Nonempty V] {R : Set (BelState V)} :
    (∃ f : ProbPenalty V, LowerSemicontinuous f ∧ compile f = R)
      ↔ R.Nonempty ∧ IsClosed R ∧ IsRadial R := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨_, zero_mem_compile f⟩, isClosed_compile hf, isRadial_compile f⟩
  · rintro ⟨hne, hcl, hrad⟩
    refine ⟨rayPenalty R, ?_, compile_rayPenalty hcl hrad hne⟩
    have hcl' : IsClosed (compile (rayPenalty R)) := by
      rw [compile_rayPenalty hcl hrad hne]
      exact hcl
    exact isClosed_compile_iff.mp hcl'

/-! ## The compile is a bijection onto the radial closed sets -/

/-- **Injectivity**: distinct penalties have distinct bodies — the
set-side face of antitonicity, with no citizenship hypothesis. -/
theorem compile_injective : Function.Injective (compile (V := V)) := by
  intro f h hfh
  exact le_antisymm (compile_subset_compile_iff.mp hfh.superset)
    (compile_subset_compile_iff.mp hfh.subset)

/-- The gauge penalty inverts the compile on citizens: the bijection's
round trip on the penalty side. -/
theorem rayPenalty_compile [Nonempty V] {f : ProbPenalty V}
    (hf : LowerSemicontinuous f) : rayPenalty (compile f) = f :=
  compile_injective (compile_rayPenalty (isClosed_compile hf)
    (isRadial_compile f) ⟨_, zero_mem_compile f⟩)

/-- The ray gauge of a nonempty closed radial set is upper
semicontinuous: the usc-grade face of the image characterization. -/
theorem upperSemicontinuous_rayGauge [Nonempty V] {R : Set (BelState V)}
    (hcl : IsClosed R) (hrad : IsRadial R) (hne : R.Nonempty) :
    UpperSemicontinuous (rayGauge R) := by
  have hz : BelState.zero V ∈ R := zero_mem_of_isRadial hrad hne
  have hlsc : LowerSemicontinuous (rayPenalty R) := by
    have hcl' : IsClosed (compile (rayPenalty R)) := by
      rw [compile_rayPenalty hcl hrad hne]
      exact hcl
    exact isClosed_compile_iff.mp hcl'
  have he : rayGauge R = fun μ => grade (rayPenalty R μ) :=
    funext fun μ => (grade_rayPenalty hz μ).symm
  rw [he]
  exact upperSemicontinuous_grade_comp hlsc

end SuFunctor.Universe
