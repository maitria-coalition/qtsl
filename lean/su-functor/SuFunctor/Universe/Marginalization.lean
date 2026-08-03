import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Nat

/-! # Marginalization of penalties: the lower-semicontinuity rider

Hiding a coordinate of a system turns a penalty `σ` on the joint carrier
into its *inf-projection* `infProj p σ` along the marginal map `p`:
the penalty of a visible state is the least penalty of any joint state
above it.  This file records what that operation does to
lower semicontinuity, on carriers of probability measures over Polish
spaces (subprobability carriers are the special case where a distinguished
cemetery point absorbs the missing mass; every statement here is made on
that chart).

Three results, one negative and two positive:

* **Lower semicontinuity is not preserved** (`exists_lowerSemicontinuous_not_lowerSemicontinuous_infProj`):
  on `ProbabilityMeasure ℕ` there is a narrowly closed set `C` — the
  escaping-mass family `escapeMix n = (1 - 1/(n+2)) δ_(n+2) + (1/(n+2)) δ_0`
  — whose image under the (narrowly continuous) live-mass coordinate is
  not closed: the visible values `1 - 1/(n+2)` accumulate at `1`, but no
  member attains it, because the mass witnessing a high value has escaped
  along the hidden coordinate.  Consequently the inf-projection of the
  (lower semicontinuous) wall of `C` fails lower semicontinuity at `1`.

* **The lower-semicontinuous envelope repairs it, invisibly to judgments**
  (`le_lscEnv_iff`, `le_hide_iff`): the envelope `lscEnv g` — the greatest
  lsc minorant — satisfies `φ ≤ lscEnv g ↔ φ ≤ g` for every lsc `φ`, so
  replacing an inf-projection by its envelope changes no domination
  judgment against an lsc specification.  The envelope only lowers the
  penalty (`lscEnv_le`), and relaxing summands before a sum is likewise
  conservative (`lscEnv_add_lscEnv_le`); moreover domination against a
  hidden-coordinate system never evaluates the infimum at all
  (`le_infProj_iff`: it is equivalent to ordinary domination upstairs).

* **Inf-compactness is the exactness certificate**
  (`sublevel_infProj_eq`, `lowerSemicontinuous_infProj`,
  `isCompact_sublevel_infProj`, `exists_infProj_attained`): if `σ` is lsc
  with compact sublevels, then the sublevels of the inf-projection are
  exactly the images of the sublevels (no closure bar), the infimum is
  attained wherever finite, and the inf-projection is again lsc with
  compact sublevels — the certificate class is closed under
  marginalization.  On probability-measure carriers over a complete
  second-countable metric space, compactness of sublevels is equivalent
  (Prokhorov) to uniform tightness of the measures in each sublevel
  (`isCompact_sublevel_of_isTightMeasureSet`), so a tightness certificate
  (e.g. a coercive moment bound on the hidden coordinates) turns the naive
  marginalization formula exact.
-/

namespace SuFunctor.Universe

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ## Inf-projection and characteristic penalties -/

section InfProj

variable {Z W : Type*}

/-- The inf-projection (marginalization) of a penalty `σ : Z → ℝ≥0∞` along
a map `p : Z → W`: the least penalty over the fiber, `⊤` where the fiber
is empty. -/
noncomputable def infProj (p : Z → W) (σ : Z → ℝ≥0∞) (w : W) : ℝ≥0∞ :=
  ⨅ (z) (_ : p z = w), σ z

theorem infProj_le (p : Z → W) (σ : Z → ℝ≥0∞) (z : Z) :
    infProj p σ (p z) ≤ σ z :=
  iInf_le_of_le z (iInf_le_of_le rfl le_rfl)

/-- Domination against a marginalized penalty never evaluates the
infimum: `φ ≤ infProj p σ` iff the pullback of `φ` is dominated by `σ`
upstairs.  (The inf–pullback adjunction.) -/
theorem le_infProj_iff {p : Z → W} {σ : Z → ℝ≥0∞} {φ : W → ℝ≥0∞} :
    φ ≤ infProj p σ ↔ φ ∘ p ≤ σ := by
  constructor
  · intro h z
    exact (h (p z)).trans (infProj_le p σ z)
  · intro h w
    exact le_iInf₂ fun z hz => hz ▸ h z

open Classical in
/-- The characteristic penalty (wall) of a set: `0` on it, `⊤` off it. -/
noncomputable def charFn (C : Set Z) : Z → ℝ≥0∞ :=
  fun z => if z ∈ C then 0 else ⊤

@[simp] theorem charFn_of_mem {C : Set Z} {z : Z} (h : z ∈ C) :
    charFn C z = 0 := by
  simp [charFn, h]

@[simp] theorem charFn_of_notMem {C : Set Z} {z : Z} (h : z ∉ C) :
    charFn C z = ⊤ := by
  simp [charFn, h]

/-- Marginalizing a wall gives the wall of the image. -/
theorem infProj_charFn (p : Z → W) (C : Set Z) :
    infProj p (charFn C) = charFn (p '' C) := by
  funext w
  by_cases hw : w ∈ p '' C
  · obtain ⟨z, hz, rfl⟩ := hw
    rw [charFn_of_mem (Set.mem_image_of_mem p hz)]
    exact le_antisymm ((infProj_le p _ z).trans_eq (charFn_of_mem hz)) zero_le
  · rw [charFn_of_notMem hw]
    rw [infProj, iInf₂_eq_top]
    intro z hz
    exact charFn_of_notMem fun hzC => hw ⟨z, hzC, hz⟩

variable [TopologicalSpace Z]

/-- A wall is lower semicontinuous exactly when its set is closed. -/
theorem lowerSemicontinuous_charFn_iff {C : Set Z} :
    LowerSemicontinuous (charFn C) ↔ IsClosed C := by
  constructor
  · intro h
    have := h.isClosed_preimage 0
    convert this using 1
    ext z
    by_cases hz : z ∈ C <;>
      simp [hz, mem_preimage, mem_Iic]
  · intro hC
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    rcases eq_or_ne y ⊤ with rfl | hy
    · convert isClosed_univ
      ext z
      by_cases hz : z ∈ C <;> simp [hz, mem_preimage, mem_Iic]
    · convert hC using 1
      ext z
      by_cases hz : z ∈ C <;> simp [hz, mem_preimage, mem_Iic, hy]

end InfProj

/-! ## The lower-semicontinuous envelope (reflector) -/

section LscEnv

variable {Z : Type*} [TopologicalSpace Z]

/-- The lower-semicontinuous envelope: the greatest lsc minorant. -/
noncomputable def lscEnv (g : Z → ℝ≥0∞) : Z → ℝ≥0∞ :=
  ⨆ h : {h : Z → ℝ≥0∞ // LowerSemicontinuous h ∧ h ≤ g}, (h : Z → ℝ≥0∞)

theorem lowerSemicontinuous_lscEnv (g : Z → ℝ≥0∞) :
    LowerSemicontinuous (lscEnv g) := by
  have : lscEnv g
      = fun z => ⨆ h : {h : Z → ℝ≥0∞ // LowerSemicontinuous h ∧ h ≤ g}, (h : Z → ℝ≥0∞) z := by
    funext z
    simp [lscEnv]
  rw [this]
  exact lowerSemicontinuous_iSup fun h => h.2.1

theorem lscEnv_le (g : Z → ℝ≥0∞) : lscEnv g ≤ g :=
  iSup_le fun h => h.2.2

theorem le_lscEnv {g h : Z → ℝ≥0∞} (hlsc : LowerSemicontinuous h)
    (hle : h ≤ g) : h ≤ lscEnv g :=
  le_iSup (fun h : {h : Z → ℝ≥0∞ // LowerSemicontinuous h ∧ h ≤ g} =>
    (h : Z → ℝ≥0∞)) ⟨h, hlsc, hle⟩

theorem lscEnv_eq_self {g : Z → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    lscEnv g = g :=
  le_antisymm (lscEnv_le g) (le_lscEnv hg le_rfl)

/-- **Judgment invisibility of the envelope.**  Against a lower
semicontinuous specification, a function and its lsc envelope dominate
the same specifications: an lsc minorant of `g` is precisely an lsc
minorant of the greatest one. -/
theorem le_lscEnv_iff {g φ : Z → ℝ≥0∞} (hφ : LowerSemicontinuous φ) :
    φ ≤ lscEnv g ↔ φ ≤ g :=
  ⟨fun h => h.trans (lscEnv_le g), fun h => le_lscEnv hφ h⟩

/-- Relaxing summands before a sum is conservative: the sum of the
envelopes is an lsc minorant of the sum. -/
theorem lscEnv_add_lscEnv_le (g₁ g₂ : Z → ℝ≥0∞) :
    lscEnv g₁ + lscEnv g₂ ≤ lscEnv (g₁ + g₂) :=
  le_lscEnv ((lowerSemicontinuous_lscEnv g₁).add (lowerSemicontinuous_lscEnv g₂))
    (add_le_add (lscEnv_le g₁) (lscEnv_le g₂))

variable {W : Type*} [TopologicalSpace W]

/-- The repaired (citizenship-preserving) marginalization: the lsc
envelope of the inf-projection. -/
noncomputable def hide (p : Z → W) (σ : Z → ℝ≥0∞) : W → ℝ≥0∞ :=
  lscEnv (infProj p σ)

omit [TopologicalSpace Z] in
/-- Judgments against a hidden-coordinate system factor through neither
the envelope nor the infimum: for lsc `φ`, domination by the repaired
marginalization is ordinary domination upstairs. -/
theorem le_hide_iff {p : Z → W} {σ : Z → ℝ≥0∞} {φ : W → ℝ≥0∞}
    (hφ : LowerSemicontinuous φ) :
    φ ≤ hide p σ ↔ φ ∘ p ≤ σ := by
  rw [hide, le_lscEnv_iff hφ, le_infProj_iff]

end LscEnv

/-! ## Exactness under the inf-compactness certificate -/

section Exact

variable {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]

/-- **Exact marginalization under the certificate.**  If `σ` is lower
semicontinuous with compact sublevels, the sublevels of its
inf-projection along a continuous map are exactly the images of the
sublevels: no closure bar.  (The compactness is in the objective's
sublevels, not the constraint set, so noncompact fibers are harmless.) -/
theorem sublevel_infProj_eq [T1Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c})
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    {w | infProj p σ w ≤ c} = p '' {z | σ z ≤ c} := by
  ext w
  constructor
  · intro hw
    -- the directed family of near-optimal fiber slices
    set F : ℕ → Set Z :=
      fun n => {z | σ z ≤ c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹} ∩ p ⁻¹' {w} with hF
    have hmod_ne_zero : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 :=
      fun n => ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    have hmod_ne_top : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      fun n => ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.succ_ne_zero n)
    have hanti : ∀ {m n : ℕ}, m ≤ n → F n ⊆ F m := by
      intro m n hmn
      refine inter_subset_inter_left _ fun z hz => ?_
      refine le_trans (show σ z ≤ c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ from hz) ?_
      refine add_le_add le_rfl (ENNReal.inv_le_inv.mpr ?_)
      exact_mod_cast Nat.succ_le_succ hmn
    have hne : ∀ n : ℕ, (F n).Nonempty := by
      intro n
      have hlt : infProj p σ w < c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
        lt_of_le_of_lt hw (ENNReal.lt_add_right hc (hmod_ne_zero n))
      rw [infProj] at hlt
      obtain ⟨z, hz⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hzw, hzlt⟩ := iInf_lt_iff.mp hz
      exact ⟨z, hzlt.le, hzw⟩
    have hcl : ∀ n, IsClosed (F n) := fun n =>
      (hσ.isClosed_preimage _).inter (isClosed_singleton.preimage hp)
    have hcp : ∀ n, IsCompact (F n) := fun n =>
      (hcpt (c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
        (ENNReal.add_ne_top.mpr ⟨hc, hmod_ne_top n⟩)).inter_right
        (isClosed_singleton.preimage hp)
    have hdir : Directed (· ⊇ ·) F := fun m n =>
      ⟨max m n, hanti (le_max_left m n), hanti (le_max_right m n)⟩
    have hnonempty : (⋂ n, F n).Nonempty :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        F hdir hne hcp hcl
    obtain ⟨z, hz⟩ := hnonempty
    have hzw : p z = w := (mem_iInter.mp hz 0).2
    have hzc : σ z ≤ c := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt
        (by exact_mod_cast hε.ne' : (ε : ℝ≥0∞) ≠ 0)
      have hn1 : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (ε : ℝ≥0∞) := by
        refine le_of_lt (lt_of_le_of_lt ?_ hn)
        exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)
      exact le_trans
        (show σ z ≤ c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ from (mem_iInter.mp hz n).1)
        (add_le_add le_rfl hn1)
    exact ⟨z, hzc, hzw⟩
  · rintro ⟨z, hz, rfl⟩
    exact (infProj_le p σ z).trans hz

/-- The infimum in an exact marginalization is attained wherever finite. -/
theorem exists_infProj_attained [T1Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c})
    {ν : W} (hν : infProj p σ ν ≠ ⊤) :
    ∃ z, p z = ν ∧ σ z = infProj p σ ν := by
  obtain ⟨z, hz, hzν⟩ : ν ∈ p '' {z | σ z ≤ infProj p σ ν} := by
    rw [← sublevel_infProj_eq hp hσ hcpt hν]
    show infProj p σ ν ≤ infProj p σ ν
    exact le_rfl
  exact ⟨z, hzν, le_antisymm hz (hzν ▸ infProj_le p σ z)⟩

/-- The certificate class is closed under marginalization: the
inf-projection of an inf-compact lsc penalty has compact sublevels. -/
theorem isCompact_sublevel_infProj [T1Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c})
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsCompact {w | infProj p σ w ≤ c} := by
  rw [sublevel_infProj_eq hp hσ hcpt hc]
  exact (hcpt c hc).image hp

/-- The inf-projection of an inf-compact lsc penalty is again lsc. -/
theorem lowerSemicontinuous_infProj [T2Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c}) :
    LowerSemicontinuous (infProj p σ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · convert isClosed_univ
    ext w
    simp [mem_preimage, mem_Iic]
  · have : infProj p σ ⁻¹' Iic y = {w | infProj p σ w ≤ y} := rfl
    rw [this]
    exact (isCompact_sublevel_infProj hp hσ hcpt hy).isClosed

end Exact

/-! ## Prokhorov consumption: tightness certificates give compact sublevels -/

section Tight

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MetricSpace 𝓧] [BorelSpace 𝓧]

/-- On a probability-measure carrier, a lower semicontinuous penalty with
uniformly tight sublevels has compact sublevels (Prokhorov): tightness
certificates are inf-compactness certificates. -/
theorem isCompact_sublevel_of_isTightMeasureSet
    {σ : ProbabilityMeasure 𝓧 → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    {c : ℝ≥0∞}
    (ht : IsTightMeasureSet
      {((μ : ProbabilityMeasure 𝓧) : Measure 𝓧) | μ ∈ {ν | σ ν ≤ c}}) :
    IsCompact {ν | σ ν ≤ c} := by
  have hcl : IsClosed {ν : ProbabilityMeasure 𝓧 | σ ν ≤ c} :=
    hσ.isClosed_preimage c
  have := isCompact_closure_of_isTightMeasureSet ht
  rwa [hcl.closure_eq] at this

variable {𝓨 : Type*} [MeasurableSpace 𝓨] [MetricSpace 𝓨] [BorelSpace 𝓨]
variable [SecondCountableTopology 𝓧] [SecondCountableTopology 𝓨]

/-- The marginal (pushforward) map of probability measures along the first
coordinate. -/
noncomputable def margFst :
    ProbabilityMeasure (𝓧 × 𝓨) → ProbabilityMeasure 𝓧 :=
  fun ρ => ρ.map (f := Prod.fst) continuous_fst.measurable.aemeasurable

theorem continuous_margFst :
    Continuous (margFst (𝓧 := 𝓧) (𝓨 := 𝓨)) :=
  ProbabilityMeasure.continuous_map continuous_fst

/-- **Exact marginalization on Polish carriers, under a tightness
certificate.**  If a lower semicontinuous penalty on the joint carrier
has uniformly tight sublevels, then hiding the second coordinate is
exact: the sublevels of the marginalized penalty are the pushforward
images of the sublevels, the marginalized penalty is again lsc with
compact sublevels, and the infimum is attained wherever finite. -/
theorem sublevel_infProj_margFst_eq
    {σ : ProbabilityMeasure (𝓧 × 𝓨) → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (ht : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsTightMeasureSet
      {((ρ : ProbabilityMeasure (𝓧 × 𝓨)) : Measure (𝓧 × 𝓨)) | ρ ∈ {ν | σ ν ≤ c}})
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    {w | infProj margFst σ w ≤ c} = margFst '' {ρ | σ ρ ≤ c} :=
  sublevel_infProj_eq continuous_margFst hσ
    (fun c hc => isCompact_sublevel_of_isTightMeasureSet hσ (ht c hc)) hc

end Tight

/-! ## The witness: escaping mass defeats lower semicontinuity -/

section Witness

/-- The escaping-mass family on `ℕ` (the point `0` playing the cemetery of
the subprobability chart): mass `1 - 1/(n+2)` at the live point `n + 2`,
the rest at the cemetery. -/
noncomputable def escapeMix (n : ℕ) : ProbabilityMeasure ℕ :=
  ⟨(1 - ((n : ℝ≥0∞) + 2)⁻¹) • (Measure.dirac (n + 2) : Measure ℕ)
      + ((n : ℝ≥0∞) + 2)⁻¹ • (Measure.dirac 0 : Measure ℕ), by
    constructor
    have hle : ((n : ℝ≥0∞) + 2)⁻¹ ≤ 1 :=
      ENNReal.inv_le_one.mpr (one_le_two.trans le_add_self)
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact tsub_add_cancel_of_le hle⟩

theorem escapeMix_toMeasure (n : ℕ) :
    (escapeMix n : Measure ℕ)
      = (1 - ((n : ℝ≥0∞) + 2)⁻¹) • (Measure.dirac (n + 2) : Measure ℕ)
        + ((n : ℝ≥0∞) + 2)⁻¹ • (Measure.dirac 0 : Measure ℕ) := rfl

/-- The live-mass coordinate: total mass away from the cemetery point. -/
noncomputable def liveMass (μ : ProbabilityMeasure ℕ) : ℝ≥0∞ :=
  (μ : Measure ℕ) {0}ᶜ

/-- Evaluation of probability measures at a clopen event is narrowly
continuous (both portmanteau polarities apply). -/
theorem continuous_measure_clopen {𝓧 : Type*} [MeasurableSpace 𝓧]
    [TopologicalSpace 𝓧] [OpensMeasurableSpace 𝓧] [HasOuterApproxClosed 𝓧]
    {s : Set 𝓧} (ho : IsOpen s) (hc : IsClosed s) :
    Continuous fun μ : ProbabilityMeasure 𝓧 => (μ : Measure 𝓧) s := by
  rw [continuous_iff_continuousAt]
  intro μ₀
  have h₁ : (μ₀ : Measure 𝓧) s
      ≤ (𝓝 μ₀).liminf fun μ : ProbabilityMeasure 𝓧 => (μ : Measure 𝓧) s :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id ho
  have h₂ : ((𝓝 μ₀).limsup fun μ : ProbabilityMeasure 𝓧 => (μ : Measure 𝓧) s)
      ≤ (μ₀ : Measure 𝓧) s :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hc
  exact tendsto_of_le_liminf_of_limsup_le h₁ h₂

theorem continuous_liveMass : Continuous liveMass :=
  continuous_measure_clopen (isOpen_discrete _) (isClosed_discrete _)

theorem liveMass_escapeMix (n : ℕ) :
    liveMass (escapeMix n) = 1 - ((n : ℝ≥0∞) + 2)⁻¹ := by
  have h2 : (n + 2 : ℕ) ∈ ({0}ᶜ : Set ℕ) := by simp
  have h0 : (0 : ℕ) ∉ ({0}ᶜ : Set ℕ) := by simp
  simp [liveMass, escapeMix_toMeasure, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.compl (measurableSet_singleton 0)),
    Set.indicator_of_mem h2, Set.indicator_of_notMem h0]

/-- Singleton evaluation of the escaping family at a fixed live point
eventually vanishes. -/
theorem eventually_escapeMix_singleton_eq_zero {ms : ℕ → ℕ}
    (hms : Tendsto ms atTop atTop) (j : ℕ) (hj : j ≠ 0) :
    ∀ᶠ k in atTop, (escapeMix (ms k) : Measure ℕ) {j} = 0 := by
  filter_upwards [hms.eventually_gt_atTop j] with k hk
  have hjne : (ms k + 2 : ℕ) ∉ ({j} : Set ℕ) := by
    simp only [Set.mem_singleton_iff]
    omega
  have h0ne : (0 : ℕ) ∉ ({j} : Set ℕ) := by
    simpa using (Ne.symm hj)
  simp [escapeMix_toMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton j),
    Set.indicator_of_notMem hjne, Set.indicator_of_notMem h0ne]

/-- Evaluation of the escaping family at the cemetery point. -/
theorem escapeMix_apply_cemetery (n : ℕ) :
    (escapeMix n : Measure ℕ) {0} = ((n : ℝ≥0∞) + 2)⁻¹ := by
  have h1 : (n + 2 : ℕ) ∉ ({0} : Set ℕ) := by simp
  have h0 : (0 : ℕ) ∈ ({0} : Set ℕ) := rfl
  simp [escapeMix_toMeasure, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton 0),
    Set.indicator_of_notMem h1, Set.indicator_of_mem h0]

/-- The cemetery weight of the escaping family vanishes in the limit. -/
theorem tendsto_escapeMix_cemetery {ms : ℕ → ℕ} (hms : Tendsto ms atTop atTop) :
    Tendsto (fun k => (escapeMix (ms k) : Measure ℕ) {0}) atTop (𝓝 0) := by
  simp only [escapeMix_apply_cemetery]
  have htop : Tendsto (fun k => ((ms k : ℝ≥0∞) + 2)) atTop (𝓝 ⊤) := by
    have h := (ENNReal.tendsto_nat_nhds_top).comp hms
    simpa using h.add (tendsto_const_nhds (x := (2 : ℝ≥0∞)))
  simpa using tendsto_inv_iff.2 htop

/-- Along any index family escaping to infinity, the escaping-mass
measures have no narrow limit: any candidate limit annihilates every
singleton, hence the whole space, contradicting unit mass.  (The
σ-additivity refusal.) -/
theorem not_tendsto_escapeMix_atTop {ms : ℕ → ℕ}
    (hms : Tendsto ms atTop atTop) (ν : ProbabilityMeasure ℕ) :
    ¬ Tendsto (fun k => escapeMix (ms k)) atTop (𝓝 ν) := by
  intro h
  have hsing : ∀ j : ℕ, (ν : Measure ℕ) {j} = 0 := by
    intro j
    have hev : Tendsto (fun k => (escapeMix (ms k) : Measure ℕ) {j}) atTop
        (𝓝 ((ν : Measure ℕ) {j})) :=
      ((continuous_measure_clopen (isOpen_discrete _)
        (isClosed_discrete _)).tendsto ν).comp h
    rcases eq_or_ne j 0 with rfl | hj
    · exact tendsto_nhds_unique hev (tendsto_escapeMix_cemetery hms)
    · refine tendsto_nhds_unique hev ?_
      exact Tendsto.congr'
        ((eventually_escapeMix_singleton_eq_zero hms j hj).mono
          fun k hk => hk.symm) tendsto_const_nhds
  have huniv : (ν : Measure ℕ) univ = 0 := by
    rw [← Set.iUnion_of_singleton ℕ]
    exact measure_iUnion_null hsing
  exact one_ne_zero ((measure_univ (μ := (ν : Measure ℕ))).symm.trans huniv)

/-- The escaping-mass family is narrowly closed: a convergent sequence in
it is eventually confined to finitely many members (else its indices
escape and the σ-additivity refusal applies), and then some member
recurs. -/
theorem isClosed_range_escapeMix : IsClosed (Set.range escapeMix) := by
  refine IsSeqClosed.isClosed ?_
  intro x ν hx hlim
  choose m hm using hx
  by_cases hfreq : ∀ B : ℕ, ∃ᶠ k in atTop, B < m k
  · exfalso
    obtain ⟨φ, hφ, hφm⟩ := Filter.extraction_forall_of_frequently hfreq
    have hesc : Tendsto (fun k => m (φ k)) atTop atTop :=
      tendsto_atTop_mono (fun k => (hφm k).le) tendsto_id
    refine not_tendsto_escapeMix_atTop hesc ν ?_
    have : (fun k => escapeMix (m (φ k))) = x ∘ φ := by
      funext k
      exact hm (φ k)
    rw [this]
    exact hlim.comp hφ.tendsto_atTop
  · push_neg at hfreq
    obtain ⟨B, hB⟩ := hfreq
    have hinf : {k | m k ≤ B}.Infinite := by
      have hfin : {k | ¬ m k ≤ B}.Finite := by
        rw [← Filter.eventually_cofinite, Nat.cofinite_eq_atTop]
        exact hB
      have h := hfin.infinite_compl
      have heq : {k | ¬ m k ≤ B}ᶜ = {k | m k ≤ B} := by
        ext k
        simp
      rwa [heq] at h
    have hval : ∃ v, v ≤ B ∧ {k | m k = v}.Infinite := by
      by_contra hcon
      push_neg at hcon
      have hsub : {k | m k ≤ B} ⊆ ⋃ v ∈ Finset.range (B + 1), {k | m k = v} := by
        intro k hk
        simp only [Set.mem_iUnion]
        exact ⟨m k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩
      exact hinf (Set.Finite.subset
        (Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet
          fun v hv => hcon v (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)))
        hsub)
    obtain ⟨v, -, hvinf⟩ := hval
    obtain ⟨φ, hφ, hφv⟩ := Filter.extraction_of_frequently_atTop
      ((Nat.frequently_atTop_iff_infinite).mpr hvinf)
    have hconst : (x ∘ φ) = fun _ => escapeMix v := by
      funext k
      rw [Function.comp_apply, ← hm (φ k), hφv k]
    have hxφ : Tendsto (x ∘ φ) atTop (𝓝 ν) := hlim.comp hφ.tendsto_atTop
    rw [hconst] at hxφ
    exact ⟨v, (tendsto_nhds_unique tendsto_const_nhds hxφ)⟩

/-- The visible values of the escaping family accumulate at `1`… -/
theorem tendsto_liveMass_escapeMix :
    Tendsto (fun n => liveMass (escapeMix n)) atTop (𝓝 1) := by
  simp only [liveMass_escapeMix]
  have h0 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 2)⁻¹) atTop (𝓝 0) := by
    have h := tendsto_escapeMix_cemetery (ms := id) tendsto_id
    simpa only [escapeMix_apply_cemetery, id_eq] using h
  have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h0
    (Or.inl ENNReal.one_ne_top)
  simpa using h

/-- …but no member attains a visible value of `1`. -/
theorem liveMass_escapeMix_lt_one (n : ℕ) : liveMass (escapeMix n) < 1 := by
  rw [liveMass_escapeMix]
  refine ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_
  exact ENNReal.inv_ne_zero.mpr
    (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.ofNat_ne_top⟩)

/-- The visible image of the (closed) escaping family is not closed. -/
theorem not_isClosed_image_liveMass :
    ¬ IsClosed (liveMass '' Set.range escapeMix) := by
  intro hcl
  have hmem : ∀ n, liveMass (escapeMix n) ∈ liveMass '' Set.range escapeMix :=
    fun n => ⟨escapeMix n, ⟨n, rfl⟩, rfl⟩
  have h1 : (1 : ℝ≥0∞) ∈ liveMass '' Set.range escapeMix :=
    hcl.mem_of_tendsto tendsto_liveMass_escapeMix
      (Eventually.of_forall hmem)
  obtain ⟨μ, ⟨n, rfl⟩, hμ⟩ := h1
  exact absurd hμ (liveMass_escapeMix_lt_one n).ne

/-- **Marginalization does not preserve lower semicontinuity.**  On the
subprobability carrier over `ℕ` (presented as probability measures with
cemetery point `0`) there is a lower semicontinuous penalty whose
marginalization along the live-mass coordinate is not lower
semicontinuous: the wall of the escaping-mass family.  The visible
values accumulate at `1` while the witnessing mass escapes along the
hidden coordinate. -/
theorem exists_lowerSemicontinuous_not_lowerSemicontinuous_infProj :
    ∃ σ : ProbabilityMeasure ℕ → ℝ≥0∞, LowerSemicontinuous σ ∧
      ¬ LowerSemicontinuous (infProj liveMass σ) := by
  refine ⟨charFn (Set.range escapeMix),
    lowerSemicontinuous_charFn_iff.mpr isClosed_range_escapeMix, ?_⟩
  rw [infProj_charFn, lowerSemicontinuous_charFn_iff]
  exact not_isClosed_image_liveMass

end Witness

end SuFunctor.Universe
