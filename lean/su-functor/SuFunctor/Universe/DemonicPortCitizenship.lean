import SuFunctor.Universe.ThinningAbsorption
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Polynomial

/-! # Demonic-port citizenship: compact imprecision lands in the house class

The imprecise tier's recommended composite shape takes
**demonic parameter ports** as its semantics: a designated roster of
unsampled inputs ranging over a declared region `Θ`, with denotation the
*set* `{⟦h_θ⟧ : θ ∈ Θ}` of precise denotations — a candidate credal body.
This module mechanizes the citizenship lemma at that statement, at the
finite-outcome stratum:

* `isCredalBody_scaleSegment_of_isCompact` — the engine: the radial
  embedding `scaleSegment K` of any nonempty **compact** `K` is a credal
  body (nonempty, closed, radial).  No convexity hypothesis anywhere.
* `isCredalBody_scaleSegment_image` — **the citizenship lemma**: a
  demonic-port image `f '' Θ` of a nonempty compact region under a map
  continuous on it lands, radially embedded, in `IsCredalBody`.  The
  intended instances are piecewise-polynomial parameter-to-denotation
  maps on compact ω-semialgebraic regions: the ω-SA region enters as its
  compactness, the piecewise-polynomial map as its continuity (per
  piece), and nothing else about either structure is used or claimed.
* `isCredalBody_scaleSegment_iUnion_image` — the piecewise face:
  finitely many compact pieces, one continuous map per piece, the union
  image lands.  (With `isCredalBody_iUnion`: the house class is closed
  under finite nonempty unions.)
* `isCredalBody_scaleSegment_polyImage` — the polynomial face at a
  scalar parameter (the interval-rate case): coordinates given by
  `Polynomial.eval` land via `Polynomial.continuous`.
* `sep_mass_one_scaleSegment_image` / `not_isCredalBody_image_of_fullMass`
  — the packaging honesty pair, specialized to port images from the
  thinning-absorption module's general lemmas: the full-mass slice of
  the radial embedding recovers the raw image exactly (nothing is lost),
  and the raw image of full-mass denotations is *never* itself a credal
  body (the embedding is required, not decorative).
* `parabMap` and its theorems — **convexity is a side condition, never
  the theorem**, made mechanical: an explicit quadratic curve
  `θ ↦ (θ, θ², 1 − θ − θ²)` on `[0, ½]` whose radially embedded image
  *is* a credal body (`isCredalBody_scaleSegment_parabImage`) and is
  *not* a convex body (`not_convexBody_scaleSegment_parabImage`), so the
  citizenship lemma's conclusion cannot be strengthened to
  `IsConvexCredalBody` (`not_isConvexCredalBody_scaleSegment_parabImage`).
  The SU's citizenship criterion is lower semicontinuity and nothing
  else: non-convex credal bodies are deliberate citizens.
* `isCredalBody_scaleSegment_thinFamily_of_isCompact` and its rate face
  — the composite shape at the jump tier: absorbed families of compact
  (NOT necessarily convex) rate regions and kernel bodies land in the
  house class.  The convexity-free complement of the Cozman-route
  landings in `ThinningAbsorption` — the split, precisely:
  general demonic-port families land as credal bodies; convexity is
  what the interval sugar *adds* (the classical Cozman/Richardson
  upgrades), not what citizenship costs.
-/

namespace SuFunctor.Universe.DemonicPort

open CredalPoset
open scoped Topology

variable {V : Type*} [Fintype V]

/-! ## The engine: radial embeddings of compact sets are credal bodies -/

/-- The radial embedding of any set is radial: scaling composes with
scaling (`s • t • x = (s*t) • x`). -/
theorem isRadial_scaleSegment (K : Set (BelState V)) :
    IsRadial (scaleSegment K) := by
  rintro z ⟨x, hx, t, h0, h1, rfl⟩ s hs0 hs1
  refine ⟨x, hx, s * t, mul_nonneg hs0 h0, by nlinarith, ?_⟩
  exact Subtype.ext (by simp [BelState.coe_scale, smul_smul])

/-- The radial embedding of a compact set is compact: it is the image
of `[0,1] ×ˢ K` under the (jointly continuous) scaling action, read on
the value side of the carrier subtype. -/
theorem isCompact_scaleSegment {K : Set (BelState V)} (hcp : IsCompact K) :
    IsCompact (scaleSegment K) := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  have him : Subtype.val '' scaleSegment K
      = (fun q : ℝ × (V → ℝ) => q.1 • q.2)
        '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Subtype.val '' K)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, t, h0, h1, rfl⟩, rfl⟩
      exact ⟨(t, (x : V → ℝ)), ⟨⟨h0, h1⟩, ⟨x, hx, rfl⟩⟩,
        (BelState.coe_scale t h0 h1 x).symm⟩
    · rintro ⟨⟨t, w⟩, ⟨⟨h0, h1⟩, ⟨x, hx, rfl⟩⟩, rfl⟩
      exact ⟨BelState.scale t h0 h1 x, ⟨x, hx, t, h0, h1, rfl⟩,
        BelState.coe_scale t h0 h1 x⟩
  rw [him]
  exact (isCompact_Icc.prod (hcp.image continuous_subtype_val)).image
    (continuous_fst.smul continuous_snd)

/-- **The engine**: the radial embedding of a nonempty compact set of
subprobability states is a credal body — nonempty, closed, radial.  No
convexity is imposed or needed: citizenship is lower semicontinuity and
nothing else. -/
theorem isCredalBody_scaleSegment_of_isCompact {K : Set (BelState V)}
    (hne : K.Nonempty) (hcp : IsCompact K) :
    IsCredalBody (scaleSegment K) := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨⟨x, subset_scaleSegment K hx⟩,
    (isCompact_scaleSegment hcp).isClosed, isRadial_scaleSegment K⟩

/-! ## The citizenship lemma -/

/-- **Demonic-port citizenship**: the image of a nonempty compact
region `Θ` under a parameter-to-denotation map continuous on `Θ` lands,
radially embedded, in the house class `IsCredalBody`.

This is the citizenship lemma at the imprecise tier's composite shape:
`f '' Θ` is the denotation `{⟦h_θ⟧ : θ ∈ Θ}` of a demonic-port family.
The intended instances are piecewise-polynomial maps on compact
ω-semialgebraic regions — the region enters as its compactness and the
map as its continuity; no ω-SA or polynomial structure is used, and
**convexity of the image is deliberately not claimed** (it fails in
general: `not_convexBody_scaleSegment_parabImage`). -/
theorem isCredalBody_scaleSegment_image {P : Type*} [TopologicalSpace P]
    {Θ : Set P} {f : P → BelState V}
    (hne : Θ.Nonempty) (hcp : IsCompact Θ) (hf : ContinuousOn f Θ) :
    IsCredalBody (scaleSegment (f '' Θ)) :=
  isCredalBody_scaleSegment_of_isCompact (hne.image f)
    (hcp.image_of_continuousOn hf)

/-! ## The piecewise face -/

/-- The house class is closed under finite nonempty unions.  (Unions of
closeds are closed only finitely; radiality and nonemptiness are free.) -/
theorem isCredalBody_iUnion {ι : Type*} [Finite ι] [Nonempty ι]
    {S : ι → Set (BelState V)} (h : ∀ i, IsCredalBody (S i)) :
    IsCredalBody (⋃ i, S i) := by
  refine ⟨?_, isClosed_iUnion_of_finite fun i => (h i).2.1, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨x, hx⟩ := (h i).1
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩
  · intro x hx t h0 h1
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, (h i).2.2 x hxi t h0 h1⟩

/-- The radial embedding commutes with unions. -/
theorem scaleSegment_iUnion {ι : Type*} (K : ι → Set (BelState V)) :
    scaleSegment (⋃ i, K i) = ⋃ i, scaleSegment (K i) := by
  ext z
  constructor
  · rintro ⟨x, hx, t, h0, h1, rfl⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, x, hxi, t, h0, h1, rfl⟩
  · intro hz
    obtain ⟨i, x, hxi, t, h0, h1, rfl⟩ := Set.mem_iUnion.mp hz
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hxi⟩, t, h0, h1, rfl⟩

/-- **The piecewise face of citizenship**: finitely many compact pieces,
one map per piece continuous on its piece — the radially embedded total
image lands in the house class.  This is the honest "piecewise" content
of "piecewise-polynomial" at first mechanization: pieces are glued by
union, and the class is closed under finite unions. -/
theorem isCredalBody_scaleSegment_iUnion_image {ι : Type*} [Finite ι]
    [Nonempty ι] {P : Type*} [TopologicalSpace P]
    {Θ : ι → Set P} {f : ι → P → BelState V}
    (hne : ∀ i, (Θ i).Nonempty) (hcp : ∀ i, IsCompact (Θ i))
    (hf : ∀ i, ContinuousOn (f i) (Θ i)) :
    IsCredalBody (⋃ i, scaleSegment (f i '' Θ i)) :=
  isCredalBody_iUnion fun i =>
    isCredalBody_scaleSegment_image (hne i) (hcp i) (hf i)

/-! ## The polynomial face (scalar parameter: the interval-rate case) -/

/-- Citizenship for polynomial parameter-to-denotation data at a scalar
parameter: if on `Θ` every coordinate of the denotation is the
evaluation of a real polynomial in the port parameter, the radially
embedded image lands in the house class.  (The multivariate/ω-SA face
needs no separate statement: `isCredalBody_scaleSegment_image` already
takes any topological parameter space.) -/
theorem isCredalBody_scaleSegment_polyImage {Θ : Set ℝ}
    {f : ℝ → BelState V} {p : V → Polynomial ℝ}
    (hne : Θ.Nonempty) (hcp : IsCompact Θ)
    (hf : ∀ θ ∈ Θ, ∀ v, (f θ : V → ℝ) v = (p v).eval θ) :
    IsCredalBody (scaleSegment (f '' Θ)) := by
  refine isCredalBody_scaleSegment_image hne hcp ?_
  rw [continuousOn_iff_continuous_restrict,
    Topology.IsInducing.subtypeVal.continuous_iff]
  have hval : (Subtype.val ∘ Θ.restrict f)
      = fun (θ : Θ) (v : V) => (p v).eval θ.1 := by
    funext θ v
    exact hf θ.1 θ.2 v
  rw [hval]
  exact continuous_pi fun v =>
    (Polynomial.continuous (p v)).comp continuous_subtype_val

/-! ## Packaging honesty: recovery is exact, and the embedding is required -/

/-- **Slice recovery at the port statement**: for a family of full-mass
denotations, the full-mass slice of the radial embedding is the raw
image itself — the credal packaging loses nothing. -/
theorem sep_mass_one_scaleSegment_image {P : Type*} {Θ : Set P}
    {f : P → BelState V} (hmass : ∀ θ ∈ Θ, (f θ).mass = 1) :
    {x ∈ scaleSegment (f '' Θ) | x.mass = 1} = f '' Θ :=
  Thinning.sep_mass_one_scaleSegment (by rintro x ⟨θ, hθ, rfl⟩; exact hmass θ hθ)

/-- **The embedding is required, not decorative**: a nonempty image of
full-mass denotations is never itself a credal body — it cannot be
radial (scaling any member by `½` halves its mass). -/
theorem not_isCredalBody_image_of_fullMass {P : Type*} {Θ : Set P}
    {f : P → BelState V} (hne : Θ.Nonempty)
    (hmass : ∀ θ ∈ Θ, (f θ).mass = 1) :
    ¬ IsCredalBody (f '' Θ) := fun h =>
  Thinning.not_isRadial_of_forall_mass_eq_one (hne.image f)
    (by rintro x ⟨θ, hθ, rfl⟩; exact hmass θ hθ) h.2.2

/-! ## The non-convex witness: the side condition is not a theorem

An explicit quadratic port map on one scalar parameter.  The curve
`θ ↦ (θ, θ², 1 − θ − θ²)` on `Θ = [0, ½]` is a bona-fide demonic-port
image (compact region, polynomial coordinates, full mass), its radial
embedding is a credal body by the citizenship lemma — and it is **not**
a convex body: the midpoint of the endpoint denotations has mass one,
so it could only be a curve point, and the curve's first two
coordinates refuse (`t·θ = ¼` and `t·θ² = ⅛` force `t = 1, θ = ¼`,
whose second coordinate is `¹⁄₁₆ ≠ ⅛`). -/

/-- Clamp to `[0, ½]` (keeps the witness map total and continuous). -/
noncomputable def parabClamp (θ : ℝ) : ℝ := max 0 (min θ (1 / 2))

theorem parabClamp_nonneg (θ : ℝ) : 0 ≤ parabClamp θ := le_max_left _ _

theorem parabClamp_le_half (θ : ℝ) : parabClamp θ ≤ 1 / 2 :=
  max_le (by norm_num) (min_le_right _ _)

theorem parabClamp_eq_of_mem {θ : ℝ} (h : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    parabClamp θ = θ := by
  unfold parabClamp
  rw [min_eq_left h.2, max_eq_right h.1]

theorem continuous_parabClamp : Continuous parabClamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The value side of the quadratic witness curve. -/
noncomputable def parabVal (θ : ℝ) : Fin 3 → ℝ := fun v =>
  if v.val = 0 then parabClamp θ
  else if v.val = 1 then parabClamp θ ^ 2
  else 1 - parabClamp θ - parabClamp θ ^ 2

theorem parabVal_zero (θ : ℝ) : parabVal θ 0 = parabClamp θ := rfl

theorem parabVal_one (θ : ℝ) : parabVal θ 1 = parabClamp θ ^ 2 := rfl

theorem parabVal_two (θ : ℝ) :
    parabVal θ 2 = 1 - parabClamp θ - parabClamp θ ^ 2 := rfl

theorem parabVal_mem (θ : ℝ) : parabVal θ ∈ belCarrier (Fin 3) := by
  have h0 := parabClamp_nonneg θ
  have h1 := parabClamp_le_half θ
  constructor
  · intro v
    by_cases hv0 : v.val = 0
    · simp only [parabVal, if_pos hv0]
      exact h0
    · by_cases hv1 : v.val = 1
      · simp only [parabVal, if_neg hv0, if_pos hv1]
        positivity
      · simp only [parabVal, if_neg hv0, if_neg hv1]
        nlinarith
  · rw [Fin.sum_univ_three, parabVal_zero, parabVal_one, parabVal_two]
    linarith

/-- The quadratic witness curve, as a map into the carrier. -/
noncomputable def parabMap (θ : ℝ) : BelState (Fin 3) :=
  ⟨parabVal θ, parabVal_mem θ⟩

@[simp] theorem coe_parabMap (θ : ℝ) :
    ((parabMap θ : BelState (Fin 3)) : Fin 3 → ℝ) = parabVal θ := rfl

theorem continuous_parabVal : Continuous parabVal := by
  apply continuous_pi
  intro v
  by_cases hv0 : v.val = 0
  · simp only [parabVal, if_pos hv0]
    exact continuous_parabClamp
  · by_cases hv1 : v.val = 1
    · simp only [parabVal, if_neg hv0, if_pos hv1]
      exact continuous_parabClamp.pow 2
    · simp only [parabVal, if_neg hv0, if_neg hv1]
      exact (continuous_const.sub continuous_parabClamp).sub
        (continuous_parabClamp.pow 2)

theorem continuous_parabMap : Continuous parabMap :=
  continuous_parabVal.subtype_mk parabVal_mem

theorem mass_parabMap (θ : ℝ) : (parabMap θ).mass = 1 := by
  show ∑ v, parabVal θ v = 1
  rw [Fin.sum_univ_three, parabVal_zero, parabVal_one, parabVal_two]
  ring

/-- The witness is a bona-fide citizen: its radially embedded image is
a credal body, by the citizenship lemma. -/
theorem isCredalBody_scaleSegment_parabImage :
    IsCredalBody (scaleSegment (parabMap '' Set.Icc (0 : ℝ) (1 / 2))) :=
  isCredalBody_scaleSegment_image ⟨0, le_refl 0, by norm_num⟩
    isCompact_Icc continuous_parabMap.continuousOn

/-- **The witness is not a convex body**: the midpoint of the endpoint
denotations escapes the embedded image. -/
theorem not_convexBody_scaleSegment_parabImage :
    ¬ ConvexBody (scaleSegment (parabMap '' Set.Icc (0 : ℝ) (1 / 2))) := by
  intro hcv
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_refl 0, by norm_num⟩
  have hhIcc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_refl _⟩
  have ha : ((parabMap 0 : BelState (Fin 3)) : Fin 3 → ℝ)
      ∈ carrierImage (scaleSegment (parabMap '' Set.Icc (0 : ℝ) (1 / 2))) :=
    mem_carrierImage (subset_scaleSegment _ ⟨0, h0Icc, rfl⟩)
  have hb : ((parabMap (1 / 2) : BelState (Fin 3)) : Fin 3 → ℝ)
      ∈ carrierImage (scaleSegment (parabMap '' Set.Icc (0 : ℝ) (1 / 2))) :=
    mem_carrierImage (subset_scaleSegment _ ⟨1 / 2, hhIcc, rfl⟩)
  have hmid := hcv ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  obtain ⟨z, hzS, hzeq⟩ := hmid
  obtain ⟨x, hxim, t, ht0, ht1, rfl⟩ := hzS
  obtain ⟨θ, hθ, rfl⟩ := hxim
  have hcl : parabClamp θ = θ := parabClamp_eq_of_mem hθ
  have hc0 : parabClamp 0 = 0 := parabClamp_eq_of_mem ⟨le_refl 0, by norm_num⟩
  have hch : parabClamp (1 / 2) = 1 / 2 :=
    parabClamp_eq_of_mem ⟨by norm_num, le_refl _⟩
  simp only [BelState.coe_scale, coe_parabMap] at hzeq
  have c0 := congrFun hzeq 0
  have c1 := congrFun hzeq 1
  have c2 := congrFun hzeq 2
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    parabVal_zero, parabVal_one, parabVal_two, hcl, hc0, hch] at c0 c1 c2
  -- c0 : t * θ = 1/2 * 0 + 1/2 * (1/2)
  -- c1 : t * θ^2 = 1/2 * 0^2 + 1/2 * (1/2)^2
  -- c2 : t * (1 - θ - θ^2) = 1/2 * (1 - 0 - 0^2) + 1/2 * (1 - 1/2 - (1/2)^2)
  norm_num at c0 c1 c2
  have hsum : t * θ + t * θ ^ 2 + t * (1 - θ - θ ^ 2) = t := by ring
  have hT : t = 1 := by linarith
  rw [hT, one_mul] at c0 c1
  -- c0 : θ = 1/4, c1 : θ^2 = 1/8
  rw [c0] at c1
  norm_num at c1

/-- The citizenship lemma's conclusion cannot be strengthened: the
witness's embedded image is a credal body but **not** a convex credal
body.  Convexity is a side condition some demonic-port families satisfy
(e.g. the interval sugar's Cozman landings), never part of citizenship. -/
theorem not_isConvexCredalBody_scaleSegment_parabImage :
    ¬ IsConvexCredalBody (scaleSegment (parabMap '' Set.Icc (0 : ℝ) (1 / 2))) :=
  fun h => not_convexBody_scaleSegment_parabImage h.2

/-- The raw witness image (unembedded) is not a credal body — the
honest-negative instance at the witness. -/
theorem not_isCredalBody_parabImage_raw :
    ¬ IsCredalBody (parabMap '' Set.Icc (0 : ℝ) (1 / 2)) :=
  not_isCredalBody_image_of_fullMass ⟨0, le_refl 0, by norm_num⟩
    fun θ _ => mass_parabMap θ

/-! ## The composite shape at the jump tier: convexity-free landings

The Cozman-route landings in `ThinningAbsorption` require convex data
(`Convex ℝ M`, `ConvexBody K`) — the interval sugar's ergonomics.  The
citizenship engine lands the same absorbed families from compactness
alone, which is the general demonic-port shape (a) of the composite
recommendation: an arbitrary compact family of jump data is received,
convex or not. -/

/-- Citizenship for absorbed families at the composite shape: closed
retention-probability region, closed kernel body, both nonempty —
**no convexity** — and the radially embedded absorbed family is a
credal body. -/
theorem isCredalBody_scaleSegment_thinFamily_of_isCompact {M : Set ℝ}
    {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMcl : IsClosed M) (hMsub : M ⊆ Set.Icc 0 1)
    (hKne : K.Nonempty) (hKcl : IsClosed K) :
    IsCredalBody (scaleSegment (Thinning.thinFamily M K)) :=
  isCredalBody_scaleSegment_of_isCompact
    (Thinning.thinFamily_nonempty hMne hMsub hKne)
    (Thinning.isCompact_thinFamily hMcl hMsub hKcl)

/-- The rate face: a closed rate region inside `[0, Λ]` at a positive
majorant, a closed kernel body — no convexity — and the radially
embedded absorbed family is a credal body. -/
theorem isCredalBody_scaleSegment_thinFamilyRate_of_isCompact
    {Lambda : ℝ} {R : Set ℝ} {K : Set (BelState V)}
    (hb : 0 < Lambda) (hRne : R.Nonempty) (hRcl : IsClosed R)
    (hR : R ⊆ Set.Icc 0 Lambda) (hKne : K.Nonempty) (hKcl : IsClosed K) :
    IsCredalBody (scaleSegment (Thinning.thinFamilyRate Lambda R K)) := by
  have hRcp : IsCompact R := IsCompact.of_isClosed_subset isCompact_Icc hRcl hR
  show IsCredalBody
    (scaleSegment (Thinning.thinFamily ((fun lam => lam / Lambda) '' R) K))
  refine isCredalBody_scaleSegment_thinFamily_of_isCompact
    (hRne.image _) ?_ ?_ hKne hKcl
  · exact (hRcp.image (continuous_id.div_const _)).isClosed
  · rintro p ⟨lam, hlam, rfl⟩
    exact ⟨div_nonneg (hR hlam).1 hb.le, (div_le_one hb).mpr (hR hlam).2⟩

end SuFunctor.Universe.DemonicPort
