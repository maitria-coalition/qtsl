import SuFunctor.Universe.CredalPoset.Defs
import Mathlib.Analysis.MeanInequalities

/-! # The credal-body poset: the inclusion theorems

`SuFunctor.Universe.CredalPoset.Defs` declares the seven classes and the
cheap bridges (T1, T3, T5).  This module proves the remaining positive
inclusions of the preregistered poset, and the headline bundle:

* **A1** (`PenaltyConvex.convexBody_compile`) — the workhorse: a convex
  penalty compiles to a convex body.  The mixture of two scaled points
  `γ₁ • μ₁`, `γ₂ • μ₂` re-polarizes as `m • μ*` with
  `m = a·γ₁ + b·γ₂` and `μ*` the `(t, 1−t)`-mixture of the directions at
  `t = a·γ₁/m`; penalty convexity bounds `grade` along `μ*` below by the
  weighted **geometric** mean of the endpoint grades, and the weighted
  AM–GM inequality on the *inverse* grades closes the harmonic-mean gap
  `m ≤ g₁ᵗ · g₂^{1−t}`.  (No `Nonempty V` needed: every compile member
  carries its own direction.)
* **T2** (`IsRichardsonBody.isConvexCredalBody`) — Richardson bodies are
  convex credal bodies (A1 + the compile dictionary).
* **T4** (`IsMVS.isUltra`) — pointwise-down hulls of finite sets are
  ultracontributions.  Closedness is the geometric leg: the down-hull's
  carrier image is exhibited as the continuous image of
  `(polytope) ×ˢ (unit box)` under coordinatewise rescaling, hence
  compact.
* **T6** (`IsCozman.isRichardsonBody`) — a classical credal set enters
  the Richardson class through the wall of its direction preimage:
  `compile (probWall (toBel ⁻¹' K)) = scaleSegment K`, and the wall of a
  (relatively) convex closed set is a convex lsc penalty.
* **T7** (the `isCredalBody` bundle) — **every named subclass lives
  inside the house class**: each of the six named classes maps into
  `IsCredalBody` (the convex class by `Defs`'s T1; the other five here,
  by composing the spine).
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

namespace CredalPoset

/-! ## Carrier-image bookkeeping -/

/-- A grade-bounded scaling of a direction lies in the body's carrier
image — the one-line membership constructor A1 uses on every branch. -/
theorem smul_mem_carrierImage_compile {f : ProbPenalty V} {c : ℝ}
    {μ : ProbState V} (h0 : 0 ≤ c) (hle : c ≤ grade (f μ)) :
    c • (μ : V → ℝ) ∈ carrierImage (compile f) :=
  ⟨scalePoint c h0 (hle.trans (grade_le_one _)) μ, ⟨μ, c, h0, hle, rfl⟩, rfl⟩

/-- Anything coordinatewise between `0` and a carrier member is a
carrier member. -/
theorem mem_belCarrier_of_le {x y : V → ℝ} (hy : y ∈ belCarrier V)
    (h0 : ∀ v, 0 ≤ x v) (hxy : x ≤ y) : x ∈ belCarrier V :=
  ⟨h0, le_trans (Finset.sum_le_sum fun v _ => hxy v) hy.2⟩

/-- The convex hull of a carrier image stays inside the carrier. -/
theorem convexHull_carrierImage_subset {S : Set (BelState V)} :
    convexHull ℝ (carrierImage S) ⊆ belCarrier V :=
  convexHull_min (fun _ ⟨x, _, hx⟩ => hx ▸ x.2) convex_belCarrier

/-! ## A1 — penalty convexity compiles to body convexity -/

/-- **A1, the workhorse**: the body of a convex penalty is convex.  At
strictly interior data the mixture `a • (γ₁ • μ₁) + b • (γ₂ • μ₂)`
re-polarizes as `m • μ*` with `m = a·γ₁ + b·γ₂`,
`μ* = mix t (1−t) μ₁ μ₂`, `t = a·γ₁/m`; then
`grade (f μ*) ≥ g₁ᵗ g₂^{1−t} ≥ m`, the first step by penalty convexity
(grades turn `+` into `·`, `grade_add`), the second by weighted AM–GM
applied to the inverse grades (`1/g₁ᵗg₂^{1−t} ≤ t/γ₁ + (1−t)/γ₂ = 1/m`).
Degenerate scales and endpoint weights short-circuit to a single ray. -/
theorem PenaltyConvex.convexBody_compile {f : ProbPenalty V}
    (hf : PenaltyConvex f) : ConvexBody (compile f) := by
  rintro x ⟨x', ⟨μ₁, γ₁, hγ₁0, hγ₁le, he₁⟩, rfl⟩
    y ⟨y', ⟨μ₂, γ₂, hγ₂0, hγ₂le, he₂⟩, rfl⟩ a b ha hb hab
  simp only [he₁, he₂, smul_smul]
  rcases hγ₁0.eq_or_lt with hγ₁ | hγ₁
  · -- `x` is the zero state: the mixture lives on the ray at `μ₂`
    rw [← hγ₁, mul_zero, zero_smul, zero_add]
    exact smul_mem_carrierImage_compile (mul_nonneg hb hγ₂0)
      ((mul_le_of_le_one_left hγ₂0 (by linarith)).trans hγ₂le)
  rcases hγ₂0.eq_or_lt with hγ₂ | hγ₂
  · -- `y` is the zero state: the mixture lives on the ray at `μ₁`
    rw [← hγ₂, mul_zero, zero_smul, add_zero]
    exact smul_mem_carrierImage_compile (mul_nonneg ha hγ₁0)
      ((mul_le_of_le_one_left hγ₁0 (by linarith)).trans hγ₁le)
  rcases ha.eq_or_lt with ha0 | ha0
  · -- endpoint weight `a = 0`
    have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_smul, zero_add, hb1, one_mul]
    exact smul_mem_carrierImage_compile hγ₂.le hγ₂le
  rcases hb.eq_or_lt with hb0 | hb0
  · -- endpoint weight `b = 0`
    have ha1 : a = 1 := by linarith
    rw [← hb0, zero_mul, zero_smul, add_zero, ha1, one_mul]
    exact smul_mem_carrierImage_compile hγ₁.le hγ₁le
  -- main case: `a`, `b`, `γ₁`, `γ₂` all strictly positive
  set m : ℝ := a * γ₁ + b * γ₂ with hm
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  set t : ℝ := a * γ₁ / m with ht
  have ht0 : 0 < t := by
    rw [ht]
    positivity
  have htm : m * t = a * γ₁ := by
    rw [ht, mul_comm m (a * γ₁ / m), div_mul_cancel₀ _ hm0.ne']
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hm0, hm]
    nlinarith [mul_pos hb0 hγ₂]
  have h1t0 : 0 < 1 - t := by linarith
  have h1t : m * (1 - t) = b * γ₂ := by
    rw [mul_sub, mul_one, htm, hm]
    ring
  have hst : t + (1 - t) = 1 := by ring
  -- the endpoint penalties are finite (their grades dominate positive scales)
  have hf₁ : f μ₁ ≠ ⊤ := by
    intro hc
    rw [hc, grade_top] at hγ₁le
    exact absurd hγ₁le (not_le.mpr hγ₁)
  have hf₂ : f μ₂ ≠ ⊤ := by
    intro hc
    rw [hc, grade_top] at hγ₂le
    exact absurd hγ₂le (not_le.mpr hγ₂)
  have hpc : f (ProbState.mix t (1 - t) ht0.le h1t0.le hst μ₁ μ₂)
      ≤ ENNReal.ofReal t * f μ₁ + ENNReal.ofReal (1 - t) * f μ₂ :=
    hf μ₁ μ₂ t (1 - t) ht0 h1t0 hst
  have hmul₁ : ENNReal.ofReal t * f μ₁ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf₁
  have hmul₂ : ENNReal.ofReal (1 - t) * f μ₂ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf₂
  -- the grade of the convexity bound is the weighted geometric mean
  have hgB : grade (ENNReal.ofReal t * f μ₁ + ENNReal.ofReal (1 - t) * f μ₂)
      = grade (f μ₁) ^ t * grade (f μ₂) ^ (1 - t) := by
    rw [grade_of_ne_top (ENNReal.add_ne_top.mpr ⟨hmul₁, hmul₂⟩),
      ENNReal.toReal_add hmul₁ hmul₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ht0.le, ENNReal.toReal_ofReal h1t0.le,
      neg_add, Real.exp_add, grade_of_ne_top hf₁, grade_of_ne_top hf₂,
      ← Real.exp_mul, ← Real.exp_mul,
      show -(t * (f μ₁).toReal) = -(f μ₁).toReal * t from by ring,
      show -((1 - t) * (f μ₂).toReal) = -(f μ₂).toReal * (1 - t) from by ring]
  -- the harmonic step: AM–GM on the inverse scales
  have hkey : m ≤ grade (f μ₁) ^ t * grade (f μ₂) ^ (1 - t) := by
    have hamgm : γ₁⁻¹ ^ t * γ₂⁻¹ ^ (1 - t) ≤ t * γ₁⁻¹ + (1 - t) * γ₂⁻¹ :=
      Real.geom_mean_le_arith_mean2_weighted ht0.le h1t0.le
        (inv_nonneg.mpr hγ₁.le) (inv_nonneg.mpr hγ₂.le) hst
    have hsum : t * γ₁⁻¹ + (1 - t) * γ₂⁻¹ = m⁻¹ := by
      apply mul_left_cancel₀ hm0.ne'
      rw [mul_add, ← mul_assoc, ← mul_assoc, htm, h1t,
        mul_inv_cancel₀ hm0.ne', mul_assoc, mul_inv_cancel₀ hγ₁.ne',
        mul_assoc, mul_inv_cancel₀ hγ₂.ne', mul_one, mul_one, hab]
    have hP : 0 < γ₁ ^ t * γ₂ ^ (1 - t) :=
      mul_pos (Real.rpow_pos_of_pos hγ₁ t) (Real.rpow_pos_of_pos hγ₂ (1 - t))
    have hinv : (γ₁ ^ t * γ₂ ^ (1 - t))⁻¹ ≤ m⁻¹ := by
      rw [mul_inv, ← Real.inv_rpow hγ₁.le, ← Real.inv_rpow hγ₂.le, ← hsum]
      exact hamgm
    calc m ≤ γ₁ ^ t * γ₂ ^ (1 - t) := (inv_le_inv₀ hP hm0).mp hinv
      _ ≤ grade (f μ₁) ^ t * grade (f μ₂) ^ (1 - t) :=
          mul_le_mul (Real.rpow_le_rpow hγ₁.le hγ₁le ht0.le)
            (Real.rpow_le_rpow hγ₂.le hγ₂le h1t0.le)
            (Real.rpow_nonneg hγ₂.le _) (Real.rpow_nonneg (grade_nonneg _) _)
  have hgrade : m ≤ grade (f (ProbState.mix t (1 - t) ht0.le h1t0.le hst μ₁ μ₂)) :=
    le_trans (hkey.trans_eq hgB.symm) (grade_anti hpc)
  have hcoe : m • ((ProbState.mix t (1 - t) ht0.le h1t0.le hst μ₁ μ₂ : ProbState V) : V → ℝ)
      = (a * γ₁) • (μ₁ : V → ℝ) + (b * γ₂) • (μ₂ : V → ℝ) := by
    rw [ProbState.coe_mix, smul_add, smul_smul, smul_smul, htm, h1t]
  rw [← hcoe]
  exact smul_mem_carrierImage_compile hm0.le hgrade

/-! ## T2 — Richardson bodies are convex credal bodies -/

/-- **T2**: Richardson bodies are convex credal bodies — nonempty by the
zero state, closed and radial by the compile dictionary, convex by A1. -/
theorem IsRichardsonBody.isConvexCredalBody [Nonempty V] {S : Set (BelState V)}
    (h : IsRichardsonBody S) : IsConvexCredalBody S := by
  obtain ⟨f, hconv, hlsc, rfl⟩ := h
  exact ⟨⟨⟨BelState.zero V, zero_mem_compile f⟩, isClosed_compile hlsc,
    isRadial_compile f⟩, hconv.convexBody_compile⟩

/-! ## T4 — pointwise-down hulls are ultracontributions -/

/-- Carrier images of finite sets are finite. -/
theorem finite_carrierImage (F : Finset (BelState V)) :
    (carrierImage (F : Set (BelState V))).Finite :=
  F.finite_toSet.image _

/-- Carrier-side membership in a pointwise-down hull: a carrier point
below some point of the spanned polytope. -/
theorem mem_carrierImage_ptwiseDownHull {F : Finset (BelState V)} {p : V → ℝ} :
    p ∈ carrierImage (ptwiseDownHull F)
      ↔ p ∈ belCarrier V
        ∧ ∃ y ∈ convexHull ℝ (carrierImage (F : Set (BelState V))), p ≤ y := by
  constructor
  · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    exact ⟨x.2, y, hy, hxy⟩
  · rintro ⟨hp, y, hy, hpy⟩
    exact ⟨⟨p, hp⟩, ⟨y, hy, hpy⟩, rfl⟩

/-- Down-hulls are convex: mixtures of dominated points are dominated by
the mixture of their dominators, which stays in the polytope. -/
theorem convexBody_ptwiseDownHull (F : Finset (BelState V)) :
    ConvexBody (ptwiseDownHull F) := by
  intro p hp q hq a b ha hb hab
  rw [mem_carrierImage_ptwiseDownHull] at hp hq ⊢
  obtain ⟨hp1, y₁, hy₁, hpy₁⟩ := hp
  obtain ⟨hq1, y₂, hy₂, hqy₂⟩ := hq
  refine ⟨convex_belCarrier hp1 hq1 ha hb hab, a • y₁ + b • y₂,
    convex_convexHull ℝ _ hy₁ hy₂ ha hb hab, ?_⟩
  exact add_le_add (smul_le_smul_of_nonneg_left hpy₁ ha)
    (smul_le_smul_of_nonneg_left hqy₂ hb)

/-- The carrier image of a down-hull is the image of
`(polytope) ×ˢ (unit box)` under coordinatewise rescaling
`(y, ε) ↦ (v ↦ ε v · y v)` — the compact presentation.  Downward: the
rescaling vector is `x v / y v` (zero where the dominator vanishes);
upward: a rescaled polytope point is dominated by its dominator. -/
theorem image_ptwiseDownHull (F : Finset (BelState V)) :
    Subtype.val '' ptwiseDownHull F
      = (fun q : (V → ℝ) × (V → ℝ) => fun v => q.2 v * q.1 v) ''
          ((convexHull ℝ (carrierImage (F : Set (BelState V)))) ×ˢ
            Set.univ.pi fun _ : V => Set.Icc (0 : ℝ) 1) := by
  ext p
  constructor
  · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    have hyb : y ∈ belCarrier V := convexHull_carrierImage_subset hy
    classical
    refine ⟨(y, fun v => if y v = 0 then 0 else (x : V → ℝ) v / y v),
      ⟨hy, fun v _ => ?_⟩, ?_⟩
    · show (if y v = 0 then (0 : ℝ) else (x : V → ℝ) v / y v) ∈ Set.Icc (0 : ℝ) 1
      by_cases h : y v = 0
      · rw [if_pos h]
        exact ⟨le_rfl, zero_le_one⟩
      · have hyv : 0 < y v := (hyb.1 v).lt_of_ne (Ne.symm h)
        rw [if_neg h]
        exact ⟨div_nonneg (x.2.1 v) hyv.le, (div_le_one hyv).mpr (hxy v)⟩
    · funext v
      show (if y v = 0 then (0 : ℝ) else (x : V → ℝ) v / y v) * y v = (x : V → ℝ) v
      by_cases h : y v = 0
      · have hx0 : (x : V → ℝ) v = 0 :=
          le_antisymm (by rw [← h]; exact hxy v) (x.2.1 v)
        rw [if_pos h, zero_mul, hx0]
      · rw [if_neg h, div_mul_cancel₀ _ h]
  · rintro ⟨⟨y, ε⟩, ⟨hy, hε⟩, rfl⟩
    have hyb : y ∈ belCarrier V := convexHull_carrierImage_subset hy
    have h0 : ∀ v, 0 ≤ ε v * y v := fun v =>
      mul_nonneg (hε v (Set.mem_univ v)).1 (hyb.1 v)
    have hle : (fun v => ε v * y v) ≤ y := fun v => by
      calc ε v * y v ≤ 1 * y v :=
            mul_le_mul_of_nonneg_right (hε v (Set.mem_univ v)).2 (hyb.1 v)
        _ = y v := one_mul _
    exact ⟨⟨fun v => ε v * y v, mem_belCarrier_of_le hyb h0 hle⟩,
      ⟨y, hy, hle⟩, rfl⟩

/-- Down-hulls are compact: continuous image of a compact product (the
polytope is the convex hull of a finite set). -/
theorem isCompact_ptwiseDownHull (F : Finset (BelState V)) :
    IsCompact (ptwiseDownHull F) := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff, image_ptwiseDownHull]
  refine IsCompact.image ?_ ?_
  · exact ((finite_carrierImage F).isCompact_convexHull ℝ).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  · exact continuous_pi fun v =>
      ((continuous_apply v).comp continuous_snd).mul
        ((continuous_apply v).comp continuous_fst)

/-- **T4**: the Mio–Vignudelli–Sarkis down-hulls are Kosoy–Appel
ultracontributions. -/
theorem IsMVS.isUltra {S : Set (BelState V)} (h : IsMVS S) : IsUltra S := by
  obtain ⟨F, hF, rfl⟩ := h
  obtain ⟨z, hz⟩ := hF
  refine ⟨⟨z, (z : V → ℝ),
      subset_convexHull ℝ _ (mem_carrierImage (Finset.mem_coe.mpr hz)), le_rfl⟩,
    (isCompact_ptwiseDownHull F).isClosed, convexBody_ptwiseDownHull F, ?_⟩
  intro y hy x hxy
  obtain ⟨w, hw, hyw⟩ := hy
  exact ⟨w, hw, hxy.trans hyw⟩

/-! ## T6 — Cozman credal sets are Richardson bodies -/

/-- The wall of the direction preimage of a (relatively) convex set of
distributions is a convex penalty: a strict mixture escaping the
preimage forces an escaped endpoint, whose wall term is `⊤` with a
nonzero coefficient. -/
theorem penaltyConvex_probWall_preimage {K : Set (BelState V)}
    (hKcv : ConvexBody K) :
    PenaltyConvex (probWall (ProbState.toBel ⁻¹' K)) := by
  intro μ ν s t hs ht hst
  set ρ := ProbState.mix s t hs.le ht.le hst μ ν with hρdef
  by_cases hρ : ρ ∈ ProbState.toBel ⁻¹' K
  · rw [probWall_apply_of_mem hρ]
    exact zero_le
  · have hnot : μ ∉ ProbState.toBel ⁻¹' K ∨ ν ∉ ProbState.toBel ⁻¹' K := by
      by_contra hc
      push Not at hc
      have hmem : s • ((μ.toBel : BelState V) : V → ℝ)
          + t • ((ν.toBel : BelState V) : V → ℝ) ∈ carrierImage K :=
        hKcv (mem_carrierImage hc.1) (mem_carrierImage hc.2) hs.le ht.le hst
      obtain ⟨k, hk, hke⟩ := hmem
      rw [ProbState.toBel_coe, ProbState.toBel_coe] at hke
      have hkey : ρ.toBel = k := by
        apply Subtype.ext
        rw [ProbState.toBel_coe, hρdef, ProbState.coe_mix]
        exact hke.symm
      apply hρ
      rw [Set.mem_preimage, hkey]
      exact hk
    rcases hnot with hμ | hν
    · rw [probWall_apply_of_not_mem hμ,
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr hs).ne', top_add]
      exact le_top
    · rw [probWall_apply_of_not_mem hν,
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht).ne', add_top]
      exact le_top

/-- The compile of the direction-preimage wall is the radial embedding:
inside the preimage the grade is `1` (the whole ray), outside it is `0`
(only the zero state, absorbed by any ray's origin). -/
theorem compile_probWall_preimage {K : Set (BelState V)} (hKne : K.Nonempty)
    (hKmass : ∀ x ∈ K, BelState.mass x = 1) :
    compile (probWall (ProbState.toBel ⁻¹' K)) = scaleSegment K := by
  ext z
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    by_cases hμ : μ ∈ ProbState.toBel ⁻¹' K
    · rw [probWall_apply_of_mem hμ, grade_zero] at hle
      refine ⟨μ.toBel, Set.mem_preimage.mp hμ, γ, h0, hle, ?_⟩
      apply Subtype.ext
      rw [BelState.coe_scale, ProbState.toBel_coe]
      exact he
    · rw [probWall_apply_of_not_mem hμ, grade_top] at hle
      obtain ⟨k, hk⟩ := hKne
      refine ⟨k, hk, 0, le_rfl, zero_le_one, ?_⟩
      apply Subtype.ext
      rw [BelState.coe_scale, he, le_antisymm hle h0, zero_smul, zero_smul]
  · rintro ⟨x, hx, γ, h0, h1, rfl⟩
    have hxp : (x : V → ℝ) ∈ probCarrier V := ⟨x.2.1, hKmass x hx⟩
    have htb : ProbState.toBel (⟨(x : V → ℝ), hxp⟩ : ProbState V) = x :=
      Subtype.ext rfl
    have hμmem : (⟨(x : V → ℝ), hxp⟩ : ProbState V) ∈ ProbState.toBel ⁻¹' K := by
      rw [Set.mem_preimage, htb]
      exact hx
    refine ⟨⟨(x : V → ℝ), hxp⟩, γ, h0, ?_, rfl⟩
    rw [probWall_apply_of_mem hμmem, grade_zero]
    exact h1

/-- **T6**: Cozman credal sets, radially embedded, are Richardson
bodies. -/
theorem IsCozman.isRichardsonBody {S : Set (BelState V)} (h : IsCozman S) :
    IsRichardsonBody S := by
  obtain ⟨K, hKne, hKcl, hKcv, hKmass, rfl⟩ := h
  exact ⟨probWall (ProbState.toBel ⁻¹' K),
    penaltyConvex_probWall_preimage hKcv,
    lowerSemicontinuous_probWall_iff.mpr
      (hKcl.preimage ProbState.continuous_toBel),
    (compile_probWall_preimage hKne hKmass).symm⟩

/-! ## T7 — the house class includes them all

Every named subclass lives inside the house class: with `Defs`'s
`IsConvexCredalBody.isCredalBody` (the convex class itself), the five
corollaries below discharge the includes-them-all theorem for the whole
preregistered roster. -/

/-- Richardson bodies are credal bodies. -/
theorem IsRichardsonBody.isCredalBody [Nonempty V] {S : Set (BelState V)}
    (h : IsRichardsonBody S) : IsCredalBody S :=
  h.isConvexCredalBody.isCredalBody

/-- Ultracontributions are credal bodies. -/
theorem IsUltra.isCredalBody {S : Set (BelState V)} (h : IsUltra S) :
    IsCredalBody S :=
  h.isConvexCredalBody.isCredalBody

/-- Mio–Vignudelli–Sarkis down-hulls are credal bodies. -/
theorem IsMVS.isCredalBody {S : Set (BelState V)} (h : IsMVS S) :
    IsCredalBody S :=
  h.isUltra.isCredalBody

/-- Halpern–Leung bodies are credal bodies. -/
theorem IsHL.isCredalBody {S : Set (BelState V)} (h : IsHL S) :
    IsCredalBody S :=
  h.isUltra.isCredalBody

/-- Cozman credal sets (radially embedded) are credal bodies. -/
theorem IsCozman.isCredalBody [Nonempty V] {S : Set (BelState V)}
    (h : IsCozman S) : IsCredalBody S :=
  h.isRichardsonBody.isCredalBody

end CredalPoset

end SuFunctor.Universe
