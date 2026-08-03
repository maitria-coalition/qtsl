import SuFunctor.Universe.Judgment
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.StdBasis

/-! # The convex chart: biconjugation as coreflection, and judgment-invisibility

Convexity enters the universe as a *certification chart*, not a
citizenship requirement.  This module carries the chart's structure at
the finite-outcome stratum:

* `ConvexPenalty` — the convex-lsc subclass (the chart's citizens; the
  class where one-draw linear-gamble certification is exact).
* `AffineGamble` / `IsMinorant` — affine gambles `μ ↦ ⟨g, μ⟩ + c` and
  the affine-minorant relation.  An affine minorant of a penalty *is*
  the content of a linear certificate row: a test, a threshold, and a
  domination claim.
* `biconj σ` — the biconjugate, presented directly as the supremum of
  the affine minorants (the pairing-with-affine-gambles form of the
  Fenchel double conjugate; on the `ℝ≥0∞` codomain the zero gamble is
  always a minorant, which keeps the supremum honest without signed
  arithmetic).
* **Fenchel–Moreau** (`biconj_eq_self`): a convex lsc penalty is the
  supremum of its affine minorants.  Proved from finite-dimensional
  Hahn–Banach separation of the epigraph, with the vertical-hyperplane
  case handled by separating from the closure of the effective domain
  (the `ℝ≥0∞` codomain supplies the classical anchor argument for
  free, since `0` minorizes everything).
* **The coreflection** (`isGreatest_biconj`, `le_biconj_iff`):
  `biconj σ` is the greatest convex-lsc minorant of `σ`; equivalently,
  biconjugation is right adjoint to the inclusion of the convex chart
  into the universe (`φ ≤ biconj σ ↔ φ ≤ σ` for chart citizens `φ` —
  a Galois connection whose left side is the inclusion).
* **Judgment-invisibility** (`sat_biconj_iff`): against a convex-lsc
  specification, a system and its convexification satisfy exactly the
  same judgments.  System non-convexity is invisible to every convex
  spec — and *composition-visible*: the witnesses in
  `SuFunctor.Universe.Witnesses` exhibit non-convex citizens whose
  convex shadows erase their content.  The checker sees the chart;
  composition sees the territory.

Everything is stated on the finite-`V` carrier, where the separation
arguments are finite-dimensional and no tightness riders appear.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-! ## Convexity for sets of distributions and for penalties -/

/-- Convexity for a set of distributions (via the carrier's convex
combination `BelState.mix`). -/
def ConvexBelSet (C : Set (BelState V)) : Prop :=
  ∀ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) ⦃μ ν : BelState V⦄,
    μ ∈ C → ν ∈ C → BelState.mix t h0 h1 μ ν ∈ C

/-- The convex-lsc chart's convexity condition for a penalty: the value
at a mixture is at most the mixture of the values, in `ℝ≥0∞`
arithmetic. -/
def ConvexPenalty (σ : Penalty V) : Prop :=
  ∀ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : BelState V),
    σ (BelState.mix t h0 h1 μ ν)
      ≤ ENNReal.ofReal t * σ μ + ENNReal.ofReal (1 - t) * σ ν

namespace BelState

theorem mix_one {μ ν : BelState V} (h0 : (0:ℝ) ≤ 1) (h1 : (1:ℝ) ≤ 1) :
    mix 1 h0 h1 μ ν = μ := by
  apply Subtype.ext
  funext v
  simp [mix_apply]

theorem mix_zero {μ ν : BelState V} (h0 : (0:ℝ) ≤ 0) (h1 : (0:ℝ) ≤ 1) :
    mix 0 h0 h1 μ ν = ν := by
  apply Subtype.ext
  funext v
  simp [mix_apply]

theorem mix_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ : BelState V) :
    mix t h0 h1 μ μ = μ := by
  apply Subtype.ext
  funext v
  simp [mix_apply]
  ring

end BelState

/-- A wall is a convex penalty iff its set is convex: the inclusion of
closed convex credal sets into the universe lands inside the chart, and
only the convex walls land there. -/
theorem convexPenalty_wall_iff {C : Set (BelState V)} :
    ConvexPenalty (wall C) ↔ ConvexBelSet C := by
  constructor
  · intro h t h0 h1 μ ν hμ hν
    have h2 := h t h0 h1 μ ν
    rw [wall_apply_of_mem hμ, wall_apply_of_mem hν, mul_zero, mul_zero,
      add_zero] at h2
    by_contra hmem
    rw [wall_apply_of_not_mem hmem] at h2
    exact ENNReal.top_ne_zero (le_antisymm h2 zero_le)
  · intro h t h0 h1 μ ν
    rcases eq_or_lt_of_le h0 with rfl0 | hpos
    · -- t = 0 : the mixture is ν
      subst rfl0
      rw [BelState.mix_zero]
      simp
    rcases eq_or_lt_of_le h1 with rfl1 | hlt1
    · -- t = 1 : the mixture is μ
      subst rfl1
      rw [BelState.mix_one]
      simp
    -- 0 < t < 1
    by_cases hμ : μ ∈ C
    · by_cases hν : ν ∈ C
      · rw [wall_apply_of_mem (h t h0 h1 hμ hν)]
        exact zero_le
      · rw [wall_apply_of_not_mem hν, ENNReal.mul_top
          fun hz => (not_le.mpr (sub_pos.mpr hlt1)) (ENNReal.ofReal_eq_zero.mp hz)]
        simp
    · rw [wall_apply_of_not_mem hμ, ENNReal.mul_top
        fun hz => (not_le.mpr hpos) (ENNReal.ofReal_eq_zero.mp hz)]
      simp

/-- Sums of chart citizens are chart citizens (the composition row stays
inside the chart — the certifiable core is `⊞`-total). -/
theorem ConvexPenalty.add {σ τ : Penalty V} (hσ : ConvexPenalty σ)
    (hτ : ConvexPenalty τ) : ConvexPenalty (σ + τ) := by
  intro t h0 h1 μ ν
  have h2 := add_le_add (hσ t h0 h1 μ ν) (hτ t h0 h1 μ ν)
  simp only [Pi.add_apply]
  calc σ (BelState.mix t h0 h1 μ ν) + τ (BelState.mix t h0 h1 μ ν)
      ≤ ENNReal.ofReal t * σ μ + ENNReal.ofReal (1 - t) * σ ν
        + (ENNReal.ofReal t * τ μ + ENNReal.ofReal (1 - t) * τ ν) := h2
    _ = ENNReal.ofReal t * (σ μ + τ μ)
        + ENNReal.ofReal (1 - t) * (σ ν + τ ν) := by ring

/-- Pointwise maxima of chart citizens are chart citizens (conjunction
stays inside the chart). -/
theorem ConvexPenalty.sup {σ τ : Penalty V} (hσ : ConvexPenalty σ)
    (hτ : ConvexPenalty τ) : ConvexPenalty (σ ⊔ τ) := by
  intro t h0 h1 μ ν
  rw [Pi.sup_apply]
  refine sup_le ?_ ?_
  · exact (hσ t h0 h1 μ ν).trans
      (add_le_add (mul_le_mul_right (le_sup_left.trans_eq (Pi.sup_apply σ τ μ).symm) _)
        (mul_le_mul_right (le_sup_left.trans_eq (Pi.sup_apply σ τ ν).symm) _))
  · exact (hτ t h0 h1 μ ν).trans
      (add_le_add (mul_le_mul_right (le_sup_right.trans_eq (Pi.sup_apply σ τ μ).symm) _)
        (mul_le_mul_right (le_sup_right.trans_eq (Pi.sup_apply σ τ ν).symm) _))

/-- Arbitrary suprema of chart citizens are chart citizens.  (Pointwise
*minima* are not: see the witnesses module — the coproduct exits the
chart, which is the whole reason the chart is a chart.) -/
theorem convexPenalty_iSup {ι : Sort*} {f : ι → Penalty V}
    (h : ∀ i, ConvexPenalty (f i)) : ConvexPenalty (⨆ i, f i) := by
  intro t h0 h1 μ ν
  rw [iSup_apply]
  refine iSup_le fun i => ?_
  refine (h i t h0 h1 μ ν).trans (add_le_add ?_ ?_)
  · refine mul_le_mul_right ?_ _
    rw [iSup_apply]
    exact le_iSup (fun j => f j μ) i
  · refine mul_le_mul_right ?_ _
    rw [iSup_apply]
    exact le_iSup (fun j => f j ν) i

/-! ## Affine gambles and minorants -/

/-- An affine gamble on distributions: a linear test plus a constant,
`μ ↦ Σ_v lin v · μ v + const`.  These are the one-draw payoffs; an
affine minorant of a penalty is exactly the content of a linear
certificate row. -/
structure AffineGamble (V : Type*) [Fintype V] where
  /-- The linear part (the test function). -/
  lin : V → ℝ
  /-- The constant part (the threshold, with sign conventions folded
  in). -/
  const : ℝ

namespace AffineGamble

variable (p : AffineGamble V)

/-- The real value of the gamble at a distribution. -/
def eval (μ : BelState V) : ℝ := ∑ v, p.lin v * (μ : V → ℝ) v + p.const

/-- The gamble read as a penalty functional (negative values clamp to
`0`; since penalties are nonnegative, minorization is unaffected). -/
noncomputable def evalPen : Penalty V := fun μ => ENNReal.ofReal (p.eval μ)

theorem continuous_eval : Continuous p.eval := by
  unfold eval
  exact (continuous_finsetSum _ fun v _ =>
    continuous_const.mul ((continuous_apply v).comp continuous_subtype_val)).add
    continuous_const

theorem lowerSemicontinuous_evalPen : LowerSemicontinuous p.evalPen :=
  (ENNReal.continuous_ofReal.comp p.continuous_eval).lowerSemicontinuous

/-- Affine gambles are affine along mixtures. -/
theorem eval_mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : BelState V) :
    p.eval (BelState.mix t h0 h1 μ ν) = t * p.eval μ + (1 - t) * p.eval ν := by
  unfold eval
  simp only [BelState.mix_apply, mul_add]
  rw [Finset.sum_add_distrib]
  have h1' : ∑ v, p.lin v * (t * (μ : V → ℝ) v)
      = t * ∑ v, p.lin v * (μ : V → ℝ) v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2' : ∑ v, p.lin v * ((1 - t) * (ν : V → ℝ) v)
      = (1 - t) * ∑ v, p.lin v * (ν : V → ℝ) v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1', h2']
  ring

theorem convexPenalty_evalPen : ConvexPenalty p.evalPen := by
  intro t h0 h1 μ ν
  unfold evalPen
  rw [p.eval_mix t h0 h1 μ ν]
  calc ENNReal.ofReal (t * p.eval μ + (1 - t) * p.eval ν)
      ≤ ENNReal.ofReal (t * p.eval μ) + ENNReal.ofReal ((1 - t) * p.eval ν) :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal t * ENNReal.ofReal (p.eval μ)
        + ENNReal.ofReal (1 - t) * ENNReal.ofReal (p.eval ν) := by
        rw [ENNReal.ofReal_mul h0, ENNReal.ofReal_mul (by linarith)]

/-- The affine-combination identity: an affine gamble's value at any
distribution is the mass-weighted combination of its values at the point
masses, with the missing mass carried by the constant (the value at the
zero state).  This is the identity that makes the Dirac skeleton
control every affine minorant. -/
theorem eval_eq_sum_dirac [DecidableEq V] (μ : BelState V) :
    p.eval μ = ∑ v, (μ : V → ℝ) v * p.eval (BelState.dirac v)
      + (1 - μ.mass) * p.const := by
  have hdv : ∀ v, p.eval (BelState.dirac v) = p.lin v + p.const := by
    intro v
    unfold eval
    congr 1
    rw [Finset.sum_eq_single v
      (fun w _ hw => by rw [BelState.dirac_apply_of_ne hw, mul_zero])
      (fun h => absurd (Finset.mem_univ v) h)]
    rw [BelState.dirac_apply_same, mul_one]
  simp_rw [hdv, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold eval BelState.mass
  have hcomm : ∑ v, (μ : V → ℝ) v * p.lin v = ∑ v, p.lin v * (μ : V → ℝ) v :=
    Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [hcomm]
  ring

end AffineGamble

/-- `p` is an affine minorant of `σ`: the gamble's penalty reading is
dominated by `σ` everywhere.  Since `σ ≥ 0`, this is equivalent to the
real-valued affine function lying below `σ` in the extended order. -/
def IsMinorant (p : AffineGamble V) (σ : Penalty V) : Prop :=
  ∀ μ, p.evalPen μ ≤ σ μ

/-- The zero gamble minorizes every penalty: the anchor the `ℝ≥0∞`
codomain provides for free. -/
theorem isMinorant_zero (σ : Penalty V) : IsMinorant ⟨0, 0⟩ σ := by
  intro μ
  simp [AffineGamble.evalPen, AffineGamble.eval]

/-! ## The biconjugate -/

/-- The biconjugate of a penalty: the supremum of its affine minorants.
This is the Fenchel double conjugate in its pairing-with-affine-gambles
presentation, kept `ℝ≥0∞`-native. -/
noncomputable def biconj (σ : Penalty V) : Penalty V :=
  fun μ => ⨆ (p : AffineGamble V) (_ : IsMinorant p σ), p.evalPen μ

theorem le_biconj_of_isMinorant {σ : Penalty V} {p : AffineGamble V}
    (hp : IsMinorant p σ) : p.evalPen ≤ biconj σ := by
  intro μ
  exact le_iSup₂ (f := fun p (_ : IsMinorant p σ) => p.evalPen μ) p hp

theorem biconj_le (σ : Penalty V) : biconj σ ≤ σ := by
  intro μ
  exact iSup₂_le fun p hp => hp μ

theorem biconj_mono {σ τ : Penalty V} (h : σ ≤ τ) : biconj σ ≤ biconj τ := by
  intro μ
  refine iSup₂_le fun p hp => ?_
  exact (le_biconj_of_isMinorant fun ν => (hp ν).trans (h ν)) μ

theorem lowerSemicontinuous_biconj (σ : Penalty V) :
    LowerSemicontinuous (biconj σ) := by
  have h : ∀ p : AffineGamble V,
      LowerSemicontinuous fun μ => ⨆ _ : IsMinorant p σ, p.evalPen μ :=
    fun p => lowerSemicontinuous_iSup fun _ => p.lowerSemicontinuous_evalPen
  exact lowerSemicontinuous_iSup h

theorem convexPenalty_biconj (σ : Penalty V) : ConvexPenalty (biconj σ) := by
  have heq : biconj σ
      = ⨆ (p : AffineGamble V) (_ : IsMinorant p σ), p.evalPen := by
    funext μ
    rw [iSup_apply]
    exact iSup_congr fun p => iSup_apply.symm
  rw [heq]
  exact convexPenalty_iSup fun p =>
    convexPenalty_iSup fun _ => p.convexPenalty_evalPen

/-! ## The Fenchel–Moreau engine

The ambient-space development: extend a penalty to `V → ℝ` by `⊤`,
form the real epigraph, and separate.  The two engine lemmas below
produce, for any point where a convex lsc penalty exceeds a real
height, an affine minorant beating that height — one lemma for points
in the closure of the effective domain (nonvertical separation of the
epigraph), one for points outside it (vertical separation of the
domain, with the zero anchor `σ ≥ 0` closing the classical gap). -/

section FenchelMoreau

open Classical in
/-- The extension of a penalty to the ambient space, `⊤` off the
carrier. -/
noncomputable def extendPen (σ : Penalty V) : (V → ℝ) → ℝ≥0∞ :=
  fun x => if h : x ∈ belCarrier V then σ ⟨x, h⟩ else ⊤

@[simp] theorem extendPen_coe (σ : Penalty V) (μ : BelState V) :
    extendPen σ (μ : V → ℝ) = σ μ := by
  unfold extendPen
  rw [dif_pos μ.2]

theorem extendPen_of_not_mem {σ : Penalty V} {x : V → ℝ}
    (h : x ∉ belCarrier V) : extendPen σ x = ⊤ := by
  unfold extendPen
  rw [dif_neg h]

/-- The `⊤`-extension of a citizen is lower semicontinuous on the
ambient space: sublevels are compact images of the (compact) subtype's
closed sublevels. -/
theorem lowerSemicontinuous_extendPen {σ : Penalty V}
    (hσ : LowerSemicontinuous σ) : LowerSemicontinuous (extendPen σ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro s
  rcases eq_or_ne s ⊤ with rfl | hs
  · have h : extendPen σ ⁻¹' Set.Iic ⊤ = Set.univ := by
      ext x; simp
    rw [h]; exact isClosed_univ
  · have hset : extendPen σ ⁻¹' Set.Iic s
        = Subtype.val '' {μ : BelState V | σ μ ≤ s} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro hx
        by_cases h : x ∈ belCarrier V
        · refine ⟨⟨x, h⟩, ?_, rfl⟩
          rwa [← extendPen_coe σ ⟨x, h⟩]
        · rw [extendPen_of_not_mem h] at hx
          exact absurd (top_le_iff.mp hx) hs
      · rintro ⟨μ, hμ, rfl⟩
        rwa [extendPen_coe]
    rw [hset]
    have hcl : IsClosed {μ : BelState V | σ μ ≤ s} :=
      lowerSemicontinuous_iff_isClosed_sublevel.mp hσ s
    exact (hcl.isCompact.image continuous_subtype_val).isClosed

/-- The effective domain of the extension: the ambient points of finite
penalty. -/
def penDom (σ : Penalty V) : Set (V → ℝ) := {x | extendPen σ x ≠ ⊤}

theorem penDom_subset (σ : Penalty V) : penDom σ ⊆ belCarrier V := by
  intro x hx
  by_contra h
  exact hx (extendPen_of_not_mem h)

theorem mem_penDom_coe_iff {σ : Penalty V} {μ : BelState V} :
    (μ : V → ℝ) ∈ penDom σ ↔ σ μ ≠ ⊤ := by
  unfold penDom
  rw [Set.mem_setOf_eq, extendPen_coe]

/-- The mixture bridge between the ambient convex combination and the
carrier's `mix`. -/
theorem extendPen_combo (σ : Penalty V) {x y : V → ℝ}
    (hx : x ∈ belCarrier V) (hy : y ∈ belCarrier V) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    extendPen σ (a • x + b • y)
      = σ (BelState.mix a ha (by linarith) ⟨x, hx⟩ ⟨y, hy⟩) := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hmem : a • x + (1 - a) • y ∈ belCarrier V :=
    convex_belCarrier hx hy ha hb hab
  unfold extendPen
  rw [dif_pos hmem]
  exact congrArg σ (Subtype.ext rfl)

theorem convex_penDom {σ : Penalty V} (hσ : ConvexPenalty σ) :
    Convex ℝ (penDom σ) := by
  intro x hx y hy a b ha hb hab
  have hxK := penDom_subset σ hx
  have hyK := penDom_subset σ hy
  have hxne : σ ⟨x, hxK⟩ ≠ ⊤ := by
    have := hx
    unfold penDom at this
    rwa [Set.mem_setOf_eq, extendPen, dif_pos hxK] at this
  have hyne : σ ⟨y, hyK⟩ ≠ ⊤ := by
    have := hy
    unfold penDom at this
    rwa [Set.mem_setOf_eq, extendPen, dif_pos hyK] at this
  unfold penDom
  rw [Set.mem_setOf_eq, extendPen_combo σ hxK hyK ha hb hab]
  refine ne_top_of_le_ne_top ?_ (hσ a ha (by linarith) ⟨x, hxK⟩ ⟨y, hyK⟩)
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hyne⟩

/-- The real epigraph of the extension. -/
def epiR (σ : Penalty V) : Set ((V → ℝ) × ℝ) :=
  {q | 0 ≤ q.2 ∧ extendPen σ q.1 ≤ ENNReal.ofReal q.2}

theorem isClosed_epiR {σ : Penalty V} (hσ : LowerSemicontinuous σ) :
    IsClosed (epiR σ) := by
  have h1 : IsClosed {p : (V → ℝ) × ℝ≥0∞ | extendPen σ p.1 ≤ p.2} :=
    lowerSemicontinuous_iff_isClosed_epigraph.mp
      (lowerSemicontinuous_extendPen hσ)
  have hmap : Continuous fun q : (V → ℝ) × ℝ => (q.1, ENNReal.ofReal q.2) :=
    continuous_fst.prodMk (ENNReal.continuous_ofReal.comp continuous_snd)
  have heq : epiR σ = {q : (V → ℝ) × ℝ | 0 ≤ q.2}
      ∩ (fun q : (V → ℝ) × ℝ => (q.1, ENNReal.ofReal q.2)) ⁻¹'
        {p : (V → ℝ) × ℝ≥0∞ | extendPen σ p.1 ≤ p.2} := by
    ext q
    simp [epiR, Set.mem_inter_iff]
  rw [heq]
  exact (isClosed_le continuous_const continuous_snd).inter (h1.preimage hmap)

theorem convex_epiR {σ : Penalty V} (hσ : ConvexPenalty σ) :
    Convex ℝ (epiR σ) := by
  rintro ⟨x, r⟩ ⟨hr0, hxr⟩ ⟨y, q⟩ ⟨hq0, hyq⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hxK : x ∈ belCarrier V := by
    by_contra h
    rw [extendPen_of_not_mem h, top_le_iff] at hxr
    exact ENNReal.ofReal_ne_top hxr
  have hyK : y ∈ belCarrier V := by
    by_contra h
    rw [extendPen_of_not_mem h, top_le_iff] at hyq
    exact ENNReal.ofReal_ne_top hyq
  have hxr' : σ ⟨x, hxK⟩ ≤ ENNReal.ofReal r := by
    rwa [extendPen, dif_pos hxK] at hxr
  have hyq' : σ ⟨y, hyK⟩ ≤ ENNReal.ofReal q := by
    rwa [extendPen, dif_pos hyK] at hyq
  constructor
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    exact add_nonneg (mul_nonneg ha hr0) (mul_nonneg (by linarith) hq0)
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    rw [extendPen_combo σ hxK hyK ha (by linarith) hab]
    calc σ (BelState.mix a ha (by linarith) ⟨x, hxK⟩ ⟨y, hyK⟩)
        ≤ ENNReal.ofReal a * σ ⟨x, hxK⟩
          + ENNReal.ofReal (1 - a) * σ ⟨y, hyK⟩ :=
          hσ a ha (by linarith) _ _
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal r
          + ENNReal.ofReal (1 - a) * ENNReal.ofReal q := by
          gcongr
      _ = ENNReal.ofReal (a * r + (1 - a) * q) := by
          rw [← ENNReal.ofReal_mul ha,
            ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - a),
            ← ENNReal.ofReal_add (mul_nonneg ha hr0)
              (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) hq0)]

/-- Linear functionals on the finite product decompose over the
standard basis. -/
private theorem dual_pi_repr [DecidableEq V] (f : StrongDual ℝ (V → ℝ))
    (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  have hx : x = ∑ v, x v • (Pi.single v (1:ℝ) : V → ℝ) := by
    funext w
    rw [Finset.sum_apply]
    have h : ∀ v, (x v • (Pi.single v (1:ℝ) : V → ℝ)) w
        = if w = v then x v else 0 := by
      intro v
      rcases eq_or_ne w v with rfl | hne
      · simp
      · simp [hne]
    simp_rw [h]
    rw [Finset.sum_ite_eq (Finset.univ : Finset V) w (fun v => x v)]
    simp
  conv_lhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [map_smul, smul_eq_mul]

/-- **Engine lemma (nonvertical case).**  At a point of the closure of
the effective domain where the penalty exceeds a real height, some
affine minorant also exceeds it: separate the point-below-the-graph
from the closed convex epigraph; the separating hyperplane cannot be
vertical at a closure point of the domain. -/
private theorem exists_minorant_of_mem_closure_dom {σ : Penalty V}
    (hσc : ConvexPenalty σ) (hσl : LowerSemicontinuous σ)
    {μ₀ : BelState V} (hcl : (μ₀ : V → ℝ) ∈ closure (penDom σ))
    {s : ℝ} (hlt : ENNReal.ofReal s < σ μ₀) :
    ∃ p : AffineGamble V, IsMinorant p σ ∧ s < p.eval μ₀ := by
  classical
  -- the point below the graph is off the epigraph
  have hnot : ((μ₀ : V → ℝ), s) ∉ epiR σ := by
    rintro ⟨-, h2⟩
    rw [extendPen_coe] at h2
    exact absurd (lt_of_lt_of_le hlt h2) (lt_irrefl _)
  obtain ⟨f, u, hfx, hepi⟩ :=
    geometric_hahn_banach_point_closed (convex_epiR hσc) (isClosed_epiR hσl)
      hnot
  -- decompose the functional
  set β : ℝ := f ((0 : V → ℝ), (1 : ℝ)) with hβ_def
  have hdecomp : ∀ (x : V → ℝ) (r : ℝ), f (x, r) = f (x, 0) + r * β := by
    intro x r
    have hxr : (x, r) = (x, (0:ℝ)) + r • ((0 : V → ℝ), (1:ℝ)) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_zero, Prod.mk_add_mk]
      simp
    rw [hxr, map_add, map_smul, smul_eq_mul]
  -- the domain is nonempty (its closure contains μ₀'s coordinates)
  have hdom_ne : (penDom σ).Nonempty := by
    rcases Set.eq_empty_or_nonempty (penDom σ) with h | h
    · rw [h, closure_empty] at hcl
      exact absurd hcl (Set.notMem_empty _)
    · exact h
  obtain ⟨x₁, hx₁⟩ := hdom_ne
  have hx₁K := penDom_subset σ hx₁
  have hx₁ne : extendPen σ x₁ ≠ ⊤ := hx₁
  -- epigraph points above x₁ at every added height
  have hx₁epi : ∀ n : ℕ, (x₁, (extendPen σ x₁).toReal + n) ∈ epiR σ := by
    intro n
    constructor
    · have := ENNReal.toReal_nonneg (a := extendPen σ x₁)
      positivity
    · rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (Nat.cast_nonneg n),
        ENNReal.ofReal_toReal hx₁ne]
      exact le_add_of_nonneg_right zero_le
  -- β is nonnegative
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    rw [not_le] at hneg
    set r₁ : ℝ := (extendPen σ x₁).toReal with hr₁
    obtain ⟨n, hn⟩ := exists_nat_gt ((f (x₁, 0) + r₁ * β - u) / (-β))
    have hβ' : (0:ℝ) < -β := by linarith
    have h1 : f (x₁, 0) + r₁ * β - u < (n : ℝ) * (-β) :=
      (div_lt_iff₀ hβ').mp hn
    have h2 := hepi _ (hx₁epi n)
    rw [hdecomp] at h2
    nlinarith
  -- β is nonzero: a vertical separator would separate μ₀ from the domain
  have hβne : β ≠ 0 := by
    intro hzero
    have hcont : Continuous fun x : V → ℝ => f (x, (0:ℝ)) :=
      f.continuous.comp (continuous_id.prodMk continuous_const)
    have hdomle : penDom σ ⊆ {x : V → ℝ | u ≤ f (x, 0)} := by
      intro x hx
      have hxne' : extendPen σ x ≠ ⊤ := hx
      have hxepi : (x, (extendPen σ x).toReal) ∈ epiR σ :=
        ⟨ENNReal.toReal_nonneg, by rw [ENNReal.ofReal_toReal hxne']⟩
      have := hepi _ hxepi
      rw [hdecomp, hzero, mul_zero, add_zero] at this
      exact this.le
    have hclosed : IsClosed {x : V → ℝ | u ≤ f (x, 0)} :=
      isClosed_le continuous_const hcont
    have hμ₀le : u ≤ f ((μ₀ : V → ℝ), 0) :=
      (hclosed.closure_subset_iff.mpr hdomle) hcl
    have hμ₀lt : f ((μ₀ : V → ℝ), 0) < u := by
      have := hfx
      rw [hdecomp, hzero, mul_zero, add_zero] at this
      exact this
    linarith
  have hβpos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβne)
  have hβ0' : β ≠ 0 := ne_of_gt hβpos
  -- the affine minorant
  have hflin : ∀ x : V → ℝ, f (x, (0:ℝ))
      = ∑ v, x v * f (Pi.single v 1, 0) := by
    intro x
    have h1 : f (x, (0:ℝ))
        = (f.comp (ContinuousLinearMap.inl ℝ (V → ℝ) ℝ)) x := rfl
    rw [h1, dual_pi_repr (f.comp (ContinuousLinearMap.inl ℝ (V → ℝ) ℝ)) x]
    rfl
  have heval : ∀ μ : BelState V,
      AffineGamble.eval ⟨fun v => -(f (Pi.single v 1, 0)) / β, u / β⟩ μ
        = (u - f ((μ : V → ℝ), 0)) / β := by
    intro μ
    show (∑ v, -(f (Pi.single v 1, 0)) / β * (μ : V → ℝ) v) + u / β
        = (u - f ((μ : V → ℝ), 0)) / β
    have hsum : ∑ v, -(f (Pi.single v 1, 0)) / β * (μ : V → ℝ) v
        = -(1 / β) * ∑ v, (μ : V → ℝ) v * f (Pi.single v 1, 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsum, ← hflin]
    field_simp
    ring
  refine ⟨⟨fun v => -(f (Pi.single v 1, 0)) / β, u / β⟩, ?_, ?_⟩
  · -- minorant
    intro μ
    rcases eq_or_ne (σ μ) ⊤ with htop | hne
    · rw [htop]; exact le_top
    have hμepi : ((μ : V → ℝ), (σ μ).toReal) ∈ epiR σ :=
      ⟨ENNReal.toReal_nonneg, by rw [extendPen_coe, ENNReal.ofReal_toReal hne]⟩
    have hsep := hepi _ hμepi
    rw [hdecomp] at hsep
    have hlt' : (u - f ((μ : V → ℝ), 0)) / β < (σ μ).toReal := by
      rw [div_lt_iff₀ hβpos]
      nlinarith
    show ENNReal.ofReal
        (AffineGamble.eval ⟨fun v => -(f (Pi.single v 1, 0)) / β, u / β⟩ μ)
      ≤ σ μ
    rw [heval μ]
    calc ENNReal.ofReal ((u - f ((μ : V → ℝ), 0)) / β)
        ≤ ENNReal.ofReal (σ μ).toReal := ENNReal.ofReal_le_ofReal hlt'.le
      _ = σ μ := ENNReal.ofReal_toReal hne
  · -- beats s at μ₀
    have hfx' : f ((μ₀ : V → ℝ), 0) + s * β < u := by
      have h2 := hfx
      rw [hdecomp] at h2
      exact h2
    rw [heval μ₀, lt_div_iff₀ hβpos]
    linarith

/-- **Engine lemma (vertical case).**  Off the closure of the effective
domain, affine minorants are unbounded: scale a hyperplane separating
the point from the domain closure — nonnegativity of penalties anchors
the scaling. -/
private theorem exists_minorant_of_not_mem_closure_dom {σ : Penalty V}
    (hσc : ConvexPenalty σ) {μ₀ : BelState V}
    (hcl : (μ₀ : V → ℝ) ∉ closure (penDom σ)) (s : ℝ) :
    ∃ p : AffineGamble V, IsMinorant p σ ∧ s < p.eval μ₀ := by
  classical
  obtain ⟨f, u, hdomlt, hgt⟩ :=
    geometric_hahn_banach_closed_point
      ((convex_penDom hσc).closure) isClosed_closure hcl
  have hgap : 0 < f (μ₀ : V → ℝ) - u := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (s / (f (μ₀ : V → ℝ) - u))
  have hd : f (μ₀ : V → ℝ) - u ≠ 0 := ne_of_gt hgap
  have hbeats : s < (n : ℝ) * (f (μ₀ : V → ℝ) - u) := by
    have h1 : s / (f (μ₀ : V → ℝ) - u) * (f (μ₀ : V → ℝ) - u) = s :=
      div_mul_cancel₀ s hd
    have h2 : s / (f (μ₀ : V → ℝ) - u) * (f (μ₀ : V → ℝ) - u)
        < (n : ℝ) * (f (μ₀ : V → ℝ) - u) :=
      mul_lt_mul_of_pos_right hn hgap
    linarith
  have heval : ∀ μ : BelState V,
      AffineGamble.eval ⟨fun v => (n : ℝ) * f (Pi.single v 1), -((n : ℝ) * u)⟩ μ
        = (n : ℝ) * (f (μ : V → ℝ) - u) := by
    intro μ
    show (∑ v, (n : ℝ) * f (Pi.single v 1) * (μ : V → ℝ) v) + -((n : ℝ) * u)
        = (n : ℝ) * (f (μ : V → ℝ) - u)
    have hsum : ∑ v, (n : ℝ) * f (Pi.single v 1) * (μ : V → ℝ) v
        = (n : ℝ) * ∑ v, (μ : V → ℝ) v * f (Pi.single v 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsum, ← dual_pi_repr f (μ : V → ℝ)]
    ring
  refine ⟨⟨fun v => (n : ℝ) * f (Pi.single v 1), -((n : ℝ) * u)⟩, ?_, ?_⟩
  · intro μ
    rcases eq_or_ne (σ μ) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · -- μ's coordinates lie in the domain, where f < u
      have hμdom : (μ : V → ℝ) ∈ penDom σ := mem_penDom_coe_iff.mpr hne
      have hflt : f (μ : V → ℝ) < u := hdomlt _ (subset_closure hμdom)
      have hnonpos : (n : ℝ) * (f (μ : V → ℝ) - u) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨Nat.cast_nonneg n, by linarith⟩)
      show ENNReal.ofReal (AffineGamble.eval
          ⟨fun v => (n : ℝ) * f (Pi.single v 1), -((n : ℝ) * u)⟩ μ)
        ≤ σ μ
      rw [heval μ, ENNReal.ofReal_eq_zero.mpr hnonpos]
      exact zero_le
  · rw [heval μ₀]
    exact hbeats

/-- **Fenchel–Moreau, minorant form**: a convex lsc penalty is the
supremum of its affine minorants. -/
theorem biconj_eq_self {σ : Penalty V} (hσc : ConvexPenalty σ)
    (hσl : LowerSemicontinuous σ) : biconj σ = σ := by
  refine le_antisymm (biconj_le σ) ?_
  intro μ₀
  by_contra hlt'
  rw [not_le] at hlt'
  obtain ⟨s, hs0, h1, h2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt'
  have hbeat : ∃ p : AffineGamble V, IsMinorant p σ ∧ s < p.eval μ₀ := by
    by_cases hcl : (μ₀ : V → ℝ) ∈ closure (penDom σ)
    · exact exists_minorant_of_mem_closure_dom hσc hσl hcl h2
    · exact exists_minorant_of_not_mem_closure_dom hσc hcl s
  obtain ⟨p, hp, hps⟩ := hbeat
  have hge : ENNReal.ofReal s ≤ biconj σ μ₀ := by
    calc ENNReal.ofReal s ≤ ENNReal.ofReal (p.eval μ₀) :=
          ENNReal.ofReal_le_ofReal hps.le
      _ = p.evalPen μ₀ := rfl
      _ ≤ biconj σ μ₀ := le_biconj_of_isMinorant hp μ₀
  exact absurd (lt_of_le_of_lt hge h1) (lt_irrefl _)

end FenchelMoreau

/-! ## The coreflection and judgment-invisibility -/

/-- Biconjugation is idempotent: the chart is a retract of the
universe. -/
theorem biconj_idem (σ : Penalty V) : biconj (biconj σ) = biconj σ :=
  biconj_eq_self (convexPenalty_biconj σ) (lowerSemicontinuous_biconj σ)

/-- **The coreflection.**  `biconj σ` is the greatest convex-lsc
minorant of `σ`: the convex chart is coreflective in the universe, with
biconjugation as the coreflector. -/
theorem isGreatest_biconj (σ : Penalty V) :
    IsGreatest
      {ψ : Penalty V | ConvexPenalty ψ ∧ LowerSemicontinuous ψ ∧ ψ ≤ σ}
      (biconj σ) := by
  constructor
  · exact ⟨convexPenalty_biconj σ, lowerSemicontinuous_biconj σ, biconj_le σ⟩
  · rintro ψ ⟨hψc, hψl, hψσ⟩
    calc ψ = biconj ψ := (biconj_eq_self hψc hψl).symm
      _ ≤ biconj σ := biconj_mono hψσ

/-- **The Galois adjunction.**  For a chart citizen `φ`, lying below
`σ` and lying below `biconj σ` are the same condition: biconjugation is
right adjoint to the inclusion of the convex chart. -/
theorem le_biconj_iff {σ φ : Penalty V} (hφc : ConvexPenalty φ)
    (hφl : LowerSemicontinuous φ) :
    φ ≤ biconj σ ↔ φ ≤ σ := by
  constructor
  · intro h
    exact h.trans (biconj_le σ)
  · intro h
    calc φ = biconj φ := (biconj_eq_self hφc hφl).symm
      _ ≤ biconj σ := biconj_mono h

/-- **Judgment-invisibility.**  Against a convex-lsc specification, a
system and its convexification satisfy exactly the same judgments —
the system side needs no hypothesis at all.  This is the theorem that
makes enclosure testing complete for every judgment against a chart
spec while leaving system-side non-convexity untouched: the checker
sees the chart, composition sees the territory (the witnesses module
shows the difference is real). -/
theorem sat_biconj_iff {σ φ : Penalty V} (hφc : ConvexPenalty φ)
    (hφl : LowerSemicontinuous φ) :
    Sat (biconj σ) φ ↔ Sat σ φ :=
  le_biconj_iff hφc hφl

end SuFunctor.Universe
