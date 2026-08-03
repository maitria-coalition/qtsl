import SuFunctor.Universe.CredalPoset.Defs
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Fin.VecNotation

/-! # The parabola body: an ultracontribution that is not finitely generated

This module carries the witness `W6` of the credal-poset
preregistration (committed before these proofs were built): the
region of the two-outcome carrier under the
parabola

  `parabolaBody = {x : Δ_{≤1}(Fin 2) | x₁ ≤ (1 − x₀²)/2}`.

Two facts are proved:

* `isHL_parabolaBody` — the body is a Halpern–Leung MWER body (hence a
  Kosoy–Appel ultracontribution, hence a convex credal body): nonempty,
  closed, convex (concavity of `t ↦ (1−t²)/2`, by the two-point Jensen
  inequality for `x ↦ x²`), pointwise-down-closed, and containing the
  full-mass member `δ₀`.  A sanity note the membership proofs make
  precise: at `x₀ = t` the parabola allows `x₁` up to `(1−t²)/2`, and
  `t + (1−t²)/2 ≤ 1 ⟺ 0 ≤ (1−t)²` (`arc_mass_le_one`), so the parabola
  constraint binds *below* the mass constraint — the boundary arc lies
  in the carrier's interior mass-wise, which is what makes its points
  extreme for the body rather than artifacts of the simplex boundary.

* `not_isMVS_parabolaBody` — the body is **not** of Mio–Vignudelli–Sarkis
  shape `C^↓` (the pointwise-down closure of a finitely generated
  polytope).  This is the poset's one extreme-point argument, and the
  load-bearing refutation for the strict edges `KA ⊋ MVS` and
  `HL ⊄ MVS`.  Route: for a finite generator set `F`, the ambient image
  of `ptwiseDownHull F` equals the convex hull of the finitely many
  **masked corners** `ε ⊙ y` (`ε ∈ {0,1}²`, `y` a generator) — the
  down-set of a point decomposes coordinatewise (Riesz), and one common
  scaling vector serves every generator
  (`carrierImage_ptwiseDownHull_eq_convexHull_maskedCorners`).  Extreme
  points of a convex hull lie in the generating set
  (`extremePoints_convexHull_subset`), so such an image has finitely
  many.  But every arc point `(t, (1−t²)/2)` is an extreme point of
  `carrierImage parabolaBody` — strict concavity of the boundary, via
  the equality case of the Jensen step (`coe_arcPt_mem_extremePoints`)
  — and `t ↦ 1/(n+2)` injects `ℕ` into the arc.  Cardinality clash.
-/

namespace SuFunctor.Universe

namespace CredalPoset

/-! ## Scalar helpers: the two-point Jensen inequality for `x ↦ x²` -/

/-- Two-point Jensen for the square: `(a·p + (1−a)·q)² ≤ a·p² + (1−a)·q²`. -/
private lemma sq_combo_le {a p q : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (a * p + (1 - a) * q) ^ 2 ≤ a * p ^ 2 + (1 - a) * q ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg (p - q))]

/-- Equality in two-point Jensen for the square forces the points to agree
(the square is *strictly* convex): the defect is `a(1−a)(p−q)²`. -/
private lemma eq_of_sq_combo_eq {a p q : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (h : a * p ^ 2 + (1 - a) * q ^ 2 = (a * p + (1 - a) * q) ^ 2) : p = q := by
  have hkey : a * (1 - a) * (p - q) ^ 2 = 0 := by linear_combination h
  have hpos : 0 < a * (1 - a) := mul_pos ha (by linarith)
  have hsq : (p - q) ^ 2 = 0 :=
    (mul_eq_zero.mp hkey).resolve_left hpos.ne'
  have := sq_eq_zero_iff.mp hsq
  linarith [this]

/-- Extensionality for `Fin 2 → ℝ` from the two coordinates. -/
private lemma funext_fin_two {f g : Fin 2 → ℝ} (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    f = g :=
  funext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

/-! ## The body -/

/-- The parabola body: distributions on two outcomes whose second weight
lies under the parabola `x₁ = (1 − x₀²)/2`.  (The subtype already
enforces carrier membership; only the parabola constraint is imposed.) -/
def parabolaBody : Set (BelState (Fin 2)) :=
  {x | (x : Fin 2 → ℝ) 1 ≤ (1 - (x : Fin 2 → ℝ) 0 ^ 2) / 2}

/-- Sanity: on the boundary arc, mass is at most one — `t + (1−t²)/2 ≤ 1`
is exactly `0 ≤ (1−t)²`.  The parabola constraint binds below the mass
constraint, so the whole arc lies in the carrier. -/
lemma arc_mass_le_one {t : ℝ} : t + (1 - t ^ 2) / 2 ≤ 1 := by
  nlinarith [sq_nonneg (t - 1)]

/-- The full-mass point `δ₀ = (1,0)` lies on the body (the parabola's
right endpoint: `0 ≤ (1 − 1²)/2`). -/
lemma dirac_zero_mem_parabolaBody : BelState.dirac 0 ∈ parabolaBody := by
  show ((BelState.dirac 0 : BelState (Fin 2)) : Fin 2 → ℝ) 1
      ≤ (1 - ((BelState.dirac 0 : BelState (Fin 2)) : Fin 2 → ℝ) 0 ^ 2) / 2
  rw [BelState.dirac_apply_same, BelState.dirac_apply_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  norm_num

theorem parabolaBody_nonempty : parabolaBody.Nonempty :=
  ⟨BelState.dirac 0, dirac_zero_mem_parabolaBody⟩

theorem isClosed_parabolaBody : IsClosed parabolaBody := by
  have hc0 : Continuous fun x : BelState (Fin 2) => (x : Fin 2 → ℝ) 0 :=
    (continuous_apply (0 : Fin 2)).comp continuous_subtype_val
  have hc1 : Continuous fun x : BelState (Fin 2) => (x : Fin 2 → ℝ) 1 :=
    (continuous_apply (1 : Fin 2)).comp continuous_subtype_val
  exact isClosed_le hc1 ((continuous_const.sub (hc0.pow 2)).div_const 2)

theorem convexBody_parabolaBody : ConvexBody parabolaBody := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha1 : a ≤ 1 := by linarith
  have hbel : a • (x : Fin 2 → ℝ) + (1 - a) • (y : Fin 2 → ℝ) ∈ belCarrier (Fin 2) :=
    convex_belCarrier x.2 y.2 ha hb hab
  refine ⟨⟨a • (x : Fin 2 → ℝ) + (1 - a) • (y : Fin 2 → ℝ), hbel⟩, ?_, rfl⟩
  have hx' : (x : Fin 2 → ℝ) 1 ≤ (1 - (x : Fin 2 → ℝ) 0 ^ 2) / 2 := hx
  have hy' : (y : Fin 2 → ℝ) 1 ≤ (1 - (y : Fin 2 → ℝ) 0 ^ 2) / 2 := hy
  show (a • (x : Fin 2 → ℝ) + (1 - a) • (y : Fin 2 → ℝ)) 1
      ≤ (1 - (a • (x : Fin 2 → ℝ) + (1 - a) • (y : Fin 2 → ℝ)) 0 ^ 2) / 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hJ := sq_combo_le (p := (x : Fin 2 → ℝ) 0) (q := (y : Fin 2 → ℝ) 0) ha ha1
  have h1 := mul_le_mul_of_nonneg_left hx' ha
  have h2 := mul_le_mul_of_nonneg_left hy' hb
  nlinarith [hJ, h1, h2]

theorem ptwiseDown_parabolaBody : PtwiseDown parabolaBody := by
  intro y hy x hle
  have hy' : (y : Fin 2 → ℝ) 1 ≤ (1 - (y : Fin 2 → ℝ) 0 ^ 2) / 2 := hy
  have h0 := Pi.le_def.mp hle 0
  have h1 := Pi.le_def.mp hle 1
  show (x : Fin 2 → ℝ) 1 ≤ (1 - (x : Fin 2 → ℝ) 0 ^ 2) / 2
  nlinarith [mul_self_le_mul_self (x.nonneg 0) h0]

/-- **The parabola body is a Kosoy–Appel ultracontribution** (witness `W6 ∈ KA`). -/
theorem isUltra_parabolaBody : IsUltra parabolaBody :=
  ⟨parabolaBody_nonempty, isClosed_parabolaBody, convexBody_parabolaBody,
    ptwiseDown_parabolaBody⟩

/-- **The parabola body is a Halpern–Leung body** (witness `W6 ∈ HL`): an
ultracontribution with the full-mass member `δ₀`. -/
theorem isHL_parabolaBody : IsHL parabolaBody :=
  ⟨isUltra_parabolaBody, BelState.dirac 0, dirac_zero_mem_parabolaBody,
    BelState.mass_dirac 0⟩

/-! ## Masked corners

The ambient image of `ptwiseDownHull F` is the convex hull of a finite
set: the `{0,1}²`-masked corners of the generators.  The two directions:
corners are dominated by generators (so their hull sits inside the
image, which is convex); conversely a dominated point `x ≤ y` scales
each coordinate of `y` by a common ratio in `[0,1]²`, the scaling passes
through convex combinations, and a `[0,1]²`-scaling of a single
generator is a bilinear interpolation of its four corners. -/

/-- Coordinatewise scaling on the two-outcome carrier: `(a·y₀, b·y₁)`.
At `a, b ∈ {0,1}` these are the four masked corners of `y`. -/
def maskMul (a b : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a * y 0, b * y 1]

@[simp] lemma maskMul_apply_zero (a b : ℝ) (y : Fin 2 → ℝ) :
    maskMul a b y 0 = a * y 0 := rfl

@[simp] lemma maskMul_apply_one (a b : ℝ) (y : Fin 2 → ℝ) :
    maskMul a b y 1 = b * y 1 := rfl

/-- The masked corners of a finite generator set: all four `{0,1}²`-masks
of all generators.  Finite by construction (`maskedCorners_finite`). -/
def maskedCorners (F : Finset (BelState (Fin 2))) : Set (Fin 2 → ℝ) :=
  maskMul 0 0 '' carrierImage (F : Set (BelState (Fin 2)))
    ∪ maskMul 0 1 '' carrierImage (F : Set (BelState (Fin 2)))
    ∪ maskMul 1 0 '' carrierImage (F : Set (BelState (Fin 2)))
    ∪ maskMul 1 1 '' carrierImage (F : Set (BelState (Fin 2)))

lemma maskedCorners_finite (F : Finset (BelState (Fin 2))) :
    (maskedCorners F).Finite := by
  have hG : (carrierImage (F : Set (BelState (Fin 2)))).Finite :=
    F.finite_toSet.image _
  exact (((hG.image _).union (hG.image _)).union (hG.image _)).union (hG.image _)

lemma carrierImage_subset_belCarrier {V : Type*} [Fintype V]
    (S : Set (BelState V)) : carrierImage S ⊆ belCarrier V := by
  rintro _ ⟨z, _, rfl⟩
  exact z.2

/-- A `[0,1]²`-scaling of a point of the hull of the generators is
dominated by that point, hence lies in the ambient image of the
down-hull.  (At mask values this puts every corner inside the image.) -/
lemma maskMul_mem_carrierImage_ptwiseDownHull (F : Finset (BelState (Fin 2)))
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {w : Fin 2 → ℝ}
    (hw : w ∈ convexHull ℝ (carrierImage (F : Set (BelState (Fin 2)))))
    (hwbel : w ∈ belCarrier (Fin 2)) :
    maskMul a b w ∈ carrierImage (ptwiseDownHull F) := by
  have hw0 : (0 : ℝ) ≤ w 0 := hwbel.1 0
  have hw1 : (0 : ℝ) ≤ w 1 := hwbel.1 1
  have hs0 : a * w 0 ≤ w 0 := mul_le_of_le_one_left hw0 ha1
  have hs1 : b * w 1 ≤ w 1 := mul_le_of_le_one_left hw1 hb1
  have hbel : maskMul a b w ∈ belCarrier (Fin 2) := by
    refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, ?_⟩
    · show (0 : ℝ) ≤ a * w 0
      exact mul_nonneg ha hw0
    · show (0 : ℝ) ≤ b * w 1
      exact mul_nonneg hb hw1
    · rw [Fin.sum_univ_two, maskMul_apply_zero, maskMul_apply_one]
      have hsum : w 0 + w 1 ≤ 1 := by
        have h := hwbel.2
        rwa [Fin.sum_univ_two] at h
      linarith
  refine ⟨⟨maskMul a b w, hbel⟩, ⟨w, hw, ?_⟩, rfl⟩
  refine Pi.le_def.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · show a * w 0 ≤ w 0
    exact hs0
  · show b * w 1 ≤ w 1
    exact hs1

/-- The ambient image of a down-hull is convex: mixtures of dominated
points are dominated by the mixture of the dominating hull points. -/
lemma convex_carrierImage_ptwiseDownHull (F : Finset (BelState (Fin 2))) :
    Convex ℝ (carrierImage (ptwiseDownHull F)) := by
  rintro _ ⟨x1, ⟨y1, hy1, hle1⟩, rfl⟩ _ ⟨x2, ⟨y2, hy2, hle2⟩, rfl⟩ s t hs ht hst
  have hbel : s • (x1 : Fin 2 → ℝ) + t • (x2 : Fin 2 → ℝ) ∈ belCarrier (Fin 2) :=
    convex_belCarrier x1.2 x2.2 hs ht hst
  refine ⟨⟨s • (x1 : Fin 2 → ℝ) + t • (x2 : Fin 2 → ℝ), hbel⟩,
    ⟨s • y1 + t • y2, convex_convexHull ℝ _ hy1 hy2 hs ht hst, ?_⟩, rfl⟩
  refine Pi.le_def.mpr fun i => ?_
  show (s • (x1 : Fin 2 → ℝ) + t • (x2 : Fin 2 → ℝ)) i ≤ (s • y1 + t • y2) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (Pi.le_def.mp hle1 i) hs)
    (mul_le_mul_of_nonneg_left (Pi.le_def.mp hle2 i) ht)

/-- The box lemma at a single generator: a `[0,1]²`-scaling of `w` is the
bilinear interpolation of the four masked corners of `w`, with the
product-form weights `(1−a)(1−b), (1−a)b, a(1−b), ab`. -/
lemma maskMul_mem_convexHull_maskedCorners (F : Finset (BelState (Fin 2)))
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {w : Fin 2 → ℝ} (hw : w ∈ carrierImage (F : Set (BelState (Fin 2)))) :
    maskMul a b w ∈ convexHull ℝ (maskedCorners F) := by
  have h00 : maskMul 0 0 w ∈ convexHull ℝ (maskedCorners F) :=
    subset_convexHull ℝ _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_image_of_mem _ hw))))
  have h01 : maskMul 0 1 w ∈ convexHull ℝ (maskedCorners F) :=
    subset_convexHull ℝ _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_image_of_mem _ hw))))
  have h10 : maskMul 1 0 w ∈ convexHull ℝ (maskedCorners F) :=
    subset_convexHull ℝ _ (Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_image_of_mem _ hw)))
  have h11 : maskMul 1 1 w ∈ convexHull ℝ (maskedCorners F) :=
    subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_image_of_mem _ hw))
  have hkey : maskMul a b w
      = (1 - a) • ((1 - b) • maskMul 0 0 w + b • maskMul 0 1 w)
        + a • ((1 - b) • maskMul 1 0 w + b • maskMul 1 1 w) := by
    apply funext_fin_two <;>
      · simp only [maskMul_apply_zero, maskMul_apply_one, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
  have hcv := convex_convexHull ℝ (maskedCorners F)
  rw [hkey]
  exact hcv (hcv h00 h01 (by linarith) hb (by ring))
    (hcv h10 h11 (by linarith) hb (by ring)) (by linarith) ha (by ring)

/-- Coordinatewise Riesz decomposition on two outcomes: a nonnegative
point below `y` is a `[0,1]²`-scaling of `y`.  (Division-by-zero
conventions make the unconditional ratio `x i / y i` correct: at
`y i = 0` domination forces `x i = 0`, and the ratio is `0`.) -/
lemma exists_maskMul_eq {x y : Fin 2 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) (hle : x ≤ y) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ x = maskMul a b y := by
  refine ⟨x 0 / y 0, x 1 / y 1, div_nonneg (hx 0) (hy 0),
    div_le_one_of_le₀ (Pi.le_def.mp hle 0) (hy 0),
    div_nonneg (hx 1) (hy 1),
    div_le_one_of_le₀ (Pi.le_def.mp hle 1) (hy 1), ?_⟩
  apply funext_fin_two
  · show x 0 = x 0 / y 0 * y 0
    exact (div_mul_cancel_of_imp fun h =>
      le_antisymm (h ▸ Pi.le_def.mp hle 0) (hx 0)).symm
  · show x 1 = x 1 / y 1 * y 1
    exact (div_mul_cancel_of_imp fun h =>
      le_antisymm (h ▸ Pi.le_def.mp hle 1) (hx 1)).symm

/-- **The masked-corners identity**: the ambient image of the down-hull
of a finite set of distributions is the convex hull of its finitely many
masked corners. -/
theorem carrierImage_ptwiseDownHull_eq_convexHull_maskedCorners
    (F : Finset (BelState (Fin 2))) :
    carrierImage (ptwiseDownHull F) = convexHull ℝ (maskedCorners F) := by
  apply Set.Subset.antisymm
  · -- a dominated point is a common scaling of its dominating hull point,
    -- and scaling passes through the hull to land on corner interpolations
    rintro _ ⟨x, ⟨y, hy, hle⟩, rfl⟩
    have hybel : y ∈ belCarrier (Fin 2) :=
      convexHull_min (carrierImage_subset_belCarrier _) convex_belCarrier hy
    obtain ⟨a, b, ha, ha1, hb, hb1, hxeq⟩ :=
      exists_maskMul_eq x.nonneg hybel.1 hle
    show (x : Fin 2 → ℝ) ∈ convexHull ℝ (maskedCorners F)
    rw [hxeq]
    have hT : convexHull ℝ (carrierImage (F : Set (BelState (Fin 2))))
        ⊆ {v : Fin 2 → ℝ | maskMul a b v ∈ convexHull ℝ (maskedCorners F)} := by
      apply convexHull_min
      · intro w hw
        exact maskMul_mem_convexHull_maskedCorners F ha ha1 hb hb1 hw
      · intro v1 h1 v2 h2 s t hs ht hst
        show maskMul a b (s • v1 + t • v2) ∈ convexHull ℝ (maskedCorners F)
        have hlin : maskMul a b (s • v1 + t • v2)
            = s • maskMul a b v1 + t • maskMul a b v2 := by
          apply funext_fin_two <;>
            · simp only [maskMul_apply_zero, maskMul_apply_one, Pi.add_apply,
                Pi.smul_apply, smul_eq_mul]
              ring
        rw [hlin]
        exact convex_convexHull ℝ _ h1 h2 hs ht hst
    exact hT hy
  · -- corners are dominated by generators; the image is convex
    apply convexHull_min
    · intro c hc
      rcases hc with ((⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩ <;>
        exact maskMul_mem_carrierImage_ptwiseDownHull F (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
          (subset_convexHull ℝ _ hw) (carrierImage_subset_belCarrier _ hw)
    · exact convex_carrierImage_ptwiseDownHull F

/-! ## The arc of extreme points -/

/-- The boundary-arc point `(t, (1−t²)/2)` of the parabola body, as a
distribution (carrier membership is `arc_mass_le_one`). -/
noncomputable def arcPt (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : BelState (Fin 2) :=
  ⟨![t, (1 - t ^ 2) / 2], by
    refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, ?_⟩
    · show (0 : ℝ) ≤ t
      exact h0
    · show (0 : ℝ) ≤ (1 - t ^ 2) / 2
      nlinarith
    · rw [Fin.sum_univ_two]
      show t + (1 - t ^ 2) / 2 ≤ 1
      exact arc_mass_le_one⟩

@[simp] lemma coe_arcPt_zero {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (arcPt t h0 h1 : Fin 2 → ℝ) 0 = t := rfl

@[simp] lemma coe_arcPt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (arcPt t h0 h1 : Fin 2 → ℝ) 1 = (1 - t ^ 2) / 2 := rfl

lemma arcPt_mem_parabolaBody {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    arcPt t h0 h1 ∈ parabolaBody := by
  show (arcPt t h0 h1 : Fin 2 → ℝ) 1
      ≤ (1 - (arcPt t h0 h1 : Fin 2 → ℝ) 0 ^ 2) / 2
  rw [coe_arcPt_zero, coe_arcPt_one]

/-- **Every arc point is an extreme point** of the ambient image of the
parabola body.  If `(t, (1−t²)/2)` is a proper mixture of two members,
the first coordinates must agree with `t` by the *strict* concavity of
the boundary (equality case of Jensen for the square), and then the
second coordinates are forced up to the boundary. -/
theorem coe_arcPt_mem_extremePoints {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (arcPt t h0 h1 : Fin 2 → ℝ)
      ∈ Set.extremePoints ℝ (carrierImage parabolaBody) := by
  rw [mem_extremePoints]
  refine ⟨mem_carrierImage (arcPt_mem_parabolaBody h0 h1), ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ ⟨s, u, hs, hu, hsu, hcomb⟩
  have hy' : (y : Fin 2 → ℝ) 1 ≤ (1 - (y : Fin 2 → ℝ) 0 ^ 2) / 2 := hy
  have hz' : (z : Fin 2 → ℝ) 1 ≤ (1 - (z : Fin 2 → ℝ) 0 ^ 2) / 2 := hz
  have hu' : u = 1 - s := by linarith
  subst hu'
  have hs1 : s < 1 := by linarith
  -- read the two coordinates of the mixture equation
  have hc0 : s * (y : Fin 2 → ℝ) 0 + (1 - s) * (z : Fin 2 → ℝ) 0 = t := by
    have h := congrFun hcomb 0
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coe_arcPt_zero] using h
  have hc1 : s * (y : Fin 2 → ℝ) 1 + (1 - s) * (z : Fin 2 → ℝ) 1
      = (1 - t ^ 2) / 2 := by
    have h := congrFun hcomb 1
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coe_arcPt_one] using h
  -- first coordinates agree: equality case of Jensen
  have hup := mul_le_mul_of_nonneg_left hy' hs.le
  have hvq := mul_le_mul_of_nonneg_left hz' (by linarith : (0 : ℝ) ≤ 1 - s)
  have hJ := sq_combo_le (p := (y : Fin 2 → ℝ) 0) (q := (z : Fin 2 → ℝ) 0)
    hs.le (by linarith)
  have hle1 : s * (y : Fin 2 → ℝ) 0 ^ 2 + (1 - s) * (z : Fin 2 → ℝ) 0 ^ 2
      ≤ t ^ 2 := by nlinarith [hc1, hup, hvq]
  have hge1 : t ^ 2
      ≤ s * (y : Fin 2 → ℝ) 0 ^ 2 + (1 - s) * (z : Fin 2 → ℝ) 0 ^ 2 := by
    calc t ^ 2 = (s * (y : Fin 2 → ℝ) 0 + (1 - s) * (z : Fin 2 → ℝ) 0) ^ 2 := by
          rw [hc0]
      _ ≤ _ := hJ
  have heq : s * (y : Fin 2 → ℝ) 0 ^ 2 + (1 - s) * (z : Fin 2 → ℝ) 0 ^ 2
      = (s * (y : Fin 2 → ℝ) 0 + (1 - s) * (z : Fin 2 → ℝ) 0) ^ 2 := by
    rw [hc0]
    exact le_antisymm hle1 hge1
  have hpq : (y : Fin 2 → ℝ) 0 = (z : Fin 2 → ℝ) 0 :=
    eq_of_sq_combo_eq hs hs1 heq
  have hpt : (y : Fin 2 → ℝ) 0 = t := by rw [← hc0, hpq]; ring
  have hqt : (z : Fin 2 → ℝ) 0 = t := hpq ▸ hpt
  -- second coordinates are forced to the boundary
  rw [hpt] at hy'
  rw [hqt] at hz'
  have hy1 : (y : Fin 2 → ℝ) 1 = (1 - t ^ 2) / 2 := by
    by_contra hne
    have hlt : (y : Fin 2 → ℝ) 1 < (1 - t ^ 2) / 2 := lt_of_le_of_ne hy' hne
    have h1' : s * (y : Fin 2 → ℝ) 1 < s * ((1 - t ^ 2) / 2) :=
      mul_lt_mul_of_pos_left hlt hs
    have h2' : (1 - s) * (z : Fin 2 → ℝ) 1 ≤ (1 - s) * ((1 - t ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hz' (by linarith)
    nlinarith [hc1]
  have hz1 : (z : Fin 2 → ℝ) 1 = (1 - t ^ 2) / 2 := by
    by_contra hne
    have hlt : (z : Fin 2 → ℝ) 1 < (1 - t ^ 2) / 2 := lt_of_le_of_ne hz' hne
    have h1' : (1 - s) * (z : Fin 2 → ℝ) 1 < (1 - s) * ((1 - t ^ 2) / 2) :=
      mul_lt_mul_of_pos_left hlt (by linarith)
    have h2' : s * (y : Fin 2 → ℝ) 1 ≤ s * ((1 - t ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hy' hs.le
    nlinarith [hc1]
  constructor
  · apply funext_fin_two
    · rw [coe_arcPt_zero]
      exact hpt
    · rw [coe_arcPt_one]
      exact hy1
  · apply funext_fin_two
    · rw [coe_arcPt_zero]
      exact hqt
    · rw [coe_arcPt_one]
      exact hz1

/-! ## The refutation -/

/-- **The parabola body is not of Mio–Vignudelli–Sarkis shape**
(witness `W6 ∉ MVS`; with `isUltra_parabolaBody` this discharges
`KA ⊋ MVS`, and with `isHL_parabolaBody`, `HL ⊄ MVS`).  A down-hull of a
finite set has an ambient image with finitely many extreme points
(masked-corners identity + `extremePoints_convexHull_subset`), but the
parabola's boundary arc `n ↦ (1/(n+2), (1−1/(n+2)²)/2)` injects `ℕ`
into the extreme points of this body's image. -/
theorem not_isMVS_parabolaBody : ¬ IsMVS parabolaBody := by
  rintro ⟨F, -, hF⟩
  have hfin : (Set.extremePoints ℝ (carrierImage parabolaBody)).Finite := by
    rw [hF, carrierImage_ptwiseDownHull_eq_convexHull_maskedCorners]
    exact (maskedCorners_finite F).subset extremePoints_convexHull_subset
  have harc0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := fun n => by positivity
  have harc1 : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hinf : (Set.extremePoints ℝ (carrierImage parabolaBody)).Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ =>
        (arcPt (1 / ((n : ℝ) + 2)) (harc0 n) (harc1 n) : Fin 2 → ℝ))
    · intro n m h
      have h0 := congrFun h 0
      simp only [coe_arcPt_zero] at h0
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp at h0
      have : (n : ℝ) = (m : ℝ) := by linarith
      exact_mod_cast this
    · intro n
      exact coe_arcPt_mem_extremePoints (harc0 n) (harc1 n)
  exact hinf hfin

end CredalPoset

end SuFunctor.Universe
