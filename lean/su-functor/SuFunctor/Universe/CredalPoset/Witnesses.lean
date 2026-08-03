import SuFunctor.Universe.CredalPoset.Defs

/-! # The witness zoo: separating bodies at `V = Fin 2`

Concrete bodies over the two-outcome carrier discharging the negative
cells of the credal-poset membership matrix.  Each witness is a
frozen set-side definition; each membership or refutation below is a
named theorem.  The zoo:

* **W1** `twoRays` — the union of the two coordinate rays: a credal
  body that is not convex (CB ⊋ CV).
* **W2** `harmonicBody` — `{x | x₀ + 2·x₁ ≤ 1}`: ultra (hence convex),
  Halpern–Leung, MVS — and **not Richardson** (the A2 core: penalty
  convexity is not necessary for body convexity), nor Cozman.
* **W3** `segBody` — the radial segment over the barycenter: Cozman
  but not pointwise-down-closed, hence not ultra (CS ⊄ KA), not HL,
  not MVS.  (Its Richardson membership follows from T6, Cozman →
  Richardson, supplied by the inclusions module.)
* **W4** `bottom` — `{0}`: ultra, MVS, Richardson (via the `⊤`
  penalty), and **not HL** (KA ⊋ HL), not Cozman.
* **W10** `halfBody` — `{x | mass x ≤ ½}`: Richardson (via a constant
  finite penalty), ultra, MVS — not HL, **not Cozman** (R ⊋ CS).

The heavy refutation `W2 ∉ R` runs entirely exp-free through the grade
transport: `harmonicBody = compile f` forces the grades
`grade (f δa′) = 1`, `grade (f δb′) = ½`, `grade (f mid′) = ⅔`, and
penalty convexity would square the middle one into `½ ≤ 4/9`.
The membership matrix and its expected verdicts were preregistered
before these proofs were built.
-/

namespace SuFunctor.Universe

open scoped ENNReal

namespace CredalPoset

/-! ## General helpers (any finite `V`) -/

section Helpers

variable {V : Type*} [Fintype V]

/-- Mass transforms linearly under scaling. -/
theorem mass_scale (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x : BelState V) :
    (BelState.scale t h0 h1 x).mass = t * x.mass := by
  simp only [BelState.mass, BelState.coe_scale, Pi.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]

/-- Scaling by `1` is the identity. -/
theorem scale_one (x : BelState V) :
    BelState.scale 1 zero_le_one le_rfl x = x :=
  Subtype.ext (by rw [BelState.coe_scale, one_smul])

/-- The radial embedding contains its generator: `K ⊆ [0,1] • K`. -/
theorem subset_scaleSegment (K : Set (BelState V)) : K ⊆ scaleSegment K :=
  fun x hx => ⟨x, hx, 1, zero_le_one, le_rfl, (scale_one x).symm⟩

/-- Every Cozman body contains a full-mass member (its generating
credal set survives at scale `1`). -/
theorem exists_mass_one_of_isCozman {S : Set (BelState V)}
    (h : IsCozman S) : ∃ x ∈ S, BelState.mass x = 1 := by
  obtain ⟨K, ⟨x, hxK⟩, -, -, hmass, rfl⟩ := h
  exact ⟨x, subset_scaleSegment K hxK, hmass x hxK⟩

/-- Pointwise-down hulls are pointwise-down-closed. -/
theorem ptwiseDown_ptwiseDownHull (F : Finset (BelState V)) :
    PtwiseDown (ptwiseDownHull F) := by
  rintro y ⟨z, hz, hyz⟩ x hxy
  exact ⟨z, hz, le_trans hxy hyz⟩

/-- A set that is not pointwise-down-closed is not an MVS body. -/
theorem not_isMVS_of_not_ptwiseDown {S : Set (BelState V)}
    (h : ¬ PtwiseDown S) : ¬ IsMVS S := by
  rintro ⟨F, -, rfl⟩
  exact h (ptwiseDown_ptwiseDownHull F)

/-- Zero mass forces the zero state. -/
theorem eq_zero_of_mass_eq_zero {x : BelState V} (h : x.mass = 0) :
    x = BelState.zero V := by
  apply Subtype.ext
  funext v
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => x.nonneg w)).mp h v (Finset.mem_univ v)
  simpa using h0

/-- A distribution coordinatewise below zero is the zero state. -/
theorem eq_zero_of_coe_le_zero {x : BelState V}
    (h : (x : V → ℝ) ≤ (0 : V → ℝ)) : x = BelState.zero V := by
  apply Subtype.ext
  funext v
  exact le_antisymm (h v) (x.nonneg v)

/-- Normalize a distribution of positive mass to a probability state. -/
noncomputable def unitize (x : BelState V) (h : 0 < x.mass) : ProbState V :=
  ⟨x.mass⁻¹ • (x : V → ℝ),
    fun v => mul_nonneg (inv_nonneg.mpr h.le) (x.nonneg v),
    by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ h.ne'⟩

@[simp] theorem coe_unitize (x : BelState V) (h : 0 < x.mass) :
    ((unitize x h : ProbState V) : V → ℝ) = x.mass⁻¹ • (x : V → ℝ) := rfl

/-- Polar decomposition through the unitization: `x = mass x • x̂`. -/
theorem coe_eq_mass_smul_unitize (x : BelState V) (h : 0 < x.mass) :
    (x : V → ℝ) = x.mass • ((unitize x h : ProbState V) : V → ℝ) := by
  rw [coe_unitize, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

/-- The tip of the ray at `μ` belongs to the body: the grade is
attained, not just approached. -/
theorem tip_mem_compile (f : ProbPenalty V) (μ : ProbState V) :
    scalePoint (grade (f μ)) (grade_nonneg _) (grade_le_one _) μ
      ∈ compile f :=
  ⟨μ, grade (f μ), grade_nonneg _, le_rfl, rfl⟩

/-- Constant penalties are convex. -/
theorem penaltyConvex_const (c : ℝ≥0∞) :
    PenaltyConvex (fun _ : ProbState V => c) := by
  intro μ ν s t hs ht hst
  refine le_of_eq ?_
  rw [← add_mul, ← ENNReal.ofReal_add hs.le ht.le, hst,
    ENNReal.ofReal_one, one_mul]

/-- The grade of the penalty height `log 2` is `1/2`. -/
theorem grade_ofReal_log_two :
    grade (ENNReal.ofReal (Real.log 2)) = 1 / 2 := by
  rw [grade_of_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.log_nonneg one_le_two),
    Real.exp_neg, Real.exp_log two_pos]
  norm_num

/-- The carrier image of a coordinate-condition body is the carrier
intersected with the ambient condition. -/
theorem carrierImage_setOf (P : (V → ℝ) → Prop) :
    carrierImage {x : BelState V | P (x : V → ℝ)}
      = belCarrier V ∩ {y | P y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hy, hP⟩
    exact ⟨⟨y, hy⟩, hP, rfl⟩

/-- Carrier image of a singleton. -/
theorem carrierImage_singleton (x : BelState V) :
    carrierImage {x} = {(x : V → ℝ)} := Set.image_singleton

/-- Carrier image of a pair. -/
theorem carrierImage_pair (x y : BelState V) :
    carrierImage {x, y} = {(x : V → ℝ), (y : V → ℝ)} :=
  Set.image_pair _ _ _

end Helpers

/-! ## `Fin 2` vocabulary -/

section Fin2

/-- A two-outcome distribution from a pair of masses (the `BelState`
sibling of `ProbState.ofPair`). -/
def bel2 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    BelState (Fin 2) :=
  ⟨![p, q], ⟨fun v => by fin_cases v <;> simpa, by
    rw [Fin.sum_univ_two]; simpa⟩⟩

@[simp] theorem bel2_apply_zero (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q ≤ 1) :
    ((bel2 p q hp hq hpq : BelState (Fin 2)) : Fin 2 → ℝ) 0 = p := rfl

@[simp] theorem bel2_apply_one (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q ≤ 1) :
    ((bel2 p q hp hq hpq : BelState (Fin 2)) : Fin 2 → ℝ) 1 = q := rfl

/-- Two-outcome mass reads off the two coordinates. -/
theorem mass_eq_two (x : BelState (Fin 2)) :
    BelState.mass x = (x : Fin 2 → ℝ) 0 + (x : Fin 2 → ℝ) 1 :=
  Fin.sum_univ_two _

@[simp] theorem mass_bel2 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q ≤ 1) : (bel2 p q hp hq hpq).mass = p + q := by
  rw [mass_eq_two, bel2_apply_zero, bel2_apply_one]

/-- `δa`: the point mass at outcome `0`. -/
def δa : BelState (Fin 2) := bel2 1 0 zero_le_one le_rfl (by norm_num)

/-- `δb`: the point mass at outcome `1`. -/
def δb : BelState (Fin 2) := bel2 0 1 le_rfl zero_le_one (by norm_num)

/-- `(1/2, 0)`: the half-mass point on the `a`-ray. -/
noncomputable def halfA : BelState (Fin 2) :=
  bel2 (1/2) 0 (by norm_num) le_rfl (by norm_num)

/-- `(0, 1/2)`: the half-mass point on the `b`-ray. -/
noncomputable def halfB : BelState (Fin 2) :=
  bel2 0 (1/2) le_rfl (by norm_num) (by norm_num)

/-- `(1/2, 1/2)`: the barycenter. -/
noncomputable def midB : BelState (Fin 2) :=
  bel2 (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem δa_zero : ((δa : BelState (Fin 2)) : Fin 2 → ℝ) 0 = 1 := rfl
@[simp] theorem δa_one : ((δa : BelState (Fin 2)) : Fin 2 → ℝ) 1 = 0 := rfl
@[simp] theorem δb_zero : ((δb : BelState (Fin 2)) : Fin 2 → ℝ) 0 = 0 := rfl
@[simp] theorem δb_one : ((δb : BelState (Fin 2)) : Fin 2 → ℝ) 1 = 1 := rfl
@[simp] theorem halfA_zero :
    ((halfA : BelState (Fin 2)) : Fin 2 → ℝ) 0 = 1/2 := rfl
@[simp] theorem halfA_one :
    ((halfA : BelState (Fin 2)) : Fin 2 → ℝ) 1 = 0 := rfl
@[simp] theorem halfB_zero :
    ((halfB : BelState (Fin 2)) : Fin 2 → ℝ) 0 = 0 := rfl
@[simp] theorem halfB_one :
    ((halfB : BelState (Fin 2)) : Fin 2 → ℝ) 1 = 1/2 := rfl
@[simp] theorem midB_zero :
    ((midB : BelState (Fin 2)) : Fin 2 → ℝ) 0 = 1/2 := rfl
@[simp] theorem midB_one :
    ((midB : BelState (Fin 2)) : Fin 2 → ℝ) 1 = 1/2 := rfl

/-- `δa′`: the flat-carrier point mass at outcome `0`. -/
def δa' : ProbState (Fin 2) :=
  ProbState.ofPair 1 0 zero_le_one le_rfl (by norm_num)

/-- `δb′`: the flat-carrier point mass at outcome `1`. -/
def δb' : ProbState (Fin 2) :=
  ProbState.ofPair 0 1 le_rfl zero_le_one (by norm_num)

/-- `mid′`: the uniform probability state. -/
noncomputable def midP : ProbState (Fin 2) :=
  ProbState.ofPair (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem δa'_zero :
    ((δa' : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 1 := rfl
@[simp] theorem δa'_one :
    ((δa' : ProbState (Fin 2)) : Fin 2 → ℝ) 1 = 0 := rfl
@[simp] theorem δb'_zero :
    ((δb' : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 0 := rfl
@[simp] theorem δb'_one :
    ((δb' : ProbState (Fin 2)) : Fin 2 → ℝ) 1 = 1 := rfl
@[simp] theorem midP_zero :
    ((midP : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 1/2 := rfl
@[simp] theorem midP_one :
    ((midP : ProbState (Fin 2)) : Fin 2 → ℝ) 1 = 1/2 := rfl

/-- Convexity of the harmonic half-plane trace. -/
theorem convex_harmonicHalfspace :
    Convex ℝ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 1} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at *
  nlinarith [mul_le_mul_of_nonneg_left hx ha,
    mul_le_mul_of_nonneg_left hy hb]

/-- Convexity of the half-mass half-space. -/
theorem convex_massHalfspace :
    Convex ℝ {y : Fin 2 → ℝ | ∑ v, y v ≤ 1/2} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at *
  nlinarith [mul_le_mul_of_nonneg_left hx ha,
    mul_le_mul_of_nonneg_left hy hb]

end Fin2

/-! ## W1: `twoRays` — a credal body that is not convex (CB ⊋ CV) -/

/-- **W1** `twoRays`: the union of the two coordinate rays
`[0,1]·δa ∪ [0,1]·δb`, cut out by "some coordinate vanishes". -/
def twoRays : Set (BelState (Fin 2)) :=
  {x | (x : Fin 2 → ℝ) 1 = 0 ∨ (x : Fin 2 → ℝ) 0 = 0}

theorem isCredalBody_twoRays : IsCredalBody twoRays := by
  refine ⟨⟨δa, Or.inl δa_one⟩, ?_, ?_⟩
  · have h1 : IsClosed {x : BelState (Fin 2) | (x : Fin 2 → ℝ) 1 = 0} :=
      isClosed_eq ((continuous_apply 1).comp continuous_subtype_val)
        continuous_const
    have h0 : IsClosed {x : BelState (Fin 2) | (x : Fin 2 → ℝ) 0 = 0} :=
      isClosed_eq ((continuous_apply 0).comp continuous_subtype_val)
        continuous_const
    have hsplit : twoRays
        = {x : BelState (Fin 2) | (x : Fin 2 → ℝ) 1 = 0}
          ∪ {x : BelState (Fin 2) | (x : Fin 2 → ℝ) 0 = 0} := rfl
    rw [hsplit]
    exact h1.union h0
  · rintro x (h | h) t h0 h1
    · exact Or.inl (by
        rw [BelState.coe_scale, Pi.smul_apply, smul_eq_mul, h, mul_zero])
    · exact Or.inr (by
        rw [BelState.coe_scale, Pi.smul_apply, smul_eq_mul, h, mul_zero])

theorem not_convexBody_twoRays : ¬ ConvexBody twoRays := by
  intro h
  have hmem := h (mem_carrierImage (Or.inl δa_one))
    (mem_carrierImage (Or.inr δb_zero))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  obtain ⟨y, hy, hey⟩ := hmem
  have h0 := congrFun hey 0
  have h1 := congrFun hey 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, δa_zero, δa_one,
    δb_zero, δb_one, mul_one, mul_zero, add_zero, zero_add] at h0 h1
  rcases hy with hc | hc
  · rw [hc] at h1
    norm_num at h1
  · rw [hc] at h0
    norm_num at h0

/-- **CB ⊋ CV**: a credal body that is not a convex credal body. -/
theorem isCredalBody_twoRays_not_convex :
    IsCredalBody twoRays ∧ ¬ IsConvexCredalBody twoRays :=
  ⟨isCredalBody_twoRays, fun h => not_convexBody_twoRays h.2⟩

/-! ## W2: `harmonicBody` — convex but not Richardson (the A2 core) -/

/-- **W2** `harmonicBody`: the carrier trace of `x₀ + 2·x₁ ≤ 1`.  The
tightest body whose ray-lengths realize the harmonic-looking grade
profile `1, ½, ⅔` on `δa′, δb′, mid′`. -/
def harmonicBody : Set (BelState (Fin 2)) :=
  {x | (x : Fin 2 → ℝ) 0 + 2 * (x : Fin 2 → ℝ) 1 ≤ 1}

theorem mem_harmonicBody_iff {x : BelState (Fin 2)} :
    x ∈ harmonicBody
      ↔ (x : Fin 2 → ℝ) 0 + 2 * (x : Fin 2 → ℝ) 1 ≤ 1 := Iff.rfl

theorem δa_mem_harmonicBody : δa ∈ harmonicBody := by
  rw [mem_harmonicBody_iff]
  norm_num

theorem halfB_mem_harmonicBody : halfB ∈ harmonicBody := by
  rw [mem_harmonicBody_iff]
  norm_num

theorem isUltra_harmonicBody : IsUltra harmonicBody := by
  refine ⟨⟨δa, δa_mem_harmonicBody⟩, ?_, ?_, ?_⟩
  · exact isClosed_le (Continuous.add
      ((continuous_apply 0).comp continuous_subtype_val)
      (continuous_const.mul
        ((continuous_apply 1).comp continuous_subtype_val)))
      continuous_const
  · show Convex ℝ (carrierImage harmonicBody)
    have himg : carrierImage harmonicBody
        = belCarrier (Fin 2) ∩ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 1} :=
      carrierImage_setOf (fun y => y 0 + 2 * y 1 ≤ 1)
    rw [himg]
    exact convex_belCarrier.inter convex_harmonicHalfspace
  · intro y hy x hxy
    have hy' := mem_harmonicBody_iff.mp hy
    rw [mem_harmonicBody_iff]
    have h0 := hxy 0
    have h1 := hxy 1
    linarith

theorem isHL_harmonicBody : IsHL harmonicBody :=
  ⟨isUltra_harmonicBody, δa, δa_mem_harmonicBody, by
    rw [mass_eq_two]; norm_num⟩

theorem isMVS_harmonicBody : IsMVS harmonicBody := by
  classical
  refine ⟨{δa, halfB}, ⟨δa, Finset.mem_insert_self _ _⟩, ?_⟩
  have himg : carrierImage
      ((({δa, halfB} : Finset (BelState (Fin 2)))
        : Set (BelState (Fin 2))))
      = {((δa : BelState (Fin 2)) : Fin 2 → ℝ),
         ((halfB : BelState (Fin 2)) : Fin 2 → ℝ)} := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact carrierImage_pair _ _
  ext x
  constructor
  · intro hx
    have hx' := mem_harmonicBody_iff.mp hx
    refine ⟨(x : Fin 2 → ℝ) 0 • ((δa : BelState (Fin 2)) : Fin 2 → ℝ)
        + (1 - (x : Fin 2 → ℝ) 0)
          • ((halfB : BelState (Fin 2)) : Fin 2 → ℝ), ?_, ?_⟩
    · rw [himg, convexHull_pair]
      exact ⟨(x : Fin 2 → ℝ) 0, 1 - (x : Fin 2 → ℝ) 0, x.nonneg 0,
        by linarith [x.apply_le_one 0], by ring, rfl⟩
    · rw [Pi.le_def, Fin.forall_fin_two]
      constructor
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, δa_zero,
          halfB_zero, mul_one, mul_zero, add_zero, le_refl]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, δa_one,
          halfB_one, mul_zero, zero_add]
        linarith
  · rintro ⟨y, hy, hxy⟩
    rw [himg, convexHull_pair] at hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have h0 := hxy 0
    have h1 := hxy 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, δa_zero, δa_one,
      halfB_zero, halfB_one, mul_one, mul_zero,
      add_zero, zero_add] at h0 h1
    rw [mem_harmonicBody_iff]
    linarith

/-- **W2 ∉ R** (the A2 core): no *convex* penalty compiles to the
harmonic body.  Exp-free: the body forces `f δa′ = 0`,
`grade (f δb′) = ½`, `grade (f mid′) = ⅔`; convexity at the half-half
mixture of the diracs plus the grade transport `grade_add` would give
`(grade (½ ⬝ f δb′))² = ½` with `grade (½ ⬝ f δb′) ≤ ⅔` — i.e.
`½ ≤ 4/9`. -/
theorem not_isRichardsonBody_harmonicBody :
    ¬ IsRichardsonBody harmonicBody := by
  rintro ⟨f, hconv, -, heq⟩
  -- (a) the penalty vanishes at the a-dirac
  have hfa : f δa' = 0 := by
    rw [← toBel_mem_compile_iff, ← heq]
    rw [mem_harmonicBody_iff]
    simp only [ProbState.toBel_coe, δa'_zero, δa'_one]
    norm_num
  -- (b) the grade at the b-dirac is exactly 1/2
  have hgb : grade (f δb') = 1 / 2 := by
    have hle : grade (f δb') ≤ 1 / 2 := by
      have htip := tip_mem_compile f δb'
      rw [← heq, mem_harmonicBody_iff] at htip
      simp only [scalePoint_coe, Pi.smul_apply, smul_eq_mul, δb'_zero,
        δb'_one, mul_zero, mul_one] at htip
      linarith
    have hge : 1 / 2 ≤ grade (f δb') := by
      have hmem : halfB ∈ compile f := by
        rw [← heq]
        exact halfB_mem_harmonicBody
      refine compile_scale_le hmem (by norm_num : (0:ℝ) < 1/2) ?_
      funext v
      fin_cases v <;>
        simp [halfB, δb', bel2, ProbState.ofPair, Pi.smul_apply,
          smul_eq_mul]
    exact le_antisymm hle hge
  -- (c) the grade at the barycenter is exactly 2/3
  have hgm : grade (f midP) = 2 / 3 := by
    have hle : grade (f midP) ≤ 2 / 3 := by
      have htip := tip_mem_compile f midP
      rw [← heq, mem_harmonicBody_iff] at htip
      simp only [scalePoint_coe, Pi.smul_apply, smul_eq_mul, midP_zero,
        midP_one] at htip
      linarith
    have hge : 2 / 3 ≤ grade (f midP) := by
      have hmem : bel2 (1/3) (1/3) (by norm_num) (by norm_num)
          (by norm_num) ∈ compile f := by
        rw [← heq, mem_harmonicBody_iff]
        norm_num
      refine compile_scale_le hmem (by norm_num : (0:ℝ) < 2/3) ?_
      funext v
      fin_cases v <;>
        simp [midP, bel2, ProbState.ofPair, Pi.smul_apply,
          smul_eq_mul] <;> norm_num
    exact le_antisymm hle hge
  -- penalty convexity at the half-half mixture of the diracs
  have hst : (1:ℝ)/2 + 1/2 = 1 := by norm_num
  have key : ∀ (h₁ : (0:ℝ) ≤ 1/2) (h₂ : (0:ℝ) ≤ 1/2)
      (h₃ : (1:ℝ)/2 + 1/2 = 1),
      ProbState.mix (1/2) (1/2) h₁ h₂ h₃ δa' δb' = midP := by
    intro h₁ h₂ h₃
    apply Subtype.ext
    funext v
    fin_cases v <;>
      simp [ProbState.coe_mix, δa', δb', midP, ProbState.ofPair,
        smul_eq_mul]
  have hc := hconv δa' δb' (1/2) (1/2) one_half_pos one_half_pos hst
  rw [key one_half_pos.le one_half_pos.le hst, hfa, mul_zero,
    zero_add] at hc
  -- squeeze: grade of the bound, squared, is the grade at δb′
  have hgB_le : grade (ENNReal.ofReal (1/2) * f δb') ≤ 2 / 3 := by
    rw [← hgm]
    exact grade_anti hc
  have hBB : ENNReal.ofReal (1/2) * f δb'
      + ENNReal.ofReal (1/2) * f δb' = f δb' := by
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hsq : grade (ENNReal.ofReal (1/2) * f δb')
      * grade (ENNReal.ofReal (1/2) * f δb') = 1 / 2 := by
    rw [← grade_add, hBB, hgb]
  have habs : grade (ENNReal.ofReal (1/2) * f δb')
      * grade (ENNReal.ofReal (1/2) * f δb') ≤ 2 / 3 * (2 / 3) :=
    mul_le_mul hgB_le hgB_le (grade_nonneg _) (by norm_num)
  rw [hsq] at habs
  norm_num at habs

/-- **W2 ∉ CS**: the harmonic body is no radially-embedded classical
credal set — the half-`b` point's radial parent is the `b`-dirac,
which violates the constraint. -/
theorem not_isCozman_harmonicBody : ¬ IsCozman harmonicBody := by
  rintro ⟨K, -, -, -, hmass, heq⟩
  have hmem : halfB ∈ scaleSegment K := by
    rw [← heq]
    exact halfB_mem_harmonicBody
  obtain ⟨x, hxK, t, h0, h1, hxe⟩ := hmem
  have hxS : x ∈ harmonicBody := by
    rw [heq]
    exact subset_scaleSegment K hxK
  -- mass bookkeeping forces t = 1/2
  have em : halfB.mass = t * x.mass := by rw [hxe, mass_scale]
  rw [hmass x hxK, mul_one] at em
  have hm : halfB.mass = 1/2 := by rw [mass_eq_two]; norm_num
  rw [hm] at em
  -- coordinate 1 then forces x₁ = 1
  have e1 : ((halfB : BelState (Fin 2)) : Fin 2 → ℝ) 1
      = t * (x : Fin 2 → ℝ) 1 := by
    rw [hxe, BelState.coe_scale, Pi.smul_apply, smul_eq_mul]
  rw [halfB_one, ← em] at e1
  have hx1 : (x : Fin 2 → ℝ) 1 = 1 := by linarith
  have hxc := mem_harmonicBody_iff.mp hxS
  have hx0 := x.nonneg 0
  rw [hx1] at hxc
  linarith

/-! ## W3: `segBody` — Cozman but not pointwise-down (CS ⊄ KA) -/

/-- **W3** `segBody`: the radial segment over the barycenter,
`[0,1] • {(½,½)}`. -/
def segBody : Set (BelState (Fin 2)) := scaleSegment {midB}

theorem isCozman_segBody : IsCozman segBody := by
  refine ⟨{midB}, ⟨midB, rfl⟩, isClosed_singleton, ?_, ?_, rfl⟩
  · show Convex ℝ (carrierImage {midB})
    rw [carrierImage_singleton]
    exact convex_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, mass_eq_two]
    norm_num

/-- **W3 ∉ KA, the down-closure leg**: `(½,0)` sits coordinatewise
below the barycenter but on no ray through it. -/
theorem not_ptwiseDown_segBody : ¬ PtwiseDown segBody := by
  intro h
  have hmid : midB ∈ segBody := subset_scaleSegment _ rfl
  have hle : ((halfA : BelState (Fin 2)) : Fin 2 → ℝ)
      ≤ ((midB : BelState (Fin 2)) : Fin 2 → ℝ) := by
    rw [Pi.le_def, Fin.forall_fin_two]
    norm_num
  obtain ⟨x, hx, t, h0, h1, hxe⟩ := h midB hmid halfA hle
  have hx' : x = midB := hx
  subst hx'
  have e0 : ((halfA : BelState (Fin 2)) : Fin 2 → ℝ) 0
      = t * ((midB : BelState (Fin 2)) : Fin 2 → ℝ) 0 := by
    rw [hxe, BelState.coe_scale, Pi.smul_apply, smul_eq_mul]
  have e1 : ((halfA : BelState (Fin 2)) : Fin 2 → ℝ) 1
      = t * ((midB : BelState (Fin 2)) : Fin 2 → ℝ) 1 := by
    rw [hxe, BelState.coe_scale, Pi.smul_apply, smul_eq_mul]
  rw [halfA_zero, midB_zero] at e0
  rw [halfA_one, midB_one] at e1
  linarith

theorem not_isUltra_segBody : ¬ IsUltra segBody :=
  fun h => not_ptwiseDown_segBody h.2.2.2

theorem not_isHL_segBody : ¬ IsHL segBody :=
  fun h => not_isUltra_segBody h.isUltra

theorem not_isMVS_segBody : ¬ IsMVS segBody :=
  not_isMVS_of_not_ptwiseDown not_ptwiseDown_segBody

-- `IsRichardsonBody segBody` follows from T6 (Cozman → Richardson,
-- the inclusions leg) composed with `isCozman_segBody`; the (W3, R)
-- matrix cell rides that composition at merge.

/-! ## W4: `bottom` — everything but HL and CS (KA ⊋ HL) -/

/-- **W4** `bottom`: the singleton of the zero state — the least
credal body. -/
def bottom : Set (BelState (Fin 2)) := {BelState.zero (Fin 2)}

theorem isUltra_bottom : IsUltra bottom := by
  refine ⟨⟨_, rfl⟩, isClosed_singleton, ?_, ?_⟩
  · show Convex ℝ (carrierImage {BelState.zero (Fin 2)})
    rw [carrierImage_singleton]
    exact convex_singleton _
  · rintro y hy x hxy
    have hy' : y = BelState.zero (Fin 2) := hy
    subst hy'
    exact eq_zero_of_coe_le_zero hxy

theorem isMVS_bottom : IsMVS bottom := by
  refine ⟨{BelState.zero (Fin 2)}, ⟨_, Finset.mem_singleton_self _⟩, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x = BelState.zero (Fin 2) := hx
    subst hx'
    refine ⟨((BelState.zero (Fin 2) : BelState (Fin 2)) : Fin 2 → ℝ),
      ?_, le_rfl⟩
    rw [Finset.coe_singleton, carrierImage_singleton,
      convexHull_singleton]
    rfl
  · rintro ⟨y, hy, hxy⟩
    rw [Finset.coe_singleton, carrierImage_singleton,
      convexHull_singleton, Set.mem_singleton_iff] at hy
    subst hy
    exact eq_zero_of_coe_le_zero hxy

/-- The hard-violation constant compiles to the bottom body. -/
theorem compile_top_eq_bottom :
    compile (fun _ : ProbState (Fin 2) => (⊤ : ℝ≥0∞)) = bottom := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    rw [grade_top] at hle
    have hγ : γ = 0 := le_antisymm hle h0
    show x = BelState.zero (Fin 2)
    apply Subtype.ext
    rw [he, hγ, zero_smul]
    rfl
  · intro hx
    have hx' : x = BelState.zero (Fin 2) := hx
    subst hx'
    exact zero_mem_compile _

/-- **W4 ∈ R** (under the no-properness reading; prereg frozen
note 1): the `⊤` penalty is convex, lsc, and compiles to `{0}`. -/
theorem isRichardsonBody_bottom : IsRichardsonBody bottom :=
  ⟨fun _ => ⊤, penaltyConvex_const ⊤, lowerSemicontinuous_const,
    compile_top_eq_bottom.symm⟩

/-- **W4 ∉ HL**: the zero state has mass `0 ≠ 1`. -/
theorem not_isHL_bottom : ¬ IsHL bottom := by
  rintro ⟨-, x, hx, hmass⟩
  have hx' : x = BelState.zero (Fin 2) := hx
  subst hx'
  rw [BelState.mass_zero] at hmass
  norm_num at hmass

/-- **W4 ∉ CS**: a Cozman body owns a full-mass member; `{0}` has
none. -/
theorem not_isCozman_bottom : ¬ IsCozman bottom := by
  intro h
  obtain ⟨x, hx, hmass⟩ := exists_mass_one_of_isCozman h
  have hx' : x = BelState.zero (Fin 2) := hx
  subst hx'
  rw [BelState.mass_zero] at hmass
  norm_num at hmass

/-! ## W10: `halfBody` — Richardson but not Cozman (R ⊋ CS) -/

/-- **W10** `halfBody`: everything of mass at most `1/2` — the compile
of the constant penalty `log 2`. -/
def halfBody : Set (BelState (Fin 2)) :=
  {x | BelState.mass x ≤ 1/2}

theorem mem_halfBody_iff {x : BelState (Fin 2)} :
    x ∈ halfBody ↔ (x : Fin 2 → ℝ) 0 + (x : Fin 2 → ℝ) 1 ≤ 1/2 := by
  show BelState.mass x ≤ 1/2 ↔ _
  rw [mass_eq_two]

/-- The constant penalty at height `log 2`. -/
noncomputable def halfPenalty : ProbPenalty (Fin 2) :=
  fun _ => ENNReal.ofReal (Real.log 2)

/-- The constant-`log 2` penalty compiles to the half-mass body. -/
theorem compile_halfPenalty : compile halfPenalty = halfBody := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    show BelState.mass x ≤ 1/2
    have hm : BelState.mass x = γ := by
      unfold BelState.mass
      rw [he]
      exact sum_smul_coe γ μ
    rw [hm]
    calc γ ≤ grade (halfPenalty μ) := hle
      _ = 1 / 2 := grade_ofReal_log_two
  · intro hx
    have hx' : BelState.mass x ≤ 1/2 := hx
    rcases eq_or_lt_of_le x.mass_nonneg with hz | hpos
    · have hzero : x = BelState.zero (Fin 2) :=
        eq_zero_of_mass_eq_zero hz.symm
      rw [hzero]
      exact zero_mem_compile _
    · refine ⟨unitize x hpos, x.mass, x.mass_nonneg, ?_,
        coe_eq_mass_smul_unitize x hpos⟩
      show x.mass ≤ grade (ENNReal.ofReal (Real.log 2))
      rw [grade_ofReal_log_two]
      exact hx'

/-- **W10 ∈ R**, with a *finite bounded* penalty: the constant
`log 2`. -/
theorem isRichardsonBody_halfBody : IsRichardsonBody halfBody :=
  ⟨halfPenalty, penaltyConvex_const _, lowerSemicontinuous_const,
    compile_halfPenalty.symm⟩

theorem isUltra_halfBody : IsUltra halfBody := by
  refine ⟨⟨BelState.zero (Fin 2), ?_⟩, ?_, ?_, ?_⟩
  · show BelState.mass (BelState.zero (Fin 2)) ≤ 1/2
    rw [BelState.mass_zero]
    norm_num
  · have hc : Continuous fun x : BelState (Fin 2) => BelState.mass x :=
      continuous_finsetSum _ fun v _ =>
        (continuous_apply v).comp continuous_subtype_val
    exact isClosed_le hc continuous_const
  · show Convex ℝ (carrierImage halfBody)
    have himg : carrierImage halfBody
        = belCarrier (Fin 2) ∩ {y : Fin 2 → ℝ | ∑ v, y v ≤ 1/2} :=
      carrierImage_setOf (fun y => ∑ v, y v ≤ 1/2)
    rw [himg]
    exact convex_belCarrier.inter convex_massHalfspace
  · intro y hy x hxy
    show BelState.mass x ≤ 1/2
    have hmono : BelState.mass x ≤ BelState.mass y :=
      Finset.sum_le_sum fun v _ => hxy v
    exact hmono.trans hy

theorem isMVS_halfBody : IsMVS halfBody := by
  classical
  refine ⟨{halfA, halfB}, ⟨halfA, Finset.mem_insert_self _ _⟩, ?_⟩
  have himg : carrierImage
      ((({halfA, halfB} : Finset (BelState (Fin 2)))
        : Set (BelState (Fin 2))))
      = {((halfA : BelState (Fin 2)) : Fin 2 → ℝ),
         ((halfB : BelState (Fin 2)) : Fin 2 → ℝ)} := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact carrierImage_pair _ _
  ext x
  constructor
  · intro hx
    have hx' := mem_halfBody_iff.mp hx
    refine ⟨(2 * (x : Fin 2 → ℝ) 0)
          • ((halfA : BelState (Fin 2)) : Fin 2 → ℝ)
        + (1 - 2 * (x : Fin 2 → ℝ) 0)
          • ((halfB : BelState (Fin 2)) : Fin 2 → ℝ), ?_, ?_⟩
    · rw [himg, convexHull_pair]
      refine ⟨2 * (x : Fin 2 → ℝ) 0, 1 - 2 * (x : Fin 2 → ℝ) 0,
        ?_, ?_, by ring, rfl⟩
      · have := x.nonneg 0
        linarith
      · have := x.nonneg 1
        linarith
    · rw [Pi.le_def, Fin.forall_fin_two]
      constructor
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, halfA_zero,
          halfB_zero, mul_zero, add_zero]
        linarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, halfA_one,
          halfB_one, mul_zero, zero_add]
        linarith
  · rintro ⟨y, hy, hxy⟩
    rw [himg, convexHull_pair] at hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have h0 := hxy 0
    have h1 := hxy 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, halfA_zero,
      halfA_one, halfB_zero, halfB_one, mul_zero, add_zero,
      zero_add] at h0 h1
    rw [mem_halfBody_iff]
    linarith

/-- **W10 ∉ HL**: no member reaches full mass. -/
theorem not_isHL_halfBody : ¬ IsHL halfBody := by
  rintro ⟨-, x, hx, hmass⟩
  have h : BelState.mass x ≤ 1/2 := hx
  rw [hmass] at h
  norm_num at h

/-- **W10 ∉ CS**: a Cozman body owns a full-mass member; the half
body caps mass at `1/2`. -/
theorem not_isCozman_halfBody : ¬ IsCozman halfBody := by
  intro h
  obtain ⟨x, hx, hmass⟩ := exists_mass_one_of_isCozman h
  have h' : BelState.mass x ≤ 1/2 := hx
  rw [hmass] at h'
  norm_num at h'

/-! ## The poset edges discharged by this zoo

Each pair below is one strict-inclusion or incomparability edge of the
predicted Hasse diagram (prereg §3), packaged as a single citable
conjunction.  (The edges through W6 — KA ⊋ MVS, MVS ⊄ HL's converse —
and the W3 Richardson cell ride the sibling legs.) -/

/-- CB ⊋ CV (via W1). -/
theorem cb_strict_cv :
    IsCredalBody twoRays ∧ ¬ IsConvexCredalBody twoRays :=
  isCredalBody_twoRays_not_convex

/-- KA ⊄ R (via W2): an ultracontribution that is not Richardson. -/
theorem ka_not_subset_r :
    IsUltra harmonicBody ∧ ¬ IsRichardsonBody harmonicBody :=
  ⟨isUltra_harmonicBody, not_isRichardsonBody_harmonicBody⟩

/-- HL ⊄ R (via W2). -/
theorem hl_not_subset_r :
    IsHL harmonicBody ∧ ¬ IsRichardsonBody harmonicBody :=
  ⟨isHL_harmonicBody, not_isRichardsonBody_harmonicBody⟩

/-- MVS ⊄ R (via W2). -/
theorem mvs_not_subset_r :
    IsMVS harmonicBody ∧ ¬ IsRichardsonBody harmonicBody :=
  ⟨isMVS_harmonicBody, not_isRichardsonBody_harmonicBody⟩

/-- HL ⊄ CS (via W2). -/
theorem hl_not_subset_cs :
    IsHL harmonicBody ∧ ¬ IsCozman harmonicBody :=
  ⟨isHL_harmonicBody, not_isCozman_harmonicBody⟩

/-- CS ⊄ KA (via W3): the radial embedding of a classical credal set
need not be pointwise-down-closed. -/
theorem cs_not_subset_ka :
    IsCozman segBody ∧ ¬ IsUltra segBody :=
  ⟨isCozman_segBody, not_isUltra_segBody⟩

/-- CS ⊄ HL (via W3). -/
theorem cs_not_subset_hl :
    IsCozman segBody ∧ ¬ IsHL segBody :=
  ⟨isCozman_segBody, not_isHL_segBody⟩

/-- CS ⊄ MVS (via W3). -/
theorem cs_not_subset_mvs :
    IsCozman segBody ∧ ¬ IsMVS segBody :=
  ⟨isCozman_segBody, not_isMVS_segBody⟩

/-- KA ⊋ HL (via W4). -/
theorem ka_strict_hl :
    IsUltra bottom ∧ ¬ IsHL bottom :=
  ⟨isUltra_bottom, not_isHL_bottom⟩

/-- MVS ⊄ HL (via W4). -/
theorem mvs_not_subset_hl :
    IsMVS bottom ∧ ¬ IsHL bottom :=
  ⟨isMVS_bottom, not_isHL_bottom⟩

/-- R ⊄ CS (via W10): strictness of CS ⊆ R. -/
theorem r_not_subset_cs :
    IsRichardsonBody halfBody ∧ ¬ IsCozman halfBody :=
  ⟨isRichardsonBody_halfBody, not_isCozman_halfBody⟩

/-- KA ⊄ CS (via W10, or W4). -/
theorem ka_not_subset_cs :
    IsUltra halfBody ∧ ¬ IsCozman halfBody :=
  ⟨isUltra_halfBody, not_isCozman_halfBody⟩

/-- MVS ⊄ CS (via W10, or W4). -/
theorem mvs_not_subset_cs :
    IsMVS halfBody ∧ ¬ IsCozman halfBody :=
  ⟨isMVS_halfBody, not_isCozman_halfBody⟩

end CredalPoset

end SuFunctor.Universe
