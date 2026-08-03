import SuFunctor.Universe.CoupledJudgment
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The radial compile: grades, bodies, and the judgment as containment-and-escape

The **radial compile** turns a penalty on the flat carrier into a
subset of the subprobability carrier: the epistemic **body**

  `compile f = { γ • μ : μ a probability state, 0 ≤ γ ≤ grade (f μ) }`,

where `grade a = e^{-a}` (with `grade ⊤ = 0`) spends the mass
coordinate on grade.  This module carries the finite-outcome dictionary
between the two pictures:

* **grade transport** — `grade` is a strictly antitone map
  `[0, ∞] → [0, 1]` turning `+` into `*` (`grade_add`), min into max
  (`grade_inf`) and max into min (`grade_sup`);
* **antitonicity** (`compile_subset_compile_iff`) — body inclusion is
  the reversed pointwise order: refinement is shrinkage;
* **the judgment, compiled** (`coupledSat_iff_compile`) — a system
  satisfies a spec atom iff its body *fits inside the safety body* and
  *sticks out of every liveness body*: containment and escape;
* **the algebra** — disjunction of systems is union of bodies
  (`compile_inf`); conjunction is intersection (`compile_sup`); and
  mechanism composition `f + g` is the fiberwise **grade product**
  (`mem_compile_add_iff`), which is *not* intersection — intersection
  computes the pointwise max, one more face of the safety-conjunction
  merge.

Everything here is order/algebra at finite `V`; the topological
stratum of the dictionary (bodies closed iff the penalty is a citizen,
radial sets closed under hyperspace limits, the hypograph
homeomorphism, and the hit-and-miss presentation of spec classes) is
deliberately left to a successor pass. -/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## The grade map -/

/-- The grade of a penalty height: `e^{-a}`, with hard violation
graded `0`.  The multiplicative presentation of the additive penalty
scale. -/
noncomputable def grade (a : ℝ≥0∞) : ℝ :=
  if a = ⊤ then 0 else Real.exp (-a.toReal)

@[simp] theorem grade_top : grade ⊤ = 0 := if_pos rfl

theorem grade_of_ne_top {a : ℝ≥0∞} (h : a ≠ ⊤) :
    grade a = Real.exp (-a.toReal) := if_neg h

@[simp] theorem grade_zero : grade 0 = 1 := by
  rw [grade_of_ne_top (by simp)]
  simp

theorem grade_nonneg (a : ℝ≥0∞) : 0 ≤ grade a := by
  by_cases h : a = ⊤
  · rw [h, grade_top]
  · rw [grade_of_ne_top h]
    exact (Real.exp_pos _).le

theorem grade_pos {a : ℝ≥0∞} (h : a ≠ ⊤) : 0 < grade a := by
  rw [grade_of_ne_top h]
  exact Real.exp_pos _

theorem grade_le_one (a : ℝ≥0∞) : grade a ≤ 1 := by
  by_cases h : a = ⊤
  · rw [h, grade_top]; norm_num
  · rw [grade_of_ne_top h, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)

theorem grade_anti {a b : ℝ≥0∞} (h : a ≤ b) : grade b ≤ grade a := by
  by_cases hb : b = ⊤
  · rw [hb, grade_top]
    exact grade_nonneg a
  · have ha : a ≠ ⊤ := fun hc => hb (top_le_iff.mp (hc ▸ h))
    rw [grade_of_ne_top ha, grade_of_ne_top hb]
    exact Real.exp_le_exp.mpr
      (neg_le_neg ((ENNReal.toReal_le_toReal ha hb).mpr h))

theorem grade_strictAnti {a b : ℝ≥0∞} (h : a < b) : grade b < grade a := by
  have ha : a ≠ ⊤ := h.ne_top
  by_cases hb : b = ⊤
  · rw [hb, grade_top]
    exact grade_pos ha
  · rw [grade_of_ne_top ha, grade_of_ne_top hb]
    exact Real.exp_lt_exp.mpr
      (neg_lt_neg ((ENNReal.toReal_lt_toReal ha hb).mpr h))

theorem grade_le_grade_iff {a b : ℝ≥0∞} : grade b ≤ grade a ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    exact absurd h (not_le.mpr (grade_strictAnti (not_le.mp hab)))
  · exact grade_anti

theorem grade_lt_grade_iff {a b : ℝ≥0∞} : grade b < grade a ↔ a < b := by
  constructor
  · intro h
    by_contra hab
    exact absurd h (not_lt.mpr (grade_anti (not_lt.mp hab)))
  · exact grade_strictAnti

/-- **Grades are multiplicative**: the additive penalty scale compiles
to the multiplicative grade scale. -/
theorem grade_add (a b : ℝ≥0∞) : grade (a + b) = grade a * grade b := by
  by_cases ha : a = ⊤
  · rw [ha, grade_top, top_add, grade_top, zero_mul]
  · by_cases hb : b = ⊤
    · rw [hb, grade_top, add_top, grade_top, mul_zero]
    · rw [grade_of_ne_top ha, grade_of_ne_top hb,
        grade_of_ne_top (ENNReal.add_ne_top.mpr ⟨ha, hb⟩),
        ENNReal.toReal_add ha hb, neg_add, Real.exp_add]

/-- Grade of a min is the max of grades. -/
theorem grade_inf (a b : ℝ≥0∞) : grade (a ⊓ b) = grade a ⊔ grade b := by
  rcases le_total a b with h | h
  · rw [inf_eq_left.mpr h, sup_eq_left.mpr (grade_anti h)]
  · rw [inf_eq_right.mpr h, sup_eq_right.mpr (grade_anti h)]

/-- Grade of a max is the min of grades. -/
theorem grade_sup (a b : ℝ≥0∞) : grade (a ⊔ b) = grade a ⊓ grade b := by
  rcases le_total a b with h | h
  · rw [sup_eq_right.mpr h, inf_eq_right.mpr (grade_anti h)]
  · rw [sup_eq_left.mpr h, inf_eq_left.mpr (grade_anti h)]

/-! ## Scaled points and polar decomposition -/

variable {V : Type*} [Fintype V]

theorem sum_smul_coe (γ : ℝ) (μ : ProbState V) :
    ∑ v, (γ • (μ : V → ℝ)) v = γ := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, μ.sum_eq_one, mul_one]

/-- Scaling a probability state into the subprobability carrier. -/
def scalePoint (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (μ : ProbState V) :
    BelState V :=
  ⟨γ • (μ : V → ℝ),
    fun v => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg h0 (μ.nonneg v),
    by rw [sum_smul_coe]; exact h1⟩

@[simp] theorem scalePoint_coe (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (μ : ProbState V) :
    ((scalePoint γ h0 h1 μ : BelState V) : V → ℝ) = γ • (μ : V → ℝ) := rfl

/-- The scale of a scaled probability state is read off by total mass:
polar decompositions agree in their radial coordinate. -/
theorem polar_scale_eq {γ γ' : ℝ} {μ μ' : ProbState V}
    (h : γ • (μ : V → ℝ) = γ' • (μ' : V → ℝ)) : γ = γ' := by
  have h1 := congrArg (fun x : V → ℝ => ∑ v, x v) h
  simpa only [sum_smul_coe] using h1

/-- At nonzero scale, polar decompositions agree in their angular
coordinate too. -/
theorem polar_state_eq {γ : ℝ} (hγ : γ ≠ 0) {μ μ' : ProbState V}
    (h : γ • (μ : V → ℝ) = γ • (μ' : V → ℝ)) : μ = μ' :=
  Subtype.ext (smul_right_injective (V → ℝ) hγ h)

/-! ## The radial compile -/

/-- The radial compile of a penalty: its epistemic body inside the
subprobability carrier — each probability state `μ`, scaled by any
grade up to `grade (f μ)`. -/
def compile (f : ProbPenalty V) : Set (BelState V) :=
  {x | ∃ (μ : ProbState V) (γ : ℝ), 0 ≤ γ ∧ γ ≤ grade (f μ)
    ∧ (x : V → ℝ) = γ • (μ : V → ℝ)}

/-- Every body owns the zero state (take scale zero). -/
theorem zero_mem_compile [Nonempty V] (f : ProbPenalty V) :
    BelState.zero V ∈ compile f := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (ProbState V))
  exact ⟨μ, 0, le_rfl, grade_nonneg _, by
    funext v
    simp [BelState.zero]⟩

/-- Membership bounds the scale by the grade, along any positive polar
decomposition — the radial coordinate cannot exceed the body's ray
length. -/
theorem compile_scale_le {f : ProbPenalty V} {x : BelState V}
    (hx : x ∈ compile f) {γ : ℝ} {μ : ProbState V} (hγ : 0 < γ)
    (hd : (x : V → ℝ) = γ • (μ : V → ℝ)) : γ ≤ grade (f μ) := by
  obtain ⟨μ₁, γ₁, h0, hle, he⟩ := hx
  have heq : γ • (μ : V → ℝ) = γ₁ • (μ₁ : V → ℝ) := by
    rw [← hd, ← he]
  have hγγ : γ = γ₁ := polar_scale_eq heq
  rw [← hγγ] at hle
  rw [← hγγ] at heq
  have hμ : μ = μ₁ := polar_state_eq hγ.ne' heq
  rw [hμ]
  exact hle

/-- **Antitonicity**: body inclusion is the reversed pointwise order.
The spec-below-system orientation becomes system-body-inside-spec-body
— refinement as shrinkage. -/
theorem compile_subset_compile_iff {f h : ProbPenalty V} :
    compile f ⊆ compile h ↔ h ≤ f := by
  constructor
  · intro hsub μ
    by_cases hfμ : f μ = ⊤
    · rw [hfμ]; exact le_top
    · have htip : scalePoint (grade (f μ)) (grade_nonneg _)
          (grade_le_one _) μ ∈ compile f :=
        ⟨μ, grade (f μ), grade_nonneg _, le_rfl, rfl⟩
      have hb := compile_scale_le (hsub htip) (grade_pos hfμ)
        (scalePoint_coe _ _ _ _)
      exact grade_le_grade_iff.mp hb
  · intro hle x hx
    obtain ⟨μ, γ, h0, hγ, he⟩ := hx
    exact ⟨μ, γ, h0, hγ.trans (grade_anti (hle μ)), he⟩

/-- **The escape dictionary**: a dip under the mark `v` is exactly a
point of the system's body outside the mark's body — the system
protrudes past the liveness body somewhere. -/
theorem dip_iff_compile_escape {σ v : ProbPenalty V} :
    Dip σ v ↔ ∃ x ∈ compile σ, x ∉ compile v := by
  constructor
  · rintro ⟨μ, hμ⟩
    have hσμ : σ μ ≠ ⊤ := (hμ.trans_le le_top).ne
    refine ⟨scalePoint (grade (σ μ)) (grade_nonneg _) (grade_le_one _) μ,
      ⟨μ, grade (σ μ), grade_nonneg _, le_rfl, rfl⟩, ?_⟩
    intro hmem
    have hb := compile_scale_le hmem (grade_pos hσμ) (scalePoint_coe _ _ _ _)
    exact absurd (grade_le_grade_iff.mp hb) (not_le.mpr hμ)
  · rintro ⟨x, hxσ, hxv⟩
    obtain ⟨μ, γ, h0, hγle, he⟩ := hxσ
    have hγpos : 0 < γ := by
      rcases h0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hxv
        exact ⟨μ, γ, h0, by rw [← h]; exact grade_nonneg _, he⟩
    have hnot : ¬ γ ≤ grade (v μ) := fun hc => hxv ⟨μ, γ, h0, hc, he⟩
    exact ⟨μ, grade_lt_grade_iff.mp (lt_of_lt_of_le (not_le.mp hnot) hγle)⟩

/-- **The judgment, compiled**: satisfaction is containment in the
safety body together with escape past every liveness body. -/
theorem coupledSat_iff_compile {σ u : ProbPenalty V}
    {𝒱 : Set (ProbPenalty V)} :
    CoupledSat σ u 𝒱
      ↔ compile σ ⊆ compile u
        ∧ ∀ v ∈ 𝒱, ∃ x ∈ compile σ, x ∉ compile v := by
  rw [CoupledSat, ← compile_subset_compile_iff]
  exact and_congr Iff.rfl
    (forall₂_congr fun v _ => dip_iff_compile_escape)

/-! ## The algebra: (min, +) compiles to (∪, grade-product) -/

/-- **Disjunction of systems is union of bodies** — exactly, with no
hull. -/
theorem compile_inf (f g : ProbPenalty V) :
    compile (f ⊓ g) = compile f ∪ compile g := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    rw [Pi.inf_apply, grade_inf] at hle
    rcases le_sup_iff.mp hle with h | h
    · exact Or.inl ⟨μ, γ, h0, h, he⟩
    · exact Or.inr ⟨μ, γ, h0, h, he⟩
  · rintro (⟨μ, γ, h0, hle, he⟩ | ⟨μ, γ, h0, hle, he⟩)
    · exact ⟨μ, γ, h0, by
        rw [Pi.inf_apply, grade_inf]
        exact hle.trans le_sup_left, he⟩
    · exact ⟨μ, γ, h0, by
        rw [Pi.inf_apply, grade_inf]
        exact hle.trans le_sup_right, he⟩

/-- **Intersection of bodies is conjunction**, not composition: the
pointwise max compiles to the body intersection.  (Compare
`mem_compile_add_iff`: mechanism composition is the grade product, a
strictly smaller body wherever both grades are strictly graded.) -/
theorem compile_sup (f g : ProbPenalty V) :
    compile (f ⊔ g) = compile f ∩ compile g := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    rw [Pi.sup_apply, grade_sup] at hle
    exact ⟨⟨μ, γ, h0, hle.trans inf_le_left, he⟩,
      ⟨μ, γ, h0, hle.trans inf_le_right, he⟩⟩
  · rintro ⟨hf, hg⟩
    obtain ⟨μ, γ, h0, hlef, he⟩ := hf
    rcases h0.lt_or_eq with hpos | hzero
    · have hleg : γ ≤ grade (g μ) := compile_scale_le hg hpos he
      exact ⟨μ, γ, h0, by
        rw [Pi.sup_apply, grade_sup]
        exact le_inf hlef hleg, he⟩
    · exact ⟨μ, γ, h0, by
        rw [Pi.sup_apply, ← hzero]
        exact grade_nonneg _, he⟩

/-- **Mechanism composition is the grade product**: the body of
`f + g` consists of the fiberwise products of ray lengths — on each
ray, the composite grade is the product of the component grades. -/
theorem mem_compile_add_iff {f g : ProbPenalty V} {x : BelState V} :
    x ∈ compile (f + g)
      ↔ ∃ (μ : ProbState V) (γ₁ γ₂ : ℝ), 0 ≤ γ₁ ∧ 0 ≤ γ₂
          ∧ γ₁ ≤ grade (f μ) ∧ γ₂ ≤ grade (g μ)
          ∧ (x : V → ℝ) = (γ₁ * γ₂) • (μ : V → ℝ) := by
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    rw [Pi.add_apply, grade_add] at hle
    by_cases hf0 : grade (f μ) = 0
    · have hγ0 : γ = 0 := le_antisymm (by rw [hf0, zero_mul] at hle; exact hle) h0
      exact ⟨μ, 0, 0, le_rfl, le_rfl, hf0.ge, grade_nonneg _, by
        rw [mul_zero]
        rw [hγ0] at he
        exact he⟩
    · have hfpos : 0 < grade (f μ) :=
        (grade_nonneg _).lt_of_ne (Ne.symm hf0)
      refine ⟨μ, grade (f μ), γ / grade (f μ), grade_nonneg _,
        div_nonneg h0 hfpos.le, le_rfl, ?_, ?_⟩
      · rw [div_le_iff₀ hfpos]
        rw [mul_comm (grade (f μ)) (grade (g μ))] at hle
        exact hle
      · rw [he]
        congr 1
        rw [mul_comm, div_mul_cancel₀ _ hfpos.ne']
  · rintro ⟨μ, γ₁, γ₂, h1, h2, hle1, hle2, he⟩
    refine ⟨μ, γ₁ * γ₂, mul_nonneg h1 h2, ?_, he⟩
    rw [Pi.add_apply, grade_add]
    exact mul_le_mul hle1 hle2 h2 (grade_nonneg _)

end SuFunctor.Universe
