import SuFunctor.Universe.Closure

/-! # The flat carrier: probability distributions

The judgment stratum of the semantic universe lives on the **flat
carrier** $\Delta(V)$: *probability* distributions on a finite outcome
space — total mass exactly one, no information order, no distinguished
partiality coordinate.  Divergence, where a model wants it, is an
*outcome* (a cemetery point of `V`), not a mass deficit: the
subprobability carrier `belCarrier` of `SuFunctor.Universe.Carrier`
remains in service as the *codomain of the radial compile* (see
`SuFunctor.Universe.VietorisDictionary`), where the mass coordinate is
spent on grade.

This module provides:

* `Universe.probCarrier V` / `Universe.ProbState V` — the probability
  simplex as a compact subset of `V → ℝ`, with point masses and the
  inclusion into the subprobability carrier;
* `Universe.ProbPenalty V` — penalty functionals on the flat carrier
  (citizenship is again lower semicontinuity, and nothing else);
* `Universe.scaledIndicator c S` — the scaled indicator penalty
  (`c` on `S`, `0` off it): lower semicontinuous for **open** `S`,
  the single-row atoms of the generation theorem
  (`SuFunctor.Universe.Generation`);
* `Universe.probWall C` — the `{0, ⊤}`-valued wall (`0` on `C`, `⊤`
  off it): lower semicontinuous for **closed** `C`.  The wall *on* an
  open set `S` — `⊤` on `S`, `0` off it, the liveness-mark of a goal
  region — is `probWall Sᶜ`.

The wall API deliberately mirrors `Universe.wall` (which lives on the
subprobability carrier); unifying the two behind one generic
definition is routine refactoring left for a quiet pass.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable (V : Type*) [Fintype V]

/-- The flat carrier $\Delta(V)$: probability weight functions on the
finite outcome space `V` — pointwise nonnegative, total mass exactly
one. -/
def probCarrier : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}

variable {V}

theorem mem_probCarrier_iff {x : V → ℝ} :
    x ∈ probCarrier V ↔ (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 :=
  Iff.rfl

/-- Probability states are subprobability states. -/
theorem probCarrier_subset_belCarrier : probCarrier V ⊆ belCarrier V :=
  fun _ hx => ⟨hx.1, le_of_eq hx.2⟩

theorem convex_probCarrier : Convex ℝ (probCarrier V) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun v => add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v)), ?_⟩
  have hsum : ∑ v, (a • x + b • y) v = a * ∑ v, x v + b * ∑ v, y v := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum, hx.2, hy.2, mul_one, mul_one, hab]

theorem isClosed_probCarrier : IsClosed (probCarrier V) := by
  have h1 : IsClosed {x : V → ℝ | ∀ v, 0 ≤ x v} := by
    have : {x : V → ℝ | ∀ v, 0 ≤ x v} = ⋂ v, {x : V → ℝ | 0 ≤ x v} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  have h2 : IsClosed {x : V → ℝ | ∑ v, x v = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact h1.inter h2

/-- The flat carrier is compact: a closed subset of the compact
subprobability carrier. -/
theorem isCompact_probCarrier : IsCompact (probCarrier V) :=
  IsCompact.of_isClosed_subset isCompact_belCarrier isClosed_probCarrier
    probCarrier_subset_belCarrier

variable (V) in
/-- A probability distribution on the finite outcome space `V`: a point
of the flat carrier `probCarrier V`.  As a subtype of the metric space
`V → ℝ` it is a compact metric space. -/
abbrev ProbState : Type _ := ↥(probCarrier V)

instance : CompactSpace (ProbState V) :=
  isCompact_iff_compactSpace.mp isCompact_probCarrier

namespace ProbState

theorem nonneg (μ : ProbState V) (v : V) : 0 ≤ (μ : V → ℝ) v := μ.2.1 v

theorem sum_eq_one (μ : ProbState V) : ∑ v, (μ : V → ℝ) v = 1 := μ.2.2

theorem apply_le_one (μ : ProbState V) (v : V) : (μ : V → ℝ) v ≤ 1 := by
  have h : (μ : V → ℝ) v ≤ ∑ w, (μ : V → ℝ) w :=
    Finset.single_le_sum (fun w _ => μ.nonneg w) (Finset.mem_univ v)
  rw [μ.sum_eq_one] at h
  exact h

/-- The inclusion of the flat carrier into the subprobability carrier. -/
def toBel (μ : ProbState V) : BelState V :=
  ⟨(μ : V → ℝ), probCarrier_subset_belCarrier μ.2⟩

@[simp] theorem toBel_coe (μ : ProbState V) :
    ((μ.toBel : BelState V) : V → ℝ) = (μ : V → ℝ) := rfl

theorem toBel_injective : Function.Injective (toBel (V := V)) := by
  intro μ ν h
  exact Subtype.ext (congrArg (fun x : BelState V => (x : V → ℝ)) h)

theorem continuous_toBel : Continuous (toBel (V := V)) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The point mass at an outcome (mass exactly one: it lives on the
flat carrier). -/
def dirac [DecidableEq V] (v : V) : ProbState V :=
  ⟨Pi.single v 1, by
    constructor
    · intro w
      rcases eq_or_ne w v with rfl | h
      · simp
      · simp [h]
    · rw [Finset.sum_eq_single v (fun w _ hw => by simp [hw])
        (fun h => absurd (Finset.mem_univ v) h)]
      simp⟩

@[simp] theorem dirac_apply_same [DecidableEq V] (v : V) :
    ((dirac v : ProbState V) : V → ℝ) v = 1 := by
  simp [dirac]

theorem dirac_apply_of_ne [DecidableEq V] {v w : V} (h : w ≠ v) :
    ((dirac v : ProbState V) : V → ℝ) w = 0 := by
  simp [dirac, h]

theorem dirac_injective [DecidableEq V] :
    Function.Injective (dirac (V := V)) := by
  intro v w h
  by_contra hne
  have h1 := congrArg (fun μ : ProbState V => (μ : V → ℝ) v) h
  rw [dirac_apply_same] at h1
  rw [dirac_apply_of_ne hne] at h1
  norm_num at h1

open Classical in
instance [Nonempty V] : Nonempty (ProbState V) :=
  ⟨dirac (Classical.arbitrary V)⟩

end ProbState

variable (V) in
/-- A penalty functional on the flat carrier: a point of the judgment
stratum's semantic universe.  Heights are extended nonnegative reals;
`⊤` is hard violation, `0` perfect compatibility.  Citizenship is
lower semicontinuity, and nothing else. -/
abbrev ProbPenalty : Type _ := ProbState V → ℝ≥0∞

/-- The sublevel reading of citizenship on the flat carrier (the
`Universe.lowerSemicontinuous_iff_isClosed_sublevel` sibling). -/
theorem lowerSemicontinuous_prob_iff_isClosed_sublevel {σ : ProbPenalty V} :
    LowerSemicontinuous σ ↔ ∀ s : ℝ≥0∞, IsClosed {μ : ProbState V | σ μ ≤ s} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  simp only [Set.preimage, Set.mem_Iic]

/-! ## Scaled indicators and walls on the flat carrier

Two families of `{0, c}`- and `{0, ⊤}`-valued penalties:

* `scaledIndicator c S` (`c` on `S`, `0` off it) is a citizen for
  **open** `S` — the atoms of the generation theorem, and the
  finite-severity liveness marks;
* `probWall C` (`0` on `C`, `⊤` off it) is a citizen for **closed**
  `C` — crisp safety; the crisp liveness-mark *on* an open goal region
  `G` is `probWall Gᶜ`.
-/

open Classical in
/-- The scaled indicator penalty: `c` on `S`, `0` off it. -/
noncomputable def scaledIndicator (c : ℝ≥0∞) (S : Set (ProbState V)) :
    ProbPenalty V :=
  fun μ => if μ ∈ S then c else 0

theorem scaledIndicator_apply_of_mem {c : ℝ≥0∞} {S : Set (ProbState V)}
    {μ : ProbState V} (h : μ ∈ S) : scaledIndicator c S μ = c := by
  simp [scaledIndicator, h]

theorem scaledIndicator_apply_of_not_mem {c : ℝ≥0∞} {S : Set (ProbState V)}
    {μ : ProbState V} (h : μ ∉ S) : scaledIndicator c S μ = 0 := by
  simp [scaledIndicator, h]

theorem scaledIndicator_le_apply {c : ℝ≥0∞} {S : Set (ProbState V)}
    (μ : ProbState V) : scaledIndicator c S μ ≤ c := by
  by_cases h : μ ∈ S
  · rw [scaledIndicator_apply_of_mem h]
  · rw [scaledIndicator_apply_of_not_mem h]; exact zero_le

/-- Scaled indicators of open sets are citizens. -/
theorem lowerSemicontinuous_scaledIndicator {c : ℝ≥0∞}
    {S : Set (ProbState V)} (hS : IsOpen S) :
    LowerSemicontinuous (scaledIndicator c S) := by
  intro μ y hy
  by_cases hμ : μ ∈ S
  · filter_upwards [hS.mem_nhds hμ] with ν hν
    rw [scaledIndicator_apply_of_mem hν]
    rw [scaledIndicator_apply_of_mem hμ] at hy
    exact hy
  · rw [scaledIndicator_apply_of_not_mem hμ] at hy
    exact absurd hy (not_lt.mpr zero_le)

open Classical in
/-- The wall of a set of probability distributions: `0` inside, `⊤`
outside.  (The flat-carrier sibling of `Universe.wall`.) -/
noncomputable def probWall (C : Set (ProbState V)) : ProbPenalty V :=
  fun μ => if μ ∈ C then 0 else ⊤

theorem probWall_apply_of_mem {C : Set (ProbState V)} {μ : ProbState V}
    (h : μ ∈ C) : probWall C μ = 0 := by simp [probWall, h]

theorem probWall_apply_of_not_mem {C : Set (ProbState V)} {μ : ProbState V}
    (h : μ ∉ C) : probWall C μ = ⊤ := by simp [probWall, h]

theorem probWall_le_iff {C : Set (ProbState V)} {σ : ProbPenalty V} :
    probWall C ≤ σ ↔ ∀ μ, μ ∉ C → σ μ = ⊤ := by
  constructor
  · intro h μ hμ
    have := h μ
    rw [probWall_apply_of_not_mem hμ] at this
    exact top_le_iff.mp this
  · intro h μ
    by_cases hμ : μ ∈ C
    · rw [probWall_apply_of_mem hμ]; exact zero_le
    · rw [probWall_apply_of_not_mem hμ, h μ hμ]

/-- The wall order is containment, contravariantly. -/
theorem probWall_le_probWall_iff {C D : Set (ProbState V)} :
    probWall D ≤ probWall C ↔ C ⊆ D := by
  rw [probWall_le_iff]
  constructor
  · intro h μ hμ
    by_contra hD
    have := h μ hD
    rw [probWall_apply_of_mem hμ] at this
    exact ENNReal.zero_ne_top this
  · intro hCD μ hμ
    exact probWall_apply_of_not_mem fun hC => hμ (hCD hC)

/-- Walls on the flat carrier are citizens exactly on closed sets. -/
theorem lowerSemicontinuous_probWall_iff {C : Set (ProbState V)} :
    LowerSemicontinuous (probWall C) ↔ IsClosed C := by
  constructor
  · intro h
    have hC : C = {μ : ProbState V | probWall C μ ≤ 0} := by
      ext μ
      constructor
      · intro hμ; simp [probWall_apply_of_mem hμ]
      · intro hμ
        by_contra hCμ
        rw [Set.mem_setOf_eq, probWall_apply_of_not_mem hCμ, top_le_iff] at hμ
        exact ENNReal.zero_ne_top hμ
    rw [hC]
    exact lowerSemicontinuous_prob_iff_isClosed_sublevel.mp h 0
  · intro hC μ y hy
    by_cases hμ : μ ∈ C
    · rw [probWall_apply_of_mem hμ] at hy
      exact absurd hy (not_lt.mpr zero_le)
    · have htop : y < ⊤ := by
        rw [probWall_apply_of_not_mem hμ] at hy; exact hy
      filter_upwards [hC.isOpen_compl.mem_nhds hμ] with ν hν
      rw [probWall_apply_of_not_mem hν]
      exact htop

/-- The wall and the `⊤`-scaled indicator are complementary
presentations of one object. -/
theorem probWall_eq_scaledIndicator_compl (C : Set (ProbState V)) :
    probWall C = scaledIndicator ⊤ Cᶜ := by
  funext μ
  by_cases h : μ ∈ C
  · rw [probWall_apply_of_mem h,
      scaledIndicator_apply_of_not_mem (fun hc => (Set.mem_compl_iff _ _).mp hc h)]
  · rw [probWall_apply_of_not_mem h, scaledIndicator_apply_of_mem h]

end SuFunctor.Universe
