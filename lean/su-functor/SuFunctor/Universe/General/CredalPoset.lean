import SuFunctor.Universe.General.Closedness

/-! # The credal-body atlas at the general carrier

The named subclasses of the credal bodies — the literature's
imprecise-probability objects — defined over the general subprobability
carrier, with the inclusion spine of the chapter's atlas proved as
general-carrier theorems.  The finite-stratum poset
(`SuFunctor.Universe.CredalPoset`) remains the reference case for the
*strict* edges (two-line rational witnesses over a two-point outcome
space); this module carries the *inclusions* at the stratum where the
chapter states them.

Design notes, general-carrier specific:

* Convexity is spelled through an explicit `mix` operation on the
  carrier (mixtures of subprobability states are subprobability
  states), not through a scalar-field convexity API: the carrier is an
  `ℝ≥0`-module, and the atlas needs only the mixture law.
* The convex-substratum criterion is carried in **grade coordinates**:
  `GradeConvex` is the division-free cross-multiplied harmonic-mean
  inequality (`e^f` convex, multiplicatively), and
  `convexBody_compile_of_gradeConvex` is the general-carrier form of
  the finite stratum's exact-rational harmonic-mean leg
  (`QtslAux.Imprecise.PenaltyCredalIso`): the body of a grade-convex
  penalty is convex, by Jensen-shaped mass bookkeeping in `ℝ≥0` — no
  exponential, no division.
* Classical credal sets enter through the direction wall: the radial
  embedding of a closed convex set of full-mass laws **is a compile**
  (`scaleSegment_eq_compile_dirWall`), so its closedness is an
  instance of the dictionary rather than a separate argument.
* The Mio–Sarkis–Vignudelli finite-generation closedness — a
  finite-stratum *theorem* — is here proved from two named interface
  facts (compactness of the generated hull, which holds for any
  carrier, and narrow-closedness of the setwise order, which is a
  regularity property of the carrier): `isClosed_ptwiseDownHull` takes
  the order-closedness as a hypothesis, and the honest general
  sentence is exactly that reduction.  Over a metrizable carrier the
  hypothesis is dischargeable (thickened indicators + weak regularity
  of finite Borel measures); over a general topological carrier it is
  not free, and no theorem below pretends otherwise.
-/

namespace SuFunctor.Universe.General

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

namespace SubProbabilityMeasure

/-- Mass is additive. -/
theorem mass_add (μ ν : FiniteMeasure X) :
    (μ + ν).mass = μ.mass + ν.mass := by
  have h : ((μ + ν).mass : ℝ≥0∞) = (μ.mass : ℝ≥0∞) + (ν.mass : ℝ≥0∞) := by
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass,
      FiniteMeasure.ennreal_mass]
    rfl
  exact_mod_cast h

/-- Mixture of two subprobability states: mixtures never exceed unit
mass. -/
noncomputable def mix (a b : ℝ≥0) (hab : a + b = 1) (ν ρ : SubProbabilityMeasure X) :
    SubProbabilityMeasure X :=
  ⟨a • (ν : FiniteMeasure X) + b • (ρ : FiniteMeasure X), by
    rw [mass_add, mass_smul, mass_smul]
    calc a * (ν : FiniteMeasure X).mass + b * (ρ : FiniteMeasure X).mass
        ≤ a * 1 + b * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left ν.mass_le_one zero_le)
            (mul_le_mul_of_nonneg_left ρ.mass_le_one zero_le)
      _ = 1 := by rw [mul_one, mul_one, hab]⟩

@[simp] theorem coe_mix (a b : ℝ≥0) (hab : a + b = 1)
    (ν ρ : SubProbabilityMeasure X) :
    ((mix a b hab ν ρ : SubProbabilityMeasure X) : FiniteMeasure X)
      = a • (ν : FiniteMeasure X) + b • (ρ : FiniteMeasure X) := rfl

end SubProbabilityMeasure

/-- Mixture of two probability directions. -/
noncomputable def pmix (s t : ℝ≥0) (hst : s + t = 1)
    (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨s • (μ : Measure X) + t • (ν : Measure X), by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, ENNReal.smul_def, ENNReal.smul_def,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add, hst,
      ENNReal.coe_one]⟩

theorem pmix_toMeasure (s t : ℝ≥0) (hst : s + t = 1)
    (μ ν : ProbabilityMeasure X) :
    (pmix s t hst μ ν : Measure X)
      = s • (μ : Measure X) + t • (ν : Measure X) := rfl

/-- Degenerate mixture, left weight zero. -/
theorem pmix_zero_left (hst : (0 : ℝ≥0) + 1 = 1)
    (μ ν : ProbabilityMeasure X) : pmix 0 1 hst μ ν = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [pmix_toMeasure, zero_smul, one_smul, zero_add]

/-- Degenerate mixture, right weight zero. -/
theorem pmix_zero_right (hst : (1 : ℝ≥0) + 0 = 1)
    (μ ν : ProbabilityMeasure X) : pmix 1 0 hst μ ν = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [pmix_toMeasure, zero_smul, one_smul, add_zero]

namespace CredalPoset

/-! ## Carrier-side vocabulary -/

/-- Convexity of a set of subprobability states: closure under
mixtures. -/
def ConvexBody (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∀ ν ∈ S, ∀ ρ ∈ S, ∀ (a b : ℝ≥0) (hab : a + b = 1),
    SubProbabilityMeasure.mix a b hab ν ρ ∈ S

/-- Pointwise-down closure: every state setwise below a member is a
member.  This is the `⊥`-closure of the Mio–Vignudelli–Sarkis /
Kosoy–Appel order (mass may leak anywhere), strictly stronger than
ray-down closure. -/
def PtwiseDown (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∀ ρ ∈ S, ∀ ν : SubProbabilityMeasure X,
    ((ν : FiniteMeasure X) : Measure X)
      ≤ ((ρ : FiniteMeasure X) : Measure X) → ν ∈ S

/-- Scaling is setwise decrease: ray-down closure follows from
pointwise-down closure. -/
theorem PtwiseDown.isRadial {S : Set (SubProbabilityMeasure X)}
    (h : PtwiseDown S) : IsRadial S := by
  intro ν hν t ht
  refine h ν hν _ ?_
  intro s
  rw [SubProbabilityMeasure.coe_scale]
  show (t • ((ν : FiniteMeasure X) : Measure X)) s
    ≤ ((ν : FiniteMeasure X) : Measure X) s
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc (t : ℝ≥0∞) * ((ν : FiniteMeasure X) : Measure X) s
      ≤ 1 * ((ν : FiniteMeasure X) : Measure X) s := by
        exact mul_le_mul_right' (by exact_mod_cast ht) _
    _ = ((ν : FiniteMeasure X) : Measure X) s := one_mul _

/-! ## The classes -/

/-- The house class: a **credal body** is a nonempty, topologically
closed, ray-down-closed subset of the general subprobability carrier —
exactly the radial compiles of lower semicontinuous penalty
functionals (`exists_lsc_compile_eq_iff`); no convexity is imposed:
citizenship is lower semicontinuity, and nothing else. -/
def IsCredalBody (S : Set (SubProbabilityMeasure X)) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ IsRadial S

/-- The convex subclass. -/
def IsConvexCredalBody (S : Set (SubProbabilityMeasure X)) : Prop :=
  IsCredalBody S ∧ ConvexBody S

/-- The convex-substratum criterion in grade coordinates: the
division-free, cross-multiplied harmonic-mean inequality — `e^f`
convex, said multiplicatively.  This is the exact condition for
convexity of the body (the finite stratum's
`QtslAux.Imprecise.PenaltyCredalIso` carries the same inequality in
exact-rational grade coordinates). -/
def GradeConvex (f : Penalty X) : Prop :=
  ∀ (μ ν : ProbabilityMeasure X) (s t : ℝ≥0) (hst : s + t = 1),
    gradeN (f μ) * gradeN (f ν)
      ≤ gradeN (f (pmix s t hst μ ν))
          * (s * gradeN (f ν) + t * gradeN (f μ))

/-- Kosoy–Appel homogeneous ultracontributions: nonempty,
topologically closed, convex, pointwise-down-closed sets of
subprobability states. -/
def IsUltra (S : Set (SubProbabilityMeasure X)) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ ConvexBody S ∧ PtwiseDown S

/-- Halpern–Leung MWER bodies: ultracontributions containing at least
one full-mass member. -/
def IsHL (S : Set (SubProbabilityMeasure X)) : Prop :=
  IsUltra S ∧ ∃ ν ∈ S, (ν : FiniteMeasure X).mass = 1

/-- Convexity of a set of probability directions: closure under
mixtures. -/
def ConvexDirections (K : Set (ProbabilityMeasure X)) : Prop :=
  ∀ μ ∈ K, ∀ ν ∈ K, ∀ (s t : ℝ≥0) (hst : s + t = 1),
    pmix s t hst μ ν ∈ K

/-- The radial embedding `[0,1] • K` of a set of probability
directions. -/
def scaleSegment (K : Set (ProbabilityMeasure X)) :
    Set (SubProbabilityMeasure X) :=
  {ν | ∃ μ ∈ K, ∃ (t : ℝ≥0) (ht : t ≤ 1),
    ν = SubProbabilityMeasure.scalePoint t ht μ}

/-- Classical credal sets (Cozman et al.): nonempty closed convex sets
of *full-mass* laws, entering the atlas through their radial
embedding. -/
def IsCozman (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∃ K : Set (ProbabilityMeasure X), K.Nonempty ∧ IsClosed K
    ∧ ConvexDirections K ∧ S = scaleSegment K

/-- Prevision-shaped bodies: cut out by an arbitrary family of
one-sided constraints `∫ h dν ≤ 1` on nonnegative bounded continuous
gambles — the hyperspace objects of Goubault-Larrecq's superlinear
prevision domains, at the general carrier. -/
def IsPrevisionBody (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∃ H : Set (X →ᵇ ℝ≥0),
    S = {ν : SubProbabilityMeasure X
      | ∀ h ∈ H, (ν : FiniteMeasure X).testAgainstNN h ≤ 1}

/-- The pointwise-down closure of the mixtures of a finite generating
set: the Mio–Sarkis–Vignudelli `C^↓` shape, spelled through explicit
finite convex combinations (the natural reading of *finitely
generated* over an `ℝ≥0`-module). -/
def ptwiseDownHull (F : Finset (SubProbabilityMeasure X)) :
    Set (SubProbabilityMeasure X) :=
  {ν | ∃ w : SubProbabilityMeasure X → ℝ≥0, (∑ x ∈ F, w x) = 1
    ∧ ((ν : FiniteMeasure X) : Measure X)
        ≤ ((∑ x ∈ F, w x • (x : FiniteMeasure X)) : FiniteMeasure X)}

/-- The Mio–Vignudelli–Sarkis `C^↓` class: pointwise-down closures of
nonempty finitely generated mixture polytopes. -/
def IsMVS (S : Set (SubProbabilityMeasure X)) : Prop :=
  ∃ F : Finset (SubProbabilityMeasure X), F.Nonempty
    ∧ S = ptwiseDownHull F

/-! ## The inclusion spine -/

/-- **T1**: convex credal bodies are credal bodies. -/
theorem IsConvexCredalBody.isCredalBody {S : Set (SubProbabilityMeasure X)}
    (h : IsConvexCredalBody S) : IsCredalBody S := h.1

/-- **T3**: ultracontributions are convex credal bodies. -/
theorem IsUltra.isConvexCredalBody {S : Set (SubProbabilityMeasure X)}
    (h : IsUltra S) : IsConvexCredalBody S :=
  ⟨⟨h.1, h.2.1, h.2.2.2.isRadial⟩, h.2.2.1⟩

/-- **T5**: Halpern–Leung bodies are ultracontributions. -/
theorem IsHL.isUltra {S : Set (SubProbabilityMeasure X)}
    (h : IsHL S) : IsUltra S := h.1

/-! ## The harmonic-mean leg: grade-convex penalties have convex bodies -/

/-- **The harmonic-mean leg at the general carrier**: the body of a
grade-convex penalty is convex.  The mass bookkeeping is the finite
stratum's exact-rational argument verbatim: the mixture of two admitted
states re-parametrizes as a mass on the mixed direction whose weights
are the mass proportions, and the cross-multiplied harmonic-mean
inequality is exactly what bounds that mass by the mixed grade.
Division-free until the final normalization, no exponential
anywhere. -/
theorem convexBody_compile_of_gradeConvex [Nonempty X] {f : Penalty X}
    (hgc : GradeConvex f) : ConvexBody (compile f) := by
  rintro x ⟨μx, γ, hγ, hex⟩ y ⟨μy, δ, hδ, hey⟩ a b hab
  -- the mixture's polar data
  have hcoe : ((SubProbabilityMeasure.mix a b hab x y :
      SubProbabilityMeasure X) : FiniteMeasure X)
      = (a * γ) • μx.toFiniteMeasure + (b * δ) • μy.toFiniteMeasure := by
    rw [SubProbabilityMeasure.coe_mix, hex, hey, smul_smul, smul_smul]
  rcases eq_or_ne (a * γ + b * δ) 0 with hm | hm
  · -- degenerate: the mixture is the bottom state
    obtain ⟨h1, h2⟩ := add_eq_zero.mp hm
    have hzero : SubProbabilityMeasure.mix a b hab x y
        = (0 : SubProbabilityMeasure X) := by
      apply SubProbabilityMeasure.ext
      rw [hcoe, h1, h2, zero_smul, zero_smul, add_zero,
        SubProbabilityMeasure.coe_zero]
    rw [hzero]
    exact zero_mem_compile f
  · -- positive mass: mix the directions with the mass proportions
    set m : ℝ≥0 := a * γ + b * δ with hmdef
    have hst : a * γ / m + b * δ / m = 1 := by
      rw [← add_div, ← hmdef, div_self hm]
    set π : ProbabilityMeasure X := pmix _ _ hst μx μy with hπdef
    -- the mixture is `m` on the mixed direction
    have hdecomp : ((SubProbabilityMeasure.mix a b hab x y :
        SubProbabilityMeasure X) : FiniteMeasure X)
        = m • π.toFiniteMeasure := by
      apply Subtype.ext
      rw [hcoe]
      show (a * γ) • (μx.toFiniteMeasure : Measure X)
          + (b * δ) • (μy.toFiniteMeasure : Measure X)
        = m • (π.toFiniteMeasure : Measure X)
      have hπm : (π.toFiniteMeasure : Measure X)
          = (a * γ / m) • (μx.toFiniteMeasure : Measure X)
            + (b * δ / m) • (μy.toFiniteMeasure : Measure X) := rfl
      rw [hπm, smul_add, smul_smul, smul_smul,
        mul_comm m (a * γ / m), div_mul_cancel₀ _ hm,
        mul_comm m (b * δ / m), div_mul_cancel₀ _ hm]
    -- the mass is below the mixed grade
    have hmle : m ≤ gradeN (f π) := by
      rcases eq_or_ne (gradeN (f μx)) 0 with hgx | hgx
      · -- left grade zero forces the left mass out
        have hγ0 : γ = 0 := le_antisymm (hgx ▸ hγ) zero_le
        have haγ : a * γ = 0 := by rw [hγ0, mul_zero]
        have hmbδ : m = b * δ := by rw [hmdef, haγ, zero_add]
        have hs0 : a * γ / m = 0 := by rw [haγ, zero_div]
        have ht1 : b * δ / m = 1 := by rw [← hmbδ, div_self hm]
        have hπy : π = μy := by
          rw [hπdef]
          apply ProbabilityMeasure.toMeasure_injective
          rw [pmix_toMeasure, hs0, ht1, zero_smul, one_smul, zero_add]
        rw [hπy, hmbδ]
        have hb1 : b ≤ 1 := by
          rw [← hab]
          exact le_add_self
        calc b * δ ≤ 1 * δ :=
              mul_le_mul_of_nonneg_right hb1 zero_le
          _ = δ := one_mul δ
          _ ≤ gradeN (f μy) := hδ
      · rcases eq_or_ne (gradeN (f μy)) 0 with hgy | hgy
        · -- right grade zero forces the right mass out
          have hδ0 : δ = 0 := le_antisymm (hgy ▸ hδ) zero_le
          have hbδ : b * δ = 0 := by rw [hδ0, mul_zero]
          have hmaγ : m = a * γ := by rw [hmdef, hbδ, add_zero]
          have hs1 : a * γ / m = 1 := by rw [← hmaγ, div_self hm]
          have ht0 : b * δ / m = 0 := by rw [hbδ, zero_div]
          have hπx : π = μx := by
            rw [hπdef]
            apply ProbabilityMeasure.toMeasure_injective
            rw [pmix_toMeasure, hs1, ht0, zero_smul, one_smul, add_zero]
          rw [hπx, hmaγ]
          have ha1 : a ≤ 1 := by
            rw [← hab]
            exact le_self_add
          calc a * γ ≤ 1 * γ :=
                mul_le_mul_of_nonneg_right ha1 zero_le
            _ = γ := one_mul γ
            _ ≤ gradeN (f μx) := hγ
        · -- both grades positive: the cross-multiplied inequality
          have hgc' := hgc μx μy _ _ hst
          -- the weight term is dominated by the product-over-mass
          have hnum : a * γ * gradeN (f μy) + b * δ * gradeN (f μx)
              ≤ gradeN (f μx) * gradeN (f μy) := by
            calc a * γ * gradeN (f μy) + b * δ * gradeN (f μx)
                ≤ a * gradeN (f μx) * gradeN (f μy)
                  + b * gradeN (f μy) * gradeN (f μx) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hγ zero_le)
                      zero_le)
                    (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hδ zero_le)
                      zero_le)
              _ = (a + b) * (gradeN (f μx) * gradeN (f μy)) := by ring
              _ = gradeN (f μx) * gradeN (f μy) := by
                  rw [hab, one_mul]
          have hweight : (a * γ / m) * gradeN (f μy)
              + (b * δ / m) * gradeN (f μx)
              ≤ gradeN (f μx) * gradeN (f μy) / m := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
              div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_right' hnum _
          have hchain : gradeN (f μx) * gradeN (f μy)
              ≤ gradeN (f π) * (gradeN (f μx) * gradeN (f μy) / m) := by
            calc gradeN (f μx) * gradeN (f μy)
                ≤ gradeN (f π) * ((a * γ / m) * gradeN (f μy)
                    + (b * δ / m) * gradeN (f μx)) := hgc'
              _ ≤ gradeN (f π)
                    * (gradeN (f μx) * gradeN (f μy) / m) :=
                  mul_le_mul_of_nonneg_left hweight zero_le
          -- cross-multiply back
          have hprodpos : (0 : ℝ≥0) < gradeN (f μx) * gradeN (f μy) :=
            mul_pos (pos_iff_ne_zero.mpr hgx) (pos_iff_ne_zero.mpr hgy)
          have hmul : m * (gradeN (f μx) * gradeN (f μy))
              ≤ gradeN (f π) * (gradeN (f μx) * gradeN (f μy)) := by
            calc m * (gradeN (f μx) * gradeN (f μy))
                ≤ m * (gradeN (f π)
                    * (gradeN (f μx) * gradeN (f μy) / m)) :=
                  mul_le_mul_of_nonneg_left hchain zero_le
              _ = gradeN (f π) * (gradeN (f μx) * gradeN (f μy)) := by
                  rw [mul_comm m, mul_assoc,
                    div_mul_cancel₀ _ hm]
          exact le_of_mul_le_mul_right hmul hprodpos
    exact ⟨π, m, hmle, hdecomp⟩

/-! ## Classical credal sets ride the dictionary -/

open Classical in
/-- The wall of a set of directions: zero on it, hard violation off
it. -/
noncomputable def dirWall (K : Set (ProbabilityMeasure X)) : Penalty X :=
  fun μ => if μ ∈ K then 0 else ⊤

theorem dirWall_apply_of_mem {K : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∈ K) : dirWall K μ = 0 := by
  simp [dirWall, h]

theorem dirWall_apply_of_not_mem {K : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∉ K) : dirWall K μ = ⊤ := by
  simp [dirWall, h]

theorem gradeN_dirWall_of_mem {K : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∈ K) :
    gradeN (dirWall K μ) = 1 := by
  rw [dirWall_apply_of_mem h, gradeN_zero]

theorem gradeN_dirWall_of_not_mem {K : Set (ProbabilityMeasure X)}
    {μ : ProbabilityMeasure X} (h : μ ∉ K) :
    gradeN (dirWall K μ) = 0 := by
  rw [dirWall_apply_of_not_mem h, gradeN_top]

/-- Walls on closed direction sets are citizens. -/
theorem lowerSemicontinuous_dirWall {K : Set (ProbabilityMeasure X)}
    (hK : IsClosed K) : LowerSemicontinuous (dirWall K) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · have hrepr : dirWall K ⁻¹' Set.Iic ⊤ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro μ
      rw [Set.mem_preimage, Set.mem_Iic]
      exact le_top
    rw [hrepr]
    exact isClosed_univ
  · have hrepr : dirWall K ⁻¹' Set.Iic y = K := by
      ext μ
      simp only [Set.mem_preimage, Set.mem_Iic]
      constructor
      · intro h
        by_contra hμ
        rw [dirWall_apply_of_not_mem hμ] at h
        exact hy (top_le_iff.mp h)
      · intro h
        rw [dirWall_apply_of_mem h]
        exact zero_le
    rw [hrepr]
    exact hK

/-- Walls on convex direction sets are grade-convex. -/
theorem gradeConvex_dirWall {K : Set (ProbabilityMeasure X)}
    (hK : ConvexDirections K) : GradeConvex (dirWall K) := by
  intro μ ν s t hst
  by_cases hμ : μ ∈ K
  · by_cases hν : ν ∈ K
    · simp [gradeN_dirWall_of_mem hμ, gradeN_dirWall_of_mem hν,
        gradeN_dirWall_of_mem (hK μ hμ ν hν s t hst), hst]
    · rw [gradeN_dirWall_of_not_mem hν, mul_zero]
      exact zero_le
  · rw [gradeN_dirWall_of_not_mem hμ, zero_mul]
    exact zero_le

/-- The radial embedding of a nonempty direction set is the body of its
wall: classical credal sets are compiles, so their topological facts
are instances of the dictionary. -/
theorem scaleSegment_eq_compile_dirWall {K : Set (ProbabilityMeasure X)}
    (hne : K.Nonempty) : scaleSegment K = compile (dirWall K) := by
  ext ν
  constructor
  · rintro ⟨μ, hμ, t, ht, rfl⟩
    refine ⟨μ, t, ?_, SubProbabilityMeasure.coe_scalePoint _ _ _⟩
    rw [gradeN_dirWall_of_mem hμ]
    exact ht
  · rintro ⟨μ, γ, hγ, he⟩
    by_cases hμ : μ ∈ K
    · have hγ1 : γ ≤ 1 := hγ.trans (gradeN_le_one _)
      exact ⟨μ, hμ, γ, hγ1, SubProbabilityMeasure.ext (by
        rw [SubProbabilityMeasure.coe_scalePoint, he])⟩
    · obtain ⟨μ₀, hμ₀⟩ := hne
      have hγ0 : γ = 0 := by
        have := hγ
        rw [gradeN_dirWall_of_not_mem hμ] at this
        exact le_antisymm this zero_le
      refine ⟨μ₀, hμ₀, 0, zero_le_one, SubProbabilityMeasure.ext (by
        rw [SubProbabilityMeasure.coe_scalePoint, he, hγ0, zero_smul,
          zero_smul])⟩

/-- **Classical credal sets are convex credal bodies**: the radial
embedding of a nonempty closed convex set of full-mass laws is a
nonempty closed radial convex subset of the carrier — closedness by
the dictionary, convexity by the harmonic-mean leg on the wall. -/
theorem IsCozman.isConvexCredalBody [Nonempty X]
    {S : Set (SubProbabilityMeasure X)} (h : IsCozman S) :
    IsConvexCredalBody S := by
  obtain ⟨K, hne, hcl, hcv, rfl⟩ := h
  rw [scaleSegment_eq_compile_dirWall hne]
  refine ⟨⟨⟨_, zero_mem_compile _⟩,
    isClosed_compile (lowerSemicontinuous_dirWall hcl),
    isRadial_compile _⟩, ?_⟩
  exact convexBody_compile_of_gradeConvex (gradeConvex_dirWall hcv)

/-! ## Prevision-shaped bodies are ultracontributions -/

/-- The pairing against a fixed nonnegative bounded continuous gamble
is narrowly continuous — the defining observation class of the weak
topology. -/
theorem continuous_pairing (h : X →ᵇ ℝ≥0) :
    Continuous fun μ : FiniteMeasure X => μ.testAgainstNN h := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp
    tendsto_id) h

/-- Pairing is monotone in the measure. -/
theorem pairing_mono {μ ν : FiniteMeasure X}
    (hle : (μ : Measure X) ≤ (ν : Measure X)) (h : X →ᵇ ℝ≥0) :
    μ.testAgainstNN h ≤ ν.testAgainstNN h := by
  rw [← ENNReal.coe_le_coe, FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.testAgainstNN_coe_eq]
  exact lintegral_mono' hle le_rfl

/-- Pairing is additive in the measure. -/
theorem pairing_add (μ ν : FiniteMeasure X) (h : X →ᵇ ℝ≥0) :
    (μ + ν).testAgainstNN h = μ.testAgainstNN h + ν.testAgainstNN h := by
  rw [← ENNReal.coe_inj, ENNReal.coe_add,
    FiniteMeasure.testAgainstNN_coe_eq, FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.testAgainstNN_coe_eq, FiniteMeasure.toMeasure_add,
    lintegral_add_measure]

/-- **Prevision-shaped bodies are ultracontributions**: each one-sided
constraint carves a closed, convex, setwise-down-closed region owning
the bottom state, and the class is intersection-stable. -/
theorem IsPrevisionBody.isUltra {S : Set (SubProbabilityMeasure X)}
    (h : IsPrevisionBody S) : IsUltra S := by
  obtain ⟨H, rfl⟩ := h
  refine ⟨⟨0, ?_⟩, ?_, ?_, ?_⟩
  · -- the bottom state satisfies every constraint
    intro h hH
    rw [SubProbabilityMeasure.coe_zero]
    have hz : (0 : FiniteMeasure X).testAgainstNN h = 0 := by
      rw [← ENNReal.coe_inj, FiniteMeasure.testAgainstNN_coe_eq,
        FiniteMeasure.toMeasure_zero, lintegral_zero_measure,
        ENNReal.coe_zero]
    rw [hz]
    exact zero_le_one
  · -- closed: an intersection of continuous sublevels
    have hrepr : {ν : SubProbabilityMeasure X
        | ∀ h ∈ H, (ν : FiniteMeasure X).testAgainstNN h ≤ 1}
        = ⋂ h ∈ H, {ν : SubProbabilityMeasure X
            | (ν : FiniteMeasure X).testAgainstNN h ≤ 1} := by
      ext ν
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrepr]
    refine isClosed_biInter fun h hH => ?_
    exact IsClosed.preimage
      ((continuous_pairing h).comp
        SubProbabilityMeasure.continuous_toFiniteMeasure)
      isClosed_Iic
  · -- convex: pairing is affine in the measure
    intro ν hν ρ hρ a b hab h hH
    rw [SubProbabilityMeasure.coe_mix, pairing_add,
      FiniteMeasure.smul_testAgainstNN_apply,
      FiniteMeasure.smul_testAgainstNN_apply, smul_eq_mul, smul_eq_mul]
    calc a * (ν : FiniteMeasure X).testAgainstNN h
        + b * (ρ : FiniteMeasure X).testAgainstNN h
        ≤ a * 1 + b * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hν h hH) zero_le)
            (mul_le_mul_of_nonneg_left (hρ h hH) zero_le)
      _ = 1 := by rw [mul_one, mul_one, hab]
  · -- setwise-down-closed: pairing is monotone
    intro ρ hρ ν hle h hH
    exact le_trans (pairing_mono hle h) (hρ h hH)

/-! ## Finite generation: the compactness half, and the honest reduction -/

/-- Members of the generating set belong to the hull. -/
theorem mem_ptwiseDownHull_of_mem {F : Finset (SubProbabilityMeasure X)}
    {ν : SubProbabilityMeasure X} (hν : ν ∈ F) : ν ∈ ptwiseDownHull F := by
  classical
  refine ⟨fun x => if x = ν then 1 else 0, ?_, ?_⟩
  · rw [Finset.sum_eq_single ν]
    · rw [if_pos rfl]
    · intro b _ hbne
      rw [if_neg hbne]
    · intro hν'
      exact absurd hν hν'
  · have hsum : (∑ x ∈ F, (if x = ν then (1 : ℝ≥0) else 0)
        • (x : FiniteMeasure X)) = (ν : FiniteMeasure X) := by
      rw [Finset.sum_eq_single ν]
      · rw [if_pos rfl, one_smul]
      · intro b _ hbne
        rw [if_neg hbne, zero_smul]
      · intro hν'
        exact absurd hν hν'
    rw [hsum]

/-- **The MVS reduction, stated honestly.**  Closedness of a finitely
generated down-closed body follows from narrow-closedness of the
setwise order relation on the carrier's finite measures — the
regularity input — together with compactness of the weight simplex,
which holds for any carrier.  The finite stratum discharges the order
hypothesis by computation; over a metrizable carrier it is
dischargeable through thickened indicators and weak regularity of
finite Borel measures; over a general topological carrier it is not
free, and this statement carries it as the named hypothesis rather
than smoothing it over. -/
theorem isClosed_ptwiseDownHull
    (horder : IsClosed {p : FiniteMeasure X × FiniteMeasure X |
      (p.1 : Measure X) ≤ (p.2 : Measure X)})
    (F : Finset (SubProbabilityMeasure X)) :
    IsClosed (ptwiseDownHull F) := by
  classical
  rw [isClosed_iff_clusterPt]
  intro ν hν
  haveI hFne : (𝓝 ν ⊓ 𝓟 (ptwiseDownHull F)).NeBot := hν
  set L := 𝓝 ν ⊓ 𝓟 (ptwiseDownHull F) with hLdef
  -- the weight simplex over the generators is compact
  set W : Set (SubProbabilityMeasure X → ℝ≥0) :=
    {w | (∑ x ∈ F, w x) = 1 ∧ ∀ x, x ∉ F → w x = 0} with hWdef
  have hWcompact : IsCompact W := by
    have hWsub : W ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ≥0) 1 := by
      intro w hw
      intro x _
      refine ⟨zero_le, ?_⟩
      by_cases hx : x ∈ F
      · calc w x ≤ ∑ y ∈ F, w y :=
            Finset.single_le_sum (fun y _ => zero_le) hx
          _ = 1 := hw.1
      · rw [hw.2 x hx]
        exact zero_le_one
    have hWclosed : IsClosed W := by
      have h1 : IsClosed {w : SubProbabilityMeasure X → ℝ≥0 |
          (∑ x ∈ F, w x) = 1} :=
        isClosed_eq
          (continuous_finsetSum _ fun x _ => continuous_apply x)
          continuous_const
      have h2 : IsClosed {w : SubProbabilityMeasure X → ℝ≥0 |
          ∀ x, x ∉ F → w x = 0} := by
        have hrepr : {w : SubProbabilityMeasure X → ℝ≥0 |
            ∀ x, x ∉ F → w x = 0}
            = ⋂ x ∈ {x : SubProbabilityMeasure X | x ∉ F},
                {w : SubProbabilityMeasure X → ℝ≥0 | w x = 0} := by
          ext w
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
        rw [hrepr]
        exact isClosed_biInter fun x _ =>
          isClosed_eq (continuous_apply x) continuous_const
      exact h1.inter h2
    exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_Icc) hWclosed hWsub
  -- the generated polytope (the weighted sums) is compact
  have hbarycompact : IsCompact ((fun w : SubProbabilityMeasure X → ℝ≥0 =>
      (∑ x ∈ F, w x • (x : FiniteMeasure X))) '' W) := by
    refine hWcompact.image ?_
    refine continuous_finsetSum _ fun x _ => ?_
    exact (SubProbabilityMeasure.continuous_smul_scalar
      (x : FiniteMeasure X)).comp (continuous_apply x)
  -- pick a cluster point of the dominating barycenters along `L`
  have hmemL : ∀ᶠ ρ : SubProbabilityMeasure X in L,
      ρ ∈ ptwiseDownHull F :=
    Filter.le_principal_iff.mp inf_le_right
  -- choose, for each hull member, a dominating barycenter
  classical
  have hdom : ∀ ρ : SubProbabilityMeasure X, ρ ∈ ptwiseDownHull F →
      ∃ β ∈ (fun w : SubProbabilityMeasure X → ℝ≥0 =>
        (∑ x ∈ F, w x • (x : FiniteMeasure X))) '' W,
        ((ρ : FiniteMeasure X) : Measure X) ≤ (β : Measure X) := by
    rintro ρ ⟨w, hw1, hw2⟩
    refine ⟨∑ x ∈ F, (fun y => if y ∈ F then w y else 0) x
      • (x : FiniteMeasure X), ⟨_, ⟨?_, fun x hx => if_neg hx⟩, rfl⟩, ?_⟩
    · have hsum1 : (∑ x ∈ F, (fun y => if y ∈ F then w y else 0) x)
          = ∑ x ∈ F, w x :=
        Finset.sum_congr rfl fun x hx => by simp [hx]
      rw [hsum1]
      exact hw1
    · have hsame : (∑ x ∈ F, (fun y => if y ∈ F then w y else 0) x
          • (x : FiniteMeasure X))
          = ∑ x ∈ F, w x • (x : FiniteMeasure X) :=
        Finset.sum_congr rfl fun x hx => by simp [hx]
      rw [hsame]
      exact hw2
  choose βfun hβmem hβdom using hdom
  -- the barycenter selections live in a compact set, so they cluster
  set bary : SubProbabilityMeasure X → FiniteMeasure X := fun ρ =>
    if hρ : ρ ∈ ptwiseDownHull F then βfun ρ hρ else 0 with hbarydef
  have hbaryev : ∀ᶠ ρ : SubProbabilityMeasure X in L,
      bary ρ ∈ (fun w : SubProbabilityMeasure X → ℝ≥0 =>
        (∑ x ∈ F, w x • (x : FiniteMeasure X))) '' W := by
    filter_upwards [hmemL] with ρ hρ
    have hb : bary ρ = βfun ρ hρ := by
      simp only [hbarydef]
      exact dif_pos hρ
    rw [hb]
    exact hβmem ρ hρ
  have hcluster : ∃ β ∈ (fun w : SubProbabilityMeasure X → ℝ≥0 =>
      (∑ x ∈ F, w x • (x : FiniteMeasure X))) '' W,
      MapClusterPt β L bary :=
    hbarycompact.exists_mapClusterPt_of_frequently
      (hbaryev.frequently)
  obtain ⟨β, hβmem', hβcluster⟩ := hcluster
  obtain ⟨wβ, hwβ, hβeq⟩ := hβmem'
  -- pass to the finer filter where the barycenters converge
  have hLle : 𝓝 ν ⊓ 𝓟 (ptwiseDownHull F) ≤ 𝓝 ν := inf_le_left
  set L' := L ⊓ Filter.comap bary (𝓝 β) with hL'def
  haveI hL'ne : L'.NeBot := by
    have h1 : (𝓝 β ⊓ Filter.map bary L).NeBot := hβcluster
    have h2 : (Filter.map bary L ⊓ 𝓝 β).NeBot := by
      rwa [inf_comm] at h1
    have h3 : (Filter.map bary (L ⊓ Filter.comap bary (𝓝 β))).NeBot := by
      rwa [Filter.push_pull]
    exact (Filter.map_neBot_iff bary).mp h3
  -- along `L'`: the states converge to `ν`, the barycenters to `β`,
  -- and the order holds eventually; order-closedness passes it to the
  -- limit
  have hpair : Tendsto
      (fun ρ : SubProbabilityMeasure X =>
        ((ρ : FiniteMeasure X), bary ρ)) L'
      (𝓝 ((ν : FiniteMeasure X), β)) := by
    rw [nhds_prod_eq]
    refine Tendsto.prodMk ?_ ?_
    · exact ((SubProbabilityMeasure.continuous_toFiniteMeasure.tendsto
        ν).mono_left (le_trans inf_le_left hLle))
    · exact tendsto_comap.mono_left inf_le_right
  have hevle : ∀ᶠ ρ : SubProbabilityMeasure X in L',
      (((ρ : FiniteMeasure X), bary ρ) :
        FiniteMeasure X × FiniteMeasure X)
        ∈ {p : FiniteMeasure X × FiniteMeasure X |
            (p.1 : Measure X) ≤ (p.2 : Measure X)} := by
    have hmemL' : ∀ᶠ ρ : SubProbabilityMeasure X in L',
        ρ ∈ ptwiseDownHull F :=
      hmemL.filter_mono inf_le_left
    filter_upwards [hmemL'] with ρ hρ
    have hb : bary ρ = βfun ρ hρ := by
      simp only [hbarydef]
      exact dif_pos hρ
    show ((ρ : FiniteMeasure X) : Measure X)
      ≤ ((bary ρ : FiniteMeasure X) : Measure X)
    rw [hb]
    exact hβdom ρ hρ
  have hlimle : ((ν : FiniteMeasure X) : Measure X) ≤ (β : Measure X) :=
    horder.mem_of_tendsto hpair hevle
  have hβeq' : (∑ x ∈ F, wβ x • (x : FiniteMeasure X)) = β := hβeq
  exact ⟨wβ, hwβ.1, by rw [hβeq']; exact hlimle⟩

/-- **The MVS placement, under the named regularity input**: finitely
generated down-closed bodies are ultracontributions, given
narrow-closedness of the setwise order (see
`isClosed_ptwiseDownHull`).  Everything else — nonemptiness,
convexity, setwise-down-closure — holds for any carrier
unconditionally. -/
theorem IsMVS.isUltra
    (horder : IsClosed {p : FiniteMeasure X × FiniteMeasure X |
      (p.1 : Measure X) ≤ (p.2 : Measure X)})
    {S : Set (SubProbabilityMeasure X)} (h : IsMVS S) : IsUltra S := by
  classical
  obtain ⟨F, hFne, rfl⟩ := h
  refine ⟨?_, isClosed_ptwiseDownHull horder F, ?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hFne
    exact ⟨ν, mem_ptwiseDownHull_of_mem hν⟩
  · -- convexity: mix the witnesses and the weights
    rintro ν ⟨wv, hwv1, hwv2⟩ ρ ⟨wr, hwr1, hwr2⟩ a b hab
    refine ⟨fun x => a * wv x + b * wr x, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hwv1, hwr1, mul_one, mul_one, hab]
    · rw [SubProbabilityMeasure.coe_mix]
      have hsplit : (∑ x ∈ F, (a * wv x + b * wr x)
          • (x : FiniteMeasure X))
          = a • (∑ x ∈ F, wv x • (x : FiniteMeasure X))
            + b • (∑ x ∈ F, wr x • (x : FiniteMeasure X)) := by
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by
          rw [add_smul, smul_smul, smul_smul]
      rw [hsplit]
      show ((a • (ν : FiniteMeasure X) + b • (ρ : FiniteMeasure X) :
        FiniteMeasure X) : Measure X) ≤ _
      have hgoal : ∀ (p q r s : FiniteMeasure X),
          ((p : Measure X) ≤ (q : Measure X)) →
          ((r : Measure X) ≤ (s : Measure X)) →
          (((a • p + b • r : FiniteMeasure X)) : Measure X)
            ≤ ((a • q + b • s : FiniteMeasure X) : Measure X) := by
        intro p q r s hpq hrs
        intro u
        show (a • (p : Measure X) + b • (r : Measure X)) u
          ≤ (a • (q : Measure X) + b • (s : Measure X)) u
        rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
          Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
          ENNReal.smul_def, ENNReal.smul_def, ENNReal.smul_def,
          ENNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul,
          smul_eq_mul]
        exact add_le_add (mul_le_mul_left' (Measure.le_iff'.mp hpq u) _)
          (mul_le_mul_left' (Measure.le_iff'.mp hrs u) _)
      exact hgoal _ _ _ _ hwv2 hwr2
  · -- setwise-down-closure: transitivity of the order
    rintro ρ ⟨w, hw1, hw2⟩ ν hle
    exact ⟨w, hw1, le_trans hle hw2⟩

end CredalPoset

end SuFunctor.Universe.General
