import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.UniformSpace.Dini

/-! # Coherent lower previsions on bounded continuous gambles

Walley's coherence axioms (W1)–(W3) for a lower prevision, stated on the
bounded continuous real gambles `X →ᵇ ℝ` over a topological carrier — the
continuous face of the bounded-Borel gamble space, and the face on which
the countably additive envelope theorem is a theorem rather than a
finitely additive phenomenon.

This module carries the carrier-generic layer, deliberately free of any
measure- or metric-theoretic machinery except where explicitly scoped:

* `IsCoherentLP`: the axioms (dominating the infimum, positive
  homogeneity, superadditivity) and their recorded standard consequences
  (normalization on constants, monotonicity, conjugacy bounds).
* `conjUpper`: the conjugate upper prevision `g ↦ -(P (-g))`, with its
  sublinearity — the sublinear bound fed to Hahn–Banach below.
* `DominatesLP`: the dominating linear functionals of a lower prevision;
  each is positive, normalized, and trapped between `P` and its conjugate.
* `SigmaSmoothAtZero`: σ-smoothness — sequential continuity at `0` along
  antitone pointwise-null sequences of gambles.  This is the classical
  discriminator (Daniell's condition, Alexandroff's σ-smoothness) between
  the finitely additive and countably additive representation regimes.
  Dominating functionals of a σ-smooth prevision are σ-smooth
  (`DominatesLP.sigmaSmoothAtZero`, a squeeze).
* `IsCoherentLP.exists_dominatesLP_eq`: the attainment half of the lower
  envelope theorem, by sublinear Hahn–Banach extension
  (`exists_extension_of_le_sublinear`) from the line through a prescribed
  gamble: some dominating linear functional touches `P` at it.  The
  argument is topology-free; no compactness, no local compactness.
* `caCredal`: the countably additive credal set of a lower prevision —
  the Borel probability measures whose expectations dominate it.
* At compact carriers, σ-smoothness is free (`Dini`):
  `IsCoherentLP.sigmaSmoothAtZero_conjUpper_of_compact`.

Sibling faces, deliberately not duplicated here: the finite-carrier
rational stack (`Qtsl.Imprecise`), the measurable-gamble general carrier
(`QtslAux.Imprecise`), and the pointfree prevision layer on lower
semicontinuous gambles.  Reconciliation across the faces is definitional
(a continuous gamble is a measurable one) and is recorded where the
packages meet, not here.
-/

namespace SuFunctor.Universe.General

open BoundedContinuousFunction Filter Topology MeasureTheory

variable {X : Type*} [TopologicalSpace X]

/-! ## Pointwise bounds for bounded continuous gambles -/

theorem bcf_neg_norm_le (g : X →ᵇ ℝ) (x : X) : -‖g‖ ≤ g x :=
  neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x)

theorem bcf_le_norm (g : X →ᵇ ℝ) (x : X) : g x ≤ ‖g‖ :=
  le_of_abs_le (by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x)

theorem bddBelow_range_bcf (g : X →ᵇ ℝ) : BddBelow (Set.range g) :=
  ⟨-‖g‖, by rintro y ⟨x, rfl⟩; exact bcf_neg_norm_le g x⟩

section Coherence

variable [Nonempty X]

/-- **Walley's coherence axioms** for a lower prevision on bounded
continuous gambles: dominating the infimum (W1), positive homogeneity
(W2), and superadditivity (W3). -/
structure IsCoherentLP (P : (X →ᵇ ℝ) → ℝ) : Prop where
  inf_le : ∀ g : X →ᵇ ℝ, (⨅ x, g x) ≤ P g
  homog : ∀ c : ℝ, 0 ≤ c → ∀ g : X →ᵇ ℝ, P (c • g) = c * P g
  superadd : ∀ f g : X →ᵇ ℝ, P f + P g ≤ P (f + g)

namespace IsCoherentLP

variable {P : (X →ᵇ ℝ) → ℝ}

omit [Nonempty X] in
theorem zero_eq (hP : IsCoherentLP P) : P 0 = 0 := by
  simpa using hP.homog 0 le_rfl 0

theorem const_le (hP : IsCoherentLP P) (c : ℝ) : c ≤ P (const X c) := by
  simpa [ciInf_const] using hP.inf_le (const X c)

theorem const_eq (hP : IsCoherentLP P) (c : ℝ) : P (const X c) = c := by
  refine le_antisymm ?_ (hP.const_le c)
  have hsum := hP.superadd (const X c) (const X (-c))
  have hzero : const X c + const X (-c) = (0 : X →ᵇ ℝ) := by
    ext x; simp
  rw [hzero, hP.zero_eq] at hsum
  have := hP.const_le (-c)
  linarith

/-- Coherent lower previsions are monotone. -/
theorem mono (hP : IsCoherentLP P) {f g : X →ᵇ ℝ} (h : ∀ x, f x ≤ g x) :
    P f ≤ P g := by
  have hsum := hP.superadd f (g - f)
  have hfg : f + (g - f) = g := by ext x; simp
  rw [hfg] at hsum
  have h0 : (0 : ℝ) ≤ P (g - f) := by
    have hinf : (0 : ℝ) ≤ ⨅ x, (g - f) x :=
      le_ciInf fun x => by simpa using sub_nonneg.mpr (h x)
    linarith [hP.inf_le (g - f)]
  linarith

theorem nonneg (hP : IsCoherentLP P) {g : X →ᵇ ℝ} (h : ∀ x, 0 ≤ g x) :
    0 ≤ P g := by
  have := hP.mono (f := 0) (g := g) (by simpa using h)
  simpa [hP.zero_eq] using this

end IsCoherentLP

/-- The conjugate upper prevision of a lower prevision. -/
noncomputable def conjUpper (P : (X →ᵇ ℝ) → ℝ) : (X →ᵇ ℝ) → ℝ := fun g => -(P (-g))

namespace IsCoherentLP

variable {P : (X →ᵇ ℝ) → ℝ}

omit [Nonempty X] in
theorem le_conjUpper (hP : IsCoherentLP P) (g : X →ᵇ ℝ) :
    P g ≤ conjUpper P g := by
  have hsum := hP.superadd g (-g)
  rw [add_neg_cancel, hP.zero_eq] at hsum
  simp only [conjUpper]
  linarith

omit [Nonempty X] in
theorem conjUpper_subadd (hP : IsCoherentLP P) (f g : X →ᵇ ℝ) :
    conjUpper P (f + g) ≤ conjUpper P f + conjUpper P g := by
  have hsum := hP.superadd (-f) (-g)
  have : -f + -g = -(f + g) := by ext x; simp; ring
  rw [this] at hsum
  simp only [conjUpper]
  linarith

omit [Nonempty X] in
theorem conjUpper_homog (hP : IsCoherentLP P) {c : ℝ} (hc : 0 ≤ c)
    (g : X →ᵇ ℝ) : conjUpper P (c • g) = c * conjUpper P g := by
  have : -(c • g) = c • (-g) := by ext x; simp
  simp only [conjUpper, this, hP.homog c hc]
  ring

omit [Nonempty X] in
theorem conjUpper_neg (_hP : IsCoherentLP P) (g : X →ᵇ ℝ) :
    conjUpper P (-g) = -(P g) := by
  simp [conjUpper]

/-- The conjugate is trapped in the norm ball: `|conjUpper P g| ≤ ‖g‖`. -/
theorem abs_conjUpper_le (hP : IsCoherentLP P) (g : X →ᵇ ℝ) :
    |conjUpper P g| ≤ ‖g‖ := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- -‖g‖ ≤ P g ≤ conjUpper P g
    have hinf : -‖g‖ ≤ ⨅ x, g x := le_ciInf fun x => bcf_neg_norm_le g x
    linarith [hP.inf_le g, hP.le_conjUpper g]
  · -- conjUpper P g = -(P (-g)) ≤ ‖g‖ since P (-g) ≥ inf (-g) ≥ -‖g‖
    have hinf : -‖g‖ ≤ ⨅ x, (-g) x :=
      le_ciInf fun x => by simpa [neg_le] using bcf_le_norm g x
    have := hP.inf_le (-g)
    simp only [conjUpper]
    linarith

end IsCoherentLP

/-- The dominating linear functionals of a lower prevision. -/
def DominatesLP (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (P : (X →ᵇ ℝ) → ℝ) : Prop :=
  ∀ g : X →ᵇ ℝ, P g ≤ L g

namespace DominatesLP

variable {P : (X →ᵇ ℝ) → ℝ} {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

omit [Nonempty X] in
theorem le_conjUpper (hL : DominatesLP L P) (g : X →ᵇ ℝ) :
    L g ≤ conjUpper P g := by
  have h := hL (-g)
  rw [map_neg] at h
  simp only [conjUpper]
  linarith

theorem nonneg (hP : IsCoherentLP P) (hL : DominatesLP L P) {g : X →ᵇ ℝ}
    (hg : ∀ x, 0 ≤ g x) : 0 ≤ L g :=
  (hP.nonneg hg).trans (hL g)

theorem one_eq (hP : IsCoherentLP P) (hL : DominatesLP L P) :
    L (const X (1 : ℝ)) = 1 := by
  have hup := hL.le_conjUpper (const X (1 : ℝ))
  have hconj : conjUpper P (const X (1 : ℝ)) = 1 := by
    have : -(const X (1 : ℝ)) = const X (-1 : ℝ) := by ext x; simp
    simp [conjUpper, this, hP.const_eq]
  have hlow := hL (const X (1 : ℝ))
  rw [hP.const_eq] at hlow
  rw [hconj] at hup
  linarith

end DominatesLP

end Coherence

/-! ## σ-smoothness -/

/-- σ-smoothness at zero: the functional carries antitone pointwise-null
sequences of gambles to null sequences.  Daniell's condition, the
classical discriminator between the finitely additive and countably
additive representation regimes. -/
def SigmaSmoothAtZero (F : (X →ᵇ ℝ) → ℝ) : Prop :=
  ∀ h : ℕ → (X →ᵇ ℝ), (∀ n x, h (n + 1) x ≤ h n x) →
    (∀ x, Tendsto (fun n => h n x) atTop (𝓝 0)) →
    Tendsto (fun n => F (h n)) atTop (𝓝 0)

/-- Members of an antitone pointwise-null sequence are nonnegative. -/
theorem antitone_null_nonneg {h : ℕ → (X →ᵇ ℝ)}
    (hanti : ∀ n x, h (n + 1) x ≤ h n x)
    (hto : ∀ x, Tendsto (fun n => h n x) atTop (𝓝 0)) (n : ℕ) (x : X) :
    0 ≤ h n x := by
  have ha : Antitone fun m => h m x :=
    antitone_nat_of_succ_le fun m => hanti m x
  exact le_of_tendsto (hto x) (eventually_atTop.mpr ⟨n, fun m hm => ha hm⟩)

section Squeeze

variable [Nonempty X] {P : (X →ᵇ ℝ) → ℝ} {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

/-- Dominating functionals of a σ-smooth coherent lower prevision are
σ-smooth: they are squeezed between `0` and the conjugate. -/
theorem DominatesLP.sigmaSmoothAtZero (hP : IsCoherentLP P)
    (hL : DominatesLP L P) (hs : SigmaSmoothAtZero (conjUpper P)) :
    SigmaSmoothAtZero fun g => L g := by
  intro h hanti hto
  have hnn : ∀ n x, 0 ≤ h n x := antitone_null_nonneg hanti hto
  have hlow : ∀ n, 0 ≤ L (h n) := fun n => hL.nonneg hP (hnn n)
  have hup : ∀ n, L (h n) ≤ conjUpper P (h n) := fun n => hL.le_conjUpper _
  exact squeeze_zero hlow hup (hs h hanti hto)

end Squeeze

/-! ## The attainment half of the lower envelope theorem -/

section HahnBanach

variable [Nonempty X] {P : (X →ᵇ ℝ) → ℝ}

omit [Nonempty X] in
private theorem exists_dominatesLP_eq_of_ne (hP : IsCoherentLP P)
    (g₀ : X →ᵇ ℝ) (hg₀ : g₀ ≠ 0) :
    ∃ L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ, DominatesLP L P ∧ L g₀ = P g₀ := by
  classical
  have hself : (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ : (X →ᵇ ℝ) →ₗ.[ℝ] ℝ)
      ⟨g₀, Submodule.mem_span_singleton_self g₀⟩ = P g₀ :=
    LinearPMap.mkSpanSingleton_apply ℝ ℝ hg₀ (P g₀)
  have hdom : ∀ x : (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ :
      (X →ᵇ ℝ) →ₗ.[ℝ] ℝ).domain,
      (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ : (X →ᵇ ℝ) →ₗ.[ℝ] ℝ) x
        ≤ conjUpper P x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hsub : (⟨c • g₀, hx⟩ : (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ :
        (X →ᵇ ℝ) →ₗ.[ℝ] ℝ).domain)
        = c • ⟨g₀, Submodule.mem_span_singleton_self g₀⟩ :=
      Subtype.ext (Submodule.coe_smul c
        (⟨g₀, Submodule.mem_span_singleton_self g₀⟩ :
          (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ :
            (X →ᵇ ℝ) →ₗ.[ℝ] ℝ).domain)).symm
    rw [hsub, LinearPMap.map_smul, hself]
    have hcoe : ((c • (⟨g₀, Submodule.mem_span_singleton_self g₀⟩ :
        (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ :
          (X →ᵇ ℝ) →ₗ.[ℝ] ℝ).domain) : (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀ :
          (X →ᵇ ℝ) →ₗ.[ℝ] ℝ).domain) : X →ᵇ ℝ) = c • g₀ :=
      Submodule.coe_smul c _
    rw [hcoe]
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · -- c < 0: the conjugate evaluates to c * P g₀ exactly
      have hrw : c • g₀ = -((-c) • g₀) := by ext x; simp
      have hval : conjUpper P (c • g₀) = c * P g₀ := by
        rw [hrw, hP.conjUpper_neg, hP.homog (-c) (by linarith)]
        ring
      rw [hval, smul_eq_mul]
    · simp [hP.zero_eq, conjUpper]
    · have hval : conjUpper P (c • g₀) = c * conjUpper P g₀ :=
        hP.conjUpper_homog (le_of_lt hc) g₀
      rw [hval, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hP.le_conjUpper g₀) (le_of_lt hc)
  obtain ⟨L, hLf, hLle⟩ :=
    exists_extension_of_le_sublinear
      (LinearPMap.mkSpanSingleton g₀ (P g₀) hg₀) (conjUpper P)
      (fun c hc g => hP.conjUpper_homog (le_of_lt hc) g)
      (fun g₁ g₂ => hP.conjUpper_subadd g₁ g₂) hdom
  refine ⟨L, ?_, ?_⟩
  · intro g
    have hg := hLle (-g)
    rw [map_neg] at hg
    simp only [conjUpper, neg_neg] at hg
    linarith
  · have h := hLf ⟨g₀, Submodule.mem_span_singleton_self g₀⟩
    rw [hself] at h
    exact h

/-- **Attainment (the lower envelope theorem, functional half)**: every
coherent lower prevision is touched at any prescribed gamble by some
dominating linear functional.  Sublinear Hahn–Banach extension from the
line through the gamble; no topology on the gamble space is consumed. -/
theorem IsCoherentLP.exists_dominatesLP_eq (hP : IsCoherentLP P)
    (g₀ : X →ᵇ ℝ) :
    ∃ L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ, DominatesLP L P ∧ L g₀ = P g₀ := by
  rcases eq_or_ne g₀ 0 with rfl | hg₀
  · have hone : (const X (1 : ℝ)) ≠ 0 := by
      intro h
      have := DFunLike.congr_fun h (Classical.arbitrary X)
      simp at this
    obtain ⟨L, hL, -⟩ := exists_dominatesLP_eq_of_ne hP (const X (1 : ℝ)) hone
    exact ⟨L, hL, by simp [hP.zero_eq]⟩
  · exact exists_dominatesLP_eq_of_ne hP g₀ hg₀

end HahnBanach

/-! ## The countably additive credal set -/

section CredalSet

variable [MeasurableSpace X]

/-- The countably additive credal set of a lower prevision: the Borel
probability measures whose expectations dominate it on every bounded
continuous gamble. -/
def caCredal (P : (X →ᵇ ℝ) → ℝ) : Set (ProbabilityMeasure X) :=
  {μ | ∀ g : X →ᵇ ℝ, P g ≤ ∫ x, g x ∂(μ : Measure X)}

theorem mem_caCredal_iff {P : (X →ᵇ ℝ) → ℝ} {μ : ProbabilityMeasure X} :
    μ ∈ caCredal P ↔ ∀ g : X →ᵇ ℝ, P g ≤ ∫ x, g x ∂(μ : Measure X) :=
  Iff.rfl

end CredalSet

/-! ## Compact carriers: σ-smoothness is free (Dini) -/

section Compact

variable [CompactSpace X] [Nonempty X] {P : (X →ᵇ ℝ) → ℝ}

/-- At compact carriers every coherent lower prevision is σ-smooth:
antitone pointwise-null sequences of continuous gambles converge
uniformly (Dini), and the conjugate is trapped in the norm ball. -/
theorem IsCoherentLP.sigmaSmoothAtZero_conjUpper_of_compact
    (hP : IsCoherentLP P) : SigmaSmoothAtZero (conjUpper P) := by
  intro h hanti hto
  -- Dini: uniform convergence of the coercions to the zero function
  have hu : TendstoUniformly (fun n => ⇑(h n)) (0 : X → ℝ) atTop :=
    Antitone.tendstoUniformly_of_forall_tendsto
      (fun n => (h n).continuous)
      (antitone_nat_of_succ_le fun n => Pi.le_def.mpr (hanti n))
      continuous_zero
      (by simpa using hto)
  -- hence norm convergence in the bounded-continuous space
  have hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 0) := by
    have hb : Tendsto h atTop (𝓝 (0 : X →ᵇ ℝ)) := by
      rw [tendsto_iff_tendstoUniformly]
      simpa using hu
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hb)
  exact squeeze_zero_norm (fun n => hP.abs_conjUpper_le (h n)) hnorm

end Compact

end SuFunctor.Universe.General
