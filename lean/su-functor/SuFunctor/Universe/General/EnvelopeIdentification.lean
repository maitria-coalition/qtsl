import SuFunctor.Universe.General.EnvelopeCoherent
import SuFunctor.Universe.General.SmoothRepresentation

/-! # The countably additive envelope theorem

The identification of the two presentations of a coherent lower
prevision — the axiomatic one (Walley's (W1)–(W3)) and the countably
additive envelope (pointwise infimum of expectations over a credal set
of Borel probability measures) — is a theorem under σ-smoothness, on
any metric Borel carrier.  No separability, completeness, or local
compactness is consumed; in particular every Polish record space
qualifies, and no finite-state hypothesis appears anywhere.

* `DominatesLP.exists_probabilityMeasure`: under σ-smoothness **every**
  dominating linear functional is integration against a member of the
  countably additive credal set — the classical (finitely additive)
  dominating set and the countably additive credal set are literally
  the same set, which is the strongest form of the identification.
* `IsCoherentLP.caCredal_nonempty` and
  `IsCoherentLP.exists_mem_caCredal_integral_eq`: the credal set is
  nonempty and touches the prevision at every prescribed gamble
  (Hahn–Banach attainment composed with the representation).
* `IsCoherentLP.isLeast_caCredal_image`: the envelope display — the
  lower prevision of a gamble is the **minimum** of its expectations
  over the credal set, attained, gamble by gamble.
* `IsCoherentLP.isLeast_caCredal_image_of_compactSpace`: at compact
  carriers the hypothesis is discharged by Dini's theorem, so the
  identification is unconditional; finite record spaces are its
  dimension-zero instances.
* `isCoherentLP_lowerEnv` and
  `sigmaSmoothAtZero_conjUpper_lowerEnv_of_tight`: closure the other
  way — the lower envelope of any nonempty family of probability
  measures is coherent, and if the family is uniformly tight the
  envelope is σ-smooth.  σ-smoothness is thus the functional face of
  the standing narrow-regularity discipline on credal sets, not an
  imported hypothesis.

The witnesses that σ-smoothness cannot be dropped — a coherent lower
prevision with empty countably additive credal set, and a represented
one whose envelope is not attained — live in `EnvelopeWitness`.
-/

namespace SuFunctor.Universe.General

open BoundedContinuousFunction Filter Topology MeasureTheory
open scoped ENNReal NNReal Pointwise

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {P : (X →ᵇ ℝ) → ℝ}

/-! ## The identification -/

/-- **Dominating functionals are countably additive** under σ-smoothness:
every dominating linear functional of a σ-smooth coherent lower
prevision is integration against a member of the countably additive
credal set.  The finitely additive and countably additive dominating
sets coincide. -/
theorem DominatesLP.exists_probabilityMeasure (hP : IsCoherentLP P)
    (hs : SigmaSmoothAtZero (conjUpper P)) {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}
    (hL : DominatesLP L P) :
    ∃ μ : ProbabilityMeasure X, μ ∈ caCredal P ∧
      ∀ g : X →ᵇ ℝ, L g = ∫ x, g x ∂(μ : Measure X) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_sigmaSmooth L
    (fun g hg => hL.nonneg hP hg) (hL.one_eq hP)
    (fun h hanti hto => hL.sigmaSmoothAtZero hP hs h hanti hto)
  refine ⟨μ, fun g => ?_, hμ⟩
  rw [← hμ g]
  exact hL g

/-- The countably additive credal set of a σ-smooth coherent lower
prevision is nonempty. -/
theorem IsCoherentLP.caCredal_nonempty (hP : IsCoherentLP P)
    (hs : SigmaSmoothAtZero (conjUpper P)) : (caCredal P).Nonempty := by
  obtain ⟨L, hL, -⟩ := hP.exists_dominatesLP_eq 0
  obtain ⟨μ, hmem, -⟩ := hL.exists_probabilityMeasure hP hs
  exact ⟨μ, hmem⟩

/-- **Attainment**: at every gamble, some member of the countably
additive credal set achieves the lower prevision. -/
theorem IsCoherentLP.exists_mem_caCredal_integral_eq (hP : IsCoherentLP P)
    (hs : SigmaSmoothAtZero (conjUpper P)) (g₀ : X →ᵇ ℝ) :
    ∃ μ ∈ caCredal P, ∫ x, g₀ x ∂(μ : Measure X) = P g₀ := by
  obtain ⟨L, hL, hLg⟩ := hP.exists_dominatesLP_eq g₀
  obtain ⟨μ, hmem, hrep⟩ := hL.exists_probabilityMeasure hP hs
  exact ⟨μ, hmem, by rw [← hrep g₀, hLg]⟩

/-- **The countably additive envelope theorem**: a σ-smooth coherent
lower prevision on the bounded continuous gambles of a metric Borel
carrier is the pointwise **minimum** of expectation over its countably
additive credal set. -/
theorem IsCoherentLP.isLeast_caCredal_image (hP : IsCoherentLP P)
    (hs : SigmaSmoothAtZero (conjUpper P)) (g₀ : X →ᵇ ℝ) :
    IsLeast ((fun μ : ProbabilityMeasure X =>
      ∫ x, g₀ x ∂(μ : Measure X)) '' caCredal P) (P g₀) := by
  constructor
  · obtain ⟨μ, hmem, hint⟩ := hP.exists_mem_caCredal_integral_eq hs g₀
    exact ⟨μ, hmem, hint⟩
  · rintro y ⟨μ, hmem, rfl⟩
    exact hmem g₀

/-- At compact carriers the identification is **unconditional**:
σ-smoothness is free by Dini's theorem.  Finite record spaces are the
dimension-zero instances. -/
theorem IsCoherentLP.isLeast_caCredal_image_of_compactSpace
    [CompactSpace X] (hP : IsCoherentLP P) (g₀ : X →ᵇ ℝ) :
    IsLeast ((fun μ : ProbabilityMeasure X =>
      ∫ x, g₀ x ∂(μ : Measure X)) '' caCredal P) (P g₀) :=
  hP.isLeast_caCredal_image hP.sigmaSmoothAtZero_conjUpper_of_compact g₀

/-! ## Closure the other way: envelopes of regular credal sets -/

/-- The lower envelope of a set of probability measures, read on
bounded continuous gambles.  (Sibling faces: the finite rational stack
and the measurable-gamble general carrier develop their own envelopes;
this one exists for the closure statements below.) -/
noncomputable def lowerEnv (M : Set (ProbabilityMeasure X)) :
    (X →ᵇ ℝ) → ℝ :=
  fun g => sInf ((fun μ : ProbabilityMeasure X =>
    ∫ x, g x ∂(μ : Measure X)) '' M)

omit [Nonempty X] in
theorem bddBelow_integral_image (M : Set (ProbabilityMeasure X))
    (g : X →ᵇ ℝ) :
    BddBelow ((fun μ : ProbabilityMeasure X =>
      ∫ x, g x ∂(μ : Measure X)) '' M) := by
  refine ⟨-‖g‖, ?_⟩
  rintro y ⟨μ, -, rfl⟩
  have hlow : ∫ x, (-‖g‖ : ℝ) ∂(μ : Measure X) ≤ ∫ x, g x ∂(μ : Measure X) :=
    integral_mono (integrable_const _) (g.integrable _)
      (fun x => bcf_neg_norm_le g x)
  simpa [measure_univ] using hlow

/-- Envelopes of nonempty families of countably additive probabilities
are coherent — direction (1) of the classical envelope theorem, at an
arbitrary carrier. -/
theorem isCoherentLP_lowerEnv {M : Set (ProbabilityMeasure X)}
    (hM : M.Nonempty) : IsCoherentLP (lowerEnv M) where
  inf_le g := by
    refine le_csInf (hM.image _) ?_
    rintro y ⟨μ, -, rfl⟩
    have hconst : ∫ x, (⨅ j, g j) ∂(μ : Measure X) = ⨅ j, g j := by
      simp
    calc (⨅ j, g j) = ∫ x, (⨅ j, g j) ∂(μ : Measure X) := hconst.symm
      _ ≤ ∫ x, g x ∂(μ : Measure X) :=
          integral_mono (integrable_const _) (g.integrable _)
            (fun x => ciInf_le (bddBelow_range_bcf g) x)
  homog c hc g := by
    simp only [lowerEnv]
    have himg : (fun μ : ProbabilityMeasure X =>
        ∫ x, (c • g) x ∂(μ : Measure X)) '' M
        = c • ((fun μ : ProbabilityMeasure X =>
            ∫ x, g x ∂(μ : Measure X)) '' M) := by
      rw [← Set.image_smul, Set.image_image]
      refine Set.image_congr fun μ _ => ?_
      have : ∀ x, (c • g) x = c * g x := fun x => by simp
      simp only [this, smul_eq_mul]
      exact integral_const_mul c _
    rw [himg, Real.sInf_smul_of_nonneg hc, smul_eq_mul]
  superadd f g := by
    simp only [lowerEnv]
    refine le_csInf (hM.image _) ?_
    rintro y ⟨μ, hμ, rfl⟩
    dsimp only
    have hsplit : ∫ x, (f + g) x ∂(μ : Measure X)
        = ∫ x, f x ∂(μ : Measure X) + ∫ x, g x ∂(μ : Measure X) := by
      have : ∀ x, (f + g) x = f x + g x := fun x => by simp
      simp only [this]
      exact integral_add (f.integrable _) (g.integrable _)
    rw [hsplit]
    exact add_le_add
      (csInf_le (bddBelow_integral_image M f) ⟨μ, hμ, rfl⟩)
      (csInf_le (bddBelow_integral_image M g) ⟨μ, hμ, rfl⟩)

/-- **Uniformly tight envelopes are σ-smooth**: the lower envelope of a
nonempty uniformly tight family of probability measures satisfies the
σ-smoothness hypothesis of the envelope theorem.  Together with
`isCoherentLP_lowerEnv` this closes the loop: σ-smoothness is exactly
the functional trace of the standing tightness/narrow-regularity
discipline on credal sets.  (At compact carriers every family is
trivially uniformly tight, matching the Dini discharge.) -/
theorem sigmaSmoothAtZero_conjUpper_lowerEnv_of_tight
    {M : Set (ProbabilityMeasure X)} (hM : M.Nonempty)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧
      ∀ μ ∈ M, (μ : Measure X) Kᶜ ≤ ENNReal.ofReal ε) :
    SigmaSmoothAtZero (conjUpper (lowerEnv M)) := by
  intro h hanti hto
  have hnn : ∀ n x, 0 ≤ h n x := antitone_null_nonneg hanti hto
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the compact from tightness, at scale ε/(2‖h 0‖ + 2)
  set δ : ℝ := ε / (2 * ‖h 0‖ + 2) with hδ_def
  have hδpos : 0 < δ := by
    have : (0 : ℝ) < 2 * ‖h 0‖ + 2 := by positivity
    exact div_pos hε this
  obtain ⟨K, hK, hKmass⟩ := htight δ hδpos
  -- Dini on the compact: uniformly small eventually
  have hdini : TendstoUniformlyOn (fun n => ⇑(h n)) (fun _ => (0 : ℝ))
      atTop K :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto hK
      (fun n => (h n).continuous.continuousOn)
      (fun x _ => antitone_nat_of_succ_le fun m => hanti m x)
      continuousOn_const (fun x _ => hto x)
  rw [Metric.tendstoUniformlyOn_iff] at hdini
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdini (ε / 2) hhalf)
  refine ⟨N, fun n hn => ?_⟩
  have hnK := hN n hn
  -- the per-measure bound
  have hbound : ∀ μ ∈ M, ∫ x, h n x ∂(μ : Measure X) ≤ ε / 2 + ‖h 0‖ * δ := by
    intro μ hμ
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    have hint : Integrable (fun x => h n x) (μ : Measure X) :=
      (h n).integrable _
    have hsplit := integral_add_compl hKmeas hint
    -- on K: below ε/2
    have hOnK : ∫ x in K, h n x ∂(μ : Measure X)
        ≤ (ε / 2) * (μ : Measure X).real K := by
      have hmono' : ∫ x in K, h n x ∂(μ : Measure X)
          ≤ ∫ _ in K, (ε / 2 : ℝ) ∂(μ : Measure X) :=
        setIntegral_mono_on hint.integrableOn
          (integrableOn_const (measure_ne_top _ _)) hKmeas
          (fun x hx => le_of_lt (lt_of_abs_lt (by
            simpa [Real.dist_eq, abs_sub_comm] using hnK x hx)))
      have hconstK : ∫ _ in K, (ε / 2 : ℝ) ∂(μ : Measure X)
          = (ε / 2) * (μ : Measure X).real K := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      exact hmono'.trans hconstK.le
    have hKle : (ε / 2) * (μ : Measure X).real K ≤ ε / 2 := by
      have h1 : (μ : Measure X).real K ≤ 1 := by
        have hmono := measure_mono (μ := (μ : Measure X)) (Set.subset_univ K)
        have h2 : ((μ : Measure X) K).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (by simp) (by simpa [measure_univ] using hmono)
        simp at h2
        exact h2
      nlinarith [le_of_lt hhalf]
    -- off K: below ‖h 0‖ · δ
    have hOffK : ∫ x in Kᶜ, h n x ∂(μ : Measure X) ≤ ‖h 0‖ * δ := by
      have hle : ∀ x, h n x ≤ ‖h 0‖ := by
        intro x
        have hmono : h n x ≤ h 0 x := by
          have ha : Antitone fun m => h m x :=
            antitone_nat_of_succ_le fun m => hanti m x
          exact ha (Nat.zero_le n)
        exact hmono.trans (bcf_le_norm (h 0) x)
      have hup : ∫ x in Kᶜ, h n x ∂(μ : Measure X)
          ≤ ∫ _ in Kᶜ, ‖h 0‖ ∂(μ : Measure X) := by
        exact setIntegral_mono_on hint.integrableOn
          (integrableOn_const (measure_ne_top _ _))
          hKmeas.compl (fun x _ => hle x)
      have hmass : (μ : Measure X).real Kᶜ ≤ δ := by
        have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKmass μ hμ)
        rw [ENNReal.toReal_ofReal (le_of_lt hδpos)] at h1
        exact h1
      calc ∫ x in Kᶜ, h n x ∂(μ : Measure X)
          ≤ ∫ _ in Kᶜ, ‖h 0‖ ∂(μ : Measure X) := hup
        _ = (μ : Measure X).real Kᶜ * ‖h 0‖ := by simp [Measure.real]
        _ ≤ δ * ‖h 0‖ :=
            mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
        _ = ‖h 0‖ * δ := mul_comm _ _
    calc ∫ x, h n x ∂(μ : Measure X)
        = ∫ x in K, h n x ∂(μ : Measure X)
          + ∫ x in Kᶜ, h n x ∂(μ : Measure X) := hsplit.symm
      _ ≤ (ε / 2) * (μ : Measure X).real K + ‖h 0‖ * δ :=
          add_le_add hOnK hOffK
      _ ≤ ε / 2 + ‖h 0‖ * δ := by linarith [hKle]
  -- assemble: the conjugate of the envelope obeys the same bound
  have htotal : ‖h 0‖ * δ < ε / 2 := by
    have hlt : 2 * ‖h 0‖ * δ < (2 * ‖h 0‖ + 2) * δ := by nlinarith
    have hδval : (2 * ‖h 0‖ + 2) * δ = ε := by
      rw [hδ_def]
      field_simp
    nlinarith
  have hconj_le : conjUpper (lowerEnv M) (h n) ≤ ε / 2 + ‖h 0‖ * δ := by
    simp only [conjUpper, lowerEnv, neg_le]
    refine le_csInf (hM.image _) ?_
    rintro y ⟨μ, hμ, rfl⟩
    dsimp only
    have hneg : ∫ x, (-(h n)) x ∂(μ : Measure X)
        = -(∫ x, h n x ∂(μ : Measure X)) := by
      have hx : ∀ x, (-(h n)) x = -(h n x) := fun x => by simp
      simp only [hx]
      exact integral_neg _
    rw [hneg, neg_le_neg_iff]
    exact hbound μ hμ
  have hconj_nonneg : 0 ≤ conjUpper (lowerEnv M) (h n) := by
    simp only [conjUpper, lowerEnv, le_neg]
    obtain ⟨μ₀, hμ₀⟩ := hM
    refine csInf_le_of_le (bddBelow_integral_image M (-(h n)))
      ⟨μ₀, hμ₀, rfl⟩ ?_
    have hneg : ∫ x, (-(h n)) x ∂(μ₀ : Measure X)
        = -(∫ x, h n x ∂(μ₀ : Measure X)) := by
      have hx : ∀ x, (-(h n)) x = -(h n x) := fun x => by simp
      simp only [hx]
      exact integral_neg _
    dsimp only
    rw [hneg]
    have h0 : (0 : ℝ) ≤ ∫ x, h n x ∂(μ₀ : Measure X) := by
      refine integral_nonneg ?_
      intro x
      exact hnn n x
    linarith
  rw [Real.dist_eq]
  have : |conjUpper (lowerEnv M) (h n)| = conjUpper (lowerEnv M) (h n) :=
    abs_of_nonneg hconj_nonneg
  simp only [sub_zero, this]
  linarith

end SuFunctor.Universe.General
