import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Pointwise

/-! # Envelope coherence and the natural extension over general state spaces

The general-carrier face of `QtslAux.Imprecise.NaturalExtension` (which is
`[Fintype X]`): an arbitrary measurable state space `X`, models the countably
additive probability measures `MeasureTheory.ProbabilityMeasure X`, gambles the
bounded measurable real-valued functions (`BddGamble`), expectation the Bochner
integral (`pmExp`).  This is exactly the scope the book's definition of the
natural extension states for itself: countably additive envelope, envelope-side
universal property.

* *Envelopes are coherent*, general carrier (`envelopeG_coherent`): the lower
  envelope `lowerEnvG M` of an arbitrary nonempty family
  `M : Set (ProbabilityMeasure X)` satisfies (W1) inf-domination, (W2) positive
  homogeneity, (W3) superadditivity (`IsCoherentG`) — no convexity or closure
  of the family consumed, no hypotheses on `X` beyond `[MeasurableSpace X]`
  `[Nonempty X]`.
* The natural-extension package at the stated general scope: assessments as
  arbitrarily indexed families `h : ι → BddGamble X`, `c : ι → ℝ` (subsuming
  set-presented `K` via the inclusion index); `CompatibleG`/`compatibleSetG`
  (= `M(K,c)`), `AvoidsSureLossG` (= `M(K,c) ≠ ∅`), `natExtG` (the envelope
  over the compatible set), and
  - NE1 `natExtG_coherent`,
  - NE2 `assessment_le_natExtG` (definitional),
  - NE3-general `natExtG_le_lowerEnvG`: for **any** nonempty family `M'` of
    countably additive models whose envelope dominates the assessment,
    `natExtG ≤ lowerEnvG M'` pointwise — the membership-forcing two-liner
    (`subset_compatibleSetG_of_dominating`: an infimum over `M'` dominating
    `c i` bounds every member of `M'` below by it) plus envelope antitonicity.
    This **is** the universal property at the definition's stated general
    scope: least among the countably-additive-envelope lower previsions
    dominating the assessment.  The classical unrestricted minimum — least
    among *all* coherent lower previsions, represented by *finitely additive*
    probabilities (Walley, *Statistical Reasoning with Imprecise
    Probabilities*, 1991, §3.3–3.4, via Hahn–Banach) — is a deliberate
    non-target here: different mathematics, named debt at the book's remark.
  - the self-certification corollary `avoidsSureLossG_of_dominating` (a
    dominating nonempty family witnesses avoidance of sure loss), and
  - the largest-credal-set dual `dominates_natExtG_iff` /
    `setOf_dominatesG_natExtG_eq` (`M(E_{K,c}) = M(K,c)`).
* The largest-compatible-set structure: `compatibleSetG` is convex — in
  mixture form `pmMix`/`pmMix_mem_compatibleSetG`, carrier-free — and, when
  the assessment's gambles are (bounded) continuous over a topological `X`
  with `[OpensMeasurableSpace X]`, closed in the topology of weak convergence
  (`isClosed_compatibleSetG`); the Portmanteau-flavored engine is
  `ProbabilityMeasure.continuous_integral_boundedContinuousFunction`, i.e.
  narrow continuity of expectation against a fixed bounded *continuous*
  gamble (`continuous_pmExp_of_continuous`).  Expectation against a merely
  measurable gamble is not narrowly continuous, so continuity is a genuine
  hypothesis here, exactly as the book's definition remarks.

## Scalar and integrability design

Gambles are plain `ℝ`-valued with the Bochner integral: the book's gamble
space is a real linear space, and bounded measurable functions are integrable
against every probability measure by one lemma (`BddGamble.integrable`), paid
once at the structure.  The one-sided `ℝ≥0∞` presentation of gambles (lower
semicontinuous, sublevel-presented) with the Choquet pairing is the *pointfree*
prevision layer's design — `Pointfree.Prevision` in `lean/pointfree`, whose
`iInfEnvelope_isSuperadditive` is the pointfree face of the same
envelopes-are-coherent fact (superlinear class closed under lower envelopes).
The two modules are sibling faces of the envelope story, cited together at the
book's mechanization remark; neither consumes the other.

## What stays finite (honest scope)

The LP-duality deficit display (`natExt_eq_dualVal`), the sure-loss
alternative (`avoidsSureLoss_iff_noSureLoss`), and the envelope-theorem
converse (`IsCoherent.exists_dominating_exp_eq`: every coherent lower
prevision *is* an envelope, via sublinear Hahn–Banach) live in
`QtslAux.Imprecise.NaturalExtension` at `[Fintype X]` and are genuinely
finite-dimensional as proven; their infinite-state analogues land in
finitely additive territory and are not attempted here.
-/

namespace Qtsl.Imprecise

open MeasureTheory Pointwise
open scoped ENNReal

/-! ## Bounded measurable gambles -/

/-- A bounded measurable real-valued gamble on a measurable state space —
the book's "bounded Borel gamble" at the honest general carrier (the ambient
σ-algebra; the Borel σ-algebra when `X` is topological). -/
structure BddGamble (X : Type*) [MeasurableSpace X] where
  /-- The underlying function. -/
  toFun : X → ℝ
  /-- Gambles are measurable. -/
  measurable' : Measurable toFun
  /-- Gambles are bounded (uniformly, by some constant). -/
  bounded' : ∃ C, ∀ x, |toFun x| ≤ C

namespace BddGamble

variable {X : Type*} [MeasurableSpace X]

instance : FunLike (BddGamble X) X ℝ where
  coe := BddGamble.toFun
  coe_injective := by
    rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
    simpa using h

@[ext] theorem ext {f g : BddGamble X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem measurable (g : BddGamble X) : Measurable g := g.measurable'

theorem bounded (g : BddGamble X) : ∃ C, ∀ x, |g x| ≤ C := g.bounded'

instance : Add (BddGamble X) :=
  ⟨fun f g =>
    ⟨fun x => f x + g x, f.measurable.add g.measurable, by
      obtain ⟨C, hC⟩ := f.bounded
      obtain ⟨D, hD⟩ := g.bounded
      exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩⟩

@[simp] theorem add_apply (f g : BddGamble X) (x : X) : (f + g) x = f x + g x :=
  rfl

instance : Neg (BddGamble X) :=
  ⟨fun f =>
    ⟨fun x => -f x, f.measurable.neg, by
      obtain ⟨C, hC⟩ := f.bounded
      exact ⟨C, fun x => by rw [abs_neg]; exact hC x⟩⟩⟩

@[simp] theorem neg_apply (f : BddGamble X) (x : X) : (-f) x = -f x := rfl

instance : SMul ℝ (BddGamble X) :=
  ⟨fun c f =>
    ⟨fun x => c * f x, f.measurable.const_mul c, by
      obtain ⟨C, hC⟩ := f.bounded
      exact ⟨|c| * C, fun x => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩⟩⟩

@[simp] theorem smul_apply (c : ℝ) (f : BddGamble X) (x : X) :
    (c • f) x = c * f x := rfl

/-- The constant gamble. -/
def const (X : Type*) [MeasurableSpace X] (c : ℝ) : BddGamble X :=
  ⟨fun _ => c, measurable_const, ⟨|c|, fun _ => le_rfl⟩⟩

@[simp] theorem const_apply (c : ℝ) (x : X) : const X c x = c := rfl

theorem bddBelow_range (g : BddGamble X) : BddBelow (Set.range g) := by
  obtain ⟨C, hC⟩ := g.bounded
  exact ⟨-C, by rintro y ⟨x, rfl⟩; exact neg_le_of_abs_le (hC x)⟩

theorem bddAbove_range (g : BddGamble X) : BddAbove (Set.range g) := by
  obtain ⟨C, hC⟩ := g.bounded
  exact ⟨C, by rintro y ⟨x, rfl⟩; exact le_of_abs_le (hC x)⟩

theorem ciInf_le_apply [Nonempty X] (g : BddGamble X) (x : X) :
    (⨅ y, g y) ≤ g x :=
  ciInf_le g.bddBelow_range x

/-- Bounded measurable gambles are integrable against every countably
additive probability measure — the whole integrability bookkeeping, paid
once. -/
theorem integrable (g : BddGamble X) (P : ProbabilityMeasure X) :
    Integrable g (P : Measure X) := by
  obtain ⟨C, hC⟩ := g.bounded
  exact (integrable_const C).mono' g.measurable.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact hC x)

end BddGamble

/-! ## Expectation under a countably additive model -/

section Expectation

variable {X : Type*} [MeasurableSpace X]

/-- Expectation (precise prevision) of a bounded measurable gamble under a
countably additive probability measure: the Bochner integral. -/
noncomputable def pmExp (P : ProbabilityMeasure X) (g : BddGamble X) : ℝ :=
  ∫ x, g x ∂(P : Measure X)

theorem pmExp_add (P : ProbabilityMeasure X) (f g : BddGamble X) :
    pmExp P (f + g) = pmExp P f + pmExp P g := by
  simp only [pmExp, BddGamble.add_apply]
  exact integral_add (f.integrable P) (g.integrable P)

theorem pmExp_smul (P : ProbabilityMeasure X) (c : ℝ) (g : BddGamble X) :
    pmExp P (c • g) = c * pmExp P g := by
  simp only [pmExp, BddGamble.smul_apply, ← smul_eq_mul]
  exact integral_smul c _

theorem pmExp_neg (P : ProbabilityMeasure X) (g : BddGamble X) :
    pmExp P (-g) = -pmExp P g := by
  simp only [pmExp, BddGamble.neg_apply]
  exact integral_neg _

theorem pmExp_const (P : ProbabilityMeasure X) (c : ℝ) :
    pmExp P (BddGamble.const X c) = c := by
  show (∫ _, c ∂(P : Measure X)) = c
  simp [integral_const]

theorem pmExp_mono (P : ProbabilityMeasure X) {f g : BddGamble X}
    (h : ∀ x, f x ≤ g x) : pmExp P f ≤ pmExp P g :=
  integral_mono (f.integrable P) (g.integrable P) h

theorem ciInf_le_pmExp [Nonempty X] (P : ProbabilityMeasure X)
    (g : BddGamble X) : (⨅ x, g x) ≤ pmExp P g :=
  calc (⨅ x, g x) = pmExp P (BddGamble.const X (⨅ x, g x)) :=
        (pmExp_const P _).symm
    _ ≤ pmExp P g := pmExp_mono P fun x => g.ciInf_le_apply x

end Expectation

/-! ## Lower envelopes are coherent — general carrier -/

section Envelope

variable {X : Type*} [MeasurableSpace X]

/-- `P` lies in the credal set of the functional `F`: its expectation
dominates `F` on every gamble.  General-carrier face of `Dominates`. -/
def DominatesG (F : BddGamble X → ℝ) (P : ProbabilityMeasure X) : Prop :=
  ∀ g, F g ≤ pmExp P g

/-- The lower envelope of a family of countably additive models. -/
noncomputable def lowerEnvG (M : Set (ProbabilityMeasure X))
    (g : BddGamble X) : ℝ :=
  sInf ((fun P => pmExp P g) '' M)

/-- A coherent lower prevision on the bounded measurable gambles over a
general measurable state space — (W1) dominating the infimum, (W2) positive
homogeneity, (W3) superadditivity.  Stated on the full-mass stratum, matching
the book's definition verbatim (the infimum in (W1) is the true pointwise
infimum, legitimate because gambles are bounded and `X` nonempty). -/
structure IsCoherentG [Nonempty X] (F : BddGamble X → ℝ) : Prop where
  /-- (W1) dominating the infimum. -/
  inf_le : ∀ g, (⨅ x, g x) ≤ F g
  /-- (W2) positive homogeneity. -/
  homog : ∀ c : ℝ, 0 ≤ c → ∀ g, F (c • g) = c * F g
  /-- (W3) superadditivity. -/
  superadd : ∀ f g, F f + F g ≤ F (f + g)

variable [Nonempty X]

theorem bddBelow_pmExp_image (M : Set (ProbabilityMeasure X))
    (g : BddGamble X) : BddBelow ((fun P => pmExp P g) '' M) :=
  ⟨⨅ x, g x, by rintro r ⟨P, -, rfl⟩; exact ciInf_le_pmExp P g⟩

theorem lowerEnvG_le_pmExp {M : Set (ProbabilityMeasure X)}
    {P : ProbabilityMeasure X} (hP : P ∈ M) (g : BddGamble X) :
    lowerEnvG M g ≤ pmExp P g :=
  csInf_le (bddBelow_pmExp_image M g) ⟨P, hP, rfl⟩

omit [Nonempty X] in
theorem le_lowerEnvG {M : Set (ProbabilityMeasure X)} (hM : M.Nonempty)
    {g : BddGamble X} {a : ℝ} (h : ∀ P ∈ M, a ≤ pmExp P g) :
    a ≤ lowerEnvG M g :=
  le_csInf (hM.image _) (by rintro r ⟨P, hP, rfl⟩; exact h P hP)

/-- *Envelopes are coherent*, general carrier: the lower envelope of an
arbitrary nonempty family of countably additive probability measures on an
arbitrary measurable space satisfies (W1)–(W3).  No convexity or closure of
the family is consumed; one-line-per-axiom shape, as at the finite stratum. -/
theorem envelopeG_coherent (M : Set (ProbabilityMeasure X))
    (hM : M.Nonempty) : IsCoherentG (lowerEnvG M) where
  inf_le g := le_lowerEnvG hM fun P _ => ciInf_le_pmExp P g
  homog c hc g := by
    have key : (fun P => pmExp P (c • g)) '' M
        = c • ((fun P => pmExp P g) '' M) := by
      ext r
      simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨pmExp P g, ⟨P, hP, rfl⟩, (pmExp_smul P c g).symm⟩
      · rintro ⟨r', ⟨P, hP, rfl⟩, rfl⟩
        exact ⟨P, hP, pmExp_smul P c g⟩
    show sInf ((fun P => pmExp P (c • g)) '' M)
        = c * sInf ((fun P => pmExp P g) '' M)
    rw [key, Real.sInf_smul_of_nonneg hc, smul_eq_mul]
  superadd f g := by
    refine le_lowerEnvG hM fun P hP => ?_
    rw [pmExp_add]
    exact add_le_add (lowerEnvG_le_pmExp hP f) (lowerEnvG_le_pmExp hP g)

/-- Envelope monotonicity in the gamble (a standard consequence, here direct
from the model side). -/
theorem lowerEnvG_mono {M : Set (ProbabilityMeasure X)} (hM : M.Nonempty)
    {f g : BddGamble X} (h : ∀ x, f x ≤ g x) :
    lowerEnvG M f ≤ lowerEnvG M g :=
  le_csInf (hM.image _) (by
    rintro r ⟨P, hP, rfl⟩
    exact (lowerEnvG_le_pmExp hP f).trans (pmExp_mono P h))

theorem lowerEnvG_const {M : Set (ProbabilityMeasure X)} (hM : M.Nonempty)
    (c : ℝ) : lowerEnvG M (BddGamble.const X c) = c := by
  apply le_antisymm
  · obtain ⟨P, hP⟩ := hM
    exact (lowerEnvG_le_pmExp hP _).trans_eq (pmExp_const P c)
  · exact le_lowerEnvG hM fun P _ => (pmExp_const P c).ge

end Envelope

/-! ## The natural extension at the stated general scope -/

section NaturalExtension

variable {X : Type*} [MeasurableSpace X] {ι : Type*}
variable (h : ι → BddGamble X) (c : ι → ℝ)

/-- `P` is compatible with the assessment `(h, c)`: every claimed lower bound
holds under `P`'s expectation.  The assessment is an arbitrarily indexed
family of gambles with claimed bounds — a set-presented assessment
`K ⊆ L`, `c : K → ℝ` is the instance `ι := K` with the inclusion index. -/
def CompatibleG (P : ProbabilityMeasure X) : Prop := ∀ i, c i ≤ pmExp P (h i)

/-- The compatible set `M(K, c)`, at the general carrier. -/
def compatibleSetG : Set (ProbabilityMeasure X) := {P | CompatibleG h c P}

theorem mem_compatibleSetG_iff {P : ProbabilityMeasure X} :
    P ∈ compatibleSetG h c ↔ ∀ i, c i ≤ pmExp P (h i) :=
  Iff.rfl

/-- `(K, c)` avoids sure loss when `M(K, c) ≠ ∅`.  (The betting/Farkas
*alternative* characterization is the finite-stratum theorem
`avoidsSureLoss_iff_noSureLoss`; at infinite state it is different
mathematics and not claimed here.) -/
def AvoidsSureLossG : Prop := (compatibleSetG h c).Nonempty

/-- The natural extension of the assessment `(h, c)`: the lower envelope of
its compatible set — the book's displayed definition, verbatim, at the
general carrier. -/
noncomputable def natExtG (g : BddGamble X) : ℝ :=
  lowerEnvG (compatibleSetG h c) g

variable [Nonempty X]

/-- NE1: the natural extension of an assessment avoiding sure loss is a
coherent lower prevision (general carrier). -/
theorem natExtG_coherent (hASL : AvoidsSureLossG h c) :
    IsCoherentG (natExtG h c) :=
  envelopeG_coherent (compatibleSetG h c) hASL

omit [Nonempty X] in
/-- NE2: the natural extension dominates the assessment — definitional. -/
theorem assessment_le_natExtG (hASL : AvoidsSureLossG h c) (i : ι) :
    c i ≤ natExtG h c (h i) :=
  le_lowerEnvG hASL fun _ hP => hP i

/-- The membership-forcing step of NE3: an envelope over `M'` dominating the
assessment forces every member of `M'` into the compatible set — an infimum
over `M'` dominating `c i` bounds every member of `M'` below by it. -/
theorem subset_compatibleSetG_of_dominating {M' : Set (ProbabilityMeasure X)}
    (hdom : ∀ i, c i ≤ lowerEnvG M' (h i)) :
    M' ⊆ compatibleSetG h c :=
  fun _ hP i => (hdom i).trans (lowerEnvG_le_pmExp hP (h i))

/-- NE3 at the definition's stated general scope — **the universal property**:
for any nonempty family `M'` of countably additive models whose lower
envelope dominates the assessment, the natural extension is below the
envelope of `M'` pointwise.  I.e. `natExtG` is least among the
countably-additive-envelope lower previsions dominating the assessment.

The classical unrestricted minimum — least among *all* coherent lower
previsions dominating the assessment, whose extreme witnesses are *finitely
additive* probabilities (Walley 1991, §3.3–3.4) — is deliberately not claimed:
at infinite `X` that identification is different mathematics
(Hahn–Banach/weak-* compactness on the ba-dual) and stays named debt at the
book's mechanization remark. -/
theorem natExtG_le_lowerEnvG {M' : Set (ProbabilityMeasure X)}
    (hM' : M'.Nonempty) (hdom : ∀ i, c i ≤ lowerEnvG M' (h i))
    (g : BddGamble X) : natExtG h c g ≤ lowerEnvG M' g :=
  csInf_le_csInf (bddBelow_pmExp_image (compatibleSetG h c) g) (hM'.image _)
    (Set.image_mono (subset_compatibleSetG_of_dominating h c hdom))

/-- Self-certification: NE3's hypothesis set already witnesses avoidance of
sure loss — a nonempty dominating family is itself made of compatible
models. -/
theorem avoidsSureLossG_of_dominating {M' : Set (ProbabilityMeasure X)}
    (hM' : M'.Nonempty) (hdom : ∀ i, c i ≤ lowerEnvG M' (h i)) :
    AvoidsSureLossG h c :=
  hM'.mono (subset_compatibleSetG_of_dominating h c hdom)

/-- The largest-credal-set dual of NE3: a countably additive model's
expectation dominates the natural extension iff the model is compatible with
the assessment — `M(E_{K,c}) = M(K,c)` at the general carrier. -/
theorem dominates_natExtG_iff (hASL : AvoidsSureLossG h c)
    (P : ProbabilityMeasure X) :
    DominatesG (natExtG h c) P ↔ CompatibleG h c P := by
  constructor
  · intro hd i
    exact (assessment_le_natExtG h c hASL i).trans (hd (h i))
  · intro hP g
    exact lowerEnvG_le_pmExp hP g

/-- The credal set of the natural extension *is* the compatible set — the
set-level form of the largest-credal-set dual.  Together with
`pmMix_mem_compatibleSetG` (convexity) and `isClosed_compatibleSetG`
(closedness, under continuity of the assessed gambles), this is the
"largest compatible closed convex set" reading: every family of compatible
models lies in `compatibleSetG` by definition of membership, and
`compatibleSetG` itself has the structure. -/
theorem setOf_dominatesG_natExtG_eq (hASL : AvoidsSureLossG h c) :
    {P | DominatesG (natExtG h c) P} = compatibleSetG h c :=
  Set.ext fun P => dominates_natExtG_iff h c hASL P

end NaturalExtension

/-! ## Convexity of the compatible set (carrier-free) -/

section Mix

variable {X : Type*} [MeasurableSpace X]

/-- The mixture of two countably additive probability measures with
`ℝ≥0∞`-weights summing to one. -/
noncomputable def pmMix (a b : ℝ≥0∞) (hab : a + b = 1)
    (P Q : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨a • (P : Measure X) + b • (Q : Measure X), by
    constructor
    simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ,
      hab]⟩

theorem pmExp_pmMix (a b : ℝ≥0∞) (hab : a + b = 1)
    (P Q : ProbabilityMeasure X) (g : BddGamble X) :
    pmExp (pmMix a b hab P Q) g
      = a.toReal * pmExp P g + b.toReal * pmExp Q g := by
  have ha : a ≠ ∞ := ((le_self_add.trans_eq hab).trans_lt ENNReal.one_lt_top).ne
  have hb : b ≠ ∞ := ((le_add_self.trans_eq hab).trans_lt ENNReal.one_lt_top).ne
  show (∫ x, g x ∂(a • (P : Measure X) + b • (Q : Measure X)))
      = a.toReal * pmExp P g + b.toReal * pmExp Q g
  rw [integral_add_measure ((g.integrable P).smul_measure ha)
      ((g.integrable Q).smul_measure hb),
    integral_smul_measure, integral_smul_measure]
  simp [pmExp, smul_eq_mul]

/-- Convexity of the compatible set, in mixture form — carrier-free: no
topology, no countability, no hypotheses on `X`. -/
theorem pmMix_mem_compatibleSetG {ι : Type*} (h : ι → BddGamble X)
    (c : ι → ℝ) {a b : ℝ≥0∞} (hab : a + b = 1) {P Q : ProbabilityMeasure X}
    (hP : P ∈ compatibleSetG h c) (hQ : Q ∈ compatibleSetG h c) :
    pmMix a b hab P Q ∈ compatibleSetG h c := by
  intro i
  rw [pmExp_pmMix a b hab P Q (h i)]
  have ha : a ≠ ∞ := ((le_self_add.trans_eq hab).trans_lt ENNReal.one_lt_top).ne
  have hb : b ≠ ∞ := ((le_add_self.trans_eq hab).trans_lt ENNReal.one_lt_top).ne
  have hsum : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hab, ENNReal.toReal_one]
  calc c i = a.toReal * c i + b.toReal * c i := by
        rw [← add_mul, hsum, one_mul]
    _ ≤ a.toReal * pmExp P (h i) + b.toReal * pmExp Q (h i) :=
        add_le_add (mul_le_mul_of_nonneg_left (hP i) ENNReal.toReal_nonneg)
          (mul_le_mul_of_nonneg_left (hQ i) ENNReal.toReal_nonneg)

end Mix

/-! ## Closedness of the compatible set under continuous assessments -/

section Closedness

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- Expectation against a fixed bounded *continuous* gamble is continuous in
the model, for the topology of weak convergence on `ProbabilityMeasure X` —
the Portmanteau-flavored engine of the closedness clause.  (For a merely
measurable gamble this fails; continuity of the gamble is a genuine
hypothesis, exactly as the book's definition remarks.) -/
theorem continuous_pmExp_of_continuous (g : BddGamble X)
    (hg : Continuous g) :
    Continuous fun P : ProbabilityMeasure X => pmExp P g := by
  obtain ⟨C, hC⟩ := g.bounded
  have hcont := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (X := X) (BoundedContinuousFunction.ofNormedAddCommGroup g hg C
      (fun x => by rw [Real.norm_eq_abs]; exact hC x))
  simpa [pmExp] using hcont

/-- The compatible set is closed in the topology of weak convergence whenever
the assessment's gambles are (bounded) continuous: it is the intersection of
the preimages of the closed rays `[c i, ∞)` under the narrowly continuous
expectation maps.  Exactly the continuity and boundedness stated are
consumed (boundedness rides inside `BddGamble`). -/
theorem isClosed_compatibleSetG {ι : Type*} (h : ι → BddGamble X)
    (c : ι → ℝ) (hcont : ∀ i, Continuous (h i)) :
    IsClosed (compatibleSetG h c) := by
  have hrep : compatibleSetG h c
      = ⋂ i, (fun P : ProbabilityMeasure X => pmExp P (h i)) ⁻¹'
          Set.Ici (c i) := by
    ext P
    simp [compatibleSetG, CompatibleG, Set.mem_iInter]
  rw [hrep]
  exact isClosed_iInter fun i =>
    isClosed_Ici.preimage (continuous_pmExp_of_continuous (h i) (hcont i))

end Closedness

end Qtsl.Imprecise
