/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: threshold polarity (safety walls, liveness tilts) over
`SubPMF`.  The successor carrier states walls and tilt families over
lower semicontinuous penalty functionals (`SuFunctor.Universe.Closure`,
`SuFunctor.Universe.Judgment`).

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Bridge
import SuFunctorLegacy.Squares

/-! # Threshold polarity: safety walls and liveness tilts

Threshold judgments over subprobability models fork on their
**polarity**.  A *safety-shaped* threshold ("with probability at least
`p`, nothing bad happens") denotes the **violation half-space**: an
upper bound `1 − p` on the mass of the bad event.  Mass loss — a model
that halts or diverges short of a verdict — cannot manufacture a
violation, so the wall is immune to partiality: the zero model and its
submass kin sit behind every safety wall.  A *liveness-shaped*
threshold ("with probability at least `p`, the goal is reached") keeps
the **satisfaction form**: a lower bound on the goal event's mass,
which mass loss honestly fails — that is what a hard liveness
threshold means.  Between the hard wall and no requirement at all sits
the **tilt family**: for `λ ∈ (0, ∞]` the penalty `λ · (p ∸ μ(goal))`
charges the shortfall linearly, and the `λ = ∞` member is the wall
itself (`livenessTilt_top`).

Choosing denotations by polarity is forced, not stylistic: over
subprobability mass the two forms of a threshold conclusion come apart
(they agree exactly on the full-mass models — `wall_polarity_slice`),
the satisfaction-form reading of a safety conclusion is refuted by a
half-mass countermodel whose certificate is impeccable (the pins in
`SuFunctorLegacy.ThresholdRefute`), and the complement conversion that would
identify the two forms is exactly the move the judgment layer has no
constructor for.

Contents:

* the two wall denotations (`safetyWall`, `livenessWall`) and their
  identification with the spec penalties of the threshold judgments
  (`safetyWall_eq_specPenalty`, `livenessWall_eq_specPenalty`) — the
  polarity table as equations into the graded layer;
* the shortfall hinge (`shortfall`; `shortfall_coe` is the
  max-of-affines identity) and the tilt family (`livenessTilt`),
  monotone in `λ` (`livenessTilt_mono_lam`), finite at every finite
  `λ` (`livenessTilt_coe_lt_top`), with the wall as its `λ = ∞` value
  (`livenessTilt_top`) and as its least upper bound over the finite
  members (`isLUB_livenessTilt`) — the order-theoretic form of the
  epi-convergence of the steepening hinge to the step;
* the full-mass slice (`SubPMF.FullMass`): complement conversion
  (`SubPMF.prob_compl_of_fullMass`), the polarity coincidence
  (`wall_polarity_slice`), and the satisfaction-form recovery that
  serves every lower-bound threshold row at once
  (`sat_probLE_iff_probGE_slice`);
* mixtures (`SubPMF.mix`; `prob_mix` is the affinity of mass) and
  convexity: walls, tilts, and their maxima are convex
  (`safetyWall_mix_le`, `livenessTilt_mix_le`, `reachAvoid_mix_le`);
  each finite tilt is the coercion of a maximum of two affine
  functionals of the model (`livenessTilt_coe_toRat`), so the
  composite below is a pointwise maximum of affine pieces over the
  wall's half-space — the piecewise-linear certifiable class, whose
  sign split at the kink is the standard two-branch case analysis of
  piecewise-linear certificate rows;
* the composite specification (`reachAvoid`): a safety wall in maximum
  with a liveness tilt — robustly safe, and optimistically live; at
  `λ = ∞` it is the spec penalty of the two-judgment conjunction
  (`reachAvoid_top_eq_specPenaltyConj`);
* the battery families under polarity (`safetyBatteryWallFamily`,
  `leakFloorFamily`, `untilBatteryFamily`), each with its graded
  square.
-/

namespace SuFunctor

open PPLC Qtsl.Imprecise
open scoped NNRat

universe u

variable {V : Type u}

/-! ## Mass on complements, and the full-mass slice -/

namespace SubPMF

theorem prob_add_prob_compl (μ : SubPMF V) (A : Set V) :
    μ.prob A + μ.prob Aᶜ = μ.mass := by
  have h := μ.prob_union_add_inter A Aᶜ
  rw [Set.union_compl_self, Set.inter_compl_self, prob_empty] at h
  unfold mass
  linarith

/-- Full mass: the model has lost nothing.  Over the whole
subprobability scene these are exactly the radially maximal models —
a model of mass `m < 1` scales by any factor up to `1/m` inside the
scene, while a full-mass model scales past nothing — so quantifying a
lower-bound judgment over the full-mass models is the envelope
stratum's lower-component reading.  The zero model is not full-mass;
that exclusion is precisely what the envelope quantifier adds to the
per-element one. -/
def FullMass (μ : SubPMF V) : Prop := μ.mass = 1

/-- Complement conversion, licensed exactly by full mass.  Over
subprobability mass in general, `μ(Aᶜ)` and `1 − μ(A)` are unrelated:
the identity consumes the mass *lower* bound, which is the reason the
judgment layer has no complement move. -/
theorem prob_compl_of_fullMass {μ : SubPMF V} (h : μ.FullMass) (A : Set V) :
    μ.prob Aᶜ = 1 - μ.prob A := by
  have h1 : μ.mass = 1 := h
  have h2 := μ.prob_add_prob_compl A
  linarith

end SubPMF

/-! ## The two polarities -/

open Classical in
/-- The safety wall: the `{0, ⊤}`-valued indicator of the violation
half-space `{μ : μ(bad) ≤ q}`, where `q` is the violation budget (for
a "probability at least `p` of staying safe" row, `q = 1 − p` and
`bad` is the offending event).  At budget `0` this is the mass-zero
half-space — the sequent-kind shape.  Partiality cannot cross a
safety wall (`safetyWall_zero`). -/
noncomputable def safetyWall (bad : Set V) (q : ℚ) : SubPMF V → ENNRat :=
  fun μ => if μ.prob bad ≤ q then 0 else ⊤

open Classical in
/-- The hard liveness wall (satisfaction form): the indicator of
`{μ : p ≤ μ(goal)}`.  Mass loss honestly fails it.  It is the `λ = ∞`
member of the tilt family (`livenessTilt_top`). -/
noncomputable def livenessWall (goal : Set V) (p : ℚ) : SubPMF V → ENNRat :=
  fun μ => if p ≤ μ.prob goal then 0 else ⊤

theorem safetyWall_of_le {bad : Set V} {q : ℚ} {μ : SubPMF V}
    (h : μ.prob bad ≤ q) : safetyWall bad q μ = 0 := by
  simp [safetyWall, h]

theorem safetyWall_of_not_le {bad : Set V} {q : ℚ} {μ : SubPMF V}
    (h : ¬ μ.prob bad ≤ q) : safetyWall bad q μ = ⊤ := by
  simp [safetyWall, h]

theorem livenessWall_of_le {goal : Set V} {p : ℚ} {μ : SubPMF V}
    (h : p ≤ μ.prob goal) : livenessWall goal p μ = 0 := by
  simp [livenessWall, h]

theorem livenessWall_of_not_le {goal : Set V} {p : ℚ} {μ : SubPMF V}
    (h : ¬ p ≤ μ.prob goal) : livenessWall goal p μ = ⊤ := by
  simp [livenessWall, h]

/-- Partiality is not a safety violation: the zero model sits behind
every safety wall with nonnegative budget. -/
theorem safetyWall_zero {bad : Set V} {q : ℚ} (hq : 0 ≤ q) :
    safetyWall bad q (SubPMF.zero V) = 0 :=
  safetyWall_of_le (by rw [SubPMF.zero_prob]; exact hq)

/-- Partiality *is* a liveness failure: the zero model fails every
hard liveness wall with positive threshold. -/
theorem livenessWall_zero {goal : Set V} {p : ℚ} (hp : 0 < p) :
    livenessWall goal p (SubPMF.zero V) = ⊤ :=
  livenessWall_of_not_le (by rw [SubPMF.zero_prob]; exact not_le.mpr hp)

/-- The safety wall over a hypernet's scene *is* the spec penalty of
the upper-bound threshold judgment: the safety half of the polarity
table, as an identity into the graded layer. -/
theorem safetyWall_eq_specPenalty (H : Hypernet) (q : ℚ) (φ : Formula) :
    safetyWall (evt H φ) q = specPenalty H (.probLE q φ) := by
  funext μ
  by_cases h : μ.prob (evt H φ) ≤ q
  · rw [safetyWall_of_le h,
      specPenalty_of_sat (show Sat H (.probLE q φ) μ from h)]
  · rw [safetyWall_of_not_le h,
      specPenalty_of_not_sat (show ¬ Sat H (.probLE q φ) μ from h)]

/-- The hard liveness wall *is* the spec penalty of the lower-bound
threshold judgment: the liveness half of the polarity table at
`λ = ∞`. -/
theorem livenessWall_eq_specPenalty (H : Hypernet) (p : ℚ) (φ : Formula) :
    livenessWall (evt H φ) p = specPenalty H (.probGE p φ) := by
  funext μ
  by_cases h : p ≤ μ.prob (evt H φ)
  · rw [livenessWall_of_le h,
      specPenalty_of_sat (show Sat H (.probGE p φ) μ from h)]
  · rw [livenessWall_of_not_le h,
      specPenalty_of_not_sat (show ¬ Sat H (.probGE p φ) μ from h)]

/-! ## The hinge and the tilt family -/

/-- The liveness shortfall `p ∸ μ(goal)`: truncated subtraction,
valued in the nonnegative-rational carrier (penalties live in the
Lawvere quantale, so the shortfall saturates at `0` rather than going
negative).  `shortfall_coe` is the hinge identity. -/
noncomputable def shortfall (goal : Set V) (p : ℚ) (μ : SubPMF V) : ℚ≥0 :=
  ⟨max (p - μ.prob goal) 0, le_max_right _ _⟩

/-- **The hinge, as a maximum of affines.**  The shortfall's rational
reading is `max (p − μ(goal)) 0`: the pointwise maximum of an affine
functional of the model (`prob` is affine — `SubPMF.prob_mix`) and
the zero functional.  Piecewise-linear, hence convex
(`livenessTilt_mix_le`); the sign split at the kink is the standard
two-branch case analysis of piecewise-linear certificate rows. -/
@[simp] theorem shortfall_coe (goal : Set V) (p : ℚ) (μ : SubPMF V) :
    (shortfall goal p μ : ℚ) = max (p - μ.prob goal) 0 :=
  rfl

theorem shortfall_eq_zero_iff {goal : Set V} {p : ℚ} {μ : SubPMF V} :
    shortfall goal p μ = 0 ↔ p ≤ μ.prob goal := by
  constructor
  · intro h
    have hc : (shortfall goal p μ : ℚ) = 0 := by rw [h]; norm_num
    rw [shortfall_coe] at hc
    have hle : p - μ.prob goal ≤ 0 := hc ▸ le_max_left _ _
    linarith
  · intro h
    have hc : (shortfall goal p μ : ℚ) = 0 := by
      rw [shortfall_coe, max_eq_right (by linarith : p - μ.prob goal ≤ 0)]
    exact_mod_cast hc

/-- The tilt family: penalty `λ · (p ∸ μ(goal))` for a tilt weight
`λ ∈ [0, ∞]` (the members of interest have `λ > 0`; `λ = 0` is the
vacuous spec).  Finite members charge the shortfall linearly — a
relaxed liveness requirement that refuses no model
(`livenessTilt_coe_lt_top`); the `λ = ∞` member is the hard wall
(`livenessTilt_top`). -/
noncomputable def livenessTilt (goal : Set V) (p : ℚ) (lam : ENNRat) :
    SubPMF V → ENNRat :=
  fun μ => lam * (shortfall goal p μ : ENNRat)

@[simp] theorem livenessTilt_apply (goal : Set V) (p : ℚ) (lam : ENNRat)
    (μ : SubPMF V) :
    livenessTilt goal p lam μ = lam * (shortfall goal p μ : ENNRat) :=
  rfl

theorem livenessTilt_coe (goal : Set V) (p : ℚ) (c : ℚ≥0) (μ : SubPMF V) :
    livenessTilt goal p (c : ENNRat) μ =
      ((c * shortfall goal p μ : ℚ≥0) : ENNRat) := by
  rw [livenessTilt_apply, WithTop.coe_mul]

/-- Finite tilts refuse nothing: every model's penalty is finite.  (A
model with a large shortfall pays a large but finite price — which is
also why a finite tilt penalty certifies no wall: see the exhibit in
`SuFunctorLegacy.ThresholdRefute`.) -/
theorem livenessTilt_coe_lt_top (goal : Set V) (p : ℚ) (c : ℚ≥0)
    (μ : SubPMF V) :
    livenessTilt goal p (c : ENNRat) μ < ⊤ := by
  rw [livenessTilt_coe]
  exact WithTop.coe_lt_top _

/-- The scaled hinge: each finite tilt is the coercion of a maximum of
two affine functionals of the model. -/
theorem livenessTilt_coe_toRat (goal : Set V) (p : ℚ) (c : ℚ≥0)
    (μ : SubPMF V) :
    ((c * shortfall goal p μ : ℚ≥0) : ℚ) =
      max ((c : ℚ) * (p - μ.prob goal)) 0 := by
  rw [NNRat.coe_mul, shortfall_coe,
    mul_max_of_nonneg _ _ c.coe_nonneg, mul_zero]

theorem livenessTilt_mono_lam (goal : Set V) (p : ℚ) {lam₁ lam₂ : ENNRat}
    (h : lam₁ ≤ lam₂) (μ : SubPMF V) :
    livenessTilt goal p lam₁ μ ≤ livenessTilt goal p lam₂ μ :=
  mul_le_mul_left h _

/-- The `λ = ∞` member of the tilt family is the hard wall. -/
theorem livenessTilt_top (goal : Set V) (p : ℚ) :
    livenessTilt goal p ⊤ = livenessWall goal p := by
  funext μ
  by_cases h : p ≤ μ.prob goal
  · rw [livenessWall_of_le h, livenessTilt_apply,
      shortfall_eq_zero_iff.mpr h]
    simp
  · rw [livenessWall_of_not_le h, livenessTilt_apply]
    have hs : shortfall goal p μ ≠ 0 := fun h0 =>
      h (shortfall_eq_zero_iff.mp h0)
    exact WithTop.top_mul fun hc => hs (WithTop.coe_eq_zero.mp hc)

/-- Tilt transport: along event inclusion, threshold relaxation, and
tilt-weight relaxation the liveness penalty only drops — the tilt
family's own transport square (the lower-bound transport row read at
the penalty level). -/
theorem livenessTilt_transport {goal₁ goal₂ : Set V} {p₁ p₂ : ℚ}
    {lam₁ lam₂ : ENNRat} (hsub : goal₁ ⊆ goal₂) (hp : p₂ ≤ p₁)
    (hlam : lam₂ ≤ lam₁) (μ : SubPMF V) :
    livenessTilt goal₂ p₂ lam₂ μ ≤ livenessTilt goal₁ p₁ lam₁ μ := by
  have hs : shortfall goal₂ p₂ μ ≤ shortfall goal₁ p₁ μ := by
    rw [← NNRat.coe_le_coe, shortfall_coe, shortfall_coe]
    have hm := μ.prob_mono hsub
    exact max_le_max (by linarith) le_rfl
  calc livenessTilt goal₂ p₂ lam₂ μ
      = lam₂ * (shortfall goal₂ p₂ μ : ENNRat) := rfl
    _ ≤ lam₁ * (shortfall goal₂ p₂ μ : ENNRat) := mul_le_mul_left hlam _
    _ ≤ lam₁ * (shortfall goal₁ p₁ μ : ENNRat) :=
        mul_le_mul_right (WithTop.coe_le_coe.mpr hs) _
    _ = livenessTilt goal₁ p₁ lam₁ μ := rfl

/-- **Epi-convergence of the tilts to the wall, order form.**  At each
model, the hard wall is the least upper bound of the finite-tilt
values: the steepening hinge converges to the step.  The family is
nondecreasing in `λ`, so on the finitely supported models of this
stratum the pointwise-supremum statement carries the epigraph
convergence of the tilts to the wall as `λ → ∞`; we state the
order-theoretic form, which is the one the graded layer consumes. -/
theorem isLUB_livenessTilt (goal : Set V) (p : ℚ) (μ : SubPMF V) :
    IsLUB (Set.range fun c : ℚ≥0 => livenessTilt goal p (c : ENNRat) μ)
      (livenessWall goal p μ) := by
  constructor
  · rintro x ⟨c, rfl⟩
    dsimp only
    by_cases h : p ≤ μ.prob goal
    · rw [livenessWall_of_le h, livenessTilt_apply,
        shortfall_eq_zero_iff.mpr h]
      simp
    · rw [livenessWall_of_not_le h]
      exact le_top
  · intro b hb
    by_cases h : p ≤ μ.prob goal
    · rw [livenessWall_of_le h]
      exact zero_le
    · rw [livenessWall_of_not_le h]
      by_contra hlt
      have hbt : b ≠ ⊤ := fun hb' => hlt (hb' ▸ le_rfl)
      obtain ⟨b', rfl⟩ := WithTop.ne_top_iff_exists.mp hbt
      have hs : shortfall goal p μ ≠ 0 := fun h0 =>
        h (shortfall_eq_zero_iff.mp h0)
      have hmem := hb (Set.mem_range_self (b' / shortfall goal p μ + 1))
      rw [livenessTilt_coe, WithTop.coe_le_coe, add_mul, one_mul,
        div_mul_cancel₀ _ hs] at hmem
      have h0 : b' + shortfall goal p μ ≤ b' + 0 := by rwa [add_zero]
      have hzero : shortfall goal p μ ≤ 0 := le_of_add_le_add_left h0
      exact hs (le_antisymm hzero zero_le)

/-! ## The envelope lemma: satisfaction-form recovery on the slice

One lemma serves every lower-bound threshold row at once: on the
full-mass slice — the radially maximal models, the envelope stratum's
lower-component quantifier range — an upper bound on a complementary
event is *equivalent* to the lower bound on the event itself.  Off the
slice the two forms come apart, safety rows claim only the violation
form, and the unrestricted (per-element) conversion is refuted in
`SuFunctorLegacy.ThresholdRefute`.  The complement enters through an
event-level hypothesis: the judgment syntax deliberately has no
complement constructor, so the complementary formula is supplied by
the negation-normal-form machinery and certified event-level. -/

theorem sat_probLE_iff_probGE_slice (H : Hypernet) {φ ψ : Formula}
    (hcompl : evt H ψ = (evt H φ)ᶜ) (p : ℚ) {μ : SubPMF (AdmVal H)}
    (hmass : μ.FullMass) :
    Sat H (.probLE (1 - p) ψ) μ ↔ Sat H (.probGE p φ) μ := by
  show μ.prob (evt H ψ) ≤ 1 - p ↔ p ≤ μ.prob (evt H φ)
  rw [hcompl, SubPMF.prob_compl_of_fullMass hmass]
  constructor <;> intro h <;> linarith

/-- The wall form of the slice coincidence: on full-mass models the
safety wall on the complementary event *is* the hard liveness wall —
the crisp-locus identity that makes the polarity fork invisible from
the total-mass world. -/
theorem wall_polarity_slice {A : Set V} {p : ℚ} {μ : SubPMF V}
    (hmass : μ.FullMass) :
    safetyWall Aᶜ (1 - p) μ = livenessWall A p μ := by
  by_cases h : p ≤ μ.prob A
  · have hyes : μ.prob Aᶜ ≤ 1 - p := by
      rw [SubPMF.prob_compl_of_fullMass hmass]
      linarith
    rw [livenessWall_of_le h, safetyWall_of_le hyes]
  · have hno : ¬ μ.prob Aᶜ ≤ 1 - p := by
      rw [SubPMF.prob_compl_of_fullMass hmass]
      intro hc
      exact h (by linarith)
    rw [livenessWall_of_not_le h, safetyWall_of_not_le hno]

/-! ## Mixtures and convexity -/

namespace SubPMF

private theorem sum_eq_sum_of_support_subset (f : V →₀ ℚ) {s : Finset V}
    (hs : f.support ⊆ s) : ∑ v ∈ f.support, f v = ∑ v ∈ s, f v :=
  Finset.sum_subset hs fun _ _ hv => Finsupp.notMem_support_iff.mp hv

/-- The convex mixture of two subprobability models. -/
noncomputable def mix (a b : ℚ≥0) (hab : a + b = 1) (μ ν : SubPMF V) :
    SubPMF V where
  wt := (a : ℚ) • μ.wt + (b : ℚ) • ν.wt
  nonneg := fun v => by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg a.coe_nonneg (μ.nonneg v))
      (mul_nonneg b.coe_nonneg (ν.nonneg v))
  mass_le_one := by
    classical
    have hsub : ((a : ℚ) • μ.wt + (b : ℚ) • ν.wt).support ⊆
        μ.wt.support ∪ ν.wt.support :=
      Finsupp.support_add.trans
        (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)
    rw [sum_eq_sum_of_support_subset _ hsub]
    have hμ : ∑ v ∈ μ.wt.support ∪ ν.wt.support, μ.wt v ≤ 1 := by
      rw [← sum_eq_sum_of_support_subset μ.wt Finset.subset_union_left]
      exact μ.mass_le_one
    have hν : ∑ v ∈ μ.wt.support ∪ ν.wt.support, ν.wt v ≤ 1 := by
      rw [← sum_eq_sum_of_support_subset ν.wt Finset.subset_union_right]
      exact ν.mass_le_one
    have hcoe : (a : ℚ) + (b : ℚ) = 1 := by exact_mod_cast hab
    calc ∑ v ∈ μ.wt.support ∪ ν.wt.support,
          ((a : ℚ) • μ.wt + (b : ℚ) • ν.wt) v
        = (a : ℚ) * ∑ v ∈ μ.wt.support ∪ ν.wt.support, μ.wt v +
            (b : ℚ) * ∑ v ∈ μ.wt.support ∪ ν.wt.support, ν.wt v := by
          simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ (a : ℚ) * 1 + (b : ℚ) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hμ a.coe_nonneg)
            (mul_le_mul_of_nonneg_left hν b.coe_nonneg)
      _ = 1 := by rw [mul_one, mul_one, hcoe]

/-- Mass is affine: the probability of every event mixes linearly.
(The hinge identity `shortfall_coe` reads each shortfall, and hence
each finite tilt, as a maximum of affine functionals through this
lemma.) -/
theorem prob_mix (a b : ℚ≥0) (hab : a + b = 1) (μ ν : SubPMF V)
    (S : Set V) :
    (mix a b hab μ ν).prob S = a * μ.prob S + b * ν.prob S := by
  classical
  unfold prob mix
  have hsub : ((a : ℚ) • μ.wt + (b : ℚ) • ν.wt).support ⊆
      μ.wt.support ∪ ν.wt.support :=
    Finsupp.support_add.trans
      (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)
  rw [Finset.sum_subset hsub (fun _ _ hv => by
    rw [Finsupp.notMem_support_iff.mp hv, ite_self])]
  rw [Finset.sum_subset
      (show μ.wt.support ⊆ μ.wt.support ∪ ν.wt.support from
        Finset.subset_union_left) (fun _ _ hv => by
    rw [Finsupp.notMem_support_iff.mp hv, ite_self]),
    Finset.sum_subset
      (show ν.wt.support ⊆ μ.wt.support ∪ ν.wt.support from
        Finset.subset_union_right) (fun _ _ hv => by
    rw [Finsupp.notMem_support_iff.mp hv, ite_self])]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hS : v ∈ S <;>
    simp [hS, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

end SubPMF

/-- Safety walls are convex: a mixture that breaches the wall has a
component that breaches it, with positive weight. -/
theorem safetyWall_mix_le (bad : Set V) (q : ℚ) (a b : ℚ≥0)
    (hab : a + b = 1) (μ ν : SubPMF V) :
    safetyWall bad q (SubPMF.mix a b hab μ ν) ≤
      (a : ENNRat) * safetyWall bad q μ +
        (b : ENNRat) * safetyWall bad q ν := by
  by_cases hmix : (SubPMF.mix a b hab μ ν).prob bad ≤ q
  · rw [safetyWall_of_le hmix]
    exact zero_le
  · rw [safetyWall_of_not_le hmix]
    rw [SubPMF.prob_mix] at hmix
    have hcoe : (a : ℚ) + (b : ℚ) = 1 := by exact_mod_cast hab
    have key : ((a : ℚ) ≠ 0 ∧ ¬ μ.prob bad ≤ q) ∨
        ((b : ℚ) ≠ 0 ∧ ¬ ν.prob bad ≤ q) := by
      by_cases hμq : μ.prob bad ≤ q
      · by_cases hνq : ν.prob bad ≤ q
        · exfalso
          apply hmix
          calc (a : ℚ) * μ.prob bad + (b : ℚ) * ν.prob bad
              ≤ (a : ℚ) * q + (b : ℚ) * q :=
                add_le_add (mul_le_mul_of_nonneg_left hμq a.coe_nonneg)
                  (mul_le_mul_of_nonneg_left hνq b.coe_nonneg)
            _ = q := by rw [← add_mul, hcoe, one_mul]
        · by_cases hb : (b : ℚ) = 0
          · exfalso
            apply hmix
            have ha1 : (a : ℚ) = 1 := by linarith
            rw [hb, ha1]
            simpa using hμq
          · exact Or.inr ⟨hb, hνq⟩
      · by_cases ha : (a : ℚ) = 0
        · have hb1 : (b : ℚ) = 1 := by linarith
          refine Or.inr ⟨by rw [hb1]; norm_num, fun hνq => ?_⟩
          apply hmix
          rw [ha, hb1]
          simpa using hνq
        · exact Or.inl ⟨ha, hμq⟩
    rcases key with ⟨ha, hμq⟩ | ⟨hb, hνq⟩
    · rw [safetyWall_of_not_le hμq,
        WithTop.mul_top (by exact_mod_cast ha), top_add]
    · rw [safetyWall_of_not_le hνq,
        WithTop.mul_top (by exact_mod_cast hb), add_top]

private theorem max_hinge_convex {p x y a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    max (p - (a * x + b * y)) 0 ≤ a * max (p - x) 0 + b * max (p - y) 0 := by
  have h1 : a = 1 - b := by linarith
  subst h1
  rcases le_total (p - ((1 - b) * x + b * y)) 0 with h | h
  · rw [max_eq_right h]
    exact add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hb (le_max_right _ _))
  · rw [max_eq_left h]
    have hid : p - ((1 - b) * x + b * y) =
        (1 - b) * (p - x) + b * (p - y) := by ring
    rw [hid]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)

/-- Liveness tilts are convex: the hinge is a maximum of two affine
functionals (`shortfall_coe`, `SubPMF.prob_mix`), and the tilt scales
it. -/
theorem livenessTilt_mix_le (goal : Set V) (p : ℚ) (lam : ENNRat)
    (a b : ℚ≥0) (hab : a + b = 1) (μ ν : SubPMF V) :
    livenessTilt goal p lam (SubPMF.mix a b hab μ ν) ≤
      (a : ENNRat) * livenessTilt goal p lam μ +
        (b : ENNRat) * livenessTilt goal p lam ν := by
  have hcoe : (a : ℚ) + (b : ℚ) = 1 := by exact_mod_cast hab
  have hs : shortfall goal p (SubPMF.mix a b hab μ ν) ≤
      a * shortfall goal p μ + b * shortfall goal p ν := by
    rw [← NNRat.coe_le_coe]
    push_cast
    rw [shortfall_coe, shortfall_coe, shortfall_coe, SubPMF.prob_mix]
    exact max_hinge_convex a.coe_nonneg b.coe_nonneg hcoe
  calc livenessTilt goal p lam (SubPMF.mix a b hab μ ν)
      = lam * (shortfall goal p (SubPMF.mix a b hab μ ν) : ENNRat) := rfl
    _ ≤ lam * ((a * shortfall goal p μ + b * shortfall goal p ν : ℚ≥0) :
          ENNRat) := mul_le_mul_right (WithTop.coe_le_coe.mpr hs) _
    _ = (a : ENNRat) * (lam * (shortfall goal p μ : ENNRat)) +
          (b : ENNRat) * (lam * (shortfall goal p ν : ENNRat)) := by
        push_cast
        ring
    _ = (a : ENNRat) * livenessTilt goal p lam μ +
          (b : ENNRat) * livenessTilt goal p lam ν := rfl

/-! ## The composite: robustly safe, optimistically live -/

/-- The reach–avoid composite: a safety wall in maximum with a
liveness tilt.  `max` is conjunction at the penalty level (a system
dominates the maximum iff it dominates both members), so the composite
is the standard specification "robustly safe, and optimistically
live": the safety half is non-negotiable at every tilt weight, while
the liveness half charges the shortfall.  At `λ = ∞` the composite is
the spec penalty of the two-judgment formal conjunction
(`reachAvoid_top_eq_specPenaltyConj`); at finite `λ` only its liveness
half leaves the indicator stratum.  As a maximum of a wall (on a
half-space cut out by one affine functional) and finitely many affine
pieces (`livenessTilt_coe_toRat`), it lies in the piecewise-linear
certifiable class, and it is convex (`reachAvoid_mix_le`). -/
noncomputable def reachAvoid (avoid goal : Set V) (q p : ℚ)
    (lam : ENNRat) : SubPMF V → ENNRat :=
  fun μ => max (safetyWall avoid q μ) (livenessTilt goal p lam μ)

@[simp] theorem reachAvoid_apply (avoid goal : Set V) (q p : ℚ)
    (lam : ENNRat) (μ : SubPMF V) :
    reachAvoid avoid goal q p lam μ =
      max (safetyWall avoid q μ) (livenessTilt goal p lam μ) :=
  rfl

/-- The composite is convex: a maximum of convex penalties. -/
theorem reachAvoid_mix_le (avoid goal : Set V) (q p : ℚ) (lam : ENNRat)
    (a b : ℚ≥0) (hab : a + b = 1) (μ ν : SubPMF V) :
    reachAvoid avoid goal q p lam (SubPMF.mix a b hab μ ν) ≤
      (a : ENNRat) * reachAvoid avoid goal q p lam μ +
        (b : ENNRat) * reachAvoid avoid goal q p lam ν := by
  refine max_le ?_ ?_
  · refine le_trans (safetyWall_mix_le avoid q a b hab μ ν) ?_
    exact add_le_add (mul_le_mul_right (le_max_left _ _) _)
      (mul_le_mul_right (le_max_left _ _) _)
  · refine le_trans (livenessTilt_mix_le goal p lam a b hab μ ν) ?_
    exact add_le_add (mul_le_mul_right (le_max_right _ _) _)
      (mul_le_mul_right (le_max_right _ _) _)

/-- At `λ = ∞` the composite is the two-wall conjunction. -/
theorem reachAvoid_top (avoid goal : Set V) (q p : ℚ) :
    reachAvoid avoid goal q p ⊤ =
      fun μ => max (safetyWall avoid q μ) (livenessWall goal p μ) := by
  funext μ
  rw [reachAvoid_apply, livenessTilt_top]

/-- The spec penalty of a two-judgment conjunction is the maximum of
the members' spec penalties: conjunction at the indicator stratum is
the join of the graded order. -/
theorem specPenaltyConj_pair (H : Hypernet) (m n : Judgment)
    (μ : SubPMF (AdmVal H)) :
    specPenaltyConj H [m, n] μ =
      max (specPenalty H m μ) (specPenalty H n μ) := by
  by_cases hm : Sat H m μ
  · by_cases hn : Sat H n μ
    · rw [specPenaltyConj_of_sat (l := [m, n]) (satConj_pair.mpr ⟨hm, hn⟩),
        specPenalty_of_sat hm, specPenalty_of_sat hn, max_self]
    · rw [specPenaltyConj_of_not_sat (l := [m, n])
          (fun hc => hn (satConj_pair.mp hc).2),
        specPenalty_of_sat hm, specPenalty_of_not_sat hn,
        max_eq_right le_top]
  · rw [specPenaltyConj_of_not_sat (l := [m, n])
        (fun hc => hm (satConj_pair.mp hc).1),
      specPenalty_of_not_sat hm, max_eq_left le_top]

/-- Over a hypernet's scene, the `λ = ∞` composite is the spec penalty
of the conjunction of its two threshold judgments: the reach–avoid
specification is an ordinary formal conjunction at the judgment layer,
and only its finite-`λ` relaxations leave the indicator stratum. -/
theorem reachAvoid_top_eq_specPenaltyConj (H : Hypernet) (q p : ℚ)
    (U φ : Formula) :
    reachAvoid (evt H U) (evt H φ) q p ⊤ =
      specPenaltyConj H [.probLE q U, .probGE p φ] := by
  funext μ
  rw [reachAvoid_apply, livenessTilt_top, specPenaltyConj_pair,
    ← safetyWall_eq_specPenalty, ← livenessWall_eq_specPenalty]

/-! ## The battery families under polarity

The safety battery's conclusion, under safety polarity, denotes the
violation half-space; the deadline- and recurrence-shaped batteries'
conclusions are liveness-shaped and keep their mass floors, paying for
partiality with an explicit leak row; and the until-shaped battery is
the formal conjunction of the two — which is the `reachAvoid`
composite at the judgment layer.  Each family's graded square (the
cell at every height) follows from its per-element square by the
quantifier collapse; the corollaries are stated by name so the graded
claims are citable. -/

/-- The safety battery's judgment-level face under safety polarity:
from the certificate's risk row — an upper bound on the avoid event —
conclude the violation half-space of the safety claim, the complement
supplied event-level by the gate.  **No mass premise**: the wall is
partiality-immune, so the square holds on the whole subprobability
scene, the zero model included.  Compare `safetyShell` (the
satisfaction-form face), which consumes a full-mass premise exactly
because its conclusion is a lower bound;
`safetyShellWall_slice_recovery` reconciles the two forms on the
slice. -/
theorem safetyShellWall (H : Hypernet) (p : ℚ) (φG U ψ : Formula)
    (hcompl : evt H ψ = (evt H φG)ᶜ)
    (hcover : ∀ σ : AdmVal H, σ ∈ evt H φG ∪ evt H U)
    (μ : SubPMF (AdmVal H)) (hU : Sat H (.probLE (1 - p) U) μ) :
    Sat H (.probLE (1 - p) ψ) μ := by
  show μ.prob (evt H ψ) ≤ 1 - p
  have hsub : evt H ψ ⊆ evt H U := by
    rw [hcompl]
    intro σ hσ
    exact (hcover σ).resolve_left hσ
  exact le_trans (μ.prob_mono hsub) hU

/-- Satisfaction-form recovery on the slice: on full-mass models the
violation half-space conclusion yields the original lower-bound
reading.  With `sat_probLE_iff_probGE_slice`, this is the exact sense
in which the polarity denotation extends the crisp reading rather than
replacing it. -/
theorem safetyShellWall_slice_recovery (H : Hypernet) (p : ℚ)
    (φG ψ : Formula) (hcompl : evt H ψ = (evt H φG)ᶜ)
    {μ : SubPMF (AdmVal H)} (hmass : μ.FullMass)
    (hV : Sat H (.probLE (1 - p) ψ) μ) :
    Sat H (.probGE p φG) μ :=
  (sat_probLE_iff_probGE_slice H hcompl p hmass).mp hV

/-- The safety battery under polarity, as a rule family.  Tag:
`(p, φG, U, ψ)` — safety threshold, safe region, avoid event, and the
event-level complement of the safe region. -/
def safetyBatteryWallFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × Formula × Formula × Formula
      gate := fun i => evt H i.2.2.2 = (evt H i.2.1)ᶜ ∧
        ∀ σ : AdmVal H, σ ∈ evt H i.2.1 ∪ evt H i.2.2.1
      top := fun i => [Judgment.probLE (1 - i.1) i.2.2.1]
      bot := fun i => [Judgment.probLE (1 - i.1) i.2.2.2] }
  square := by
    rintro ⟨p, φG, U, ψ⟩ ⟨hcompl, hcover⟩ μ h
    rw [satConj_singleton] at h ⊢
    exact safetyShellWall H p φG U ψ hcompl hcover μ h

/-- The graded square of the polarity-form safety battery: the cell at
every height. -/
theorem safetyBatteryWall_graded (H : Hypernet)
    (t : (safetyBatteryWallFamily H).rules.Tag)
    (ht : (safetyBatteryWallFamily H).rules.gate t) :
    ∀ σ : Penalty H,
      specPenaltyConj H ((safetyBatteryWallFamily H).rules.top t) ≤ σ →
        specPenaltyConj H ((safetyBatteryWallFamily H).rules.bot t) ≤ σ :=
  (safetyBatteryWallFamily H).gradedSquare t ht

/-- The mass-floor battery shape: a satisfaction-form (lower-bound)
conclusion beside a named **leak row**.  A liveness-shaped conclusion
keeps its mass floor — mass loss counts against it — so at the
partiality strata the battery carries one extra premise bounding the
leak, and its square is escape-corrected transport with the leak event
as the escape: exactly the content of `monElimFamily`, under the
deadline/recurrence reading.  The leak premise is also what admits the
lower-bound conclusion past the zero-model obstruction (lower-bound
conclusions need a lower-bound premise; the verdict row is one). -/
abbrev leakFloorFamily (H : Hypernet) : SemRuleFamily H := monElimFamily H

/-- The graded square of the mass-floor battery shape: the cell at
every height. -/
theorem leakFloor_graded (H : Hypernet)
    (t : (leakFloorFamily H).rules.Tag)
    (ht : (leakFloorFamily H).rules.gate t) :
    ∀ σ : Penalty H,
      specPenaltyConj H ((leakFloorFamily H).rules.top t) ≤ σ →
        specPenaltyConj H ((leakFloorFamily H).rules.bot t) ≤ σ :=
  (leakFloorFamily H).gradedSquare t ht

/-- The until-shaped battery's judgment-level face: hold-phase safety
in formal conjunction with leak-corrected reach — the two polarity
repairs composing as a product (concatenation of premise lists,
componentwise square).  Its `λ = ∞` denotation over the scene is the
wall pair of the `reachAvoid` composite. -/
def untilBatteryFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := (ℚ × Formula × Formula × Formula) ×
        (ℚ × ℚ × Formula × Formula × Formula)
      gate := fun i => (safetyBatteryWallFamily H).rules.gate i.1 ∧
        (leakFloorFamily H).rules.gate i.2
      top := fun i => (safetyBatteryWallFamily H).rules.top i.1 ++
        (leakFloorFamily H).rules.top i.2
      bot := fun i => (safetyBatteryWallFamily H).rules.bot i.1 ++
        (leakFloorFamily H).rules.bot i.2 }
  square := by
    rintro ⟨t₁, t₂⟩ ⟨h₁, h₂⟩ μ h
    rw [satConj_append] at h ⊢
    exact ⟨(safetyBatteryWallFamily H).square t₁ h₁ μ h.1,
      (leakFloorFamily H).square t₂ h₂ μ h.2⟩

/-- The graded square of the until-shaped battery: the cell at every
height. -/
theorem untilBattery_graded (H : Hypernet)
    (t : (untilBatteryFamily H).rules.Tag)
    (ht : (untilBatteryFamily H).rules.gate t) :
    ∀ σ : Penalty H,
      specPenaltyConj H ((untilBatteryFamily H).rules.top t) ≤ σ →
        specPenaltyConj H ((untilBatteryFamily H).rules.bot t) ≤ σ :=
  (untilBatteryFamily H).gradedSquare t ht

end SuFunctor
