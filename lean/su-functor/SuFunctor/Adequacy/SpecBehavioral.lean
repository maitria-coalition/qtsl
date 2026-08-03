import SuFunctor.Universe.SpecElab
import SuFunctor.Adequacy.Envelope
import QtslAux.QStreett
import QtslAux.Deadline

/-! # Behavioral-tier semantics of the probability and return formers

The probability-threshold former (`P_{≥p}[ψ]`) and the expected-return
formers denote *regions of states*, read against the behavioral tier:
the kernel path measure of a Markov chain (`Qtsl.Battery.pathMeasure`).
This module states their **directed** adequacy cells — every theorem
here is a `sound` (no-overclaim) implication whose direction and
approximation source are printed in its docstring, and no completeness
counterpart exists in this module *by design*: the producers are
certificate batteries (Lyapunov/supermartingale data), which can fail
to certify true claims.

Contents:

* **The directed-cell template** (`safeProper_mono`,
  `safetyAtom_modelClass_mono`): a region-level inclusion transports to
  a model-class inclusion at the coupled judgment.  Every former-level
  directed square below is its region-level approximation lemma
  composed with this template.
* **The credal face** (`satCredal_lower_singletonC_geC` and kin): at
  the singleton lift of a precise model, the lower-kind credal reading
  of an event threshold is plain event probability — the compatibility
  lemma between the credal envelope stratum and the behavioral tier
  (order theory on a nonempty singleton, stated at the landed
  vocabulary).  The zero-mass fence
  (`satCredal_lower_singletonC_zero`) records why the judgment carries
  a properness presupposition at all: at the zero lift the lower face
  is vacuous for *every* constraint.
* **The probability-threshold region** (`probThresholdSet`): its
  event-inclusion and threshold-weakening monotonicities (the
  approximation sources), the generic producer cell, and the composed
  specimen `sprob_sound_of_streettBundle` — a bundled quantitative
  Streett certificate produces the threshold claim on any event
  containing the Streett event.
* **The finite-horizon return region** (`finReturn`, `returnGESet`):
  reward-domination, horizon-extension, and bound-weakening
  monotonicities; the deadline square `returnGE_sound_of_deadline` — a
  geometrically decaying Lyapunov certificate produces the behavioral
  expected-return claim with indicator reward.  The horizon of a
  summed (per-tick) return is a *natural number* throughout: the
  behavioral tier is tick-indexed and unitless, so a discrete sum's
  upper index admits no rational reading (an integral-time horizon is
  meaningful only for time-integral accumulation, which is not this
  tier).
* **The discounted square** (`discountedReturn_le_of_drift`): a
  geometric-drift certificate bounds the discounted expected return
  from above, uniformly in the horizon — the upper (LE) face of the
  discounted-return former.

The pasting between this tier's two carriers — exact-rational
finite-support laws (`SubPMF`) on the credal side, Bochner/`ℝ≥0∞`
measures on the kernel side — is the finite-dimensional-distributions
stratum and is deliberately not claimed here. -/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Filter Finset

namespace SuFunctor.Universe

universe u v

/-! ## The directed-cell template

A directed former square concludes a *containment* of model classes:
the class compiled against the certificate's under-approximation sits
inside the community claim's class.  Both statements below are the
transport making that one step: region inclusion in, model-class
inclusion out. -/

section Template

variable {X : Type u}

/-- Safe-and-proper is monotone in the region: enlarging the permitted
target enlarges the class.  The engine of every directed cell below. -/
theorem safeProper_mono {C D : Set X} (h : C ⊆ D) :
    safeProper C ⊆ safeProper D := by
  rintro σ ⟨hsub, hne⟩
  exact ⟨hsub.trans h, hne⟩

/-- **The directed-cell template**: a region-level inclusion transports
to a model-class inclusion of the corresponding safety atoms at the
coupled judgment.  Direction: compiled (smaller region) → community
(larger region); the reverse containment fails whenever the inclusion
is strict. -/
theorem safetyAtom_modelClass_mono {C D : Set X} (h : C ⊆ D) :
    (safetyAtom C).modelClass ⊆ (safetyAtom D).modelClass := by
  rw [safetyAtom_modelClass, safetyAtom_modelClass]
  exact safeProper_mono h

end Template

/-! ## The credal face: threshold atoms at the singleton lift

The compatibility lemmas between the credal envelope stratum and a
precise behavioral law: lifting a single subprobability model to the
credal judgment and reading an event-threshold atom gives back plain
event probability.  These are order theory on a nonempty singleton —
the *compatibility* face of the probabilistic former's square, not the
square itself. -/

section CredalFace

variable {V : Type u}

/-- The lower-kind (≥-threshold) credal reading of an event atom at the
singleton lift of a nonzero model is the model's own event
probability.  (The ray-lift sibling is `satCredal_lower_rayC_geC`.) -/
theorem satCredal_lower_singletonC_geC {μ : SubPMF V}
    (hμ : μ ≠ SubPMF.zero V) (A : Set V) (q : ℚ) :
    SatCredal .lower (singletonC μ) (geC A q) ↔ q ≤ μ.prob A :=
  satCredal_lower_singletonC hμ _

/-- The upper-kind (≤-threshold) credal reading at the singleton lift,
with no nonzero hypothesis: the whole-set reader of a singleton reads
the one model. -/
theorem satCredal_upper_singletonC_leC (μ : SubPMF V) (A : Set V)
    (q : ℚ) :
    SatCredal .upper (singletonC μ) (leC A q) ↔ μ.prob A ≤ q :=
  satCredal_upper_singletonC μ _

/-- The upper-kind reading survives the ray lift: event-probability
upper bounds are down-closed, so the whole-set reader of the ray agrees
with the model's own verdict. -/
theorem satCredal_upper_rayC_leC (μ : SubPMF V) (A : Set V) (q : ℚ) :
    SatCredal .upper (rayC μ) (leC A q) ↔ μ.prob A ≤ q :=
  satCredal_upper_rayC (downClosed_leC A q)

/-- **The zero-mass fence**: at the singleton lift of the *zero* model,
the lower-kind reading is vacuously satisfied by every constraint —
including `geC A 1`.  The radially maximal slice of `{0}` is empty
(the zero point is refuted against its own scalings), so a lower-kind
judgment over it quantifies over nothing.  This vacuity is exactly what
the judgment's properness presupposition exists to exclude: a
probability-threshold claim is honest only at proper (nonzero)
lifts. -/
theorem satCredal_lower_singletonC_zero (c : SubPMF V → Prop) :
    SatCredal .lower (singletonC (SubPMF.zero V)) c := by
  rintro ν ⟨hν, hmax⟩
  have hν0 : ν = SubPMF.zero V := (singletonC_iff _ ν).mp hν
  exfalso
  refine hmax 2 (by norm_num) (SubPMF.zero V) ?_ (singletonC_self _)
  rw [SubPMF.zero_wt, hν0, SubPMF.zero_wt, smul_zero]

end CredalFace

/-! ## The probability-threshold region

`P_{≥p}[·]` denotes a region of states: those from which the chain's
path measure assigns the event at least `p`.  The former's directed
square is event-inclusion monotonicity transported by the template. -/

section ProbThreshold

open Qtsl.Battery

variable {S : Type*} [MeasurableSpace S]

/-- The behavioral denotation of the probability-threshold former: the
set of start states from which the event's path-measure probability is
at least `p`. -/
def probThresholdSet (K : Kernel S S) [IsMarkovKernel K] (p : ℝ)
    (E : Set (ℕ → S)) : Set S :=
  {x | ENNReal.ofReal p ≤ pathMeasure K x E}

variable {K : Kernel S S} [IsMarkovKernel K]

theorem mem_probThresholdSet_iff {p : ℝ} {E : Set (ℕ → S)} {x : S} :
    x ∈ probThresholdSet K p E ↔
      ENNReal.ofReal p ≤ pathMeasure K x E :=
  Iff.rfl

/-- **Approximation source, event face**: enlarging the event enlarges
the region.  Direction: a claim certified on an under-approximating
event `E` is sound for every community event `E' ⊇ E`; the converse
fails. -/
theorem probThresholdSet_mono {p : ℝ} {E E' : Set (ℕ → S)}
    (hE : E ⊆ E') :
    probThresholdSet K p E ⊆ probThresholdSet K p E' :=
  fun _x hx => le_trans hx (measure_mono hE)

/-- **Approximation source, threshold face**: weakening the threshold
enlarges the region — certifying at a stronger threshold suffices for
every weaker claim. -/
theorem probThresholdSet_anti_threshold {p q : ℝ} {E : Set (ℕ → S)}
    (hpq : p ≤ q) :
    probThresholdSet K q E ⊆ probThresholdSet K p E :=
  fun _x hx => le_trans (ENNReal.ofReal_le_ofReal hpq) hx

/-- The generic producer cell: any lower bound on the path measure of
an under-approximating event yields membership in the community
event's threshold region.  Every battery conclusion feeds the former
through this cell. -/
theorem probThresholdSet_mem_of_le {p : ℝ} {E' E : Set (ℕ → S)} {x : S}
    (h : ENNReal.ofReal p ≤ pathMeasure K x E') (hsub : E' ⊆ E) :
    x ∈ probThresholdSet K p E :=
  le_trans h (measure_mono hsub)

/-- **The probability-threshold former's directed square at the coupled
judgment**: the model class of the region compiled against the
certificate's event is contained in the community event's class.
`sound` only; no completeness statement exists in this module — the
containment is strict whenever the certificate's event is. -/
theorem sprobAtom_modelClass_mono {p : ℝ} {E E' : Set (ℕ → S)}
    (hE : E ⊆ E') :
    (safetyAtom (probThresholdSet K p E)).modelClass ⊆
      (safetyAtom (probThresholdSet K p E')).modelClass :=
  safetyAtom_modelClass_mono (probThresholdSet_mono hE)

/-- **The specimen square**: a bundled quantitative Streett certificate
(fail-closed confinement battery `V₀` plus one localized
supermartingale per request/response pair) places the start state in
the probability-threshold region of *any* event containing the Streett
event.  Direction: certificate acceptance → community claim; the
battery can fail to certify a true claim, and no converse is stated.
Approximation sources: the battery's own confinement localization, and
the event inclusion `hE`. -/
theorem sprob_sound_of_streettBundle
    {K : Kernel S S} [IsMarkovKernel K]
    {D Dbar U : Set S} {V₀ : S → ℝ} {p thr : ℝ} {x : S}
    {ι : Type*} [Countable ι]
    {Rq G : ι → Set S} {W : ι → S → ℝ} {ε C : ι → ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar)
    (hU : MeasurableSet U) (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y)
    (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → Integrable (W i) (K y))
    (hWdrift : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i →
      ∫ z, W i z ∂K y ≤ W i y)
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∈ Rq i → y ∉ G i →
      ∫ z, W i z ∂K y ≤ W i y - ε i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr)
    {E : Set (ℕ → S)}
    (hE : {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ Rq i) →
      ∃ᶠ n in atTop, ω n ∈ G i} ⊆ E) :
    x ∈ probThresholdSet K p E :=
  probThresholdSet_mem_of_le
    (Qtsl.QStreett.sound_QStreettBundle hD hDbar hU hV₀ hRq hG hW hΘ
      hDsub hR3 hR4 hV₀int hV₀drift hV₀floor hV₀nonneg hε hW0 hWC hWint
      hWdrift hWdriftR hx hthr)
    hE

end ProbThreshold

/-! ## The finite-horizon return region

The summed (per-tick) expected-return former.  Its horizon is a
**natural number**: the behavioral tier's subjects are tick-indexed and
unitless, so the discrete sum's upper index admits no rational reading
— there is no clock here against which a rational time could be
rounded.  (Time-integral accumulation, whose horizon is honestly
rational, is a different lift and not this tier.) -/

section Return

open Qtsl.Battery

/-- The per-tick accumulated reward of a path over `n` ticks. -/
def finReturn {S : Type*} (r : S → ℝ) (n : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ t ∈ Finset.range n, r (ω t)

variable {S : Type*} [MeasurableSpace S]

/-- The behavioral denotation of the lower-bounded expected-return
former: states from which the expected `n`-tick accumulated reward is
at least `b`. -/
def returnGESet (K : Kernel S S) [IsMarkovKernel K] (r : S → ℝ)
    (b : ℝ) (n : ℕ) : Set S :=
  {x | b ≤ ∫ ω, finReturn r n ω ∂pathMeasure K x}

/-- The upper-bounded mirror. -/
def returnLESet (K : Kernel S S) [IsMarkovKernel K] (r : S → ℝ)
    (b : ℝ) (n : ℕ) : Set S :=
  {x | ∫ ω, finReturn r n ω ∂pathMeasure K x ≤ b}

variable {K : Kernel S S} [IsMarkovKernel K]

/-- **Approximation source, reward face**: pointwise reward domination
enlarges the lower-bound region.  Direction: a return bound certified
against an under-approximating reward is sound for the dominating
reward. -/
theorem returnGESet_mono_reward {r r' : S → ℝ} {b : ℝ} {n : ℕ}
    (hr : ∀ s, r s ≤ r' s)
    (hint : ∀ x, Integrable (finReturn r n) (pathMeasure K x))
    (hint' : ∀ x, Integrable (finReturn r' n) (pathMeasure K x)) :
    returnGESet K r b n ⊆ returnGESet K r' b n := by
  intro x hx
  refine le_trans hx (integral_mono (hint x) (hint' x) fun ω => ?_)
  exact Finset.sum_le_sum fun t _ => hr (ω t)

/-- **Approximation source, horizon face**: for nonnegative rewards,
extending the horizon enlarges the lower-bound region — a bound
certified at a shorter horizon is sound at every longer one. -/
theorem returnGESet_mono_horizon {r : S → ℝ} {b : ℝ} {n n' : ℕ}
    (hr : ∀ s, 0 ≤ r s) (hn : n ≤ n')
    (hint : ∀ x, Integrable (finReturn r n) (pathMeasure K x))
    (hint' : ∀ x, Integrable (finReturn r n') (pathMeasure K x)) :
    returnGESet K r b n ⊆ returnGESet K r b n' := by
  intro x hx
  refine le_trans hx (integral_mono (hint x) (hint' x) fun ω => ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun t ht => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp ht) hn))
    fun t _ _ => hr (ω t)

/-- **Approximation source, bound face**: weakening the bound enlarges
the region. -/
theorem returnGESet_anti_bound {r : S → ℝ} {b b' : ℝ} {n : ℕ}
    (hb : b' ≤ b) :
    returnGESet K r b n ⊆ returnGESet K r b' n :=
  fun _x hx => le_trans hb hx

/-- **The return former's directed square at the coupled judgment**,
one instance of the template over the reward face: the model class
compiled against the under-approximating reward is contained in the
dominating reward's class.  `sound` only. -/
theorem returnGEAtom_modelClass_mono_reward {r r' : S → ℝ} {b : ℝ}
    {n : ℕ} (hr : ∀ s, r s ≤ r' s)
    (hint : ∀ x, Integrable (finReturn r n) (pathMeasure K x))
    (hint' : ∀ x, Integrable (finReturn r' n) (pathMeasure K x)) :
    (safetyAtom (returnGESet K r b n)).modelClass ⊆
      (safetyAtom (returnGESet K r' b n)).modelClass :=
  safetyAtom_modelClass_mono
    (returnGESet_mono_reward hr hint hint')

end Return

/-! ## The deadline square

A geometrically decaying Lyapunov certificate (the deadline stock's
hypotheses) produces the behavioral expected-return claim with
indicator reward: reaching the target within the horizon contributes.
Stated at the stock's own generality — an abstract filtered probability
space — which is where the certificate's conditional-drift data lives;
the specialization to the kernel path measure is a separate (named)
stratum, not a hidden premise. -/

section Deadline

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {L : ℕ → Ω → ℝ} {X : ℕ → Ω → S} {B : Set S}
  {β a : ℝ}

/-- The indicator sum dominates the hit indicator: if some tick in the
window lands in `B`, the accumulated indicator reward is at least
one. -/
theorem hitProb_real_le_integral_indicatorSum [IsFiniteMeasure μ]
    (hmB : ∀ k, MeasurableSet[𝒢 k] {ω | X k ω ∈ B}) (n : ℕ) :
    μ.real {ω | ∃ k ≤ n, X k ω ∈ B} ≤
      ∫ ω, finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
        (fun t => X t ω) ∂μ := by
  classical
  set H : Set Ω := {ω | ∃ k ≤ n, X k ω ∈ B} with hH
  have hmeas : ∀ k, MeasurableSet {ω | X k ω ∈ B} :=
    fun k => (𝒢.le k) _ (hmB k)
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Finset.range (n + 1), {ω | X k ω ∈ B} := by
      ext ω
      simp [hH]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ => hmeas k
  -- each indicator term, rewritten over the sample space
  have hterm : ∀ t, (fun ω => (B.indicator fun _ => (1 : ℝ)) (X t ω)) =
      ({ω | X t ω ∈ B}).indicator fun _ => (1 : ℝ) := by
    intro t
    funext ω
    by_cases h : X t ω ∈ B <;>
      simp [Set.indicator, h]
  have hintTerm : ∀ t, Integrable
      (fun ω => (B.indicator fun _ => (1 : ℝ)) (X t ω)) μ := by
    intro t
    rw [hterm t]
    exact (integrable_const (1 : ℝ)).indicator (hmeas t)
  have hintSum : Integrable
      (fun ω => finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
        (fun t => X t ω)) μ := by
    have : (fun ω => finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
        (fun t => X t ω)) =
        fun ω => ∑ t ∈ Finset.range (n + 1),
          (B.indicator fun _ => (1 : ℝ)) (X t ω) := rfl
    rw [this]
    exact integrable_finsetSum _ fun t _ => hintTerm t
  -- pointwise: the hit indicator is dominated by the indicator sum
  have hpt : ∀ ω, H.indicator (fun _ => (1 : ℝ)) ω ≤
      finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
        (fun t => X t ω) := by
    intro ω
    by_cases hω : ω ∈ H
    · have hind : H.indicator (fun _ => (1 : ℝ)) ω = 1 :=
        Set.indicator_of_mem hω _
      obtain ⟨k, hk, hkB⟩ := hω
      have hk' : k ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      have hone : (B.indicator fun _ => (1 : ℝ)) (X k ω) = 1 :=
        Set.indicator_of_mem hkB _
      have hnonneg : ∀ t ∈ Finset.range (n + 1),
          0 ≤ (B.indicator fun _ => (1 : ℝ)) (X t ω) := by
        intro t _
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      calc H.indicator (fun _ => (1 : ℝ)) ω = 1 := hind
        _ = (B.indicator fun _ => (1 : ℝ)) (X k ω) := hone.symm
        _ ≤ ∑ t ∈ Finset.range (n + 1),
              (B.indicator fun _ => (1 : ℝ)) (X t ω) :=
            Finset.single_le_sum hnonneg hk'
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun t _ =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
  calc μ.real H = ∫ ω, H.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        rw [integral_indicator_const (1 : ℝ) hHmeas, smul_eq_mul,
          mul_one, measureReal_def]
    _ ≤ ∫ ω, finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
          (fun t => X t ω) ∂μ :=
        integral_mono ((integrable_const (1 : ℝ)).indicator hHmeas)
          hintSum hpt

/-- **The deadline square** (directed; lower/GE face).  A geometrically
decaying Lyapunov certificate — conditional drift `≤ β·L` off the
target, barrier `a` off the target — produces the behavioral
expected-return claim with indicator reward at horizon `n + 1` ticks
and bound `1 − βⁿ·(∫L₀)/a`.  Direction: certificate → community claim;
the approximation sources are the tail bound itself and the
indicator-sum domination of the hit indicator.  No converse is stated:
the certificate can be arbitrarily loose. -/
theorem returnGE_sound_of_deadline [IsProbabilityMeasure μ]
    (hβ : 0 ≤ β) (ha : 0 < a)
    (hint : ∀ n, Integrable (L n) μ) (hnonneg : 0 ≤ L)
    (hmB : ∀ n, MeasurableSet[𝒢 n] {ω | X n ω ∈ B})
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, X n ω ∉ B →
      (μ[L (n + 1) | 𝒢 n]) ω ≤ β * L n ω)
    (hbarrier : ∀ n ω, X n ω ∉ B → a ≤ L n ω) (n : ℕ) :
    1 - β ^ n * (∫ ω, L 0 ω ∂μ) / a ≤
      ∫ ω, finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
        (fun t => X t ω) ∂μ := by
  classical
  have hmeas : ∀ k, MeasurableSet {ω | X k ω ∈ B} :=
    fun k => (𝒢.le k) _ (hmB k)
  set H : Set Ω := {ω | ∃ k ≤ n, X k ω ∈ B} with hH
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Finset.range (n + 1), {ω | X k ω ∈ B} := by
      ext ω
      simp [hH]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ => hmeas k
  have hcompl : Hᶜ = {ω | ∀ k ≤ n, X k ω ∉ B} := by
    ext ω
    simp [hH]
  -- the tail bound, converted to the real line
  have hV0 : 0 ≤ ∫ ω, L 0 ω ∂μ :=
    integral_nonneg fun ω => hnonneg 0 ω
  have hnum : 0 ≤ β ^ n * ∫ ω, L 0 ω ∂μ :=
    mul_nonneg (pow_nonneg hβ n) hV0
  have htail : μ Hᶜ ≤
      ENNReal.ofReal (β ^ n * ∫ ω, L 0 ω ∂μ) / ENNReal.ofReal a := by
    rw [hcompl]
    exact Qtsl.Deadline.deadline_tail_div hβ hint hnonneg hmB hdrift ha
      hbarrier n
  have htailR : μ.real Hᶜ ≤ β ^ n * (∫ ω, L 0 ω ∂μ) / a := by
    have hne : ENNReal.ofReal (β ^ n * ∫ ω, L 0 ω ∂μ) /
        ENNReal.ofReal a ≠ ⊤ := by
      exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
        (ENNReal.ofReal_pos.mpr ha).ne'
    have := ENNReal.toReal_mono hne htail
    rwa [ENNReal.toReal_div, ENNReal.toReal_ofReal hnum,
      ENNReal.toReal_ofReal ha.le] at this
  have hsplit : μ.real H = 1 - μ.real Hᶜ := by
    have := measureReal_compl (μ := μ) hHmeas
    rw [probReal_univ] at this
    linarith
  calc 1 - β ^ n * (∫ ω, L 0 ω ∂μ) / a
      ≤ 1 - μ.real Hᶜ := by linarith
    _ = μ.real H := hsplit.symm
    _ ≤ ∫ ω, finReturn (B.indicator fun _ => (1 : ℝ)) (n + 1)
          (fun t => X t ω) ∂μ :=
        hitProb_real_le_integral_indicatorSum hmB n

end Deadline

/-! ## The discounted square

A geometric-drift certificate bounds the discounted expected return
from above, uniformly in the horizon — the upper (LE) face of the
discounted-return former.  The rate enters as the discount `γ`; the
drift factor `β` may exceed one so long as `γ·β < 1` (the spectral
condition). -/

section Discounted

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {L : ℕ → Ω → ℝ} {β : ℝ}

/-- Iterated drift: an unconditional geometric conditional drift bounds
every marginal expectation by the geometrically discounted initial
one.  (The survival-restricted engine at the empty target set.) -/
theorem integral_le_pow_mul [IsFiniteMeasure μ] (hβ : 0 ≤ β)
    (hint : ∀ n, Integrable (L n) μ) (hnonneg : 0 ≤ L)
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, (μ[L (n + 1) | 𝒢 n]) ω ≤ β * L n ω)
    (n : ℕ) :
    ∫ ω, L n ω ∂μ ≤ β ^ n * ∫ ω, L 0 ω ∂μ := by
  have h := Qtsl.Deadline.setIntegral_survival_le (μ := μ) (𝒢 := 𝒢)
    (V := L) (X := fun _ ω => ω) (B := (∅ : Set Ω)) hβ hint hnonneg
    (fun k => by
      -- `simpa` (not `simp` + `exact`): the goal's set rewrites to `∅`,
      -- but a bare `MeasurableSet.empty` elaborates at the ambient
      -- σ-algebra; the ascribed `simpa` keeps the filtration instance.
      simpa using (MeasurableSet.empty :
        MeasurableSet[𝒢 k] (∅ : Set Ω)))
    (fun k => by
      filter_upwards [hdrift k] with ω hω
      exact fun _ => hω)
    n
  have huniv : {ω : Ω | ∀ k < n, (fun _ ω => ω) k ω ∉ (∅ : Set Ω)} =
      Set.univ :=
    Set.eq_univ_of_forall fun ω k _ => Set.notMem_empty ω
  rwa [huniv, setIntegral_univ] at h

/-- The discounted partial return: per-tick rewards, geometrically
discounted, accumulated over `n` ticks. -/
def discountedPartialReturn (γ : ℝ) (r : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, γ ^ t * r t ω

/-- **The discounted square** (directed; upper/LE face).  A geometric
conditional-drift certificate `L` dominating the reward bounds the
discounted expected return by the spectral geometric sum.  Direction:
certificate → community claim. -/
theorem discountedReturn_le_of_drift [IsFiniteMeasure μ]
    {γ : ℝ} {r : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hint : ∀ n, Integrable (L n) μ) (hnonneg : 0 ≤ L)
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, (μ[L (n + 1) | 𝒢 n]) ω ≤ β * L n ω)
    (hrint : ∀ n, Integrable (r n) μ)
    (hr : ∀ n ω, r n ω ≤ L n ω) (n : ℕ) :
    ∫ ω, discountedPartialReturn γ r n ω ∂μ ≤
      (∑ t ∈ Finset.range n, (γ * β) ^ t) * ∫ ω, L 0 ω ∂μ := by
  have hterm : ∀ t, Integrable (fun ω => γ ^ t * r t ω) μ :=
    fun t => (hrint t).const_mul _
  have hsum : ∫ ω, discountedPartialReturn γ r n ω ∂μ =
      ∑ t ∈ Finset.range n, γ ^ t * ∫ ω, r t ω ∂μ := by
    unfold discountedPartialReturn
    rw [integral_finsetSum _ fun t _ => hterm t]
    exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  have h1 : ∫ ω, r t ω ∂μ ≤ ∫ ω, L t ω ∂μ :=
    integral_mono (hrint t) (hint t) fun ω => hr t ω
  have h2 : ∫ ω, L t ω ∂μ ≤ β ^ t * ∫ ω, L 0 ω ∂μ :=
    integral_le_pow_mul hβ hint hnonneg hdrift t
  calc γ ^ t * ∫ ω, r t ω ∂μ
      ≤ γ ^ t * (β ^ t * ∫ ω, L 0 ω ∂μ) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hγ t)
    _ = (γ * β) ^ t * ∫ ω, L 0 ω ∂μ := by
        rw [mul_pow]; ring

/-- The horizon-uniform corollary at the spectral condition
`γ·β < 1`: the discounted expected return is bounded by
`(1 − γβ)⁻¹ · ∫L₀`, for **every** horizon — the discounted-return
former's upper-face producer bound.  (The infinite-horizon passage is
one monotone-convergence step for nonnegative rewards and is not
claimed here.) -/
theorem discountedReturn_le_of_drift' [IsFiniteMeasure μ]
    {γ : ℝ} {r : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : γ * β < 1)
    (hint : ∀ n, Integrable (L n) μ) (hnonneg : 0 ≤ L)
    (hdrift : ∀ n, ∀ᵐ ω ∂μ, (μ[L (n + 1) | 𝒢 n]) ω ≤ β * L n ω)
    (hrint : ∀ n, Integrable (r n) μ)
    (hr : ∀ n ω, r n ω ≤ L n ω) (n : ℕ) :
    ∫ ω, discountedPartialReturn γ r n ω ∂μ ≤
      (1 - γ * β)⁻¹ * ∫ ω, L 0 ω ∂μ := by
  have hq : 0 ≤ γ * β := mul_nonneg hγ hβ
  have hlt : 0 < 1 - γ * β := by linarith
  have hV0 : 0 ≤ ∫ ω, L 0 ω ∂μ :=
    integral_nonneg fun ω => hnonneg 0 ω
  refine le_trans
    (discountedReturn_le_of_drift hβ hγ hint hnonneg hdrift hrint hr n)
    (mul_le_mul_of_nonneg_right ?_ hV0)
  -- ∑_{t<n} q^t ≤ (1 - q)⁻¹ for 0 ≤ q < 1
  have hmul : (∑ t ∈ Finset.range n, (γ * β) ^ t) * (1 - γ * β) ≤ 1 := by
    have hgeom := geom_sum_mul (γ * β) n
    have hpow : 0 ≤ (γ * β) ^ n := pow_nonneg hq n
    nlinarith [hgeom, hpow]
  have hdiv : (∑ t ∈ Finset.range n, (γ * β) ^ t) ≤ 1 / (1 - γ * β) :=
    (le_div_iff₀ hlt).mpr hmul
  rw [← one_div]
  exact hdiv

end Discounted

end SuFunctor.Universe

/-! ## Axiom receipts -/

#print axioms SuFunctor.Universe.safeProper_mono
#print axioms SuFunctor.Universe.safetyAtom_modelClass_mono
#print axioms SuFunctor.Universe.satCredal_lower_singletonC_geC
#print axioms SuFunctor.Universe.satCredal_upper_singletonC_leC
#print axioms SuFunctor.Universe.satCredal_upper_rayC_leC
#print axioms SuFunctor.Universe.satCredal_lower_singletonC_zero
#print axioms SuFunctor.Universe.probThresholdSet_mono
#print axioms SuFunctor.Universe.probThresholdSet_anti_threshold
#print axioms SuFunctor.Universe.probThresholdSet_mem_of_le
#print axioms SuFunctor.Universe.sprobAtom_modelClass_mono
#print axioms SuFunctor.Universe.sprob_sound_of_streettBundle
#print axioms SuFunctor.Universe.returnGESet_mono_reward
#print axioms SuFunctor.Universe.returnGESet_mono_horizon
#print axioms SuFunctor.Universe.returnGESet_anti_bound
#print axioms SuFunctor.Universe.returnGEAtom_modelClass_mono_reward
#print axioms SuFunctor.Universe.hitProb_real_le_integral_indicatorSum
#print axioms SuFunctor.Universe.returnGE_sound_of_deadline
#print axioms SuFunctor.Universe.integral_le_pow_mul
#print axioms SuFunctor.Universe.discountedPartialReturn
#print axioms SuFunctor.Universe.discountedReturn_le_of_drift
#print axioms SuFunctor.Universe.discountedReturn_le_of_drift'
