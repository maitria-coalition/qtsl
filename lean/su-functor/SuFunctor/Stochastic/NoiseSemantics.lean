import SuFunctor.Universe.TransportCitizenship
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Noise-port semantics: the probabilistic tier at finite outcome

A probabilistic hypernet is an ordinary hypernet together with a
designated roster of **noise ports** — inputs read as fresh uniform
draws from `[0,1]` — and its denotation is the pushforward of the
uniform reference measure through the deterministic semantics.
Randomness enters at the interface, never at a box: the deterministic
calculus, its wire format, and its digest scheme never learn the
extension exists.

This module mechanizes that semantics at the **finite-outcome
stratum**: deterministic maps (and, for cell-boundary honesty,
relations) from the noise cube into a finite outcome type, denoting
points of the landed flat carrier `Universe.probCarrier`.  The maps
quantified over are arbitrary measurable maps — a superclass of the
piecewise-polynomial maps the calculus denotes (`Qtsl.DenotationClass`
carves that class at the exact-rational stratum; its ℝ-reading rides
the completion statement `PPLC.PrimitiveBasisSound`, which is staged
separately and deliberately not duplicated here).

Main results:

* `noiseCube` — the uniform reference measure on `[0,1]^N`, a
  probability measure.
* `noiseDenotFun`, `noiseDenot` — the pushforward denotation of a
  measurable outcome map, landing in `Universe.ProbState`.
  **Normalization is a theorem, not a constraint**
  (`noiseDenotFun_mem_probCarrier`): every total measurable map
  denotes total mass exactly one.  There is no way to write a
  sub-stochastic object at this tier — which is precisely what the
  measure-weighted tier above it must *deliberately* extend.
* `noiseDenot_comp` — **discard is marginalization**: composing with
  an outcome projection pushes the denotation forward along it
  (`Universe.ProbState.push`, the landed pushforward).
* `copy_ne_fresh`, `copyPair_fst_marginal`, … — the
  **copy-vs-resample separation witness**: sharing one draw between
  two output coordinates and drawing twice independently agree on
  both marginals and differ as joints ("toss a coin and copy it ≠
  toss two coins").  Copy is not natural on stochastic content; the
  two presentations differ in noise arity, so the syntax never
  conflates them.
* `noiseDenot_eq_of_selections` — the **null-boundary singleton
  lemma**: the denotation of a relation (the `cell` semantics is
  possibilistic on shared piece boundaries) is a credal *set* of
  outcomes of tie-break selections; when the ambiguity locus is
  null, that set is a singleton.  `cellRel_selections_agree`
  instantiates it at a two-closed-piece threshold cell, whose
  boundary is a point and hence null: the generic case of a noise
  gate is precise, and the credal codomain degenerates exactly
  there.
-/

namespace SuFunctor.Stochastic

open MeasureTheory SuFunctor.Universe

/-! ## The uniform reference measure -/

/-- The uniform probability measure on `[0,1] ⊆ ℝ`. -/
noncomputable def unitUniform : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unitUniform := by
  constructor
  show (volume : Measure ℝ).restrict (Set.Icc 0 1) Set.univ = 1
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- The uniform reference measure on the noise cube `[0,1]^N`:
independent uniform draws, one per noise port. -/
noncomputable def noiseCube (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ => unitUniform

instance (N : ℕ) : IsProbabilityMeasure (noiseCube N) := by
  unfold noiseCube
  infer_instance

/-- Cylinder sets of the noise cube factor as products. -/
theorem noiseCube_pi (N : ℕ) (t : Fin N → Set ℝ) :
    noiseCube N (Set.univ.pi t) = ∏ i, unitUniform (t i) :=
  Measure.pi_pi _ _

/-! ## The pushforward denotation -/

variable {N : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V]

/-- The raw denotation of an outcome map: the mass the uniform
reference measure pushes onto each outcome. -/
noncomputable def noiseDenotFun (g : (Fin N → ℝ) → V) : V → ℝ :=
  fun v => (noiseCube N (g ⁻¹' {v})).toReal

omit [Fintype V] in
/-- Preimage masses add over finite outcome sets: the preimages of
distinct outcomes are disjoint, and measurability makes the finite
additivity available. -/
theorem noiseCube_preimage_finset (g : (Fin N → ℝ) → V) (hg : Measurable g)
    (s : Finset V) :
    noiseCube N (g ⁻¹' ↑s) = ∑ v ∈ s, noiseCube N (g ⁻¹' {v}) := by
  have hset : g ⁻¹' ↑s = ⋃ v ∈ s, g ⁻¹' {v} := by
    ext u
    simp
  rw [hset]
  refine measure_biUnion_finset ?_ fun v _ => hg (measurableSet_singleton v)
  intro v _ w _ hvw
  refine Set.disjoint_left.mpr fun u hu hu' => hvw ?_
  have h1 : g u = v := hu
  have h2 : g u = w := hu'
  rw [← h1, h2]

/-- **Normalization is a theorem, not a constraint**: the denotation
of a total measurable outcome map has total mass exactly one. -/
theorem sum_noiseDenotFun (g : (Fin N → ℝ) → V) (hg : Measurable g) :
    ∑ v, noiseDenotFun g v = 1 := by
  have h := noiseCube_preimage_finset g hg Finset.univ
  have huniv : g ⁻¹' ↑(Finset.univ : Finset V) = Set.univ := by
    ext u
    simp
  rw [huniv, measure_univ] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum fun v _ => measure_ne_top _ _] at h'
  simpa [noiseDenotFun] using h'.symm

/-- The denotation of a total measurable outcome map lies in the flat
carrier: nonnegative coordinates, mass exactly one.  Sub-stochastic
content is unwritable at this tier. -/
theorem noiseDenotFun_mem_probCarrier (g : (Fin N → ℝ) → V)
    (hg : Measurable g) : noiseDenotFun g ∈ probCarrier V :=
  ⟨fun _ => ENNReal.toReal_nonneg, sum_noiseDenotFun g hg⟩

/-- The denotation of a measurable outcome map, as a point of the flat
carrier: the pushforward of the uniform reference measure through the
deterministic semantics. -/
noncomputable def noiseDenot (g : (Fin N → ℝ) → V) (hg : Measurable g) :
    ProbState V :=
  ⟨noiseDenotFun g, noiseDenotFun_mem_probCarrier g hg⟩

@[simp] theorem noiseDenot_coe (g : (Fin N → ℝ) → V) (hg : Measurable g) :
    ((noiseDenot g hg : ProbState V) : V → ℝ) = noiseDenotFun g := rfl

/-- The denotation depends only on the map (the measurability proof is
proof-irrelevant). -/
theorem noiseDenot_congr {g g' : (Fin N → ℝ) → V} (h : g = g')
    (hg : Measurable g) (hg' : Measurable g') :
    noiseDenot g hg = noiseDenot g' hg' := by
  subst h
  rfl

/-! ## Discard is marginalization -/

variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- **Discard is marginalization**: post-composing the outcome map with
a projection pushes the denotation forward along it.  Deleting (or not
exposing) an output coordinate of a probabilistic hypernet
marginalizes its kernel — the Markov-category discard, semantically
natural. -/
theorem noiseDenot_comp (g : (Fin N → ℝ) → V) (π : V → W)
    (hg : Measurable g) (hπg : Measurable (π ∘ g)) :
    noiseDenot (π ∘ g) hπg = ProbState.push π (noiseDenot g hg) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  rw [ProbState.push_coe, noiseDenot_coe, noiseDenot_coe]
  show (noiseCube N ((π ∘ g) ⁻¹' {w})).toReal = pushFun π (noiseDenotFun g) w
  have hset : (π ∘ g) ⁻¹' {w}
      = g ⁻¹' ↑(Finset.univ.filter fun v => π v = w) := by
    ext u
    simp [Function.comp]
  rw [hset, noiseCube_preimage_finset g hg,
    ENNReal.toReal_sum fun v _ => measure_ne_top _ _]
  show ∑ v ∈ Finset.univ.filter fun v => π v = w, noiseDenotFun g v
    = pushFun π (noiseDenotFun g) w
  rw [Finset.sum_filter]
  rfl

/-! ## The copy-vs-resample separation witness

"Toss a coin and copy it" and "toss two coins" have the same marginals
and different joints.  Sharing is an explicit copy of one noise draw;
independence is a second noise port; the two are different
presentations — different noise arity, hence different rosters and
digests — and the semantics separates them, so copy-naturality on
stochastic content fails semantically while never being conflated
syntactically. -/

/-- A fair threshold bit of one uniform draw. -/
noncomputable def bit (u : ℝ) : Bool := decide (u < 2⁻¹)

theorem bit_eq_true_iff {u : ℝ} : bit u = true ↔ u < 2⁻¹ :=
  decide_eq_true_iff

theorem bit_eq_false_iff {u : ℝ} : bit u = false ↔ ¬u < 2⁻¹ := by
  rw [← Bool.not_eq_true, bit_eq_true_iff]

theorem measurable_bit : Measurable bit := by
  have h : bit = fun u => if u < (2⁻¹ : ℝ) then true else false := by
    funext u
    by_cases hu : u < (2⁻¹ : ℝ) <;> simp [bit, hu]
  rw [h]
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_bitProj {N : ℕ} (i : Fin N) :
    Measurable fun u : Fin N → ℝ => bit (u i) :=
  measurable_bit.comp (measurable_pi_apply i)

/-- The fair Bernoulli state: mass `1/2` on each outcome. -/
noncomputable def bern : ProbState Bool :=
  ⟨fun _ => 2⁻¹, fun _ => by norm_num, by rw [Fintype.sum_bool]; norm_num⟩

/-- Uniform mass below the threshold. -/
theorem unitUniform_Iio_half :
    unitUniform (Set.Iio (2⁻¹ : ℝ)) = ENNReal.ofReal 2⁻¹ := by
  unfold unitUniform
  rw [Measure.restrict_apply measurableSet_Iio]
  have h : Set.Iio (2⁻¹ : ℝ) ∩ Set.Icc 0 1 = Set.Ico 0 2⁻¹ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [h, Real.volume_Ico]
  norm_num

/-- Uniform mass at or above the threshold. -/
theorem unitUniform_Ici_half :
    unitUniform (Set.Ici (2⁻¹ : ℝ)) = ENNReal.ofReal 2⁻¹ := by
  unfold unitUniform
  rw [Measure.restrict_apply measurableSet_Ici]
  have h : Set.Ici (2⁻¹ : ℝ) ∩ Set.Icc 0 1 = Set.Icc 2⁻¹ 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith, h2⟩
  rw [h, Real.volume_Icc]
  norm_num

/-- Points carry no uniform mass. -/
theorem unitUniform_singleton (x : ℝ) : unitUniform {x} = 0 := by
  unfold unitUniform
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

/-- A single threshold bit of any one coordinate denotes the fair
Bernoulli state, at every noise arity: the marginal law of one shared
draw and of one fresh draw agree. -/
theorem noiseDenot_bitProj {N : ℕ} (i : Fin N) :
    noiseDenot (fun u => bit (u i)) (measurable_bitProj i) = bern := by
  classical
  refine Subtype.ext (funext fun b => ?_)
  rw [noiseDenot_coe]
  show (noiseCube N ((fun u : Fin N → ℝ => bit (u i)) ⁻¹' {b})).toReal = 2⁻¹
  cases b
  · have hset : ((fun u : Fin N → ℝ => bit (u i)) ⁻¹' {false})
        = Set.univ.pi fun j =>
            if j = i then Set.Ici (2⁻¹ : ℝ) else Set.univ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
      constructor
      · intro h j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl]
          exact Set.mem_Ici.mpr (not_lt.mp (bit_eq_false_iff.mp h))
        · rw [if_neg hj]
          exact Set.mem_univ _
      · intro h
        have hi := h i
        rw [if_pos rfl] at hi
        exact bit_eq_false_iff.mpr (not_lt.mpr (Set.mem_Ici.mp hi))
    rw [hset, noiseCube_pi,
      Finset.prod_eq_single i
        (fun j _ hj => by rw [if_neg hj]; exact measure_univ)
        (fun h => absurd (Finset.mem_univ i) h),
      if_pos rfl, unitUniform_Ici_half,
      ENNReal.toReal_ofReal (by norm_num)]
  · have hset : ((fun u : Fin N → ℝ => bit (u i)) ⁻¹' {true})
        = Set.univ.pi fun j =>
            if j = i then Set.Iio (2⁻¹ : ℝ) else Set.univ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
      constructor
      · intro h j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl]
          exact Set.mem_Iio.mpr (bit_eq_true_iff.mp h)
        · rw [if_neg hj]
          exact Set.mem_univ _
      · intro h
        have hi := h i
        rw [if_pos rfl] at hi
        exact bit_eq_true_iff.mpr (Set.mem_Iio.mp hi)
    rw [hset, noiseCube_pi,
      Finset.prod_eq_single i
        (fun j _ hj => by rw [if_neg hj]; exact measure_univ)
        (fun h => absurd (Finset.mem_univ i) h),
      if_pos rfl, unitUniform_Iio_half,
      ENNReal.toReal_ofReal (by norm_num)]

/-- One draw, copied to both coordinates: sharing. -/
noncomputable def copyPair (u : Fin 1 → ℝ) : Bool × Bool :=
  (bit (u 0), bit (u 0))

/-- Two independent draws, one per coordinate: resampling. -/
noncomputable def freshPair (u : Fin 2 → ℝ) : Bool × Bool :=
  (bit (u 0), bit (u 1))

theorem measurable_copyPair : Measurable copyPair :=
  (measurable_bitProj (0 : Fin 1)).prodMk (measurable_bitProj (0 : Fin 1))

theorem measurable_freshPair : Measurable freshPair :=
  (measurable_bitProj (0 : Fin 2)).prodMk (measurable_bitProj (1 : Fin 2))

theorem copyPair_preimage_tf : copyPair ⁻¹' {(true, false)} = ∅ := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, copyPair,
    Prod.mk.injEq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem freshPair_preimage_tf :
    freshPair ⁻¹' {(true, false)}
      = Set.univ.pi fun j : Fin 2 =>
          if j = 0 then Set.Iio (2⁻¹ : ℝ) else Set.Ici (2⁻¹ : ℝ) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, freshPair,
    Prod.mk.injEq, Set.mem_univ_pi, Fin.forall_fin_two]
  simp [bit_eq_true_iff, bit_eq_false_iff, not_lt]

/-- The shared-draw joint puts no mass on disagreement. -/
theorem noiseDenot_copyPair_tf :
    (noiseDenot copyPair measurable_copyPair : Bool × Bool → ℝ)
      (true, false) = 0 := by
  rw [noiseDenot_coe]
  show (noiseCube 1 (copyPair ⁻¹' {(true, false)})).toReal = 0
  rw [copyPair_preimage_tf]
  simp

/-- The fresh-draw joint puts mass `1/4` on each outcome pair. -/
theorem noiseDenot_freshPair_tf :
    (noiseDenot freshPair measurable_freshPair : Bool × Bool → ℝ)
      (true, false) = 4⁻¹ := by
  rw [noiseDenot_coe]
  show (noiseCube 2 (freshPair ⁻¹' {(true, false)})).toReal = 4⁻¹
  rw [freshPair_preimage_tf, noiseCube_pi, Fin.prod_univ_two,
    if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0),
    unitUniform_Iio_half, unitUniform_Ici_half,
    ← ENNReal.ofReal_mul (by norm_num)]
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- **Copy is sharing, never resampling**: the joint of one copied
draw differs from the joint of two fresh draws.  The separation
witness for the failure of copy-naturality on stochastic content. -/
theorem copy_ne_fresh :
    noiseDenot copyPair measurable_copyPair
      ≠ noiseDenot freshPair measurable_freshPair := by
  intro h
  have := congrFun (congrArg Subtype.val h) (true, false)
  rw [noiseDenot_copyPair_tf, noiseDenot_freshPair_tf] at this
  norm_num at this

/-- The first marginal of the shared-draw joint is the fair
Bernoulli state. -/
theorem copyPair_fst_marginal :
    ProbState.push Prod.fst (noiseDenot copyPair measurable_copyPair)
      = bern := by
  rw [← noiseDenot_comp copyPair Prod.fst measurable_copyPair
    (measurable_fst.comp measurable_copyPair)]
  exact noiseDenot_bitProj 0

/-- The second marginal of the shared-draw joint is the fair
Bernoulli state. -/
theorem copyPair_snd_marginal :
    ProbState.push Prod.snd (noiseDenot copyPair measurable_copyPair)
      = bern := by
  rw [← noiseDenot_comp copyPair Prod.snd measurable_copyPair
    (measurable_snd.comp measurable_copyPair)]
  exact noiseDenot_bitProj 0

/-- The first marginal of the fresh-draw joint is the fair Bernoulli
state — equal to the shared-draw marginal, though the joints differ. -/
theorem freshPair_fst_marginal :
    ProbState.push Prod.fst (noiseDenot freshPair measurable_freshPair)
      = bern := by
  rw [← noiseDenot_comp freshPair Prod.fst measurable_freshPair
    (measurable_fst.comp measurable_freshPair)]
  exact noiseDenot_bitProj 0

/-- The second marginal of the fresh-draw joint is the fair Bernoulli
state. -/
theorem freshPair_snd_marginal :
    ProbState.push Prod.snd (noiseDenot freshPair measurable_freshPair)
      = bern := by
  rw [← noiseDenot_comp freshPair Prod.snd measurable_freshPair
    (measurable_snd.comp measurable_freshPair)]
  exact noiseDenot_bitProj 1

/-! ## The null-boundary singleton lemma

The `cell` semantics is possibilistic on shared piece boundaries, so a
noise gate denotes, in full honesty, the *set* of pushforwards ranging
over admissible tie-break selections — a credal body.  When the
ambiguity locus is null, the body is a singleton: the precise case is
the generic special case of the credal codomain, not a separate
semantics. -/

/-- The ambiguity locus of a relation: noise points where at least two
distinct outcomes are admissible. -/
def ambiguousLocus (R : Set ((Fin N → ℝ) × V)) : Set (Fin N → ℝ) :=
  {u | ∃ v w, v ≠ w ∧ (u, v) ∈ R ∧ (u, w) ∈ R}

/-- A selection of a relation: a total tie-breaking choice of
admissible outcomes. -/
def IsSelection (R : Set ((Fin N → ℝ) × V)) (g : (Fin N → ℝ) → V) : Prop :=
  ∀ u, (u, g u) ∈ R

/-- **The null-boundary singleton lemma**: when the ambiguity locus of
a relation is null, all measurable selections denote the same state —
the credal body of admissible tie-breaks is a singleton. -/
theorem noiseDenot_eq_of_selections (R : Set ((Fin N → ℝ) × V))
    {g₁ g₂ : (Fin N → ℝ) → V}
    (hnull : noiseCube N (ambiguousLocus R) = 0)
    (hs₁ : IsSelection R g₁) (hs₂ : IsSelection R g₂)
    (h₁ : Measurable g₁) (h₂ : Measurable g₂) :
    noiseDenot g₁ h₁ = noiseDenot g₂ h₂ := by
  have hsub : {u | g₁ u ≠ g₂ u} ⊆ ambiguousLocus R := fun u hu =>
    ⟨g₁ u, g₂ u, hu, hs₁ u, hs₂ u⟩
  have hne : noiseCube N {u | g₁ u ≠ g₂ u} = 0 :=
    measure_mono_null hsub hnull
  refine Subtype.ext (funext fun v => ?_)
  rw [noiseDenot_coe, noiseDenot_coe]
  show (noiseCube N (g₁ ⁻¹' {v})).toReal = (noiseCube N (g₂ ⁻¹' {v})).toReal
  congr 1
  apply measure_congr
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun u hu => ?_) hne
    intro heq
    exact hu.2 (by rw [Set.mem_preimage, Set.mem_singleton_iff, ← heq]
                   exact hu.1)
  · refine measure_mono_null (fun u hu => ?_) hne
    intro heq
    exact hu.2 (by rw [Set.mem_preimage, Set.mem_singleton_iff, heq]
                   exact hu.1)

/-- A two-closed-piece threshold cell, as a relation: `true` on
`u ≤ 1/2`, `false` on `1/2 ≤ u`, both admissible on the shared
boundary — the relational denotation shape of one `cell` against a
polynomial threshold. -/
def cellRel : Set ((Fin 1 → ℝ) × Bool) :=
  {p | (p.2 = true ∧ p.1 0 ≤ 2⁻¹) ∨ (p.2 = false ∧ (2⁻¹ : ℝ) ≤ p.1 0)}

/-- The ambiguity locus of the threshold cell is exactly the shared
piece boundary. -/
theorem ambiguousLocus_cellRel :
    ambiguousLocus cellRel = {u | u 0 = (2⁻¹ : ℝ)} := by
  ext u
  simp only [ambiguousLocus, cellRel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, w, hvw, hv, hw⟩
    rcases hv with ⟨hv, h1⟩ | ⟨hv, h1⟩ <;>
      rcases hw with ⟨hw, h2⟩ | ⟨hw, h2⟩
    · exact absurd (hv.trans hw.symm) hvw
    · exact le_antisymm h1 h2
    · exact le_antisymm h2 h1
    · exact absurd (hv.trans hw.symm) hvw
  · intro h
    exact ⟨true, false, by decide, Or.inl ⟨rfl, h.le⟩, Or.inr ⟨rfl, h.ge⟩⟩

/-- Piece boundaries of polynomial thresholds are null under the
uniform reference measure: the boundary-nonatomicity condition, at the
witness cell. -/
theorem noiseCube_ambiguousLocus_cellRel :
    noiseCube 1 (ambiguousLocus cellRel) = 0 := by
  rw [ambiguousLocus_cellRel]
  have hset : {u : Fin 1 → ℝ | u 0 = (2⁻¹ : ℝ)}
      = Set.univ.pi fun _ : Fin 1 => ({(2⁻¹ : ℝ)} : Set ℝ) := by
    ext u
    simp [Fin.forall_fin_one]
  rw [hset, noiseCube_pi, Fin.prod_univ_one, unitUniform_singleton]

/-- At the threshold cell, every pair of measurable tie-break
selections denotes the same state: the credal body is a singleton
because the boundary is null. -/
theorem cellRel_selections_agree {g₁ g₂ : (Fin 1 → ℝ) → Bool}
    (hs₁ : IsSelection cellRel g₁) (hs₂ : IsSelection cellRel g₂)
    (h₁ : Measurable g₁) (h₂ : Measurable g₂) :
    noiseDenot g₁ h₁ = noiseDenot g₂ h₂ :=
  noiseDenot_eq_of_selections cellRel noiseCube_ambiguousLocus_cellRel
    hs₁ hs₂ h₁ h₂

end SuFunctor.Stochastic

#print axioms SuFunctor.Stochastic.sum_noiseDenotFun
#print axioms SuFunctor.Stochastic.noiseDenotFun_mem_probCarrier
#print axioms SuFunctor.Stochastic.noiseDenot_comp
#print axioms SuFunctor.Stochastic.copy_ne_fresh
#print axioms SuFunctor.Stochastic.copyPair_fst_marginal
#print axioms SuFunctor.Stochastic.freshPair_fst_marginal
#print axioms SuFunctor.Stochastic.noiseDenot_eq_of_selections
#print axioms SuFunctor.Stochastic.cellRel_selections_agree
