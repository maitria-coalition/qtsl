import SuFunctor.Universe.General.ClosureGeneral
import Mathlib.Topology.Semicontinuity.Lindelof
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # The generation theorem at the general carrier: gamble rows see
the whole universe

The finite storey pins the universe to certificate-shaped data twice:
rational threshold rows on coordinates see the whole probability face
(`SuFunctor.Universe.Generation.iSup_boxRows_eq_self`), and quadratic
gambles see the whole compact finite-dimensional subprobability carrier
(`SuFunctor.Universe.Tents.iSup_tents_eq_self`).  Both witness species
are finite-dimensional artifacts: coordinates and squared Euclidean
distance read the carrier through a basis that a general outcome space
does not have.  What survives at full generality is the **gamble row**:

* an **atom** `gambleAtomSet ι g a b` is a rational interval constraint
  `a < ∫ g dν < b` on the expectation of one bounded continuous
  nonnegative gamble `g : X →ᵇ ℝ≥0` — precisely a sub-basic open of the
  narrow topology, which is *defined* by these reads;
* a **row** `gambleRow ι c F` is a height `c` on a finite menu
  `F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)` of atoms (a basic open), `0` off it.

The row species keeps the certificate-shaped reading: height and
thresholds are rational data, exactly as in the finite storey's box
rows, whose coordinate reads `μ ↦ μ v` are the special case
`g = 𝟙_{v}` on a finite discrete carrier.  **Localic reading**: the
atoms are the generators of the frame of the carrier — the pullbacks of
the rational-interval generators of `O(ℝ≥0)` along the gamble reads
that present the weak topology as an initial topology — and a row is a
finite meet of generators with a rational grade.  The generation
theorem says every lsc penalty is a join of rational-graded finite
meets of frame generators; the full frame-side (point-free) statement
is deliberately not attempted here — the pointfree package carries that
storey.

Everything is proved once over an **inducing presentation**
`ι : Y → FiniteMeasure X` of an arbitrary carrier `Y` and instantiated
twice, on probability directions (`Penalty X`, the box-rows sibling)
and on the general subprobability carrier (`StatePenalty X`, the tents
sibling):

* `iSup_gambleRows_eq_self` — **directed generation, unconditional**:
  every lsc penalty is the pointwise supremum of its gamble-row
  minorants.  No countability, no metrizability, no compactness: the
  layer-cake argument runs on the initial-topology basis alone
  (`exists_gambleRowSet_subset` replaces the finite storey's metric
  balls).
* `exists_countable_gambleRows_eq_self` — **countable generation**
  under `SecondCountableTopology Y`: a countable set of rows suffices,
  by Bourbaki's countable-envelope theorem for semicontinuous functions
  on hereditarily Lindelöf spaces
  (`exists_countable_lowerSemicontinuous_isLUB`).
* `secondCountableTopology_probabilityMeasure` — the hypothesis
  discharged over a compact metrizable Borel outcome space: Prokhorov
  compactness of `ProbabilityMeasure X` plus Lévy–Prokhorov
  metrizability make the carrier compact metric, hence second
  countable.

**Honest residue, stated exactly.**  For a *noncompact* separable
metrizable outcome space mathlib currently provides metrizability of
`ProbabilityMeasure X` (Lévy–Prokhorov) but no separability instance,
so the countable theorem's hypothesis is carried honestly rather than
discharged; and the subprobability carrier's metrizability is
mechanized in the house pointfree package (dagger chart), which
su-functor does not import — its second-countability supply is likewise
left as hypothesis.  The directed theorem needs none of this.
-/

namespace SuFunctor.Universe.General

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-! ## Scaled indicators over an arbitrary carrier -/

section ScaledIndicator

variable {Y : Type*}

open Classical in
/-- The scaled indicator penalty: `c` on `S`, `0` off it. -/
noncomputable def scaledIndicator (c : ℝ≥0∞) (S : Set Y) : Y → ℝ≥0∞ :=
  fun ν => if ν ∈ S then c else 0

theorem scaledIndicator_apply_of_mem {c : ℝ≥0∞} {S : Set Y} {ν : Y}
    (h : ν ∈ S) : scaledIndicator c S ν = c := by
  simp [scaledIndicator, h]

theorem scaledIndicator_apply_of_not_mem {c : ℝ≥0∞} {S : Set Y} {ν : Y}
    (h : ν ∉ S) : scaledIndicator c S ν = 0 := by
  simp [scaledIndicator, h]

/-- Scaled indicators of open sets are citizens — over any carrier. -/
theorem lowerSemicontinuous_scaledIndicator [TopologicalSpace Y] {c : ℝ≥0∞}
    {S : Set Y} (hS : IsOpen S) :
    LowerSemicontinuous (scaledIndicator c S) := by
  intro ν y hy
  by_cases hν : ν ∈ S
  · filter_upwards [hS.mem_nhds hν] with ρ hρ
    rw [scaledIndicator_apply_of_mem hρ]
    rw [scaledIndicator_apply_of_mem hν] at hy
    exact hy
  · rw [scaledIndicator_apply_of_not_mem hν] at hy
    exact absurd hy (not_lt.mpr zero_le)

end ScaledIndicator

/-! ## Gamble atoms and rows over an inducing presentation -/

section Engine

variable {Y : Type*} [TopologicalSpace Y]

/-- The gamble-read profile of a presented carrier: every state, read
through all its expectations of bounded continuous nonnegative
gambles.  The narrow topology is the initial topology of exactly this
map. -/
noncomputable def testProfile (ι : Y → FiniteMeasure X) : Y → (X →ᵇ ℝ≥0) → ℝ≥0 :=
  fun ν g => (ι ν).testAgainstNN g

/-- A **gamble atom**: the states whose expectation of the gamble `g`
lies strictly between the rational thresholds `a` and `b` — a sub-basic
open of the narrow topology.  (Thresholds compare in `ℝ`, so a negative
lower threshold lawfully denotes "no lower constraint".) -/
def gambleAtomSet (ι : Y → FiniteMeasure X) (g : X →ᵇ ℝ≥0) (a b : ℚ) :
    Set Y :=
  {ν | (a : ℝ) < ((ι ν).testAgainstNN g : ℝ)
    ∧ ((ι ν).testAgainstNN g : ℝ) < (b : ℝ)}

theorem isOpen_gambleAtomSet {ι : Y → FiniteMeasure X} (hι : Continuous ι)
    (g : X →ᵇ ℝ≥0) (a b : ℚ) : IsOpen (gambleAtomSet ι g a b) := by
  have hcont : Continuous fun ν : Y => ((ι ν).testAgainstNN g : ℝ) :=
    NNReal.continuous_coe.comp
      ((FiniteMeasure.continuous_testAgainstNN_eval g).comp hι)
  have hrepr : gambleAtomSet ι g a b
      = {ν : Y | (a : ℝ) < ((ι ν).testAgainstNN g : ℝ)}
        ∩ {ν : Y | ((ι ν).testAgainstNN g : ℝ) < (b : ℝ)} :=
    Set.setOf_and
  rw [hrepr]
  exact (IsOpen.preimage hcont isOpen_Ioi).inter
    (IsOpen.preimage hcont isOpen_Iio)

/-- A **row set**: the finite menu of gamble constraints, met jointly —
a basic open of the narrow topology. -/
def gambleRowSet (ι : Y → FiniteMeasure X)
    (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) : Set Y :=
  ⋂ p ∈ F, gambleAtomSet ι p.1 p.2.1 p.2.2

theorem isOpen_gambleRowSet {ι : Y → FiniteMeasure X} (hι : Continuous ι)
    (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) : IsOpen (gambleRowSet ι F) :=
  isOpen_biInter_finset fun p _ => isOpen_gambleAtomSet hι p.1 p.2.1 p.2.2

/-- A **gamble row**: rational height on a finite menu of gamble
constraints, `0` off it — the certificate-shaped generator. -/
noncomputable def gambleRow (ι : Y → FiniteMeasure X) (c : ℝ≥0∞)
    (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) : Y → ℝ≥0∞ :=
  scaledIndicator c (gambleRowSet ι F)

theorem lowerSemicontinuous_gambleRow {ι : Y → FiniteMeasure X}
    (hι : Continuous ι) (c : ℝ≥0∞) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) :
    LowerSemicontinuous (gambleRow ι c F) :=
  lowerSemicontinuous_scaledIndicator (isOpen_gambleRowSet hι F)

/-! ## The presented carrier reads its topology off the profile -/

/-- The profile of an inducing presentation is inducing: the carrier's
topology is the initial topology of its gamble reads.  (The two
downstream hops are mathlib's own definitions: the weak topology on
finite measures is induced from the weak dual, whose topology is
induced from the product.) -/
theorem isInducing_testProfile {ι : Y → FiniteMeasure X}
    (hι : Topology.IsInducing ι) : Topology.IsInducing (testProfile ι) := by
  have h2 : Topology.IsInducing (FiniteMeasure.toWeakDualBCNN :
      FiniteMeasure X → WeakDual ℝ≥0 (X →ᵇ ℝ≥0)) := ⟨rfl⟩
  have h3 : Topology.IsInducing (fun (ψ : WeakDual ℝ≥0 (X →ᵇ ℝ≥0))
      (g : X →ᵇ ℝ≥0) => ψ g) := ⟨rfl⟩
  have hfe : testProfile ι
      = (fun (ψ : WeakDual ℝ≥0 (X →ᵇ ℝ≥0)) (g : X →ᵇ ℝ≥0) => ψ g)
        ∘ (FiniteMeasure.toWeakDualBCNN ∘ ι) := by
    funext ν g
    exact (FiniteMeasure.toWeakDualBCNN_apply _ _).symm
  rw [hfe]
  exact (h3.comp h2).comp hι

/-- **The basis lemma**: on a presented carrier, every open
neighborhood contains a gamble-row neighborhood with rational
thresholds — the finite storey's rational box inside a metric ball,
rebuilt on the initial topology alone. -/
theorem exists_gambleRowSet_subset {ι : Y → FiniteMeasure X}
    (hι : Topology.IsInducing ι) {U : Set Y} (hU : IsOpen U) {ν₀ : Y}
    (hν₀ : ν₀ ∈ U) :
    ∃ F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ),
      ν₀ ∈ gambleRowSet ι F ∧ gambleRowSet ι F ⊆ U := by
  classical
  obtain ⟨W, hW, hWeq⟩ := (isInducing_testProfile hι).isOpen_iff.mp hU
  have hmemW : testProfile ι ν₀ ∈ W := by
    rw [← hWeq] at hν₀
    exact hν₀
  have hnhds : W ∈ 𝓝 (testProfile ι ν₀) := hW.mem_nhds hmemW
  rw [nhds_pi] at hnhds
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hnhds
  -- rational squeeze inside each coordinate neighborhood
  have key : ∀ g : X →ᵇ ℝ≥0, ∃ a b : ℚ,
      ((a : ℝ) < (testProfile ι ν₀ g : ℝ)
        ∧ ((testProfile ι ν₀ g : ℝ≥0) : ℝ) < (b : ℝ))
      ∧ ∀ y : ℝ≥0, (a : ℝ) < (y : ℝ) → (y : ℝ) < (b : ℝ) → y ∈ t g := by
    intro g
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ht g)
    set c : ℝ≥0 := testProfile ι ν₀ g with hc
    obtain ⟨a, ha₁, ha₂⟩ :=
      exists_rat_btwn (show (c : ℝ) - ε < (c : ℝ) from sub_lt_self _ hε)
    obtain ⟨b, hb₁, hb₂⟩ :=
      exists_rat_btwn (show (c : ℝ) < (c : ℝ) + ε from lt_add_of_pos_right _ hε)
    refine ⟨a, b, ⟨ha₂, hb₁⟩, fun y hy₁ hy₂ => ?_⟩
    apply hball
    rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  choose a b hab hsq using key
  refine ⟨I.image fun g => (g, a g, b g), ?_, ?_⟩
  · -- the tip is in the row set
    rw [gambleRowSet, Set.mem_iInter₂]
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨g, hgI, rfl⟩ := hp
    exact ⟨(hab g).1, (hab g).2⟩
  · -- the row set factors through the product neighborhood
    intro ν hν
    rw [gambleRowSet, Set.mem_iInter₂] at hν
    rw [← hWeq]
    refine hsub (Set.mem_pi.mpr fun g hgI => ?_)
    have hmem := hν (g, a g, b g)
      (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hgI))
    exact hsq g _ hmem.1 hmem.2

/-! ## Directed generation: unconditional -/

/-- **The generation theorem at the general carrier — directed form,
unconditional.**  Every lsc penalty on a presented carrier is the
pointwise supremum of its gamble-row minorants: rational heights on
finite menus of rational gamble constraints.  No countability,
metrizability, or compactness hypothesis appears; the finite storey's
metric-ball step is replaced by the initial-topology basis lemma. -/
theorem iSup_gambleRows_eq_self {ι : Y → FiniteMeasure X}
    (hι : Topology.IsInducing ι) {f : Y → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    ⨆ (q : ℚ) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) (_ : 0 < q)
        (_ : ∀ ν, gambleRow ι (ENNReal.ofReal q) F ν ≤ f ν),
      gambleRow ι (ENNReal.ofReal q) F = f := by
  apply le_antisymm
  · exact iSup_le fun q => iSup_le fun F => iSup_le fun _ =>
      iSup_le fun hmin => fun ν => hmin ν
  · intro ν₀
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt'
    have hcoe : ((Real.toNNReal (q : ℝ)) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := rfl
    rw [hcoe] at h1 h2
    have hq0 : 0 < q := by
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal q := (zero_le.trans_lt h1 : (0:ℝ≥0∞) < _)
      exact_mod_cast ENNReal.ofReal_pos.mp hpos
    -- the superlevel is open; a gamble row fits between the point and it
    have hopen : IsOpen (f ⁻¹' Set.Ioi (ENNReal.ofReal (q : ℝ))) :=
      lowerSemicontinuous_iff_isOpen_preimage.mp hf _
    have hν₀mem : ν₀ ∈ f ⁻¹' Set.Ioi (ENNReal.ofReal (q : ℝ)) := h2
    obtain ⟨F, hmemF, hsubF⟩ := exists_gambleRowSet_subset hι hopen hν₀mem
    -- the row is a minorant of `f`
    have hmin : ∀ ν, gambleRow ι (ENNReal.ofReal q) F ν ≤ f ν := by
      intro ν
      by_cases hν : ν ∈ gambleRowSet ι F
      · rw [gambleRow, scaledIndicator_apply_of_mem hν]
        exact (hsubF hν).le
      · rw [gambleRow, scaledIndicator_apply_of_not_mem hν]
        exact zero_le
    -- the row attains the height at `ν₀`, beating the supremum
    have happ : gambleRow ι (ENNReal.ofReal q) F ν₀ = ENNReal.ofReal q := by
      rw [gambleRow, scaledIndicator_apply_of_mem hmemF]
    have hle : gambleRow ι (ENNReal.ofReal q) F
        ≤ ⨆ (q : ℚ) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) (_ : 0 < q)
            (_ : ∀ ν, gambleRow ι (ENNReal.ofReal q) F ν ≤ f ν),
          gambleRow ι (ENNReal.ofReal q) F := by
      refine le_iSup_of_le q ?_
      refine le_iSup_of_le F ?_
      refine le_iSup_of_le hq0 ?_
      exact le_iSup_of_le hmin le_rfl
    have hcontra : ENNReal.ofReal q
        ≤ (⨆ (q : ℚ) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) (_ : 0 < q)
            (_ : ∀ ν, gambleRow ι (ENNReal.ofReal q) F ν ≤ f ν),
          gambleRow ι (ENNReal.ofReal q) F) ν₀ := by
      calc ENNReal.ofReal q = gambleRow ι (ENNReal.ofReal q) F ν₀ := happ.symm
        _ ≤ _ := hle ν₀
    exact absurd (lt_of_le_of_lt hcontra h1) (lt_irrefl _)

/-! ## Countable generation: second countability is the exact toll -/

/-- **Countable generation.**  On a second-countable presented carrier,
a *countable* set of gamble rows already generates every lsc penalty:
the directed family of row minorants has the penalty as its least upper
bound, and Bourbaki's countable-envelope theorem for lower
semicontinuous functions on hereditarily Lindelöf spaces extracts a
countable subfamily with the same supremum. -/
theorem exists_countable_gambleRows_eq_self [SecondCountableTopology Y]
    {ι : Y → FiniteMeasure X} (hι : Topology.IsInducing ι) {f : Y → ℝ≥0∞}
    (hf : LowerSemicontinuous f) :
    ∃ R : Set (ℚ × Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)), R.Countable
      ∧ (∀ p ∈ R, ∀ ν, gambleRow ι (ENNReal.ofReal p.1) p.2 ν ≤ f ν)
      ∧ ⨆ p ∈ R, gambleRow ι (ENNReal.ofReal p.1) p.2 = f := by
  classical
  set 𝓕 : Set (Y → ℝ≥0∞) :=
    {h | ∃ p : ℚ × Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ), 0 < p.1
      ∧ (∀ ν, gambleRow ι (ENNReal.ofReal p.1) p.2 ν ≤ f ν)
      ∧ h = gambleRow ι (ENNReal.ofReal p.1) p.2} with h𝓕def
  have h𝓕lsc : ∀ h ∈ 𝓕, LowerSemicontinuous h := by
    rintro h ⟨p, -, -, rfl⟩
    exact lowerSemicontinuous_gambleRow hι.continuous _ _
  have h𝓕lub : IsLUB 𝓕 f := by
    constructor
    · rintro h ⟨p, -, hmin, rfl⟩
      intro ν
      exact hmin ν
    · intro u hu
      rw [← iSup_gambleRows_eq_self hι hf]
      refine iSup_le fun q => iSup_le fun F => iSup_le fun hq =>
        iSup_le fun hmin => ?_
      exact hu ⟨(q, F), hq, hmin, rfl⟩
  obtain ⟨𝓕', h𝓕'sub, h𝓕'count, h𝓕'lub⟩ :=
    exists_countable_lowerSemicontinuous_isLUB h𝓕lsc h𝓕lub
  have hpick : ∀ h ∈ 𝓕', ∃ p : ℚ × Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ), 0 < p.1
      ∧ (∀ ν, gambleRow ι (ENNReal.ofReal p.1) p.2 ν ≤ f ν)
      ∧ h = gambleRow ι (ENNReal.ofReal p.1) p.2 :=
    fun h hh => h𝓕'sub hh
  choose! pick hpos hmin hrow using hpick
  refine ⟨pick '' 𝓕', h𝓕'count.image pick, ?_, ?_⟩
  · rintro p ⟨h, hh, rfl⟩
    exact hmin h hh
  · rw [iSup_image]
    have hcongr : ⨆ h ∈ 𝓕',
        gambleRow ι (ENNReal.ofReal (pick h).1) (pick h).2
        = ⨆ h ∈ 𝓕', h :=
      biSup_congr fun h hh => (hrow h hh).symm
    rw [hcongr, ← sSup_eq_iSup, h𝓕'lub.sSup_eq]

end Engine

/-! ## The two carriers of the chapter -/

section Carriers

/-- The probability carrier is presented by its inclusion into the
finite measures. -/
theorem isInducing_prob_toFiniteMeasure :
    Topology.IsInducing (ProbabilityMeasure.toFiniteMeasure :
      ProbabilityMeasure X → FiniteMeasure X) :=
  (ProbabilityMeasure.toFiniteMeasure_isEmbedding X).toIsInducing

/-- So is the general subprobability carrier. -/
theorem isInducing_state_toFiniteMeasure :
    Topology.IsInducing (SubProbabilityMeasure.toFiniteMeasure :
      SubProbabilityMeasure X → FiniteMeasure X) :=
  SubProbabilityMeasure.isClosedEmbedding_toFiniteMeasure.toIsEmbedding.toIsInducing

/-- **Directed generation on probability directions** — the general
sibling of the finite storey's box-row theorem
(`SuFunctor.Universe.Generation.iSup_boxRows_eq_self`): every lsc
penalty on the probability carrier is the pointwise supremum of its
gamble-row minorants.  Unconditional. -/
theorem iSup_gambleRows_eq_self_prob {f : Penalty X}
    (hf : LowerSemicontinuous f) :
    ⨆ (q : ℚ) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) (_ : 0 < q)
        (_ : ∀ μ, gambleRow ProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal q) F μ ≤ f μ),
      gambleRow ProbabilityMeasure.toFiniteMeasure (ENNReal.ofReal q) F
        = f :=
  iSup_gambleRows_eq_self isInducing_prob_toFiniteMeasure hf

/-- **Directed generation on the general subprobability carrier** — the
general sibling of the finite storey's tents theorem
(`SuFunctor.Universe.Tents.iSup_tents_eq_self`): with arbitrary finite
menus of bounded continuous gambles, nothing in the universe is
invisible.  The quadratic species of the finite statement was a
compact-finite-dimensional artifact; the gamble menus are the honest
general witnesses.  Unconditional. -/
theorem iSup_gambleRows_eq_self_state {f : StatePenalty X}
    (hf : LowerSemicontinuous f) :
    ⨆ (q : ℚ) (F : Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)) (_ : 0 < q)
        (_ : ∀ ν, gambleRow SubProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal q) F ν ≤ f ν),
      gambleRow SubProbabilityMeasure.toFiniteMeasure (ENNReal.ofReal q) F
        = f :=
  iSup_gambleRows_eq_self isInducing_state_toFiniteMeasure hf

/-- **Countable generation on probability directions**, under second
countability of the carrier — the exact toll the finite storey paid
with `Countable (ℚ × (V → ℚ) × (V → ℚ))`. -/
theorem exists_countable_gambleRows_eq_self_prob
    [SecondCountableTopology (ProbabilityMeasure X)] {f : Penalty X}
    (hf : LowerSemicontinuous f) :
    ∃ R : Set (ℚ × Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)), R.Countable
      ∧ (∀ p ∈ R, ∀ μ, gambleRow ProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal p.1) p.2 μ ≤ f μ)
      ∧ ⨆ p ∈ R, gambleRow ProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal p.1) p.2 = f :=
  exists_countable_gambleRows_eq_self isInducing_prob_toFiniteMeasure hf

/-- **Countable generation on the general subprobability carrier**,
under second countability of the carrier.  (Metrizability of this
carrier over metrizable separable Borel outcome spaces is mechanized in
the house pointfree package via the dagger chart; its second
countability is carried here as an honest hypothesis.) -/
theorem exists_countable_gambleRows_eq_self_state
    [SecondCountableTopology (SubProbabilityMeasure X)] {f : StatePenalty X}
    (hf : LowerSemicontinuous f) :
    ∃ R : Set (ℚ × Finset ((X →ᵇ ℝ≥0) × ℚ × ℚ)), R.Countable
      ∧ (∀ p ∈ R, ∀ ν, gambleRow SubProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal p.1) p.2 ν ≤ f ν)
      ∧ ⨆ p ∈ R, gambleRow SubProbabilityMeasure.toFiniteMeasure
          (ENNReal.ofReal p.1) p.2 = f :=
  exists_countable_gambleRows_eq_self isInducing_state_toFiniteMeasure hf

end Carriers

/-! ## Discharging second countability: the compact metrizable supply -/

/-- **The supply theorem**: over a compact metrizable Borel outcome
space, the probability carrier is second countable — Prokhorov
compactness plus Lévy–Prokhorov metrizability make it a compact metric
space, and compact metric spaces are second countable.  This discharges
the countable-generation hypothesis for the first genuinely
infinite-dimensional carriers (e.g. `X = [0,1]`). -/
theorem secondCountableTopology_probabilityMeasure
    [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X] :
    SecondCountableTopology (ProbabilityMeasure X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  haveI : SecondCountableTopology X := inferInstance
  haveI : TopologicalSpace.SeparableSpace X := inferInstance
  haveI : CompactSpace (ProbabilityMeasure X) := inferInstance
  haveI : TopologicalSpace.MetrizableSpace (ProbabilityMeasure X) := inferInstance
  letI : MetricSpace (ProbabilityMeasure X) :=
    TopologicalSpace.metrizableSpaceMetric _
  infer_instance

end SuFunctor.Universe.General
