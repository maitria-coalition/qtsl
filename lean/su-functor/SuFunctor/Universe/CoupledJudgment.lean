import SuFunctor.Universe.ProbCarrier
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # The coupled judgment: ∀ at the safety face, ∃ at the liveness face

The satisfaction judgment of the flat stratum couples two conjuncts of
opposite quantifier polarity.  A **spec atom** is a pair `(u, 𝒱)`: a
safety slot `u` (one penalty) and a liveness slot `𝒱` (a set of
penalties, finite in the intended reading).  A system `σ` satisfies the
atom iff

* **safety, ∀-flavored**: `u ≤ σ` pointwise — every distribution the
  spec penalizes is at least as hard for the system; and
* **liveness, ∃-flavored**: for each `v ∈ 𝒱` the system **dips** under
  `v` somewhere — some distribution the spec marks as good is strictly
  cheaper for the system than the mark.  Negation lives at the
  judgment: a dip is exactly `¬ v ≤ σ` (`dip_iff_not_le`).

Headline facts, each with its proof or an exact witness below:

* **Ex falso inverts.**  The inconsistent system (`⊤`) satisfies no
  atom with a nonempty liveness slot (`not_coupledSat_top_system`); the
  vacuous atom `(0, {⊤})` is satisfied exactly by the proper systems
  (`coupledSat_zero_topSpec_iff`); `(⊤, 𝒱)` and any atom with `0` in
  its liveness slot are unsatisfiable.
* **The con theorem.**  An atom is satisfiable iff every liveness
  demand exceeds the safety floor somewhere, and then the safety slot
  itself is the freest model (`exists_coupledSat_iff_con`,
  `coupledSat_self_iff_con`).
* **Refinement is polarized.**  Raising the system preserves the
  safety conjunct and can destroy the liveness conjunct
  (`exists_refinement_destroys_liveness`).
* **Two impossibilities force the shape of atoms.**  No single penalty
  expresses a disjunction of safety claims
  (`no_safety_disjunction`, with the coordinate-row witness on the
  two-outcome carrier), and no single penalty expresses a conjunction
  of liveness claims (`no_liveness_conjunction`) — which is why the
  liveness slot is a *set* while the safety slot merges by pointwise
  max (`coupledSat_and_iff`).  The invertible merges both land on
  `⊔`: safety conjunction and liveness disjunction (`dip_sup_iff`).
* **The compiled refinement order** (`coupled_refinement_iff`): for a
  satisfiable atom, model-class inclusion is equivalent to
  `u' ≤ u` together with a floor-relative covering of the liveness
  demands — an Egli–Milner-shaped order whose upper half collapsed to
  one pointwise inequality and whose lower half runs through
  `u ⊔ v'`.  Constructive content: the equivalence is witnessed by
  the freest model and the candidate counterexample `u ⊔ v'`.
* **Disjunct matching is sufficient but not necessary** for refinement
  between disjunctions of atoms (`matching_not_necessary`), and the
  repair — **diamond splitting** — has an exact side condition that is
  itself a single pointwise domination row
  (`diamond_splitting`).
* **On affine rows the judgment is finitary**: pointwise order and
  dips both reduce to vertex comparisons (`affRow_le_iff`,
  `dip_affRow_iff`), so satisfaction against affine-row data is
  decidable coordinate arithmetic (`coupledSat_affRow_iff` and the
  `Decidable` instance).

Statements about model classes are class-parametric (`P` ranges over
predicates on penalties, instantiated at `LowerSemicontinuous` for the
universe's citizens and at `fun _ => True` for the unrestricted
reading), in the style of `gradedObligation_iff_le`.
-/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## The judgment, on an arbitrary carrier

The core is order theory: no topology enters until the witnesses.  `K`
is the carrier of distributions; penalties are `K → ℝ≥0∞` with the
pointwise order. -/

variable {K : Type*}

/-- The dip relation: the system is strictly cheaper than the mark `v`
at some distribution.  This is the ∃-face of the judgment — and it is
exactly the negation of the pointwise order (`dip_iff_not_le`). -/
def Dip (σ v : K → ℝ≥0∞) : Prop := ∃ μ, σ μ < v μ

theorem dip_iff_not_le {σ v : K → ℝ≥0∞} : Dip σ v ↔ ¬ v ≤ σ := by
  simp [Dip, Pi.le_def, not_forall, not_le]

theorem not_dip_iff_le {σ v : K → ℝ≥0∞} : ¬ Dip σ v ↔ v ≤ σ := by
  rw [dip_iff_not_le, not_not]

/-- Dips survive lowering the system. -/
theorem Dip.mono_system {σ σ' v : K → ℝ≥0∞} (h : Dip σ' v) (hσ : σ ≤ σ') :
    Dip σ v := by
  obtain ⟨μ, hμ⟩ := h
  exact ⟨μ, lt_of_le_of_lt (hσ μ) hμ⟩

/-- Dips survive raising the mark. -/
theorem Dip.mono_mark {σ v v' : K → ℝ≥0∞} (h : Dip σ v) (hv : v ≤ v') :
    Dip σ v' := by
  obtain ⟨μ, hμ⟩ := h
  exact ⟨μ, lt_of_lt_of_le hμ (hv μ)⟩

/-- The zero penalty is below every system, pointwise. -/
theorem pi_zero_le (σ : K → ℝ≥0∞) : (0 : K → ℝ≥0∞) ≤ σ :=
  fun _ => zero_le

/-- No system dips under the zero penalty. -/
theorem not_dip_zero {σ : K → ℝ≥0∞} : ¬ Dip σ (0 : K → ℝ≥0∞) := by
  rintro ⟨μ, hμ⟩
  rw [Pi.zero_apply] at hμ
  exact absurd hμ (not_lt.mpr zero_le)

/-- The coupled satisfaction judgment against a spec atom `(u, 𝒱)`:
pointwise domination of the safety slot, and a dip under every member
of the liveness slot. -/
def CoupledSat (σ u : K → ℝ≥0∞) (𝒱 : Set (K → ℝ≥0∞)) : Prop :=
  u ≤ σ ∧ ∀ v ∈ 𝒱, Dip σ v

/-- The con condition: every liveness demand exceeds the safety floor
somewhere.  `con_iff_forall_not_le` reads it as non-domination. -/
def Con (u : K → ℝ≥0∞) (𝒱 : Set (K → ℝ≥0∞)) : Prop :=
  ∀ v ∈ 𝒱, Dip u v

theorem con_iff_forall_not_le {u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} :
    Con u 𝒱 ↔ ∀ v ∈ 𝒱, ¬ v ≤ u := by
  unfold Con
  exact forall₂_congr fun v _ => dip_iff_not_le

/-! ## Ex falso inversion -/

/-- The inconsistent system dips under nothing. -/
theorem not_dip_top {v : K → ℝ≥0∞} : ¬ Dip (⊤ : K → ℝ≥0∞) v := by
  rintro ⟨μ, hμ⟩
  rw [Pi.top_apply] at hμ
  exact not_top_lt hμ

/-- **Ex falso inverts**: the inconsistent system satisfies no atom
whose liveness slot is nonempty.  (Under the option-A reading every
atom's liveness slot is nonempty, so the inconsistent system satisfies
nothing at all.) -/
theorem not_coupledSat_top_system {u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)}
    (h𝒱 : 𝒱.Nonempty) : ¬ CoupledSat (⊤ : K → ℝ≥0∞) u 𝒱 := by
  rintro ⟨-, hlive⟩
  obtain ⟨v, hv⟩ := h𝒱
  exact not_dip_top (hlive v hv)

/-- The vacuous atom `(0, {⊤})` demands exactly properness: some
distribution is realizable at finite penalty. -/
theorem coupledSat_zero_topSpec_iff {σ : K → ℝ≥0∞} :
    CoupledSat σ 0 {(⊤ : K → ℝ≥0∞)} ↔ ∃ μ, σ μ ≠ ⊤ := by
  constructor
  · rintro ⟨-, hlive⟩
    obtain ⟨μ, hμ⟩ := hlive ⊤ (Set.mem_singleton _)
    rw [Pi.top_apply] at hμ
    exact ⟨μ, lt_top_iff_ne_top.mp hμ⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨pi_zero_le σ, ?_⟩
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    refine ⟨μ, ?_⟩
    rw [Pi.top_apply]
    exact lt_top_iff_ne_top.mpr hμ

/-- An atom whose safety slot is `⊤` is unsatisfiable (given any
liveness demand): the safety face forces the inconsistent system. -/
theorem not_coupledSat_top_safety {σ : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)}
    (h𝒱 : 𝒱.Nonempty) : ¬ CoupledSat σ (⊤ : K → ℝ≥0∞) 𝒱 := by
  rintro ⟨hsafe, hlive⟩
  obtain ⟨v, hv⟩ := h𝒱
  obtain ⟨μ, hμ⟩ := hlive v hv
  have hσ : (⊤ : ℝ≥0∞) ≤ σ μ := by simpa using hsafe μ
  exact not_top_lt (lt_of_le_of_lt hσ hμ)

/-- An atom with the zero penalty in its liveness slot is
unsatisfiable: no system dips under `0`. -/
theorem not_coupledSat_of_zero_mem {σ u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)}
    (h : (0 : K → ℝ≥0∞) ∈ 𝒱) : ¬ CoupledSat σ u 𝒱 := by
  rintro ⟨-, hlive⟩
  exact not_dip_zero (hlive 0 h)

/-! ## The con theorem: satisfiability characterized, with the freest
model -/

/-- The safety slot is a model of its own atom exactly under con. -/
theorem coupledSat_self_iff_con {u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} :
    CoupledSat u u 𝒱 ↔ Con u 𝒱 :=
  ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩

/-- Any model transfers its dips down to the safety floor. -/
theorem Con.of_coupledSat {σ u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)}
    (h : CoupledSat σ u 𝒱) : Con u 𝒱 := fun v hv =>
  (h.2 v hv).mono_system h.1

/-- **The con theorem.**  An atom is satisfiable iff every liveness
demand exceeds the safety floor somewhere — and then the safety slot
itself is a model: the spec's own safety slot is its freest model. -/
theorem exists_coupledSat_iff_con {u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} :
    (∃ σ, CoupledSat σ u 𝒱) ↔ Con u 𝒱 :=
  ⟨fun ⟨_, h⟩ => Con.of_coupledSat h, fun h => ⟨u, coupledSat_self_iff_con.mpr h⟩⟩

/-! ## Refinement is polarized -/

/-- Raising the system preserves the safety conjunct... -/
theorem safety_mono {σ σ' u : K → ℝ≥0∞} (hσ : σ ≤ σ') (h : u ≤ σ) :
    u ≤ σ' := h.trans hσ

/-- ...and can destroy the liveness conjunct: an exact witness with
constant data.  Refinement (raising penalties) is safe for the ∀-face
and dangerous for the ∃-face. -/
theorem exists_refinement_destroys_liveness [Nonempty K] :
    ∃ (σ σ' u : K → ℝ≥0∞) (𝒱 : Set (K → ℝ≥0∞)),
      CoupledSat σ u 𝒱 ∧ σ ≤ σ' ∧ ¬ CoupledSat σ' u 𝒱 := by
  refine ⟨fun _ => 1, fun _ => 2, 0, {fun _ => 2}, ⟨pi_zero_le _, ?_⟩,
    fun _ => one_le_two, ?_⟩
  · rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨Classical.arbitrary K, ENNReal.one_lt_two⟩
  · rintro ⟨-, hlive⟩
    obtain ⟨μ, hμ⟩ := hlive (fun _ => 2) (Set.mem_singleton _)
    exact absurd hμ (lt_irrefl _)

/-! ## The invertible merges, and the two impossibilities -/

/-- **Liveness disjoins by pointwise max, exactly**: the ∃-quantifier
absorbs its natural connective. -/
theorem dip_sup_iff {σ v₁ v₂ : K → ℝ≥0∞} :
    Dip σ (v₁ ⊔ v₂) ↔ Dip σ v₁ ∨ Dip σ v₂ := by
  constructor
  · rintro ⟨μ, hμ⟩
    rw [Pi.sup_apply, lt_sup_iff] at hμ
    exact hμ.imp (fun h => ⟨μ, h⟩) fun h => ⟨μ, h⟩
  · rintro (h | h)
    · exact h.mono_mark le_sup_left
    · exact h.mono_mark le_sup_right

/-- The doomed direction: a dip under a pointwise min forces dips under
both (at one coinciding witness), and not conversely — see
`min_liveness_merge_incomplete` for the converse's failure. -/
theorem dip_inf {σ v₁ v₂ : K → ℝ≥0∞} (h : Dip σ (v₁ ⊓ v₂)) :
    Dip σ v₁ ∧ Dip σ v₂ :=
  ⟨h.mono_mark inf_le_left, h.mono_mark inf_le_right⟩

/-- **Safety conjoins by pointwise max, exactly** — so atoms are closed
under conjunction with safety slots merging invertibly and liveness
slots accumulating as sets. -/
theorem coupledSat_and_iff {σ u₁ u₂ : K → ℝ≥0∞}
    {𝒱₁ 𝒱₂ : Set (K → ℝ≥0∞)} :
    CoupledSat σ u₁ 𝒱₁ ∧ CoupledSat σ u₂ 𝒱₂
      ↔ CoupledSat σ (u₁ ⊔ u₂) (𝒱₁ ∪ 𝒱₂) := by
  constructor
  · rintro ⟨⟨h₁, hl₁⟩, ⟨h₂, hl₂⟩⟩
    refine ⟨sup_le h₁ h₂, ?_⟩
    rintro v (hv | hv)
    · exact hl₁ v hv
    · exact hl₂ v hv
  · rintro ⟨hsafe, hlive⟩
    exact ⟨⟨le_sup_left.trans hsafe, fun v hv => hlive v (Or.inl hv)⟩,
      ⟨le_sup_right.trans hsafe, fun v hv => hlive v (Or.inr hv)⟩⟩

/-- **No single penalty expresses a disjunction of safety claims.**
For incomparable `u₁, u₂` there is no `s` whose principal filter (over
any class containing `u₁`, `u₂`, and their min) is the union of
theirs: the min-merge over-approximates.  This is why disjunction
escapes the atoms and lives in the disjunctive normal form. -/
theorem no_safety_disjunction {P : (K → ℝ≥0∞) → Prop} {u₁ u₂ : K → ℝ≥0∞}
    (hP₁ : P u₁) (hP₂ : P u₂) (hPinf : P (u₁ ⊓ u₂))
    (h₁ : ¬ u₁ ≤ u₂) (h₂ : ¬ u₂ ≤ u₁) :
    ¬ ∃ s : K → ℝ≥0∞, ∀ σ, P σ → (s ≤ σ ↔ u₁ ≤ σ ∨ u₂ ≤ σ) := by
  rintro ⟨s, hs⟩
  have hs₁ : s ≤ u₁ := (hs u₁ hP₁).mpr (Or.inl le_rfl)
  have hs₂ : s ≤ u₂ := (hs u₂ hP₂).mpr (Or.inr le_rfl)
  rcases (hs _ hPinf).mp (le_inf hs₁ hs₂) with h | h
  · exact h₁ (le_inf_iff.mp h).2
  · exact h₂ (le_inf_iff.mp h).1

/-! ## The compiled refinement order -/

/-- **The compiled refinement order** between satisfiable atoms:
model-class inclusion (over any class `P` containing the freest model
and the candidate counterexamples `u ⊔ v'`) holds iff the refined
safety floor is below the original and every refined liveness demand
is covered, floor-relatively, by an original one.

The two halves are the Egli–Milner shape with the deltas that are
findings: the upper (safety) half collapsed to one pointwise
inequality because safety merges invertibly, and the lower (liveness)
half is floor-relative — the covering runs through `u ⊔ v'`, the
refining atom's own safety floor entering its liveness comparison. -/
theorem coupled_refinement_iff {P : (K → ℝ≥0∞) → Prop} {u u' : K → ℝ≥0∞}
    {𝒱 𝒱' : Set (K → ℝ≥0∞)} (hcon : Con u 𝒱) (hPu : P u)
    (hPsup : ∀ v' ∈ 𝒱', P (u ⊔ v')) :
    (∀ σ, P σ → CoupledSat σ u 𝒱 → CoupledSat σ u' 𝒱')
      ↔ u' ≤ u ∧ ∀ v' ∈ 𝒱', ∃ v ∈ 𝒱, v ≤ u ⊔ v' := by
  constructor
  · intro h
    have hu : CoupledSat u u' 𝒱' := h u hPu (coupledSat_self_iff_con.mpr hcon)
    refine ⟨hu.1, fun v' hv' => ?_⟩
    by_contra hno
    push_neg at hno
    have hsat : CoupledSat (u ⊔ v') u 𝒱 :=
      ⟨le_sup_left, fun v hv => dip_iff_not_le.mpr (hno v hv)⟩
    obtain ⟨μ, hμ⟩ := (h _ (hPsup v' hv') hsat).2 v' hv'
    exact absurd hμ (not_lt.mpr ((le_sup_right : v' ≤ u ⊔ v') μ))
  · rintro ⟨hu', hcov⟩ σ _ ⟨hsafe, hlive⟩
    refine ⟨hu'.trans hsafe, fun v' hv' => ?_⟩
    obtain ⟨v, hv, hvle⟩ := hcov v' hv'
    obtain ⟨μ, hμ⟩ := hlive v hv
    have h1 : σ μ < (u ⊔ v') μ := lt_of_lt_of_le hμ (hvle μ)
    rw [Pi.sup_apply, lt_sup_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (not_lt.mpr (hsafe μ))
    · exact ⟨μ, h1⟩

/-! ## Diamond splitting -/

/-- **Diamond splitting, with its side condition as a domination
row.**  A single liveness demand `w` refines into a family `{w j}`
(under the shared safety floor `u`, over any class containing the
candidate counterexample) iff `w ≤ u ⊔ ⨆ j, w j` — one pointwise
domination row, checkable by the ∀-face machinery.  This is the exact
repair for the failure of disjunct matching
(`matching_not_necessary`). -/
theorem diamond_splitting {P : (K → ℝ≥0∞) → Prop} {u w : K → ℝ≥0∞}
    {ι : Sort*} (wj : ι → K → ℝ≥0∞)
    (hPsup : P (u ⊔ ⨆ j, wj j)) :
    (∀ σ, P σ → CoupledSat σ u {w} → ∃ j, CoupledSat σ u {wj j})
      ↔ w ≤ u ⊔ ⨆ j, wj j := by
  constructor
  · intro h
    by_contra hno
    have hdip : Dip (u ⊔ ⨆ j, wj j) w := dip_iff_not_le.mpr hno
    have hsat : CoupledSat (u ⊔ ⨆ j, wj j) u {w} := by
      refine ⟨le_sup_left, ?_⟩
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hdip
    obtain ⟨j, hj⟩ := h _ hPsup hsat
    obtain ⟨μ, hμ⟩ := hj.2 (wj j) (Set.mem_singleton _)
    exact absurd hμ
      (not_lt.mpr (((le_iSup wj j).trans le_sup_right :
        wj j ≤ u ⊔ ⨆ j, wj j) μ))
  · intro hle σ _ ⟨hsafe, hlive⟩
    obtain ⟨μ, hμ⟩ := hlive w (Set.mem_singleton _)
    have h1 : σ μ < (u ⊔ ⨆ j, wj j) μ := lt_of_lt_of_le hμ (hle μ)
    rw [Pi.sup_apply, lt_sup_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (not_lt.mpr (hsafe μ))
    · rw [iSup_apply, lt_iSup_iff] at h1
      obtain ⟨j, hj⟩ := h1
      refine ⟨j, hsafe, ?_⟩
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨μ, hj⟩

/-! ## Instantiations on the flat carrier

Topology enters: the witnesses live on the two-outcome flat carrier,
with walls on closed sets and scaled indicators on open sets as the
lsc citizens they are. -/

variable {V : Type*} [Fintype V]

/-- Arbitrary suprema of flat-carrier citizens are citizens. -/
theorem lsc_prob_iSup {ι : Sort*} {f : ι → ProbPenalty V}
    (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (⨆ i, f i) := by
  have heq : (⨆ i, f i) = fun μ => ⨆ i, f i μ := funext fun _ => iSup_apply
  rw [heq]
  exact lowerSemicontinuous_iSup h

/-- **Reachability.**  Against the liveness mark of an open goal
region `G` — the wall `⊤` on `G`, `0` off it — a dip says exactly:
some distribution in `G` is realizable at finite penalty. -/
theorem dip_probWall_compl_iff {σ : ProbPenalty V} {G : Set (ProbState V)} :
    Dip σ (probWall Gᶜ) ↔ ∃ μ ∈ G, σ μ ≠ ⊤ := by
  constructor
  · rintro ⟨μ, hμ⟩
    by_cases hG : μ ∈ G
    · rw [probWall_apply_of_not_mem (fun hc => (Set.mem_compl_iff _ _).mp hc hG)] at hμ
      exact ⟨μ, hG, lt_top_iff_ne_top.mp hμ⟩
    · rw [probWall_apply_of_mem hG] at hμ
      exact absurd hμ (not_lt.mpr zero_le)
  · rintro ⟨μ, hG, hne⟩
    refine ⟨μ, ?_⟩
    rw [probWall_apply_of_not_mem (fun hc => (Set.mem_compl_iff _ _).mp hc hG)]
    exact lt_top_iff_ne_top.mpr hne

/-- The `⊔`-merge of liveness marks is exact while the `⊓`-merge is
not: two liveness demands with disjoint open goals are jointly
satisfiable, but their pointwise min carries no demand at all.  (The
converse of `dip_inf` fails.) -/
theorem min_liveness_merge_incomplete :
    ∃ (σ v₁ v₂ : ProbPenalty (Fin 2)),
      Dip σ v₁ ∧ Dip σ v₂ ∧ ¬ Dip σ (v₁ ⊓ v₂) := by
  classical
  refine ⟨0, probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 0}ᶜ,
    probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 1}ᶜ, ?_, ?_, ?_⟩
  · exact dip_probWall_compl_iff.mpr ⟨ProbState.dirac 0, by
      simp only [Set.mem_setOf_eq, ProbState.dirac_apply_same]; norm_num,
      by simp⟩
  · exact dip_probWall_compl_iff.mpr ⟨ProbState.dirac 1, by
      simp only [Set.mem_setOf_eq, ProbState.dirac_apply_same]; norm_num,
      by simp⟩
  · rintro ⟨μ, hμ⟩
    rw [Pi.inf_apply, lt_inf_iff] at hμ
    obtain ⟨h₁, h₂⟩ := hμ
    -- both walls are `⊤` at the dip point, so `μ` lies in both goals —
    -- but the goal regions are disjoint on the flat carrier.
    have hm₁ : (1:ℝ)/2 < (μ : Fin 2 → ℝ) 0 := by
      by_contra hc
      rw [probWall_apply_of_mem hc, Pi.zero_apply] at h₁
      exact absurd h₁ (lt_irrefl 0)
    have hm₂ : (1:ℝ)/2 < (μ : Fin 2 → ℝ) 1 := by
      by_contra hc
      rw [probWall_apply_of_mem hc, Pi.zero_apply] at h₂
      exact absurd h₂ (lt_irrefl 0)
    have hsum := μ.sum_eq_one
    rw [Fin.sum_univ_two] at hsum
    linarith

/-- **No single penalty expresses a conjunction of liveness claims.**
Over the two-outcome flat carrier, with the two point-mass goal
regions: no candidate `χ` has, against every citizen system, a dip
exactly when both goals are reached.  Liveness demands with disjoint
witnesses cannot merge — the liveness slot must be a set. -/
theorem no_liveness_conjunction :
    ¬ ∃ χ : ProbPenalty (Fin 2), ∀ σ : ProbPenalty (Fin 2),
        LowerSemicontinuous σ →
        (Dip σ χ ↔
          Dip σ (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 0}ᶜ)
            ∧ Dip σ (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 1}ᶜ)) := by
  classical
  rintro ⟨χ, hχ⟩
  set δ₀ : ProbState (Fin 2) := ProbState.dirac 0 with hδ₀
  set δ₁ : ProbState (Fin 2) := ProbState.dirac 1 with hδ₁
  have hδ₀0 : (δ₀ : Fin 2 → ℝ) 0 = 1 := ProbState.dirac_apply_same 0
  have hδ₀1 : (δ₀ : Fin 2 → ℝ) 1 = 0 :=
    ProbState.dirac_apply_of_ne (by decide)
  have hδ₁1 : (δ₁ : Fin 2 → ℝ) 1 = 1 := ProbState.dirac_apply_same 1
  have hδ₁0 : (δ₁ : Fin 2 → ℝ) 0 = 0 :=
    ProbState.dirac_apply_of_ne (by decide)
  -- the two committed systems and the hedger
  have hlsc₀ : LowerSemicontinuous (probWall {δ₀}) :=
    lowerSemicontinuous_probWall_iff.mpr isClosed_singleton
  have hlsc₁ : LowerSemicontinuous (probWall {δ₁}) :=
    lowerSemicontinuous_probWall_iff.mpr isClosed_singleton
  have hlscb : LowerSemicontinuous (probWall {δ₀, δ₁}) :=
    lowerSemicontinuous_probWall_iff.mpr
      ((Set.finite_singleton δ₁).insert δ₀).isClosed
  -- `probWall {δ₀}` reaches goal 0, not goal 1
  have hd₀ : Dip (probWall {δ₀})
      (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 0}ᶜ) :=
    dip_probWall_compl_iff.mpr ⟨δ₀, by
      simp only [Set.mem_setOf_eq, hδ₀0]; norm_num,
      by rw [probWall_apply_of_mem (Set.mem_singleton _)]
         exact ENNReal.zero_ne_top⟩
  have hnd₀ : ¬ Dip (probWall {δ₀})
      (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 1}ᶜ) := by
    rw [dip_probWall_compl_iff]
    rintro ⟨μ, hμG, hμne⟩
    have hμmem : μ ∈ ({δ₀} : Set (ProbState (Fin 2))) := by
      by_contra hc
      exact hμne (probWall_apply_of_not_mem hc)
    rw [Set.mem_singleton_iff] at hμmem
    subst hμmem
    rw [Set.mem_setOf_eq, hδ₀1] at hμG
    norm_num at hμG
  -- symmetric facts for `probWall {δ₁}`
  have hd₁ : Dip (probWall {δ₁})
      (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 1}ᶜ) :=
    dip_probWall_compl_iff.mpr ⟨δ₁, by
      simp only [Set.mem_setOf_eq, hδ₁1]; norm_num,
      by rw [probWall_apply_of_mem (Set.mem_singleton _)]
         exact ENNReal.zero_ne_top⟩
  have hnd₁ : ¬ Dip (probWall {δ₁})
      (probWall {μ | (1:ℝ)/2 < (μ : Fin 2 → ℝ) 0}ᶜ) := by
    rw [dip_probWall_compl_iff]
    rintro ⟨μ, hμG, hμne⟩
    have hμmem : μ ∈ ({δ₁} : Set (ProbState (Fin 2))) := by
      by_contra hc
      exact hμne (probWall_apply_of_not_mem hc)
    rw [Set.mem_singleton_iff] at hμmem
    subst hμmem
    rw [Set.mem_setOf_eq, hδ₁0] at hμG
    norm_num at hμG
  -- each committed system pins `χ` to zero at its point mass
  have hχδ₀ : χ δ₀ = 0 := by
    have hnd : ¬ Dip (probWall {δ₀}) χ := by
      rw [hχ _ hlsc₀]
      rintro ⟨-, h⟩
      exact hnd₀ h
    have hle := not_dip_iff_le.mp hnd δ₀
    rwa [probWall_apply_of_mem (Set.mem_singleton _), le_zero_iff] at hle
  have hχδ₁ : χ δ₁ = 0 := by
    have hnd : ¬ Dip (probWall {δ₁}) χ := by
      rw [hχ _ hlsc₁]
      rintro ⟨h, -⟩
      exact hnd₁ h
    have hle := not_dip_iff_le.mp hnd δ₁
    rwa [probWall_apply_of_mem (Set.mem_singleton _), le_zero_iff] at hle
  -- the hedger reaches both goals, so it must dip under `χ` — nowhere to
  have hdb : Dip (probWall {δ₀, δ₁}) χ := by
    rw [hχ _ hlscb]
    constructor
    · exact dip_probWall_compl_iff.mpr ⟨δ₀, by
        simp only [Set.mem_setOf_eq, hδ₀0]; norm_num,
        by rw [probWall_apply_of_mem (Set.mem_insert _ _)]
           exact ENNReal.zero_ne_top⟩
    · exact dip_probWall_compl_iff.mpr ⟨δ₁, by
        simp only [Set.mem_setOf_eq, hδ₁1]; norm_num,
        by rw [probWall_apply_of_mem
             (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))]
           exact ENNReal.zero_ne_top⟩
  obtain ⟨μ, hμ⟩ := hdb
  by_cases hmem : μ ∈ ({δ₀, δ₁} : Set (ProbState (Fin 2)))
  · rw [probWall_apply_of_mem hmem] at hμ
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem'
    · rw [hχδ₀] at hμ
      exact absurd hμ (lt_irrefl 0)
    · rw [Set.mem_singleton_iff] at hmem'
      subst hmem'
      rw [hχδ₁] at hμ
      exact absurd hμ (lt_irrefl 0)
  · rw [probWall_apply_of_not_mem hmem] at hμ
    exact not_top_lt hμ

/-- The coordinate rows on the two-outcome carrier are incomparable
citizens whose min is a citizen: the hypotheses of
`no_safety_disjunction`, discharged concretely.  No citizen's filter
is the union of the two coordinate filters. -/
theorem no_safety_disjunction_coordinates :
    ¬ ∃ s : ProbPenalty (Fin 2), ∀ σ : ProbPenalty (Fin 2),
        LowerSemicontinuous σ →
        (s ≤ σ ↔
          (fun μ : ProbState (Fin 2) =>
            ENNReal.ofReal ((μ : Fin 2 → ℝ) 0)) ≤ σ
            ∨ (fun μ : ProbState (Fin 2) =>
                ENNReal.ofReal ((μ : Fin 2 → ℝ) 1)) ≤ σ) := by
  classical
  have hcont : ∀ i : Fin 2,
      Continuous fun μ : ProbState (Fin 2) =>
        ENNReal.ofReal ((μ : Fin 2 → ℝ) i) := fun i =>
    ENNReal.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_subtype_val)
  have h₁ : ¬ (fun μ : ProbState (Fin 2) =>
      ENNReal.ofReal ((μ : Fin 2 → ℝ) 0))
        ≤ fun μ : ProbState (Fin 2) =>
            ENNReal.ofReal ((μ : Fin 2 → ℝ) 1) := by
    intro h
    have hd := h (ProbState.dirac 0)
    simp only [ProbState.dirac_apply_same,
      ProbState.dirac_apply_of_ne (by decide : (1 : Fin 2) ≠ 0),
      ENNReal.ofReal_one, ENNReal.ofReal_zero] at hd
    exact absurd hd (not_le.mpr zero_lt_one)
  have h₂ : ¬ (fun μ : ProbState (Fin 2) =>
      ENNReal.ofReal ((μ : Fin 2 → ℝ) 1))
        ≤ fun μ : ProbState (Fin 2) =>
            ENNReal.ofReal ((μ : Fin 2 → ℝ) 0) := by
    intro h
    have hd := h (ProbState.dirac 1)
    simp only [ProbState.dirac_apply_same,
      ProbState.dirac_apply_of_ne (by decide : (0 : Fin 2) ≠ 1),
      ENNReal.ofReal_one, ENNReal.ofReal_zero] at hd
    exact absurd hd (not_le.mpr zero_lt_one)
  exact no_safety_disjunction
    ((hcont 0).lowerSemicontinuous) ((hcont 1).lowerSemicontinuous)
    (((hcont 0).lowerSemicontinuous).inf ((hcont 1).lowerSemicontinuous))
    h₁ h₂

/-! ## Disjunct matching is not necessary -/

/-- A convenient two-outcome distribution from a pair of masses. -/
def ProbState.ofPair (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ProbState (Fin 2) :=
  ⟨![a, b], ⟨fun v => by fin_cases v <;> simpa, by
    rw [Fin.sum_univ_two]; simpa⟩⟩

@[simp] theorem ProbState.ofPair_apply_zero (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    ((ProbState.ofPair a b ha hb hab : ProbState (Fin 2)) : Fin 2 → ℝ) 0
      = a := rfl

@[simp] theorem ProbState.ofPair_apply_one (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    ((ProbState.ofPair a b ha hb hab : ProbState (Fin 2)) : Fin 2 → ℝ) 1
      = b := rfl

/-- **Disjunct matching is sufficient but not necessary.**  Over the
two-outcome flat carrier: a single liveness demand (the constant mark
`1`) is covered by two scaled-indicator demands on overlapping open
half-spaces — every model of the premise models one of the two
conclusion disjuncts — while *neither* disjunct alone suffices, each
refuted by a wall system committed to the other side.  Refinement
between disjunctions of atoms is not per-disjunct matching; the repair
is `diamond_splitting`. -/
theorem matching_not_necessary :
    ∃ (w w₁ w₂ : ProbPenalty (Fin 2)),
      LowerSemicontinuous w ∧ LowerSemicontinuous w₁
        ∧ LowerSemicontinuous w₂ ∧
      (∀ σ : ProbPenalty (Fin 2), CoupledSat σ 0 {w} →
        CoupledSat σ 0 {w₁} ∨ CoupledSat σ 0 {w₂}) ∧
      ¬ (∀ σ : ProbPenalty (Fin 2), LowerSemicontinuous σ →
          CoupledSat σ 0 {w} → CoupledSat σ 0 {w₁}) ∧
      ¬ (∀ σ : ProbPenalty (Fin 2), LowerSemicontinuous σ →
          CoupledSat σ 0 {w} → CoupledSat σ 0 {w₂}) := by
  classical
  refine ⟨1, scaledIndicator 1 {μ | (μ : Fin 2 → ℝ) 0 < 1/2},
    scaledIndicator 1 {μ | (1:ℝ)/4 < (μ : Fin 2 → ℝ) 0}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_scaledIndicator
      (IsOpen.preimage
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)
        isOpen_Iio)
  · exact lowerSemicontinuous_scaledIndicator
      (IsOpen.preimage
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)
        isOpen_Ioi)
  · -- the cover: a dip under the constant mark happens at some
    -- distribution, whose first coordinate falls on one side of 1/2 or the other
    rintro σ ⟨-, hlive⟩
    obtain ⟨μ, hμ⟩ := hlive 1 (Set.mem_singleton _)
    rw [Pi.one_apply] at hμ
    by_cases hside : (μ : Fin 2 → ℝ) 0 < 1/2
    · exact Or.inl ⟨pi_zero_le _, by
        rintro v hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact ⟨μ, by rwa [scaledIndicator_apply_of_mem hside]⟩⟩
    · refine Or.inr ⟨pi_zero_le _, ?_⟩
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      have hmem : (1:ℝ)/4 < (μ : Fin 2 → ℝ) 0 := by
        push_neg at hside
        linarith
      exact ⟨μ, by rwa [scaledIndicator_apply_of_mem hmem]⟩
  · -- the left disjunct does not suffice: the system walled onto
    -- the right half-space models the premise and not the disjunct
    intro hall
    have hclosed : IsClosed {μ : ProbState (Fin 2) | 1/2 ≤ (μ : Fin 2 → ℝ) 0} :=
      IsClosed.preimage
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)
        isClosed_Ici
    have hlsc : LowerSemicontinuous
        (probWall {μ : ProbState (Fin 2) | 1/2 ≤ (μ : Fin 2 → ℝ) 0}) :=
      lowerSemicontinuous_probWall_iff.mpr hclosed
    have hsat : CoupledSat
        (probWall {μ : ProbState (Fin 2) | 1/2 ≤ (μ : Fin 2 → ℝ) 0}) 0 {1} := by
      refine ⟨pi_zero_le _, ?_⟩
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      refine ⟨ProbState.ofPair (3/4) (1/4) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
      rw [probWall_apply_of_mem (by
        simp only [Set.mem_setOf_eq, ProbState.ofPair_apply_zero]
        norm_num), Pi.one_apply]
      norm_num
    obtain ⟨-, hlive⟩ := hall _ hlsc hsat
    obtain ⟨μ, hμ⟩ := hlive _ (Set.mem_singleton _)
    by_cases hmem : 1/2 ≤ (μ : Fin 2 → ℝ) 0
    · rw [probWall_apply_of_mem hmem,
        scaledIndicator_apply_of_not_mem (by
          simp only [Set.mem_setOf_eq, not_lt]
          exact hmem)] at hμ
      exact absurd hμ (lt_irrefl 0)
    · rw [probWall_apply_of_not_mem hmem] at hμ
      exact not_top_lt hμ
  · -- the right disjunct does not suffice, symmetrically: the system
    -- walled onto the left quarter-space models the premise and not it
    intro hall
    have hclosed : IsClosed {μ : ProbState (Fin 2) | (μ : Fin 2 → ℝ) 0 ≤ 1/4} :=
      IsClosed.preimage
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)
        isClosed_Iic
    have hlsc : LowerSemicontinuous
        (probWall {μ : ProbState (Fin 2) | (μ : Fin 2 → ℝ) 0 ≤ 1/4}) :=
      lowerSemicontinuous_probWall_iff.mpr hclosed
    have hsat : CoupledSat
        (probWall {μ : ProbState (Fin 2) | (μ : Fin 2 → ℝ) 0 ≤ 1/4}) 0 {1} := by
      refine ⟨pi_zero_le _, ?_⟩
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      refine ⟨ProbState.ofPair (1/4) (3/4) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
      rw [probWall_apply_of_mem (by
        simp only [Set.mem_setOf_eq, ProbState.ofPair_apply_zero]
        norm_num), Pi.one_apply]
      norm_num
    obtain ⟨-, hlive⟩ := hall _ hlsc hsat
    obtain ⟨μ, hμ⟩ := hlive _ (Set.mem_singleton _)
    by_cases hmem : (μ : Fin 2 → ℝ) 0 ≤ 1/4
    · rw [probWall_apply_of_mem hmem,
        scaledIndicator_apply_of_not_mem (by
          simp only [Set.mem_setOf_eq, not_lt]
          exact hmem)] at hμ
      exact absurd hμ (lt_irrefl 0)
    · rw [probWall_apply_of_not_mem hmem] at hμ
      exact not_top_lt hμ

/-! ## Affine rows: the judgment is finitary on rational data

An affine row is the expected-height functional of a coefficient
vector.  Pointwise comparisons and dips against affine rows both
reduce to *vertex* comparisons — finitely many coefficient
inequalities — so the coupled judgment against affine-row data is
decidable coordinate arithmetic.  (With `⊤` coefficients, affine rows
include the crisp walls of coordinate support regions; with finite
rational coefficients they are the exact-certificate fragment.) -/

noncomputable def affRow (a : V → ℝ≥0∞) : ProbPenalty V :=
  fun μ => ∑ v, a v * ENNReal.ofReal ((μ : V → ℝ) v)

theorem affRow_dirac [DecidableEq V] (a : V → ℝ≥0∞) (v : V) :
    affRow a (ProbState.dirac v) = a v := by
  rw [affRow, Finset.sum_eq_single v]
  · rw [ProbState.dirac_apply_same, ENNReal.ofReal_one, mul_one]
  · intro w _ hw
    rw [ProbState.dirac_apply_of_ne hw, ENNReal.ofReal_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- Pointwise order between affine rows is coefficientwise order: the
∀-face of the judgment is decided at the vertices. -/
theorem affRow_le_iff [DecidableEq V] {a b : V → ℝ≥0∞} :
    affRow (V := V) a ≤ affRow b ↔ ∀ v, a v ≤ b v := by
  constructor
  · intro h v
    have := h (ProbState.dirac v)
    rwa [affRow_dirac, affRow_dirac] at this
  · intro h μ
    exact Finset.sum_le_sum fun v _ => mul_le_mul_right' (h v) _

/-- A dip between affine rows is a coefficientwise strict inequality:
the ∃-face of the judgment is also decided at the vertices. -/
theorem dip_affRow_iff [DecidableEq V] {a b : V → ℝ≥0∞} :
    Dip (affRow (V := V) a) (affRow b) ↔ ∃ v, a v < b v := by
  constructor
  · rintro ⟨μ, hμ⟩
    obtain ⟨v, -, hv⟩ := Finset.exists_lt_of_sum_lt hμ
    refine ⟨v, ?_⟩
    by_contra hab
    rw [not_lt] at hab
    exact absurd hv (not_lt.mpr (mul_le_mul_right' hab _))
  · rintro ⟨v, hv⟩
    exact ⟨ProbState.dirac v, by rw [affRow_dirac, affRow_dirac]; exact hv⟩

/-- **The judgment is finitary on affine rows**: satisfaction against
affine-row data reduces to finitely many coefficient comparisons —
`|V|` inequalities for the safety face and one strict inequality per
liveness row, each at a vertex. -/
theorem coupledSat_affRow_iff [DecidableEq V] {ι : Type*}
    (s u : V → ℝ≥0∞) (b : ι → V → ℝ≥0∞) :
    CoupledSat (affRow (V := V) s) (affRow u)
        (Set.range fun i => affRow (b i))
      ↔ (∀ v, u v ≤ s v) ∧ ∀ i, ∃ v, s v < b i v := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨affRow_le_iff.mp hsafe, fun i =>
      dip_affRow_iff.mp (hlive _ (Set.mem_range_self i))⟩
  · rintro ⟨hsafe, hlive⟩
    refine ⟨affRow_le_iff.mpr hsafe, ?_⟩
    rintro v ⟨i, rfl⟩
    exact dip_affRow_iff.mpr (hlive i)

/-- Decidability of the coupled judgment on affine-row data over
finite index types: the constructive content of
`coupledSat_affRow_iff`. -/
noncomputable instance [DecidableEq V] {ι : Type*} [Fintype ι]
    (s u : V → ℝ≥0∞) (b : ι → V → ℝ≥0∞) :
    Decidable (CoupledSat (affRow (V := V) s) (affRow u)
      (Set.range fun i => affRow (b i))) :=
  decidable_of_iff _ (coupledSat_affRow_iff s u b).symm

end SuFunctor.Universe
