import SuFunctor.Universe.CoupledJudgment

/-! # Finite spec syntax: the rectangle fragment and a closed class beyond it

Two boundary theorems for the coupled judgment's *finite syntax*, each
an exact refutation over the flat carrier.

* **The rectangle is a proper fragment** (`no_rectangle_coupling`).
  The decoupled form — one collection of safety claims disjoined, one
  collection of liveness claims conjoined,
  `(⋁ j, □ g j) ∧ (⋀ h ∈ H, ◇ h)` — cannot express the coupled
  disjunction "commit to forbidding `W₁` and reach `U₁`, or commit to
  forbidding `W₂` and reach `U₂`" (three-outcome carrier, disjoint
  open bands).  Three systems refute every rectangle at once: the
  freest branch-1 system donates so weak a safety cover that every
  `W₁`-respecting system inherits it; the sharpest branch-2 system
  pins every shared liveness demand to a single distribution; and the
  *crosser* — branch 1's wall worn with branch 2's reach — then passes
  the rectangle while satisfying neither disjunct.  Safety disjuncts
  cannot see which branch a system committed to, and shared liveness
  cannot re-discriminate: coupling is exactly what the disjunct index
  carries.  Strengthening over the prose witness: both collections are
  arbitrary here — index type of any cardinality (empty included) and
  a liveness collection of any size — finiteness was never used.

* **A closed class beyond every finite presentation**
  (`isClosed_atMostOneRealizable`,
  `atMostOneRealizable_not_definable`).  The class of
  possibilistically deterministic-or-inconsistent systems — at most
  one distribution realizable at finite penalty — is closed in *every*
  topology that closes the principal filters of citizens: it is an
  intersection, over all rationals, of unions of two wall filters
  (`atMostOneRealizable_eq_iInter`), and closed sets absorb arbitrary
  intersections — no countability, no enumeration.  Yet it is the
  model class of no finite disjunction of atoms: of `n + 1`
  deterministic systems some two land in one disjunct (pigeonhole),
  and the wall of their two points then models that disjunct — safety
  borrowed from each point separately, every dipped demand re-dipped
  at the sharper system's point — while realizing two distributions.
  **Closed does not imply judgment-definable**: judgment classes are
  exactly the finitely presented constructible sets over the
  principal-filter sub-basis, and one countable intersection already
  escapes every finite presentation.
-/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## A three-outcome state builder -/

/-- A three-outcome distribution from its three masses. -/
def ProbState.ofTriple (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) : ProbState (Fin 3) :=
  ⟨![a, b, c], ⟨fun v => by fin_cases v <;> simpa, by
    rw [Fin.sum_univ_three]; simpa⟩⟩

@[simp] theorem ProbState.ofTriple_apply_zero (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ((ProbState.ofTriple a b c ha hb hc habc : ProbState (Fin 3)) : Fin 3 → ℝ) 0
      = a := rfl

@[simp] theorem ProbState.ofTriple_apply_one (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ((ProbState.ofTriple a b c ha hb hc habc : ProbState (Fin 3)) : Fin 3 → ℝ) 1
      = b := rfl

@[simp] theorem ProbState.ofTriple_apply_two (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ((ProbState.ofTriple a b c ha hb hc habc : ProbState (Fin 3)) : Fin 3 → ℝ) 2
      = c := rfl

/-! ## The rectangle is a proper fragment

The four regions of the coupling witness: two disjoint open bands of
third-outcome mass (the branch commitments) and two disjoint open goal
corners (the branch reaches). -/

/-- Branch 1's forbidden band: high mass on the third outcome. -/
def couplingW₁ : Set (ProbState (Fin 3)) := {μ | 3/4 < (μ : Fin 3 → ℝ) 2}

/-- Branch 2's forbidden band: middling mass on the third outcome. -/
def couplingW₂ : Set (ProbState (Fin 3)) :=
  {μ | 1/2 < (μ : Fin 3 → ℝ) 2 ∧ (μ : Fin 3 → ℝ) 2 < 3/4}

/-- Branch 1's goal: high mass on the first outcome. -/
def couplingU₁ : Set (ProbState (Fin 3)) := {μ | 3/4 < (μ : Fin 3 → ℝ) 0}

/-- Branch 2's goal: high mass on the second outcome. -/
def couplingU₂ : Set (ProbState (Fin 3)) := {μ | 3/4 < (μ : Fin 3 → ℝ) 1}

theorem isOpen_couplingW₁ : IsOpen couplingW₁ :=
  isOpen_lt continuous_const
    ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)

theorem isOpen_couplingW₂ : IsOpen couplingW₂ := by
  have h : couplingW₂
      = {μ : ProbState (Fin 3) | 1/2 < (μ : Fin 3 → ℝ) 2}
        ∩ {μ : ProbState (Fin 3) | (μ : Fin 3 → ℝ) 2 < 3/4} := rfl
  rw [h]
  exact (isOpen_lt continuous_const
      ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)).inter
    (isOpen_lt ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)
      continuous_const)

theorem isOpen_couplingU₁ : IsOpen couplingU₁ :=
  isOpen_lt continuous_const
    ((continuous_apply (0 : Fin 3)).comp continuous_subtype_val)

theorem isOpen_couplingU₂ : IsOpen couplingU₂ :=
  isOpen_lt continuous_const
    ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val)

/-- **The rectangle is a proper fragment.**  The coupled disjunction
`(□⟨W₁⟩ ∧ ◇⟨U₁⟩) ∨ (□⟨W₂⟩ ∧ ◇⟨U₂⟩)` — walls on open sets written as
`probWall` of the complement — has the model class of no rectangle
`(⋁ j, □ g j) ∧ (⋀ h ∈ H, ◇ h)`, over any class of systems containing
the walls of closed sets.  The index family of safety disjuncts and
the collection of liveness demands are both arbitrary: the prose
witness's finiteness assumptions were never used. -/
theorem no_rectangle_coupling {P : ProbPenalty (Fin 3) → Prop}
    (hP : ∀ C : Set (ProbState (Fin 3)), IsClosed C → P (probWall C))
    {J : Type*} (g : J → ProbPenalty (Fin 3))
    (H : Set (ProbPenalty (Fin 3))) :
    ¬ ∀ σ, P σ →
        (((∃ j, g j ≤ σ) ∧ ∀ h ∈ H, Dip σ h) ↔
          (CoupledSat σ (probWall couplingW₁ᶜ) {probWall couplingU₁ᶜ}
            ∨ CoupledSat σ (probWall couplingW₂ᶜ) {probWall couplingU₂ᶜ})) := by
  classical
  intro hiff
  set ρ : ProbState (Fin 3) := ProbState.dirac 1 with hρdef
  set w : ProbState (Fin 3) :=
    ProbState.ofTriple 0 (3/8) (5/8) le_rfl (by norm_num) (by norm_num)
      (by norm_num) with hwdef
  -- the bait's region memberships
  have hρU₂ : ρ ∈ couplingU₂ := by
    simp only [hρdef, couplingU₂, Set.mem_setOf_eq, ProbState.dirac_apply_same]
    norm_num
  have hρW₁ : ρ ∉ couplingW₁ := by
    simp only [hρdef, couplingW₁, Set.mem_setOf_eq,
      ProbState.dirac_apply_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
    norm_num
  have hρW₂ : ρ ∉ couplingW₂ := by
    simp only [hρdef, couplingW₂, Set.mem_setOf_eq,
      ProbState.dirac_apply_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
    norm_num
  have hρU₁ : ρ ∉ couplingU₁ := by
    simp only [hρdef, couplingU₁, Set.mem_setOf_eq,
      ProbState.dirac_apply_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
    norm_num
  -- the crosser point's region memberships
  have hwW₂ : w ∈ couplingW₂ := by
    simp only [hwdef, couplingW₂, Set.mem_setOf_eq,
      ProbState.ofTriple_apply_two]
    norm_num
  have hwW₁ : w ∉ couplingW₁ := by
    simp only [hwdef, couplingW₁, Set.mem_setOf_eq,
      ProbState.ofTriple_apply_two]
    norm_num
  have hwU₁ : w ∉ couplingU₁ := by
    simp only [hwdef, couplingU₁, Set.mem_setOf_eq,
      ProbState.ofTriple_apply_zero]
    norm_num
  have hwU₂ : w ∉ couplingU₂ := by
    simp only [hwdef, couplingU₂, Set.mem_setOf_eq,
      ProbState.ofTriple_apply_one]
    norm_num
  -- the three refuting systems are in the class
  have hPfree : P (probWall couplingW₁ᶜ) := hP _ isOpen_couplingW₁.isClosed_compl
  have hPB : P (probWall {ρ}) := hP _ isClosed_singleton
  have hPX : P (probWall {ρ, w}) :=
    hP _ ((Set.finite_singleton w).insert ρ).isClosed
  -- the freest branch-1 system satisfies the first disjunct
  have hFree : CoupledSat (probWall couplingW₁ᶜ) (probWall couplingW₁ᶜ)
      {probWall couplingU₁ᶜ} := by
    refine ⟨le_rfl, ?_⟩
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    refine dip_probWall_compl_iff.mpr ⟨ProbState.dirac 0, ?_, ?_⟩
    · simp only [couplingU₁, Set.mem_setOf_eq, ProbState.dirac_apply_same]
      norm_num
    · have hmem : ProbState.dirac 0 ∈ couplingW₁ᶜ := by
        simp only [Set.mem_compl_iff, couplingW₁, Set.mem_setOf_eq,
          ProbState.dirac_apply_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
        norm_num
      rw [probWall_apply_of_mem hmem]
      exact ENNReal.zero_ne_top
  -- the sharpest branch-2 system satisfies the second disjunct
  have hB : CoupledSat (probWall {ρ}) (probWall couplingW₂ᶜ)
      {probWall couplingU₂ᶜ} := by
    refine ⟨probWall_le_iff.mpr fun μ hμ => ?_, ?_⟩
    · have hμW : μ ∈ couplingW₂ := not_not.mp hμ
      refine probWall_apply_of_not_mem ?_
      rw [Set.mem_singleton_iff]
      rintro rfl
      exact hρW₂ hμW
    · rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      refine dip_probWall_compl_iff.mpr ⟨ρ, hρU₂, ?_⟩
      rw [probWall_apply_of_mem (Set.mem_singleton _)]
      exact ENNReal.zero_ne_top
  -- pull the rectangle's data through the two disjunct models
  obtain ⟨⟨j₀, hj₀⟩, -⟩ := (hiff _ hPfree).mpr (Or.inl hFree)
  obtain ⟨-, hHall⟩ := (hiff _ hPB).mpr (Or.inr hB)
  -- every shared liveness demand is positive at the bait
  have hHρ : ∀ h ∈ H, 0 < h ρ := by
    intro h hh
    obtain ⟨μ, hμ⟩ := hHall h hh
    have hμρ : μ = ρ := by
      by_contra hne
      rw [probWall_apply_of_not_mem
        (fun hc => hne (Set.mem_singleton_iff.mp hc))] at hμ
      exact not_top_lt hμ
    rw [hμρ, probWall_apply_of_mem (Set.mem_singleton _)] at hμ
    exact hμ
  -- the crosser passes the rectangle...
  have hXrect : (∃ j, g j ≤ probWall {ρ, w})
      ∧ ∀ h ∈ H, Dip (probWall {ρ, w}) h := by
    constructor
    · refine ⟨j₀, fun μ => ?_⟩
      by_cases hμ : μ ∈ couplingW₁
      · have hnot : μ ∉ ({ρ, w} : Set (ProbState (Fin 3))) := by
          intro hmem
          rcases Set.mem_insert_iff.mp hmem with rfl | hmem'
          · exact hρW₁ hμ
          · rw [Set.mem_singleton_iff] at hmem'
            exact hwW₁ (hmem' ▸ hμ)
        rw [probWall_apply_of_not_mem hnot]
        exact le_top
      · have h0 := hj₀ μ
        rw [probWall_apply_of_mem ((Set.mem_compl_iff _ _).mpr hμ)] at h0
        exact h0.trans zero_le
    · intro h hh
      exact ⟨ρ, by
        rw [probWall_apply_of_mem (Set.mem_insert _ _)]
        exact hHρ h hh⟩
  -- ...but satisfies neither coupled disjunct
  rcases (hiff _ hPX).mp hXrect with hd | hd
  · -- no reach into U₁: both finite-penalty points miss it
    obtain ⟨μ, hμU, hμne⟩ :=
      dip_probWall_compl_iff.mp (hd.2 _ (Set.mem_singleton _))
    have hmem : μ ∈ ({ρ, w} : Set (ProbState (Fin 3))) := by
      by_contra hc
      exact hμne (probWall_apply_of_not_mem hc)
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem'
    · exact hρU₁ hμU
    · rw [Set.mem_singleton_iff] at hmem'
      exact hwU₁ (hmem' ▸ hμU)
  · -- the branch-2 wall is broken at the crosser's second point
    have hwc : w ∉ couplingW₂ᶜ := fun hc => hc hwW₂
    have h0 := hd.1 w
    rw [probWall_apply_of_not_mem hwc,
      probWall_apply_of_mem
        (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))] at h0
    simp at h0

/-- The rectangle refutation at the universe's citizens. -/
theorem no_rectangle_coupling_lsc {J : Type*} (g : J → ProbPenalty (Fin 3))
    (H : Set (ProbPenalty (Fin 3))) :
    ¬ ∀ σ, LowerSemicontinuous σ →
        (((∃ j, g j ≤ σ) ∧ ∀ h ∈ H, Dip σ h) ↔
          (CoupledSat σ (probWall couplingW₁ᶜ) {probWall couplingU₁ᶜ}
            ∨ CoupledSat σ (probWall couplingW₂ᶜ) {probWall couplingU₂ᶜ})) :=
  no_rectangle_coupling (fun _ hC => lowerSemicontinuous_probWall_iff.mpr hC)
    g H

/-! ## A class closed in every admissible topology, definable in none -/

/-- The possibilistically deterministic-or-inconsistent systems: at
most one distribution is realizable at finite penalty. -/
def atMostOneRealizable (V : Type*) [Fintype V] : Set (ProbPenalty V) :=
  {σ | Set.Subsingleton {μ | σ μ ≠ ⊤}}

/-- The wall on the open upper half-space `{q < μ 0}`: `⊤` there, `0`
off it. -/
noncomputable def upperHalfWall (q : ℚ) : ProbPenalty (Fin 2) :=
  probWall {μ : ProbState (Fin 2) | (q : ℝ) < (μ : Fin 2 → ℝ) 0}ᶜ

/-- The wall on the open lower half-space `{μ 0 < q}`: `⊤` there, `0`
off it. -/
noncomputable def lowerHalfWall (q : ℚ) : ProbPenalty (Fin 2) :=
  probWall {μ : ProbState (Fin 2) | (μ : Fin 2 → ℝ) 0 < (q : ℝ)}ᶜ

theorem lowerSemicontinuous_upperHalfWall (q : ℚ) :
    LowerSemicontinuous (upperHalfWall q) :=
  lowerSemicontinuous_probWall_iff.mpr
    (isOpen_lt continuous_const
      ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)).isClosed_compl

theorem lowerSemicontinuous_lowerHalfWall (q : ℚ) :
    LowerSemicontinuous (lowerHalfWall q) :=
  lowerSemicontinuous_probWall_iff.mpr
    (isOpen_lt ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)
      continuous_const).isClosed_compl

theorem upperHalfWall_le_iff {q : ℚ} {σ : ProbPenalty (Fin 2)} :
    upperHalfWall q ≤ σ
      ↔ ∀ μ : ProbState (Fin 2), (q : ℝ) < (μ : Fin 2 → ℝ) 0 → σ μ = ⊤ := by
  rw [upperHalfWall, probWall_le_iff]
  constructor
  · intro h μ hμ
    exact h μ fun hc => hc hμ
  · intro h μ hμ
    exact h μ (not_not.mp hμ)

theorem lowerHalfWall_le_iff {q : ℚ} {σ : ProbPenalty (Fin 2)} :
    lowerHalfWall q ≤ σ
      ↔ ∀ μ : ProbState (Fin 2), (μ : Fin 2 → ℝ) 0 < (q : ℝ) → σ μ = ⊤ := by
  rw [lowerHalfWall, probWall_le_iff]
  constructor
  · intro h μ hμ
    exact h μ fun hc => hc hμ
  · intro h μ hμ
    exact h μ (not_not.mp hμ)

/-- Two-outcome distributions agree once their first coordinates do. -/
theorem ProbState.ext_of_apply_zero {μ ν : ProbState (Fin 2)}
    (h : (μ : Fin 2 → ℝ) 0 = (ν : Fin 2 → ℝ) 0) : μ = ν := by
  have hμ := μ.sum_eq_one
  have hν := ν.sum_eq_one
  rw [Fin.sum_univ_two] at hμ hν
  have h1 : (μ : Fin 2 → ℝ) 1 = (ν : Fin 2 → ℝ) 1 := by linarith
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h
  · exact h1

/-- The at-most-one-realizable class is an intersection, over all
rationals, of unions of two wall filters: a system realizes at most
one distribution iff, at every rational threshold, it is fully walled
above it or fully walled below it. -/
theorem atMostOneRealizable_eq_iInter :
    atMostOneRealizable (Fin 2)
      = ⋂ q : ℚ,
          ({σ | upperHalfWall q ≤ σ} ∪ {σ | lowerHalfWall q ≤ σ}) := by
  ext σ
  simp only [Set.mem_iInter, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · -- at most one realizable point ⟹ at each threshold, one side is walled
    intro hσ q
    rw [or_iff_not_imp_left]
    intro hup
    rw [upperHalfWall_le_iff] at hup
    push Not at hup
    obtain ⟨μ₁, hμ₁q, hμ₁ne⟩ := hup
    rw [lowerHalfWall_le_iff]
    intro μ hμq
    by_contra hne
    have heq : μ = μ₁ := hσ hne hμ₁ne
    rw [heq] at hμq
    exact lt_asymm hμq hμ₁q
  · -- walled at each threshold ⟹ two realizable points cannot differ
    intro hall μ₁ hμ₁ μ₂ hμ₂
    by_contra hne
    have hcoord : (μ₁ : Fin 2 → ℝ) 0 ≠ (μ₂ : Fin 2 → ℝ) 0 :=
      fun h => hne (ProbState.ext_of_apply_zero h)
    rcases lt_or_gt_of_ne hcoord with hlt | hlt
    · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
      rcases hall q with hup | hlo
      · rw [upperHalfWall_le_iff] at hup
        exact hμ₂ (hup μ₂ hq₂)
      · rw [lowerHalfWall_le_iff] at hlo
        exact hμ₁ (hlo μ₁ hq₁)
    · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
      rcases hall q with hup | hlo
      · rw [upperHalfWall_le_iff] at hup
        exact hμ₁ (hup μ₁ hq₂)
      · rw [lowerHalfWall_le_iff] at hlo
        exact hμ₂ (hlo μ₂ hq₁)

/-- **Closed in every admissible topology.**  On any carrier of
systems — a type with any topology, read into the two-outcome flat
penalties — in which every citizen's principal filter is closed, the
at-most-one-realizable class pulls back closed.  With the carrier the
citizens themselves (`f` the inclusion) this is the memo statement;
the identity behind it is `atMostOneRealizable_eq_iInter`, and no
countability enters: closed sets absorb arbitrary intersections. -/
theorem isClosed_atMostOneRealizable {X : Type*} [TopologicalSpace X]
    (f : X → ProbPenalty (Fin 2))
    (hf : ∀ χ : ProbPenalty (Fin 2), LowerSemicontinuous χ →
      IsClosed {x | χ ≤ f x}) :
    IsClosed (f ⁻¹' atMostOneRealizable (Fin 2)) := by
  have hpre : f ⁻¹' atMostOneRealizable (Fin 2)
      = ⋂ q : ℚ,
          ({x | upperHalfWall q ≤ f x} ∪ {x | lowerHalfWall q ≤ f x}) := by
    rw [atMostOneRealizable_eq_iInter, Set.preimage_iInter]
    simp only [Set.preimage_union]
    rfl
  rw [hpre]
  exact isClosed_iInter fun q =>
    (hf _ (lowerSemicontinuous_upperHalfWall q)).union
      (hf _ (lowerSemicontinuous_lowerHalfWall q))

/-- The first coordinate of the `k`-th pigeon point: `k / (n + 1)`. -/
noncomputable def pigeonCoord (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (k : ℝ) / (n + 1)

/-- `n + 1` pairwise-distinct two-outcome distributions with rational
coordinates. -/
noncomputable def pigeonPoints (n : ℕ) (k : Fin (n + 1)) :
    ProbState (Fin 2) :=
  ProbState.ofPair (pigeonCoord n k) (1 - pigeonCoord n k)
    (by
      unfold pigeonCoord
      positivity)
    (by
      unfold pigeonCoord
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hk : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (k.isLt).le
      rw [sub_nonneg, div_le_one hpos]
      exact hk)
    (by ring)

theorem pigeonPoints_injective (n : ℕ) :
    Function.Injective (pigeonPoints n) := by
  intro k₁ k₂ h
  have h0 := congrArg (fun μ : ProbState (Fin 2) => (μ : Fin 2 → ℝ) 0) h
  simp only [pigeonPoints, ProbState.ofPair_apply_zero, pigeonCoord] at h0
  have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [div_eq_div_iff hpos hpos] at h0
  have hk : (k₁ : ℝ) = (k₂ : ℝ) := mul_right_cancel₀ hpos h0
  exact Fin.ext (by exact_mod_cast hk)

/-- **Closed does not imply judgment-definable** (the pigeonhole
witness).  The at-most-one-realizable class — closed in every
admissible topology by `isClosed_atMostOneRealizable` — is not the
model class of any finite disjunction of atoms, over any class of
systems containing the walls of finite sets.  Of the `n + 1`
deterministic systems `probWall {pigeonPoints n k}` some two land in
one disjunct; the wall of their two points then models that disjunct
— safety borrowed pointwise, every undipped liveness demand forced
below the sharper wall — while realizing two distributions. -/
theorem atMostOneRealizable_not_definable {P : ProbPenalty (Fin 2) → Prop}
    (hP : ∀ S : Set (ProbState (Fin 2)), S.Finite → P (probWall S)) :
    ¬ ∃ (n : ℕ) (u : Fin n → ProbPenalty (Fin 2))
        (𝒱 : Fin n → Set (ProbPenalty (Fin 2))),
        ∀ σ, P σ →
          ((∃ i, CoupledSat σ (u i) (𝒱 i))
            ↔ σ ∈ atMostOneRealizable (Fin 2)) := by
  rintro ⟨n, u, 𝒱, hiff⟩
  classical
  -- each deterministic system models some disjunct
  have hmem : ∀ k : Fin (n + 1),
      ∃ i, CoupledSat (probWall {pigeonPoints n k}) (u i) (𝒱 i) := by
    intro k
    refine (hiff _ (hP _ (Set.finite_singleton _))).mpr ?_
    intro μ₁ h₁ μ₂ h₂
    have hm₁ : μ₁ ∈ ({pigeonPoints n k} : Set (ProbState (Fin 2))) := by
      by_contra hc
      exact h₁ (probWall_apply_of_not_mem hc)
    have hm₂ : μ₂ ∈ ({pigeonPoints n k} : Set (ProbState (Fin 2))) := by
      by_contra hc
      exact h₂ (probWall_apply_of_not_mem hc)
    rw [Set.mem_singleton_iff] at hm₁ hm₂
    rw [hm₁, hm₂]
  choose φ hφ using hmem
  -- two pigeons share a disjunct
  obtain ⟨k₁, k₂, hkne, hkeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt φ (by simp)
  have h₁ := hφ k₁
  have h₂ := hφ k₂
  rw [← hkeq] at h₂
  set p₁ : ProbState (Fin 2) := pigeonPoints n k₁ with hp₁
  set p₂ : ProbState (Fin 2) := pigeonPoints n k₂ with hp₂
  have hpne : p₁ ≠ p₂ := fun h => hkne (pigeonPoints_injective n h)
  -- the two-point wall borrows the shared disjunct's safety...
  have hsafe : u (φ k₁) ≤ probWall {p₁, p₂} := by
    intro μ
    by_cases hμ : μ ∈ ({p₁, p₂} : Set (ProbState (Fin 2)))
    · rw [probWall_apply_of_mem hμ]
      rcases Set.mem_insert_iff.mp hμ with rfl | hμ'
      · have hle := h₁.1 p₁
        rwa [probWall_apply_of_mem (Set.mem_singleton _)] at hle
      · rw [Set.mem_singleton_iff] at hμ'
        subst hμ'
        have hle := h₂.1 p₂
        rwa [probWall_apply_of_mem (Set.mem_singleton _)] at hle
    · rw [probWall_apply_of_not_mem hμ]
      exact le_top
  -- ...but realizes two distributions, so it is outside the class
  have hnot : probWall {p₁, p₂} ∉ atMostOneRealizable (Fin 2) := by
    intro hsub
    apply hpne
    refine hsub ?_ ?_
    · rw [Set.mem_setOf_eq,
        probWall_apply_of_mem (Set.mem_insert _ _)]
      exact ENNReal.zero_ne_top
    · rw [Set.mem_setOf_eq,
        probWall_apply_of_mem
          (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))]
      exact ENNReal.zero_ne_top
  -- so some liveness demand goes undipped; it transfers to the sharper wall
  have hpairP : P (probWall {p₁, p₂}) :=
    hP _ ((Set.finite_singleton p₂).insert p₁)
  have hnosat : ¬ CoupledSat (probWall {p₁, p₂}) (u (φ k₁)) (𝒱 (φ k₁)) := by
    intro hsat
    exact hnot ((hiff _ hpairP).mp ⟨φ k₁, hsat⟩)
  have hbad : ∃ v ∈ 𝒱 (φ k₁), ¬ Dip (probWall {p₁, p₂}) v := by
    by_contra hall
    push Not at hall
    exact hnosat ⟨hsafe, hall⟩
  obtain ⟨v, hv, hnd⟩ := hbad
  have hvle : v ≤ probWall {p₁} :=
    (not_dip_iff_le.mp hnd).trans
      (probWall_le_probWall_iff.mpr
        (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  exact absurd (h₁.2 v hv) (not_dip_iff_le.mpr hvle)

/-- The refutation instantiated at the universe's citizens. -/
theorem atMostOneRealizable_not_definable_lsc :
    ¬ ∃ (n : ℕ) (u : Fin n → ProbPenalty (Fin 2))
        (𝒱 : Fin n → Set (ProbPenalty (Fin 2))),
        ∀ σ, LowerSemicontinuous σ →
          ((∃ i, CoupledSat σ (u i) (𝒱 i))
            ↔ σ ∈ atMostOneRealizable (Fin 2)) :=
  atMostOneRealizable_not_definable fun _ hS =>
    lowerSemicontinuous_probWall_iff.mpr hS.isClosed

end SuFunctor.Universe
