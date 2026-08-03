import SuFunctor.Universe.DemonicClock

/-! # The spacelike seam: a closed trace relation is one more conjunct

Two spatial cells sharing a boundary interface compose across the seam
by exactly the machinery the demonic clock already landed — because
that machinery never consumed temporal structure.  The joint carrier of
the two cells is the product of their record spaces ("just another
`K`"); the seam constraint — trace/flux compatibility at the interface
— is a **closed relation** on that product; and its indicator penalty
is a wall like any other, entering entailment as one more conjunct on
the premise floor.  No new compositor exists in this file, and that is
the theorem.

Contents:

* **The carrier-generic wall.**  `seamWall B` (`0` on `B`, `⊤` off it)
  on an *arbitrary* carrier — the generic sibling of `wall`
  (`BelState`) and `probWall` (`ProbState`), which are untouched.
  Citizenship is exactly closedness of the relation
  (`lowerSemicontinuous_seamWall_iff`), by the same sublevel argument,
  which never used anything about either concrete carrier.
* **The canonical closed relation.**  `traceAgree τ₁ τ₂` — equality of
  boundary traces — is closed whenever the trace maps are continuous
  into a Hausdorff trace fibre (`isClosed_traceAgree`): the two fees a
  spacelike seam actually pays, both on the *interface data*, neither
  on the cells.
* **The seam is a conjunct.**  `coupledSat_sup_seamWall_iff`:
  satisfaction of the seam-joined atom is satisfaction of the original
  atom plus hard violation (`⊤`) off the trace relation.
* **The instantiated criterion.**  `spacelike_seam_union_refinement_iff`
  and its canonical trace form: entailment across a spacelike seam is
  decided by the same finite blocking table with the trace wall joined
  into the premise floor — `cross_site_union_refinement_iff_lsc` at the
  two-cell joint carrier, the wall's citizenship discharged by
  closedness of the relation.  The clocked seam was the harder case;
  the spacelike seam is its degenerate-transport instance, with no
  realization quantifier anywhere.
* **Closedness is load-bearing at statement level.**
  `not_lowerSemicontinuous_seamWall_halfSpace`: the wall of the open
  half-space relation `{p | p.1 < p.2}` is *not* a citizen — dropping
  closedness of the trace relation is unrepairable, not merely
  unproved.  Positive control: the diagonal trace relation on `ℝ`
  (`lowerSemicontinuous_seamWall_diagonal`).
-/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## The carrier-generic wall -/

section SeamWall

variable {K : Type*}

open Classical in
/-- The wall of a set of an arbitrary carrier: `0` inside, `⊤`
outside.  The carrier-generic sibling of `wall` (on `BelState`) and
`probWall` (on `ProbState`); a seam's trace relation enters the
premise floor as `seamWall B` on the joint carrier. -/
noncomputable def seamWall (B : Set K) : K → ℝ≥0∞ :=
  fun x => if x ∈ B then 0 else ⊤

theorem seamWall_apply_of_mem {B : Set K} {x : K} (h : x ∈ B) :
    seamWall B x = 0 := by simp [seamWall, h]

theorem seamWall_apply_of_not_mem {B : Set K} {x : K} (h : x ∉ B) :
    seamWall B x = ⊤ := by simp [seamWall, h]

/-- Dominating the seam wall is hard violation off the relation. -/
theorem seamWall_le_iff {B : Set K} {σ : K → ℝ≥0∞} :
    seamWall B ≤ σ ↔ ∀ x ∉ B, σ x = ⊤ := by
  constructor
  · intro h x hx
    have := h x
    rw [seamWall_apply_of_not_mem hx] at this
    exact top_le_iff.mp this
  · intro h x
    by_cases hx : x ∈ B
    · rw [seamWall_apply_of_mem hx]; exact zero_le
    · rw [seamWall_apply_of_not_mem hx, h x hx]

variable [TopologicalSpace K]

/-- **Citizenship of the wall is exactly closedness of the relation**,
over any topological carrier: the sublevel argument of
`lowerSemicontinuous_probWall_iff`, which never consumed anything
about its concrete carrier. -/
theorem lowerSemicontinuous_seamWall_iff {B : Set K} :
    LowerSemicontinuous (seamWall B) ↔ IsClosed B := by
  constructor
  · intro h
    have hB : B = seamWall B ⁻¹' Set.Iic 0 := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_preimage, Set.mem_Iic, seamWall_apply_of_mem hx,
          le_refl]
      · intro hx
        by_contra hBx
        rw [Set.mem_preimage, Set.mem_Iic, seamWall_apply_of_not_mem hBx,
          top_le_iff] at hx
        exact ENNReal.zero_ne_top hx
    rw [hB]
    exact lowerSemicontinuous_iff_isClosed_preimage.mp h 0
  · intro hB x y hy
    by_cases hx : x ∈ B
    · rw [seamWall_apply_of_mem hx] at hy
      exact absurd hy (not_lt.mpr zero_le)
    · have htop : y < ⊤ := by
        rw [seamWall_apply_of_not_mem hx] at hy; exact hy
      filter_upwards [hB.isOpen_compl.mem_nhds hx] with z hz
      rw [seamWall_apply_of_not_mem hz]
      exact htop

end SeamWall

/-! ## The two-cell joint carrier and the canonical trace relation -/

section TwoCell

variable {K₁ K₂ : Type*}

/-- The canonical trace relation of a spacelike seam: **equality of
boundary traces**.  `τ₁` and `τ₂` read each cell's record at the
shared interface (germ coordinates on the collar); the relation holds
of a joint record exactly when the two readings agree. -/
def traceAgree {T : Type*} (τ₁ : K₁ → T) (τ₂ : K₂ → T) : Set (K₁ × K₂) :=
  {p | τ₁ p.1 = τ₂ p.2}

theorem mem_traceAgree_iff {T : Type*} {τ₁ : K₁ → T} {τ₂ : K₂ → T}
    {p : K₁ × K₂} : p ∈ traceAgree τ₁ τ₂ ↔ τ₁ p.1 = τ₂ p.2 :=
  Iff.rfl

variable [TopologicalSpace K₁] [TopologicalSpace K₂]

/-- **The two fees of a spacelike seam**: trace agreement is a closed
relation on the joint carrier whenever the trace maps are continuous
into a Hausdorff trace fibre.  Both fees live on the interface data;
neither cell owes compactness, separation, or anything else. -/
theorem isClosed_traceAgree {T : Type*} [TopologicalSpace T] [T2Space T]
    {τ₁ : K₁ → T} {τ₂ : K₂ → T} (h₁ : Continuous τ₁) (h₂ : Continuous τ₂) :
    IsClosed (traceAgree τ₁ τ₂) :=
  isClosed_eq (h₁.comp continuous_fst) (h₂.comp continuous_snd)

/-- The canonical trace wall is a citizen. -/
theorem lowerSemicontinuous_seamWall_traceAgree {T : Type*}
    [TopologicalSpace T] [T2Space T] {τ₁ : K₁ → T} {τ₂ : K₂ → T}
    (h₁ : Continuous τ₁) (h₂ : Continuous τ₂) :
    LowerSemicontinuous (seamWall (traceAgree τ₁ τ₂)) :=
  lowerSemicontinuous_seamWall_iff.mpr (isClosed_traceAgree h₁ h₂)

end TwoCell

/-! ## The seam is one more conjunct on the premise floor -/

section SeamConjunct

variable {K : Type*} {m : ℕ}

/-- **Trace compatibility is one more premise-floor conjunct**:
satisfaction of the seam-joined atom is satisfaction of the original
atom plus hard violation off the trace relation.  The seam adds a
constraint, never a compositor. -/
theorem coupledSat_sup_seamWall_iff {σ u : K → ℝ≥0∞} {B : Set K}
    {𝒱 : Set (K → ℝ≥0∞)} :
    CoupledSat σ (u ⊔ seamWall B) 𝒱
      ↔ (∀ x ∉ B, σ x = ⊤) ∧ CoupledSat σ u 𝒱 := by
  rw [coupledSat_sup_wall_iff, seamWall_le_iff]

variable [TopologicalSpace K]

/-- **The spacelike-seam entailment criterion, relation form**: for any
closed relation `B` on a carrier, union-refinement from the
seam-joined premise atom is decided by the finite blocking table of
the joined atom — `cross_site_union_refinement_iff_lsc` with the
wall's citizenship discharged by closedness.  Stated over one carrier
`K` because the criterion is carrier-blind; the two-cell reading
instantiates `K := K₁ × K₂` below. -/
theorem seam_union_refinement_iff {B : Set K} (hB : IsClosed B)
    {u : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} {u' : Fin m → K → ℝ≥0∞}
    {𝒱' : Fin m → Set (K → ℝ≥0∞)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ seamWall B) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ seamWall B) 𝒱 u' c :=
  cross_site_union_refinement_iff_lsc hu
    (lowerSemicontinuous_seamWall_iff.mpr hB) h𝒱'

end SeamConjunct

section TwoCellCriterion

variable {K₁ K₂ : Type*} [TopologicalSpace K₁] [TopologicalSpace K₂] {m : ℕ}

/-- **THE INSTANCE (memo §2.1): a spacelike seam is a sampler wall
with less structure.**  Two cells' joint carrier is the product of
their record spaces; a closed trace relation on it enters as one more
premise-floor conjunct; and entailment across the seam is the same
finite blocking table — no new compositor, no realization quantifier,
no rate mismatch.  The clocked seam was the harder case; this is its
degenerate-transport instance. -/
theorem spacelike_seam_union_refinement_iff {B : Set (K₁ × K₂)}
    (hB : IsClosed B) {u : K₁ × K₂ → ℝ≥0∞} {𝒱 : Set (K₁ × K₂ → ℝ≥0∞)}
    {u' : Fin m → K₁ × K₂ → ℝ≥0∞} {𝒱' : Fin m → Set (K₁ × K₂ → ℝ≥0∞)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ seamWall B) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ seamWall B) 𝒱 u' c :=
  seam_union_refinement_iff hB hu h𝒱'

/-- The canonical instance: **entailment across an
equality-of-boundary-traces seam is the blocking table**, with the
wall's citizenship paid by the two interface fees (continuous traces,
Hausdorff trace fibre). -/
theorem spacelike_seam_trace_union_refinement_iff {T : Type*}
    [TopologicalSpace T] [T2Space T] {τ₁ : K₁ → T} {τ₂ : K₂ → T}
    (h₁ : Continuous τ₁) (h₂ : Continuous τ₂)
    {u : K₁ × K₂ → ℝ≥0∞} {𝒱 : Set (K₁ × K₂ → ℝ≥0∞)}
    {u' : Fin m → K₁ × K₂ → ℝ≥0∞} {𝒱' : Fin m → Set (K₁ × K₂ → ℝ≥0∞)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ →
        CoupledSat σ (u ⊔ seamWall (traceAgree τ₁ τ₂)) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c →
          Blocked (u ⊔ seamWall (traceAgree τ₁ τ₂)) 𝒱 u' c :=
  spacelike_seam_union_refinement_iff (isClosed_traceAgree h₁ h₂) hu h𝒱'

end TwoCellCriterion

/-! ## Closedness is load-bearing at statement level -/

section Witnesses

/-- **Dropping closedness of the trace relation is unrepairable**: the
wall of the canonical *open* half-space relation on the two-cell
carrier `ℝ × ℝ` is not a citizen.  No lsc discharge exists for a
non-closed relation, by `lowerSemicontinuous_seamWall_iff` — so the
closedness hypothesis of the seam criterion cannot be weakened, only
moved. -/
theorem not_lowerSemicontinuous_seamWall_halfSpace :
    ¬ LowerSemicontinuous (seamWall {p : ℝ × ℝ | p.1 < p.2}) := by
  rw [lowerSemicontinuous_seamWall_iff]
  intro h
  have hpre : IsClosed (Set.Ioi (0 : ℝ)) := by
    have h2 := h.preimage
      (continuous_const.prodMk continuous_id :
        Continuous fun t : ℝ => ((0 : ℝ), t))
    convert h2 using 1
    ext t
    simp only [Set.mem_Ioi, Set.mem_preimage, Set.mem_setOf_eq]
  have h0 : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    rw [← hpre.closure_eq, closure_Ioi]
    exact Set.self_mem_Ici
  exact lt_irrefl 0 (Set.mem_Ioi.mp h0)

/-- Positive control: the diagonal trace relation on `ℝ` (identity
traces into a Hausdorff fibre) is a citizen. -/
theorem lowerSemicontinuous_seamWall_diagonal :
    LowerSemicontinuous (seamWall (traceAgree (id : ℝ → ℝ) id)) :=
  lowerSemicontinuous_seamWall_traceAgree continuous_id continuous_id

end Witnesses

end SuFunctor.Universe

#print axioms SuFunctor.Universe.lowerSemicontinuous_seamWall_iff
#print axioms SuFunctor.Universe.isClosed_traceAgree
#print axioms SuFunctor.Universe.coupledSat_sup_seamWall_iff
#print axioms SuFunctor.Universe.spacelike_seam_union_refinement_iff
#print axioms SuFunctor.Universe.spacelike_seam_trace_union_refinement_iff
#print axioms SuFunctor.Universe.not_lowerSemicontinuous_seamWall_halfSpace
#print axioms SuFunctor.Universe.lowerSemicontinuous_seamWall_diagonal
