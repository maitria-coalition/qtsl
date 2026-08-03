import Qtsl.CellFlavorsExpansion

/-!
# The cell rule pair at flavored schemas, coverage, and pruning discharge

The two certificate rules that read the `cell` box — Cell-In-Interior
(from a strict-interior premise, conclude the full one-hot vector) and
Cell-Out (from a strict separating witness, zero one indicator) — are
proven sound against the raw `SimpC` schema (`sound_cellInInterior`,
`sound_cellOut` in `Qtsl.Soundness`). This module restates the pair's
semantic content against the flavored membership predicates of
`Qtsl.CellFlavors`, so that the rules' premises become *dischargeable*
at flavored schemas — restatement + transport, never new soundness:

1. **Pinning** (Cell-In-Interior's step): strict membership determines
   the box's one-hot cell. Tensor-simplicial
   (`CellSchemaTS.interior_onehot`): dischargeable from per-cluster
   exclusion certificates — `product_exclusion` composed with
   `interior_determines`. Full-semialgebraic
   (`CellSchemaSA.interior_onehot`): hypothesis-free —
   `sign_exclusion` is a theorem of the presentation.
2. **Zeroing** (Cell-Out's step): a single refutation witness kills
   membership. Tensor-simplicial: one cluster-level refutation
   (`notMem_of_cluster`, `onehot_ne_of_cluster`) — at 1-D cluster
   complexes this is exactly the landed 1-D witness vocabulary.
   Full-semialgebraic: one strict opposite-sign arithmetic atom at a
   named presenter (`signNotMem_of_witness`,
   `CellSchemaSA.onehot_ne_of_witness`) — plain arithmetic, no
   geometry.
3. **Coverage** (the second vacuity door): every value vector lies
   weakly in some sign cell (`signMem_total`) — full-roster
   semialgebraic schemas cannot vacuate pointwise for want of a
   containing cell. Coverage is free *because* the signs are weak;
   walls belong weakly to both neighbors and strictly to neither.
4. **Pruning discharge** (the first consumers of
   `CellSchemaSA.EmptyCellOk`): universal per-cell obligations checked
   on unpruned cells extend to every inhabited cell
   (`EmptyCellOk.prune_discharge` — a branch over a pruned cell is ex
   falso), and an emptiness-certified pruned roster still covers its
   admitted points (`memVia_total_unpruned`).
-/

namespace PPLC

/-! ## Tensor-simplicial: the rule pair -/

/-- **Pinning (Cell-In-Interior, TS)**: under per-cluster exclusion
certificates, a point strictly inside product cell `κ` forces any
weakly-containing product cell — in particular the box's one-hot
cell — to be `κ`. The premise burden is additive in the clusters
(`product_exclusion`), never quadratic in the exponentially many
product cells. -/
theorem CellSchemaTS.interior_onehot {T : CellSchemaTS}
    (hd : ∀ c, (T.complexes c).CellIntDisjoint) {κ k : T.CellIdx}
    {x : Fin T.D → ℚ} (hs : T.MemStrict κ x) (hk : T.Mem k x) : k = κ :=
  T.interior_determines (T.product_exclusion hd) hs hk

/-- **Witness transport (Cell-Out, TS)**: one cluster-level refutation
kills product membership — the Cell-Out witness against a product cell
is a witness against its chosen cell at any single cluster. -/
theorem CellSchemaTS.notMem_of_cluster {T : CellSchemaTS}
    {ν : T.CellIdx} {x : Fin T.D → ℚ} (c : Fin T.m)
    (hc : ¬ MaskRegion (T.complexes c)
      ((T.complexes c).cells.get (ν c)).1
      ((T.complexes c).cells.get (ν c)).2 (T.proj c x)) :
    ¬ T.Mem ν x :=
  fun h => hc (h c)

/-- **Zeroing (Cell-Out, TS)**: with a cluster-level refutation of cell
`ν` in hand, the box's one-hot cell (weakly containing the input) is
not `ν` — its indicator is zero. -/
theorem CellSchemaTS.onehot_ne_of_cluster {T : CellSchemaTS}
    {k ν : T.CellIdx} {x : Fin T.D → ℚ} (c : Fin T.m)
    (hc : ¬ MaskRegion (T.complexes c)
      ((T.complexes c).cells.get (ν c)).1
      ((T.complexes c).cells.get (ν c)).2 (T.proj c x))
    (hk : T.Mem k x) : k ≠ ν :=
  fun he => T.notMem_of_cluster c hc (he ▸ hk)

/-! ## Full-semialgebraic: the rule pair -/

/-- **Pinning (Cell-In-Interior, SA)**: a value vector strictly inside
sign cell `σ` forces any weakly-containing sign cell to be `σ` — with
no disjointness hypothesis at all: `sign_exclusion` is a theorem of
the presentation. The rule's side condition discharges for free. -/
theorem CellSchemaSA.interior_onehot (S : CellSchemaSA)
    {y : Fin S.k → ℚ} {σ τ : Fin S.k → Bool}
    (hs : S.MemViaStrict y σ) (hw : S.MemVia y τ) : τ = σ :=
  CellFlavorsExpansion.sign_interior_determines hs hw

/-- **Witness (Cell-Out, SA)**: a single strict opposite-sign atom at a
named presenter refutes weak sign-cell membership — the Cell-Out
witness at a semialgebraic schema is plain arithmetic on one
presenter's output wire, no geometry. -/
theorem signNotMem_of_witness {k : ℕ} {y : Fin k → ℚ}
    {σ : Fin k → Bool} (i : Fin k) (hi : signVal (σ i) (y i) < 0) :
    ¬ SignMem y σ :=
  fun h => absurd (h i) (not_le.mpr hi)

/-- **Zeroing (Cell-Out, SA)**: with a strict opposite-sign witness
against sign cell `τ`, the box's one-hot cell (weakly containing the
value vector) is not `τ`. -/
theorem CellSchemaSA.onehot_ne_of_witness (S : CellSchemaSA)
    {y : Fin S.k → ℚ} {σ τ : Fin S.k → Bool} (i : Fin S.k)
    (hi : signVal (τ i) (y i) < 0) (hσ : S.MemVia y σ) : σ ≠ τ :=
  fun he => signNotMem_of_witness i hi (he ▸ hσ)

/-! ## Coverage: the second vacuity door, closed structurally -/

/-- **Sign totality**: every value vector lies weakly in some sign cell
— take the sign of each coordinate, walls resolving to `⊕`. With the
full roster, a semialgebraic cell application can never lack a
containing cell, so schema-induced pointwise vacuity is structurally
impossible. -/
theorem signMem_total {k : ℕ} (y : Fin k → ℚ) : ∃ σ, SignMem y σ := by
  refine ⟨fun i => decide (0 ≤ y i), fun i => ?_⟩
  show 0 ≤ signVal (decide (0 ≤ y i)) (y i)
  by_cases h : 0 ≤ y i
  · rw [decide_eq_true h]
    simpa [signVal] using h
  · rw [decide_eq_false h]
    simp only [signVal, Bool.false_eq_true, if_false]
    -- `h : ¬ 0 ≤ y i`; linarith's preprocessing reads it as `y i < 0`
    linarith

/-- Schema-level face of coverage. -/
theorem CellSchemaSA.memVia_total (S : CellSchemaSA) (y : Fin S.k → ℚ) :
    ∃ σ, S.MemVia y σ :=
  signMem_total y

/-! ## The pruning discharge: `EmptyCellOk`'s first consumers -/

/-- **Wholesale pruning discharge**: at a value vector whose emptiness
certificates check out (`EmptyCellOk`), universal per-cell obligations
verified on the *unpruned* cells extend to every cell the vector
weakly inhabits — a branch over a pruned cell is ex falso. This is the
witness-economy payoff: emptiness certificates are schema-level data
precisely because they prune universal downstream obligations
wholesale. -/
theorem CellSchemaSA.EmptyCellOk.prune_discharge {S : CellSchemaSA}
    {y : Fin S.k → ℚ} (h : S.EmptyCellOk y)
    {P : (Fin S.k → Bool) → Prop}
    (hP : ∀ σ, S.prunedEmpty σ = false → S.MemVia y σ → P σ) :
    ∀ σ, S.MemVia y σ → P σ := by
  intro σ hmem
  cases hp : S.prunedEmpty σ with
  | false => exact hP σ hp hmem
  | true => exact absurd hmem (h σ hp)

/-- **Honest coverage for pruned rosters**: at an admitted value vector
(`EmptyCellOk`), some *unpruned* sign cell weakly contains it — an
emptiness-certified pruned roster still covers, so pruning with
certificates never reopens the pointwise vacuity door. -/
theorem CellSchemaSA.memVia_total_unpruned {S : CellSchemaSA}
    {y : Fin S.k → ℚ} (h : S.EmptyCellOk y) :
    ∃ σ, S.prunedEmpty σ = false ∧ S.MemVia y σ := by
  obtain ⟨σ, hσ⟩ := S.memVia_total y
  cases hp : S.prunedEmpty σ with
  | false => exact ⟨σ, hp, hσ⟩
  | true => exact absurd hσ (h σ hp)

#print axioms CellSchemaTS.interior_onehot
#print axioms CellSchemaSA.interior_onehot
#print axioms signNotMem_of_witness
#print axioms signMem_total
#print axioms CellSchemaSA.EmptyCellOk.prune_discharge
#print axioms CellSchemaSA.memVia_total_unpruned

end PPLC
