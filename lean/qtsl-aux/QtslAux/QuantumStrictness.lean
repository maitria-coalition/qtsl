/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumTower

/-! # Strictness: when a coarse-graining genuinely loses off-diagonal mass

The tower module landed the inequality — `offDiagMass_pushforward_le`,
"coarser is more classical" as a real-valued Lyapunov-style statement —
and its own proof exposes exactly two slack sources: the within-fiber
terms it DROPS (off-diagonal fine entries inside a merged block, which
land on the coarse diagonal and are erased from the coarse mass), and
the triangle-inequality slack per cross block (`‖∑ block‖ ≤ ∑ ‖·‖`,
strict exactly at misaligned — partially or exactly cancelling —
entries). This module characterizes when the drop is STRICT, by making
both steps tight per block:

* **The block ledger**: `blockMass f Q c c'` is the fine off-diagonal
  ℓ¹ mass the `(c, c')` fiber block contributes to `Q.offDiagMass`
  (the fiber-partition regroup `offDiagMass_eq_sum_blockMass` says the
  contributions add up to the whole), and each coarse block's
  contribution to the coarse mass is bounded by its block's ledger
  (`blockContribution_le`).

* **The characterization** (`offDiagMass_pushforward_eq_iff` /
  `offDiagMass_pushforward_lt_iff`): the pushforward preserves the
  off-diagonal mass iff EVERY coarse block's contribution attains its
  block's fine ℓ¹ mass (`NonCancelling`) — unpacked
  (`nonCancelling_iff`): every merged block is off-diagonally silent
  (`f a = f b → a ≠ b → gram a b = 0`) AND every cross block is
  norm-additive (no cancellation). Strict iff some merged block
  carries a nonzero off-diagonal entry
  (`offDiagMass_pushforward_lt_of_merged_pair`) or some cross block
  cancels at all.

* **Equality by cancellation is impossible**
  (`offDiagMass_pushforward_lt_of_cancellation`): a nonzero entry in a
  cross block whose coarse entry vanishes — exact cancellation —
  FORCES a strict drop. Equality never hides cancellation; the
  equality condition IS block-wise non-cancellation. The landed
  `mergeMeasure`/`degeneracy` decoherence witness is exactly this
  specimen, and both strictness mechanisms are exercised on the site:
  the decohering rung of the diamond tower is strict via the
  cancelling `(pointLo, span)` cross pair
  (`diamondMeasure_cancellation_strict`) AND independently via the
  erased `(pointLo, pointHi)` merged pair
  (`diamondMeasure_merged_pair_strict`, Gram entry `−1`).

* **Lazy rungs never drop**, in both senses: injective (padding)
  merges preserve the mass on the nose
  (`offDiagMass_pushforward_of_injective`), and every rung past a
  diagonal stage is an equality
  (`offDiagMass_pushforward_of_isDiagonal`; on the diamond tower,
  `towerMeasure_offDiagMass_succ_eq_of_pos` — the toy's mass profile
  drops strictly exactly once, at the decohering rung).

* **Equality without diagonality is constructible** — coarse-graining
  is not automatically decoherence: `alignMeasure` (branch vectors
  `(3/10, 0)`, `(0, 2/5)`, `(3/10, 2/5)` at the state `(1, 0)` — the
  same 3-4-5 total as `mergeMeasure`, a different branch
  decomposition) has its merged pair orthogonal and its cross blocks
  positively aligned, so the genuine non-injective merge `mergeCoarse`
  preserves its off-diagonal mass `1/2` exactly
  (`alignMeasure_offDiagMass_pushforward_eq`) while fine and coarse
  measures both remain genuinely quantum. Alignment vs cancellation is
  purely a property of the branch decomposition.

Scope fences inherited from the record tier: finite index types,
matrix grade, toy grade at the witnesses; the physical reading
(strictness = the coarse description genuinely forgets quantum
structure; equality = lossless re-indexing of the off-diagonal data)
is interpretation, not new claims. -/

namespace Qtsl

namespace QuantumStrictness

open Matrix DiamondSite QuantumRecords QuantumDForm QuantumTransport
  QuantumCoarseGraining QuantumDiamondMeasure QuantumTower
open scoped ComplexOrder

universe u

/-- Nonnegativity of the defect-functional term shape (the tower's
private workhorse, re-proved locally). -/
private theorem ite_norm_nonneg (P : Prop) [Decidable P] (x : ℂ) :
    0 ≤ if P then 0 else ‖x‖ := by
  split
  · exact le_rfl
  · exact norm_nonneg _

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ]

/-! ## The block ledger -/

/-- **The block ledger**: the fine off-diagonal ℓ¹ mass the `(c, c')`
fiber block contributes to `Q.offDiagMass`. The fiber-partition
regroup (`offDiagMass_eq_sum_blockMass`) says these contributions add
up to the whole fine mass; `blockContribution_le` bounds each coarse
block's contribution by its ledger. -/
noncomputable def blockMass (f : ι → κ) (Q : QuantumMeasure ι)
    (c c' : κ) : ℝ :=
  ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', if a = b then 0 else ‖Q.gram a b‖

omit [Fintype κ] in
theorem blockMass_nonneg (f : ι → κ) (Q : QuantumMeasure ι) (c c' : κ) :
    0 ≤ blockMass f Q c c' :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    ite_norm_nonneg _ _

omit [Fintype κ] in
/-- In a cross block the diagonal guard is vacuous: distinct coarse
atoms have disjoint fibers, so every entry is off-diagonal. -/
theorem blockMass_of_ne (f : ι → κ) (Q : QuantumMeasure ι) {c c' : κ}
    (hcc : c ≠ c') :
    blockMass f Q c c'
      = ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', ‖Q.gram a b‖ :=
  Finset.sum_congr rfl fun _ ha => Finset.sum_congr rfl fun _ hb =>
    if_neg fun hab => hcc
      (((mem_fiber f).mp ha).symm.trans
        ((congrArg f hab).trans ((mem_fiber f).mp hb)))

/-- **The non-cancellation predicate**: every coarse block's
contribution to the coarse off-diagonal mass attains its block's fine
ℓ¹ mass. (The coarse entry `(Q.pushforward f).gram c c'` is the fine
event form at the fibers, by `pushforward_gram`.) By
`nonCancelling_iff` this unpacks to: every merged block is
off-diagonally silent, and every cross block is norm-additive — no
entry is erased into a merged alternative, and no entries cancel. By
`offDiagMass_pushforward_eq_iff` it is EXACTLY the condition for the
coarse-graining to preserve the off-diagonal mass. -/
def NonCancelling (f : ι → κ) (Q : QuantumMeasure ι) : Prop :=
  ∀ c c' : κ,
    (if c = c' then 0 else ‖(Q.pushforward f).gram c c'‖)
      = blockMass f Q c c'

/-- **Per-block bound**: each coarse block's contribution to the
coarse off-diagonal mass is at most its block's fine ℓ¹ mass — the
landed inequality's per-block content, extracted. Diagonal coarse
blocks contribute nothing (their merged mass is erased); cross blocks
obey the triangle inequality. -/
theorem blockContribution_le (f : ι → κ) (Q : QuantumMeasure ι)
    (c c' : κ) :
    (if c = c' then 0 else ‖(Q.pushforward f).gram c c'‖)
      ≤ blockMass f Q c c' := by
  by_cases hcc : c = c'
  · rw [if_pos hcc]
    exact blockMass_nonneg f Q c c'
  · rw [if_neg hcc, blockMass_of_ne f Q hcc, pushforward_gram]
    calc ‖Q.eventForm (fiber f c) (fiber f c')‖
        ≤ ∑ a ∈ fiber f c, ‖∑ b ∈ fiber f c', Q.gram a b‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', ‖Q.gram a b‖ :=
          Finset.sum_le_sum fun a _ => norm_sum_le _ _

omit [DecidableEq ι] in
/-- The fiber-block regroup (generic in the codomain): double sums
over fiber blocks are double sums over the fine index. -/
private theorem sum_fiber_blocks {M : Type*} [AddCommMonoid M]
    (f : ι → κ) (g : ι → ι → M) :
    ∑ c, ∑ c', ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
      = ∑ a, ∑ b, g a b := by
  calc ∑ c, ∑ c', ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
      = ∑ c, ∑ a ∈ fiber f c, ∑ c', ∑ b ∈ fiber f c', g a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a ∈ fiber f c, ∑ b, g a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
          sum_fiber f fun b => g a b
    _ = ∑ a, ∑ b, g a b := sum_fiber f fun a => ∑ b, g a b

/-- **The fine mass is the sum of the block ledgers**: the
fiber-partition regroup of `offDiagMass`. -/
theorem offDiagMass_eq_sum_blockMass (f : ι → κ) (Q : QuantumMeasure ι) :
    Q.offDiagMass = ∑ c, ∑ c', blockMass f Q c c' := by
  simp only [blockMass]
  exact (sum_fiber_blocks f fun a b =>
    if a = b then 0 else ‖Q.gram a b‖).symm

/-! ## The characterization -/

/-- **The equality face of the strictness characterization**: a
coarse-graining preserves the off-diagonal mass iff it is
non-cancelling — every coarse block's contribution attains its
block's fine ℓ¹ mass. With `offDiagMass_pushforward_lt_iff`, the
tower's antitone functional is characterized rung by rung. -/
theorem offDiagMass_pushforward_eq_iff (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).offDiagMass = Q.offDiagMass
      ↔ NonCancelling f Q := by
  rw [offDiagMass_eq_sum_blockMass f Q]
  show (∑ c, ∑ c', if c = c' then 0 else ‖(Q.pushforward f).gram c c'‖)
      = (∑ c, ∑ c', blockMass f Q c c') ↔ NonCancelling f Q
  constructor
  · intro h c c'
    have houter : ∀ x ∈ (Finset.univ : Finset κ),
        (∑ c' : κ, if x = c' then 0 else ‖(Q.pushforward f).gram x c'‖)
          ≤ ∑ c' : κ, blockMass f Q x c' := fun x _ =>
      Finset.sum_le_sum fun y _ => blockContribution_le f Q x y
    have hrow := (Finset.sum_eq_sum_iff_of_le houter).mp h c
      (Finset.mem_univ c)
    exact (Finset.sum_eq_sum_iff_of_le fun y _ =>
      blockContribution_le f Q c y).mp hrow c' (Finset.mem_univ c')
  · intro h
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl
      fun c' _ => h c c'

/-- **The strict face**: the off-diagonal mass drops strictly iff the
merge cancels somewhere — some merged block carries a nonzero
off-diagonal entry, or some cross block's entries fail to align. -/
theorem offDiagMass_pushforward_lt_iff (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).offDiagMass < Q.offDiagMass
      ↔ ¬ NonCancelling f Q :=
  (offDiagMass_pushforward_le f Q).lt_iff_ne.trans
    (not_congr (offDiagMass_pushforward_eq_iff f Q))

/-- **The honest unpacking of non-cancellation**: merged blocks are
off-diagonally silent, and cross blocks are norm-additive. The first
conjunct is the erasure mechanism ruled out; the second is
cancellation ruled out. -/
theorem nonCancelling_iff (f : ι → κ) (Q : QuantumMeasure ι) :
    NonCancelling f Q ↔
      (∀ a b : ι, f a = f b → a ≠ b → Q.gram a b = 0) ∧
      (∀ c c' : κ, c ≠ c' →
        ‖(Q.pushforward f).gram c c'‖
          = ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', ‖Q.gram a b‖) := by
  constructor
  · intro h
    refine ⟨fun a b hf hab => ?_, fun c c' hcc => ?_⟩
    · have h0 := h (f a) (f a)
      rw [if_pos rfl] at h0
      simp only [blockMass] at h0
      have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun a' _ =>
        Finset.sum_nonneg fun b' _ => ite_norm_nonneg _ _).mp h0.symm a
        ((mem_fiber f).mpr rfl)
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun b' _ =>
        ite_norm_nonneg _ _).mp hrow b ((mem_fiber f).mpr hf.symm)
      rw [if_neg hab] at hterm
      exact norm_eq_zero.mp hterm
    · have h0 := h c c'
      rw [if_neg hcc, blockMass_of_ne f Q hcc] at h0
      exact h0
  · rintro ⟨h1, h2⟩ c c'
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl]
      simp only [blockMass]
      refine (Finset.sum_eq_zero fun a ha =>
        Finset.sum_eq_zero fun b hb => ?_).symm
      by_cases hab : a = b
      · rw [if_pos hab]
      · rw [if_neg hab,
          h1 a b (((mem_fiber f).mp ha).trans
            ((mem_fiber f).mp hb).symm) hab, norm_zero]
    · rw [if_neg hcc, blockMass_of_ne f Q hcc]
      exact h2 c c' hcc

/-! ## Sufficient conditions: the two strictness mechanisms -/

/-- A nonzero off-diagonal entry inside a merged block breaks
non-cancellation (the erasure mechanism). -/
theorem not_nonCancelling_of_merged_pair {f : ι → κ}
    {Q : QuantumMeasure ι} {a b : ι} (hf : f a = f b) (hab : a ≠ b)
    (hg : Q.gram a b ≠ 0) : ¬ NonCancelling f Q :=
  fun h => hg (((nonCancelling_iff f Q).mp h).1 a b hf hab)

/-- **Erasure forces strictness**: merging two alternatives that
genuinely interfere strictly drops the off-diagonal mass — their
overlap lands on the coarse diagonal and is lost. -/
theorem offDiagMass_pushforward_lt_of_merged_pair (f : ι → κ)
    (Q : QuantumMeasure ι) {a b : ι} (hf : f a = f b) (hab : a ≠ b)
    (hg : Q.gram a b ≠ 0) :
    (Q.pushforward f).offDiagMass < Q.offDiagMass :=
  (offDiagMass_pushforward_lt_iff f Q).mpr
    (not_nonCancelling_of_merged_pair hf hab hg)

/-- **Exact cancellation forces strictness — equality by cancellation
is impossible**: if a cross block carries a nonzero entry while its
coarse entry vanishes (the entries cancel exactly, as in the landed
decoherence-by-coarse-graining witness), the off-diagonal mass drops
strictly. Equality never hides cancellation: by
`offDiagMass_pushforward_eq_iff`, equality forces every cross block
to be norm-additive. -/
theorem offDiagMass_pushforward_lt_of_cancellation (f : ι → κ)
    (Q : QuantumMeasure ι) {c c' : κ} (hcc : c ≠ c') {a b : ι}
    (ha : f a = c) (hb : f b = c') (hg : Q.gram a b ≠ 0)
    (h0 : (Q.pushforward f).gram c c' = 0) :
    (Q.pushforward f).offDiagMass < Q.offDiagMass := by
  refine (offDiagMass_pushforward_lt_iff f Q).mpr fun hnc => ?_
  have h2 := ((nonCancelling_iff f Q).mp hnc).2 c c' hcc
  rw [h0, norm_zero] at h2
  have hle : ‖Q.gram a b‖
      ≤ ∑ a' ∈ fiber f c, ∑ b' ∈ fiber f c', ‖Q.gram a' b'‖ :=
    calc ‖Q.gram a b‖
        ≤ ∑ b' ∈ fiber f c', ‖Q.gram a b'‖ :=
          Finset.single_le_sum (fun _ _ => norm_nonneg _)
            ((mem_fiber f).mpr hb)
      _ ≤ ∑ a' ∈ fiber f c, ∑ b' ∈ fiber f c', ‖Q.gram a' b'‖ :=
          Finset.single_le_sum
            (fun a' _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            ((mem_fiber f).mpr ha)
  rw [← h2] at hle
  exact hg (norm_le_zero_iff.mp hle)

/-! ## Lazy rungs never drop, in both senses -/

/-- **Padding merges are non-cancelling**: an injective merge has
subsingleton fibers — nothing merges, nothing cancels. -/
theorem nonCancelling_of_injective (f : ι → κ) (Q : QuantumMeasure ι)
    (hf : Function.Injective f) : NonCancelling f Q := by
  intro c c'
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl]
    simp only [blockMass]
    refine (Finset.sum_eq_zero fun a ha =>
      Finset.sum_eq_zero fun b hb => ?_).symm
    have hab : a = b := hf
      (((mem_fiber f).mp ha).trans ((mem_fiber f).mp hb).symm)
    rw [if_pos hab]
  · rw [if_neg hcc, blockMass_of_ne f Q hcc, pushforward_gram]
    rcases Finset.eq_empty_or_nonempty (fiber f c) with he | ⟨a, ha⟩
    · rw [he]
      simp [QuantumMeasure.eventForm]
    · have hsa : fiber f c = {a} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun x hx =>
          hf (((mem_fiber f).mp hx).trans ((mem_fiber f).mp ha).symm)⟩
      rcases Finset.eq_empty_or_nonempty (fiber f c') with he' | ⟨b, hb⟩
      · rw [he']
        simp [QuantumMeasure.eventForm]
      · have hsb : fiber f c' = {b} :=
          Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, fun x hx =>
            hf (((mem_fiber f).mp hx).trans
              ((mem_fiber f).mp hb).symm)⟩
        rw [hsa, hsb]
        simp [QuantumMeasure.eventForm]

/-- **Padding merges preserve the off-diagonal mass on the nose** —
identity-grade rungs of a tower are exactly lossless. -/
theorem offDiagMass_pushforward_of_injective (f : ι → κ)
    (Q : QuantumMeasure ι) (hf : Function.Injective f) :
    (Q.pushforward f).offDiagMass = Q.offDiagMass :=
  (offDiagMass_pushforward_eq_iff f Q).mpr
    (nonCancelling_of_injective f Q hf)

/-- **Post-decoherence merges are non-cancelling**: a diagonal
measure has nothing off-diagonal to erase or cancel. -/
theorem nonCancelling_of_isDiagonal (f : ι → κ) (Q : QuantumMeasure ι)
    (hd : Q.IsDiagonal) : NonCancelling f Q := by
  intro c c'
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl]
    simp only [blockMass]
    refine (Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => ?_).symm
    by_cases hab : a = b
    · rw [if_pos hab]
    · rw [if_neg hab, hd hab, norm_zero]
  · rw [if_neg hcc, blockMass_of_ne f Q hcc,
      pushforward_isDiagonal f Q hd hcc, norm_zero]
    refine (Finset.sum_eq_zero fun a ha =>
      Finset.sum_eq_zero fun b hb => ?_).symm
    have hab : a ≠ b := fun h => hcc
      (((mem_fiber f).mp ha).symm.trans (h ▸ (mem_fiber f).mp hb))
    rw [hd hab, norm_zero]

/-- Past a diagonal stage every merge is an equality (trivially, at
mass zero — but stated through the characterization: the rung is
lazy, not merely small). -/
theorem offDiagMass_pushforward_of_isDiagonal (f : ι → κ)
    (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) :
    (Q.pushforward f).offDiagMass = Q.offDiagMass :=
  (offDiagMass_pushforward_eq_iff f Q).mpr
    (nonCancelling_of_isDiagonal f Q hd)

/-- **The tower-facing face**: rung `n` of a refinement tower drops
the off-diagonal mass strictly iff its step merge cancels on the
`n`-th stage measure. -/
theorem offDiagMass_stageMeasure_succ_lt_iff {X : ℕ → Type u}
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    (Q : QuantumMeasure (X 0)) (step : ∀ n, X n → X (n + 1)) (n : ℕ) :
    (stageMeasure Q step (n + 1)).offDiagMass
        < (stageMeasure Q step n).offDiagMass
      ↔ ¬ NonCancelling (step n) (stageMeasure Q step n) :=
  offDiagMass_pushforward_lt_iff (step n) (stageMeasure Q step n)

/-! ## The diamond tower's decohering rung, characterized

The landed strict drop convicts the degeneracy merge of
cancellation-or-erasure through the characterization — and both
mechanisms are then exhibited concretely, independently forcing the
same strict drop. -/

/-- The decohering rung is NOT non-cancelling — the characterization
consumed backward from the landed strict drop, no new arithmetic. -/
theorem diamondMeasure_not_nonCancelling :
    ¬ NonCancelling degeneracy diamondMeasure :=
  (offDiagMass_pushforward_lt_iff degeneracy diamondMeasure).mp
    towerMeasure_offDiagMass_lt

/-- The coarse cross entry vanishes: the `(true, false)` block of the
degeneracy merge sums to zero (from the landed diagonality). -/
theorem diamondMeasure_pushforward_gram_true_false :
    (diamondMeasure.pushforward degeneracy).gram true false = 0 :=
  diamondMeasure_pushforward_isDiagonal (by decide)

/-- **The cancellation mechanism, concrete on the site**: the pair
`(pointLo, span)` contributes `3/5` to a cross block whose coarse
entry is `0` — exact cancellation in the wild
(`gram pointHi span = −3/5` is the cancelling partner), and
strictness is forced by `offDiagMass_pushforward_lt_of_cancellation`
alone. -/
theorem diamondMeasure_cancellation_strict :
    (diamondMeasure.pushforward degeneracy).offDiagMass
      < diamondMeasure.offDiagMass :=
  offDiagMass_pushforward_lt_of_cancellation degeneracy diamondMeasure
    (show (true : Bool) ≠ false by decide)
    (show degeneracy pointLo = true by decide)
    (show degeneracy span = false by decide)
    (by rw [diamondMeasure_gram_pointLo_span]; norm_num)
    diamondMeasure_pushforward_gram_true_false

/-- The two instantaneous events overlap with Gram entry `−1`: the
one new value-level item (`⟨(1,0), (−1,4/5)⟩ = −1`), consumed from
the landed presentation with no matrix arithmetic beyond the landed
cocktail. -/
theorem diamondMeasure_gram_pointLo_pointHi :
    diamondMeasure.gram pointLo pointHi = -1 := by
  rw [diamondMeasure, map_gram, diamondEquiv_symm_pointLo,
    diamondEquiv_symm_pointHi]
  show decoherenceFunctional mergeFamily mergeState 0 1 = -1
  norm_num [decoherenceFunctional, mergeFamily, mergeState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_neg, map_one,
    map_ofNat, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- **The erasure mechanism, concrete on the site**: the degeneracy
merge fuses the two instantaneous events, whose mutual overlap `−1`
is erased onto the coarse diagonal — strictness forced by
`offDiagMass_pushforward_lt_of_merged_pair` alone. The decohering
rung is strict via BOTH mechanisms, independently. -/
theorem diamondMeasure_merged_pair_strict :
    (diamondMeasure.pushforward degeneracy).offDiagMass
      < diamondMeasure.offDiagMass :=
  offDiagMass_pushforward_lt_of_merged_pair degeneracy diamondMeasure
    (show degeneracy pointLo = degeneracy pointHi by decide)
    (fun h => absurd (congrArg Diamond.hi h) (by decide))
    (by rw [diamondMeasure_gram_pointLo_pointHi]; norm_num)

/-- Every rung past the decohering one is non-cancelling: the tower
is lazy from stage 1 on. -/
theorem towerMeasure_nonCancelling_of_pos {n : ℕ} (h : 1 ≤ n) :
    NonCancelling (towerStep n) (towerMeasure n) :=
  nonCancelling_of_isDiagonal _ _ (towerMeasure_isDiagonal_of_pos h)

/-- **The lazy rungs are non-strict**: past the decohering rung the
mass profile is constant — on the 3-stage toy the drop is strict
exactly once. -/
theorem towerMeasure_offDiagMass_succ_eq_of_pos {n : ℕ} (h : 1 ≤ n) :
    (towerMeasure (n + 1)).offDiagMass = (towerMeasure n).offDiagMass :=
  (offDiagMass_pushforward_eq_iff (towerStep n) (towerMeasure n)).mpr
    (towerMeasure_nonCancelling_of_pos h)

/-! ## The align witness: equality without diagonality

The same site, the same merge, the same 3-4-5 total state as the
landed cancellation specimen `mergeMeasure` — but the branch
decomposition is ALIGNED: the merged pair orthogonal, the cross
blocks positively aligned. The genuine non-injective merge preserves
the off-diagonal mass `1/2` exactly, and both fine and coarse
measures remain genuinely quantum: coarse-graining is not
automatically decoherence, and the tower's antitone functional is not
secretly strict away from diagonality. -/

/-- The aligned class operators (first columns are the branch vectors
`(3/10, 0)`, `(0, 2/5)`, `(3/10, 2/5)`). -/
noncomputable def alignFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![3/10, 0; 0, 0], !![0, 0; 2/5, 0], !![3/10, 0; 2/5, 0]]

/-- The aligned state. -/
noncomputable def alignState : Fin 2 → ℂ := ![1, 0]

/-- Unit total weight (the branch vectors sum to the 3-4-5 state). -/
private theorem alignNorm :
    ∑ α, ∑ β, decoherenceFunctional alignFamily alignState α β = 1 := by
  simp only [Fin.sum_univ_three, decoherenceFunctional, alignFamily,
    alignState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_ofNat, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- The aligned quantum measure on `Fin 3`. -/
noncomputable def alignMeasure : QuantumMeasure (Fin 3) :=
  QuantumMeasure.ofPresentation alignFamily alignState alignNorm

private theorem alignMeasure_gram_01 : alignMeasure.gram 0 1 = 0 := by
  show decoherenceFunctional alignFamily alignState 0 1 = 0
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

private theorem alignMeasure_gram_10 : alignMeasure.gram 1 0 = 0 := by
  show decoherenceFunctional alignFamily alignState 1 0 = 0
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

private theorem alignMeasure_gram_02 :
    alignMeasure.gram 0 2 = 9 / 100 := by
  show decoherenceFunctional alignFamily alignState 0 2 = 9 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_20 :
    alignMeasure.gram 2 0 = 9 / 100 := by
  show decoherenceFunctional alignFamily alignState 2 0 = 9 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_12 :
    alignMeasure.gram 1 2 = 16 / 100 := by
  show decoherenceFunctional alignFamily alignState 1 2 = 16 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_21 :
    alignMeasure.gram 2 1 = 16 / 100 := by
  show decoherenceFunctional alignFamily alignState 2 1 = 16 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

/-- The aligned measure genuinely interferes: the `(0, 2)` overlap is
`9/100 ≠ 0`. -/
theorem alignMeasure_not_isDiagonal : ¬ alignMeasure.IsDiagonal :=
  fun h => by
    have hc := h (show (0 : Fin 3) ≠ 2 by decide)
    rw [alignMeasure_gram_02] at hc
    norm_num at hc

/-- The preserved mass is genuinely nonzero: equality below is not
the trivial `0 = 0`. -/
theorem alignMeasure_offDiagMass_pos : 0 < alignMeasure.offDiagMass :=
  (offDiagMass_nonneg _).lt_of_ne fun h =>
    alignMeasure_not_isDiagonal
      ((offDiagMass_eq_zero_iff _).mp h.symm)

/-- **The align witness is non-cancelling under the landed merge**:
the merged block is silent (`gram 0 1 = 0`) and the cross blocks are
norm-additive (`‖9/100 + 16/100‖ = 9/100 + 16/100` — positively
aligned entries). -/
theorem alignMeasure_nonCancelling :
    NonCancelling mergeCoarse alignMeasure := by
  intro c c'
  fin_cases c <;> fin_cases c'
  · -- (0, 0): the merged block is silent
    rw [if_pos rfl]
    simp only [blockMass, fiber, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_01,
      alignMeasure_gram_10]
  · -- (0, 1): the aligned cross block
    rw [if_neg (by decide),
      blockMass_of_ne mergeCoarse alignMeasure (by decide)]
    simp only [pushforward_gram, QuantumMeasure.eventForm,
      fiber, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_02,
      alignMeasure_gram_12, norm_div, Complex.norm_ofNat]
  · -- (1, 0): the conjugate cross block
    rw [if_neg (by decide),
      blockMass_of_ne mergeCoarse alignMeasure (by decide)]
    simp only [pushforward_gram, QuantumMeasure.eventForm,
      fiber, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_20,
      alignMeasure_gram_21, norm_div, Complex.norm_ofNat]
  · -- (1, 1): a singleton fiber has no off-diagonal entries
    rw [if_pos rfl]
    simp only [blockMass, fiber, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]

/-- **Equality without diagonality**: a genuine (non-injective) merge
of a genuinely quantum measure that preserves the off-diagonal mass
on the nose — the antitone inequality admits equality away from
diagonality, exactly when nothing cancels. -/
theorem alignMeasure_offDiagMass_pushforward_eq :
    (alignMeasure.pushforward mergeCoarse).offDiagMass
      = alignMeasure.offDiagMass :=
  (offDiagMass_pushforward_eq_iff mergeCoarse alignMeasure).mpr
    alignMeasure_nonCancelling

/-- Equality without diagonality on BOTH ends: the coarse measure is
still genuinely quantum (`coarse gram (0,1) = 1/4 ≠ 0`). -/
theorem alignMeasure_pushforward_not_isDiagonal :
    ¬ (alignMeasure.pushforward mergeCoarse).IsDiagonal := by
  intro h
  have hc := h (show (0 : Fin 2) ≠ 1 by decide)
  rw [pushforward_gram] at hc
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three] at hc
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_02,
    alignMeasure_gram_12] at hc

end QuantumStrictness

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStrictness.blockMass_nonneg
#print axioms Qtsl.QuantumStrictness.blockMass_of_ne
#print axioms Qtsl.QuantumStrictness.blockContribution_le
#print axioms Qtsl.QuantumStrictness.offDiagMass_eq_sum_blockMass
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_eq_iff
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_iff
#print axioms Qtsl.QuantumStrictness.nonCancelling_iff
#print axioms Qtsl.QuantumStrictness.not_nonCancelling_of_merged_pair
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_of_merged_pair
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_of_cancellation
#print axioms Qtsl.QuantumStrictness.nonCancelling_of_injective
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_of_injective
#print axioms Qtsl.QuantumStrictness.nonCancelling_of_isDiagonal
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_of_isDiagonal
#print axioms Qtsl.QuantumStrictness.offDiagMass_stageMeasure_succ_lt_iff
#print axioms Qtsl.QuantumStrictness.diamondMeasure_not_nonCancelling
#print axioms Qtsl.QuantumStrictness.diamondMeasure_pushforward_gram_true_false
#print axioms Qtsl.QuantumStrictness.diamondMeasure_cancellation_strict
#print axioms Qtsl.QuantumStrictness.diamondMeasure_gram_pointLo_pointHi
#print axioms Qtsl.QuantumStrictness.diamondMeasure_merged_pair_strict
#print axioms Qtsl.QuantumStrictness.towerMeasure_nonCancelling_of_pos
#print axioms Qtsl.QuantumStrictness.towerMeasure_offDiagMass_succ_eq_of_pos
#print axioms Qtsl.QuantumStrictness.alignMeasure_not_isDiagonal
#print axioms Qtsl.QuantumStrictness.alignMeasure_offDiagMass_pos
#print axioms Qtsl.QuantumStrictness.alignMeasure_nonCancelling
#print axioms Qtsl.QuantumStrictness.alignMeasure_offDiagMass_pushforward_eq
#print axioms Qtsl.QuantumStrictness.alignMeasure_pushforward_not_isDiagonal
