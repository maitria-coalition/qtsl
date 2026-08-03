import Qtsl.LatticeInv

/-!
# Class-stratum alias fixture: `QLatticeInv`

`QLatticeInv` in the alias-derivation fixture pattern (`AliasSmallGain`
is the exemplar; `AliasStructural` / `AliasPathSugar` /
`AliasStreettDegenerate` are the class-stratum siblings), at the same
lemma-level transposition: the elaboration lands on the base rule's
**in-repo soundness lemma**
(`PPLC.Qtsl.Semiflow.qLatticeInv_sound_of_blockInv` — the Behavior form
is hypothesis-identical modulo the dynamics carrier and is not
separately fixtured) with computed arguments; the derivation-calculus
cell plumbing arrives with the class-stratum presentation.

Catalogue: tier **alias** → `QBlockInv` — "the unpacking is a single
`QBlockInv` whose facet rows are the lattice member's, cited not
re-proven".  The base lemma takes **8 explicit hypotheses** — the
down-closedness of the cell set `C`, the four lattice-consistency
conditions of the join-irreducible chart (`joinCover`, `strictCover`,
`cellsSup`, `embOrder`), the cell containment, and the cited member's
two components (invariance of the block union + initial containment in
the cell union) — and the generic gate discharges **all 8 from the
structure's fields** (8 → 0), concluding `InvScopeSat` on the
down-closed cell union `⋃↓C`.

What the concrete instance shows (the fixture's point): the concluded
region is a union of cells of which the top one is **not itself
invariant** (`topCell_not_invariant` below) — cellwise invariance
fails, and the conclusion genuinely rides the exactness identity
`region = blockRegion` (`qLatticeInv_exact`, exposed here as the
`region_eq_blockRegion` face) together with the block union's
invariance.  Zero facet-row machinery appears at the demo site: the
`_of_blockInv` interface consumes bare invariance + initialization (the
cited `QBlockInv` member's own assembly components); the
BernCone-sign-row discharge routes (`HasFacetRows`, boundary dwell) are
the base rule's other business, not the alias's.

Decode note: at the S1 fragment depth a `decodeQtslPresentationOps`
hypothesis would be decorative rather than load-bearing (the wave-1
adjudication); the decode marriage rides the campaign's per-row
fragment widening.  The catalogue's D1 flag (registry-backed citation
vs the alias criterion) is the wiring leg's design note, not this
fixture's.
-/

namespace SuFunctor

namespace QtslSem

open Set
open PPLC PPLC.Qtsl

/-!
## QLatticeInv — invariance scope on a down-closed cell union
-/

/-- A lattice-invariance step: the join-irreducible chart of a block
lattice (`blocks` over the index `β`, join-irreducibles selected by
`emb`, lower covers by `cover`, the per-irreducible cells), the
down-closed cell set `C`, and the initial set `X0`.  The 8 proof
fields mirror the base lemma's explicit hypothesis list verbatim — the
whole content of the alias rides here, so the gate below takes no
hypotheses at all.

The structure deliberately carries no instance assumptions beyond
`[PartialOrder ι]` (the field types need only the order): `[Finite ι]`
is consumed by the gate and the exactness face only. -/
structure LatticeInvStep (X ι β : Type*) [PartialOrder ι]
    (φ : Semiflow X) where
  blocks : β → Set X
  emb : ι → β
  cover : ι → β
  cells : ι → Set X
  C : Set ι
  X0 : Set X
  -- the down-closed cell set (the rule's R1-recomputed side condition)
  downClosed : IsLowerSet C
  -- the join-irreducible chart (4)
  joinCover : ∀ b : β, ∀ x ∈ blocks b,
    ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b
  strictCover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i)
  cellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i
  embOrder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j
  -- cell containment
  cellSub : ∀ i : ι, cells i ⊆ blocks (emb i)
  -- the cited QBlockInv member (2)
  blockInv : φ.Invariant (⋃ i ∈ C, blocks (emb i))
  init : X0 ⊆ ⋃ i ∈ C, cells i

namespace LatticeInvStep

variable {X ι β : Type*} [PartialOrder ι] {φ : Semiflow X}

/-- The elaboration: the alias's concluded region — the down-closed
cell union `⋃↓C` (the catalogue's computed argument). -/
def region (st : LatticeInvStep X ι β φ) : Set X :=
  ⋃ i ∈ st.C, st.cells i

/-- The cited member's region: the block union over the same cell
set. -/
def blockRegion (st : LatticeInvStep X ι β φ) : Set X :=
  ⋃ i ∈ st.C, st.blocks (st.emb i)

/-- **The exactness face**: the tiling identity the alias's unpacking
rides — the down-closed cell union *is* the block union — a single
application of `qLatticeInv_exact` to the six lattice fields. -/
theorem region_eq_blockRegion [Finite ι] (st : LatticeInvStep X ι β φ) :
    st.region = st.blockRegion :=
  qLatticeInv_exact st.downClosed st.joinCover st.strictCover
    st.cellsSup st.embOrder st.cellSub

end LatticeInvStep

/-- **The generic gate**: `InvScopeSat` on the down-closed cell union,
discharged entirely from the structure's fields — a single application
of `Semiflow.qLatticeInv_sound_of_blockInv` to the 8 proof fields (the
base lemma takes 8 explicit hypotheses; the step form takes none:
8 → 0). -/
theorem latticeInv_gate {X ι β : Type*} [PartialOrder ι] [Finite ι]
    {φ : Semiflow X} (st : LatticeInvStep X ι β φ) :
    φ.InvScopeSat st.region st.X0 :=
  Semiflow.qLatticeInv_sound_of_blockInv st.downClosed st.joinCover
    st.strictCover st.cellsSup st.embOrder st.cellSub st.blockInv st.init

namespace LatticeDemo

/-- The decay semiflow on `ℝ`: everything slides down at unit rate.
Real dynamics — `Iic` blocks absorb it, but the demo's top cell does
not (`topCell_not_invariant`). -/
noncomputable def decayFlow : Semiflow ℝ where
  flow t x := x - t
  flow_zero x := by simp
  flow_add s t x := by push_cast; ring

/-- The block lattice: a three-step chain with bottom —
`∅ ⊂ Iic 0 ⊂ Iic 1 ⊂ Iic 2`. -/
def blocksDemo : Fin 4 → Set ℝ
  | 0 => ∅
  | 1 => Iic 0
  | 2 => Iic 1
  | 3 => Iic 2

/-- Join-irreducibles: the three nonempty blocks. -/
def embDemo : Fin 3 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3

/-- Lower covers: each irreducible covers its predecessor. -/
def coverDemo : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The cells: the tiling `Iic 0, Ioc 0 1, Ioc 1 2` — each block minus
its lower cover. -/
def cellsDemo : Fin 3 → Set ℝ
  | 0 => Iic 0
  | 1 => Ioc 0 1
  | 2 => Ioc 1 2

/-- The concrete step — the 8 hypotheses of the base lemma, each
discharged on the three-step chain under decay: `C = Iic 1` is a
*proper* lower set (the top cell is cropped), and `X0 = Icc 0 1`
touches both retained cells (the `init` discharge walks the tiling
through a case split at `0`).  The block-union invariance is real
dynamics: decay moves down and `Iic` blocks absorb it. -/
noncomputable def step : LatticeInvStep ℝ (Fin 3) (Fin 4) decayFlow where
  blocks := blocksDemo
  emb := embDemo
  cover := coverDemo
  cells := cellsDemo
  C := Set.Iic 1
  X0 := Icc 0 1
  downClosed := isLowerSet_Iic 1
  joinCover := by
    intro b x hx
    fin_cases b
    · exact absurd hx (Set.notMem_empty x)
    · exact ⟨0, hx, subset_rfl⟩
    · exact ⟨1, hx, subset_rfl⟩
    · exact ⟨2, hx, subset_rfl⟩
  strictCover := by
    intro i
    fin_cases i
    · exact Set.empty_ssubset.mpr Set.nonempty_Iic
    · exact Set.Iic_ssubset_Iic.mpr (by norm_num)
    · exact Set.Iic_ssubset_Iic.mpr (by norm_num)
  cellsSup := by
    intro i
    fin_cases i
    · exact fun x hx => hx.1
    · exact fun x hx => ⟨not_le.mp hx.2, hx.1⟩
    · exact fun x hx => ⟨not_le.mp hx.2, hx.1⟩
  embOrder := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | decide
      | exact absurd (Set.mem_Iic.mp (h Set.self_mem_Iic)) (by norm_num)
  cellSub := by
    intro i
    fin_cases i
    · exact subset_rfl
    · exact Ioc_subset_Iic_self
    · exact Ioc_subset_Iic_self
  blockInv := by
    rintro x hx t
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨i, hiC, hxi⟩ := hx
    refine ⟨i, hiC, ?_⟩
    have hdrop : x - (t : ℝ) ≤ x := sub_le_self x t.coe_nonneg
    fin_cases i <;>
      exact Set.mem_Iic.mpr (le_trans hdrop (Set.mem_Iic.mp hxi))
  init := by
    rintro x ⟨h0, h1⟩
    rw [Set.mem_iUnion₂]
    by_cases hx : x ≤ 0
    · exact ⟨0, Set.mem_Iic.mpr (by decide), hx⟩
    · exact ⟨1, Set.mem_Iic.mpr (by decide), not_le.mp hx, h1⟩

/-- The concluded region, displayed: the retained cells tile
`Iic 0 ∪ Ioc 0 1` (the top cell `Ioc 1 2` is cropped by `C`). -/
theorem step_region_eq : step.region = Iic 0 ∪ Ioc 0 1 := by
  ext x
  simp only [LatticeInvStep.region, Set.mem_iUnion₂]
  constructor
  · rintro ⟨i, hiC, hx⟩
    fin_cases i
    · exact Or.inl hx
    · exact Or.inr hx
    · exact absurd (Set.mem_Iic.mp hiC) (by decide)
  · rintro (hx | hx)
    · exact ⟨0, Set.mem_Iic.mpr (by decide), hx⟩
    · exact ⟨1, Set.mem_Iic.mpr (by decide), hx⟩

/-- The concrete face, from the bare gate: invariance scope on the
two-cell tiling from initial mass touching both cells — 8 term-level
certificate checks, zero facet-row machinery at this site. -/
theorem face : decayFlow.InvScopeSat (Iic 0 ∪ Ioc 0 1) (Icc 0 1) :=
  step_region_eq ▸ latticeInv_gate step

/-- The face with the tiling melted (the display form): the cell union
*is* the block union `Iic 1` — the exactness identity, concretely. -/
theorem face_melted : decayFlow.InvScopeSat (Iic 1) (Icc 0 1) := by
  have h := face
  rwa [Set.Iic_union_Ioc_eq_Iic (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- **The honesty face**: the top retained cell is *not* itself
invariant — decay exits `Ioc 0 1` through `0`.  Cellwise invariance
fails; the gate's conclusion rides the exactness identity and the
block union's invariance, exactly as the alias's unpacking says. -/
theorem topCell_not_invariant : ¬ decayFlow.Invariant (Ioc 0 1) := by
  intro h
  have h0 := h 1 ⟨one_pos, le_refl 1⟩ 1
  have hval : decayFlow.flow 1 1 = (0 : ℝ) := by
    simp [decayFlow]
  rw [hval] at h0
  exact absurd h0.1 (lt_irrefl 0)

end LatticeDemo

end QtslSem

end SuFunctor
