import SuFunctor.Universe.FellTopology
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! # The one-point collapse: `CL(Y) ≅ {B ∈ 𝒦(Y⁺) : ∞ ∈ B}`

The collapse dictionary's embedding form (temporal-sheaf memo
§9.1(a)), promoted from prose: adjoining the point at infinity is a
homeomorphism from the Fell hyperspace of closed subsets of an ambient
onto the `∞`-containing slice of the hyperspace of its one-point
compactification (`fellCloseds_homeoOnePoint`), and the slice is
closed in that hyperspace (`FellCloseds.isClosed_setOf_infty_mem`).

The headline is **stratum-general**: with the Fell topology on both
hyperspaces the homeomorphism needs no hypotheses on the ambient at
all — the memo's locally-compact-Hausdorff reading is recovered as a
corollary, because on that stratum the compactification is compact
Hausdorff, where the landed collapse `fell_eq_vietoris` renames the
upstairs topology to Vietoris
(`FellCloseds.topology_eq_vietoris`, instantiated at the one-point
stratum by `FellCloseds.topology_onePoint_eq_vietoris`) and closed
sets are exactly the compact ones (`FellCloseds.isCompact_coe`) — so
the slice is literally `{B ∈ 𝒦(Y⁺) : ∞ ∈ B}` with Vietoris, and every
compact-stratum theorem about the Vietoris hyperspace becomes
objectwise-citable over the site through this homeomorphism.

The subbasis bookkeeping is the memo's, one face at a time:

* Fell miss classes of compacts pull back and forth through the
  `∞`-demands — a compact upstairs containing `∞` can never be missed
  on the slice (`preimage_onePointExtend_miss_of_infty_mem`), one
  avoiding `∞` restricts to a compact downstairs
  (`preimage_onePointExtend_miss_of_infty_notMem`);
* hit classes of opens containing `∞` are vacuous on the slice
  (`preimage_onePointExtend_hit_of_infty_mem`), and the rest restrict
  to hit classes downstairs
  (`preimage_onePointExtend_hit_of_infty_notMem`);
* in the return direction both faces transport unconditionally along
  the open embedding (`preimage_onePointRestrict_hit`,
  `preimage_onePointRestrict_miss`).

The `∞`-membership condition on the slice is load-bearing: dropping it
breaks the correspondence (restriction forgets which closed sets
upstairs contained `∞`, so extension-after-restriction would silently
adjoin `∞` to slice-external citizens — the preregistered mutant
locus).
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace
open scoped OnePoint

variable {α : Type*} [TopologicalSpace α]

attribute [local instance] SuFunctor.Universe.fell

namespace fell

/-- Adjoin the point at infinity: the set-level extension
`s ↦ {∞} ∪ s` along the coercion into the one-point
compactification. -/
def onePointExtend (s : Set α) : Set (OnePoint α) :=
  insert ∞ ((↑) '' s)

omit [TopologicalSpace α] in
@[simp]
theorem infty_mem_onePointExtend (s : Set α) : ∞ ∈ onePointExtend s :=
  mem_insert _ _

omit [TopologicalSpace α] in
/-- Pulling the extension back along the coercion recovers the set:
the first inverse law, valid everywhere. -/
@[simp]
theorem preimage_coe_onePointExtend (s : Set α) :
    ((↑) : α → OnePoint α) ⁻¹' onePointExtend s = s := by
  simp only [onePointExtend, insert_eq, preimage_union, OnePoint.coe_preimage_infty,
    preimage_image_eq _ OnePoint.coe_injective, empty_union]

omit [TopologicalSpace α] in
/-- Extending the coercion-preimage of an `∞`-containing set recovers
the set: the second inverse law, exactly on the `∞`-slice. -/
theorem onePointExtend_preimage_coe {s : Set (OnePoint α)} (h : ∞ ∈ s) :
    onePointExtend (((↑) : α → OnePoint α) ⁻¹' s) = s := by
  rw [onePointExtend, image_preimage_eq_inter_range, ← OnePoint.compl_infty, ← sdiff_eq,
    insert_sdiff_singleton, insert_eq_self.mpr h]

omit [TopologicalSpace α] in
/-- A miss class over a compact containing `∞` pulls back to nothing:
every extension contains `∞`. -/
theorem preimage_onePointExtend_miss_of_infty_mem {K : Set (OnePoint α)} (h : ∞ ∈ K) :
    onePointExtend ⁻¹' {t : Set (OnePoint α) | Disjoint t K} = (∅ : Set (Set α)) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  exact Set.disjoint_left.mp hs (infty_mem_onePointExtend s) h

omit [TopologicalSpace α] in
/-- A miss class over a compact avoiding `∞` pulls back to the miss
class over its trace downstairs. -/
theorem preimage_onePointExtend_miss_of_infty_notMem {K : Set (OnePoint α)} (h : ∞ ∉ K) :
    onePointExtend ⁻¹' {t : Set (OnePoint α) | Disjoint t K}
      = {s : Set α | Disjoint s (((↑) : α → OnePoint α) ⁻¹' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, onePointExtend, Set.disjoint_left]
  constructor
  · intro hd a has haK
    exact hd (mem_insert_of_mem _ (mem_image_of_mem _ has)) haK
  · intro hd x hx hxK
    rcases mem_insert_iff.mp hx with rfl | ⟨a, ha, rfl⟩
    · exact h hxK
    · exact hd ha hxK

omit [TopologicalSpace α] in
/-- A hit class over an open containing `∞` pulls back to everything:
every extension hits it at `∞`. -/
theorem preimage_onePointExtend_hit_of_infty_mem {V : Set (OnePoint α)} (h : ∞ ∈ V) :
    onePointExtend ⁻¹' {t : Set (OnePoint α) | (t ∩ V).Nonempty} = (univ : Set (Set α)) :=
  eq_univ_of_forall fun s => ⟨∞, infty_mem_onePointExtend s, h⟩

omit [TopologicalSpace α] in
/-- A hit class over an open avoiding `∞` pulls back to the hit class
over its trace downstairs. -/
theorem preimage_onePointExtend_hit_of_infty_notMem {V : Set (OnePoint α)} (h : ∞ ∉ V) :
    onePointExtend ⁻¹' {t : Set (OnePoint α) | (t ∩ V).Nonempty}
      = {s : Set α | (s ∩ ((↑) : α → OnePoint α) ⁻¹' V).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, onePointExtend]
  constructor
  · rintro ⟨x, hx, hxV⟩
    rcases mem_insert_iff.mp hx with rfl | ⟨a, ha, rfl⟩
    · exact absurd hxV h
    · exact ⟨a, ha, hxV⟩
  · rintro ⟨a, has, haV⟩
    exact ⟨↑a, mem_insert_of_mem _ (mem_image_of_mem _ has), haV⟩

/-- **Adjoining `∞` is Fell-continuous** at the powerset level, over
an arbitrary ambient.  The four subbasic preimages are the four
lemmas above; the only nontrivial transport is compactness of an
`∞`-avoiding compact's trace, which rides the open embedding. -/
theorem continuous_onePointExtend :
    Continuous (onePointExtend : Set α → Set (OnePoint α)) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · by_cases h : ∞ ∈ K
    · rw [preimage_onePointExtend_miss_of_infty_mem h]
      exact isOpen_empty
    · rw [preimage_onePointExtend_miss_of_infty_notMem h]
      refine isOpen_disjoint_of_isCompact ?_
      refine OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage' hK ?_
      intro x hxK
      exact OnePoint.ne_infty_iff_exists.mp (fun hx => h (hx ▸ hxK))
  · by_cases h : ∞ ∈ V
    · rw [preimage_onePointExtend_hit_of_infty_mem h]
      exact isOpen_univ
    · rw [preimage_onePointExtend_hit_of_infty_notMem h]
      exact isOpen_inter_nonempty_of_isOpen (hV.preimage OnePoint.continuous_coe)

/-- Restrict along the coercion: the set-level return map
`s ↦ s ∩ Y`, viewed downstairs. -/
def onePointRestrict (s : Set (OnePoint α)) : Set α :=
  ((↑) : α → OnePoint α) ⁻¹' s

omit [TopologicalSpace α] in
/-- Hit classes pull back to hit classes along restriction: hitting
`U` downstairs is hitting its image upstairs. -/
theorem preimage_onePointRestrict_hit (U : Set α) :
    onePointRestrict ⁻¹' {t : Set α | (t ∩ U).Nonempty}
      = {s : Set (OnePoint α) | (s ∩ (↑) '' U).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, onePointRestrict]
  constructor
  · rintro ⟨a, has, haU⟩
    exact ⟨↑a, has, mem_image_of_mem _ haU⟩
  · rintro ⟨x, hxs, a, haU, rfl⟩
    exact ⟨a, hxs, haU⟩

omit [TopologicalSpace α] in
/-- Miss classes pull back to miss classes along restriction: missing
`K` downstairs is missing its image upstairs. -/
theorem preimage_onePointRestrict_miss (K : Set α) :
    onePointRestrict ⁻¹' {t : Set α | Disjoint t K}
      = {s : Set (OnePoint α) | Disjoint s ((↑) '' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, onePointRestrict, Set.disjoint_left]
  constructor
  · intro h x hxs hxK
    obtain ⟨a, haK, rfl⟩ := hxK
    exact h hxs haK
  · intro h a has haK
    exact h has (mem_image_of_mem _ haK)

/-- **Restriction along the coercion is Fell-continuous** at the
powerset level, over an arbitrary ambient: both faces transport
unconditionally (opens by the open embedding, compacts by continuous
image). -/
theorem continuous_onePointRestrict :
    Continuous (onePointRestrict : Set (OnePoint α) → Set α) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · rw [preimage_onePointRestrict_miss]
    exact isOpen_disjoint_of_isCompact (hK.image OnePoint.continuous_coe)
  · rw [preimage_onePointRestrict_hit]
    exact isOpen_inter_nonempty_of_isOpen (OnePoint.isOpenMap_coe V hV)

end fell

namespace FellCloseds

/-- Adjoin the point at infinity to a closed set: `F ↦ F ∪ {∞}` is
closed in the one-point compactification (its complement is the open
image of the open complement). -/
def onePointExtend (F : FellCloseds α) : FellCloseds (OnePoint α) :=
  ⟨fell.onePointExtend (F : Set α), by
    rw [OnePoint.isClosed_iff_of_mem (fell.infty_mem_onePointExtend _),
      fell.preimage_coe_onePointExtend]
    exact F.isClosed⟩

@[simp]
theorem coe_onePointExtend (F : FellCloseds α) :
    (F.onePointExtend : Set (OnePoint α)) = insert ∞ ((↑) '' (F : Set α)) := rfl

theorem infty_mem_onePointExtend (F : FellCloseds α) :
    ∞ ∈ (F.onePointExtend : Set (OnePoint α)) :=
  mem_insert _ _

/-- Restrict a closed set of the one-point compactification along the
coercion: closedness descends by continuity. -/
def onePointRestrict (B : FellCloseds (OnePoint α)) : FellCloseds α :=
  ⟨fell.onePointRestrict (B : Set (OnePoint α)), B.isClosed.preimage OnePoint.continuous_coe⟩

@[simp]
theorem coe_onePointRestrict (B : FellCloseds (OnePoint α)) :
    (B.onePointRestrict : Set α) = ((↑) : α → OnePoint α) ⁻¹' (B : Set (OnePoint α)) := rfl

theorem onePointRestrict_onePointExtend (F : FellCloseds α) :
    F.onePointExtend.onePointRestrict = F :=
  FellCloseds.ext (fell.preimage_coe_onePointExtend (F : Set α))

theorem onePointExtend_onePointRestrict {B : FellCloseds (OnePoint α)}
    (h : ∞ ∈ (B : Set (OnePoint α))) :
    B.onePointRestrict.onePointExtend = B :=
  FellCloseds.ext (fell.onePointExtend_preimage_coe h)

/-- Extension is continuous on the closed-set carriers. -/
theorem continuous_onePointExtend :
    Continuous (onePointExtend : FellCloseds α → FellCloseds (OnePoint α)) :=
  isEmbedding_coe.isInducing.continuous_iff.mpr
    (fell.continuous_onePointExtend.comp continuous_coe)

/-- Restriction is continuous on the closed-set carriers. -/
theorem continuous_onePointRestrict :
    Continuous (onePointRestrict : FellCloseds (OnePoint α) → FellCloseds α) :=
  isEmbedding_coe.isInducing.continuous_iff.mpr
    (fell.continuous_onePointRestrict.comp continuous_coe)

/-- **The `∞`-slice is closed in the hyperspace of the one-point
compactification**: it is the hit class of the compact `{∞}`.  (Its
complement is the memo's `In(Y)`.)  With the collapse homeomorphism
this re-derives Fell compactness of `CL(Y)` from compactness of the
upstairs hyperspace — the memo's original route — though the landed
Alexander argument (`FellCloseds.compactSpace`) never needed it. -/
theorem isClosed_setOf_infty_mem :
    IsClosed {B : FellCloseds (OnePoint α) | ∞ ∈ (B : Set (OnePoint α))} := by
  have heq : {B : FellCloseds (OnePoint α) | ∞ ∈ (B : Set (OnePoint α))}
      = {B : FellCloseds (OnePoint α) | ((B : Set (OnePoint α)) ∩ {∞}).Nonempty} := by
    ext B
    simp [Set.inter_singleton_nonempty]
  rw [heq]
  exact isClosed_inter_nonempty_of_isCompact isCompact_singleton

end FellCloseds

/-- **The one-point collapse dictionary, embedding form** (temporal-sheaf
memo §9.1(a)): adjoining `∞` is a homeomorphism from the Fell
hyperspace of closed subsets of `α` onto the `∞`-containing slice of
the hyperspace of the one-point compactification — stratum-general,
with no hypotheses on the ambient.  On a (weakly) locally compact
Hausdorff ambient the upstairs hyperspace topology is Vietoris and its
citizens are the compact sets
(`FellCloseds.topology_onePoint_eq_vietoris`,
`FellCloseds.isCompact_coe`), so this is `CL(Y) ≅ {B ∈ 𝒦(Y⁺) : ∞ ∈ B}`
in the classical form, and every compact-case hyperspace theorem is
objectwise-citable at the noncompact stratum through it. -/
def fellCloseds_homeoOnePoint :
    FellCloseds α ≃ₜ {B : FellCloseds (OnePoint α) // ∞ ∈ (B : Set (OnePoint α))} where
  toFun F := ⟨F.onePointExtend, F.infty_mem_onePointExtend⟩
  invFun B := B.1.onePointRestrict
  left_inv F := F.onePointRestrict_onePointExtend
  right_inv B := Subtype.ext (FellCloseds.onePointExtend_onePointRestrict B.2)
  continuous_toFun := FellCloseds.continuous_onePointExtend.subtype_mk _
  continuous_invFun := FellCloseds.continuous_onePointRestrict.comp continuous_subtype_val

@[simp]
theorem fellCloseds_homeoOnePoint_apply_coe (F : FellCloseds α) :
    ((fellCloseds_homeoOnePoint F : FellCloseds (OnePoint α)) : Set (OnePoint α))
      = insert ∞ ((↑) '' (F : Set α)) := rfl

@[simp]
theorem fellCloseds_homeoOnePoint_symm_apply_coe
    (B : {B : FellCloseds (OnePoint α) // ∞ ∈ (B : Set (OnePoint α))}) :
    ((fellCloseds_homeoOnePoint.symm B : FellCloseds α) : Set α)
      = ((↑) : α → OnePoint α) ⁻¹' (B.1 : Set (OnePoint α)) := rfl

namespace FellCloseds

/-- On a compact Hausdorff ambient the hyperspace topology **is** the
(subspace) Vietoris topology: the carrier-level face of the landed
collapse `fell_eq_vietoris`. -/
theorem topology_eq_vietoris [CompactSpace α] [T2Space α] :
    (FellCloseds.topology : TopologicalSpace (FellCloseds α))
      = .induced (↑) (TopologicalSpace.vietoris α) := by
  show TopologicalSpace.induced _ (SuFunctor.Universe.fell α) = _
  rw [fell_eq_vietoris]

/-- On a weakly locally compact Hausdorff ambient the collapse
dictionary reads in its classical form: the one-point
compactification is compact Hausdorff, so its hyperspace carries the
Vietoris topology and `fellCloseds_homeoOnePoint` lands in the
`∞`-slice of the Vietoris hyperspace. -/
theorem topology_onePoint_eq_vietoris [WeaklyLocallyCompactSpace α] [T2Space α] :
    (FellCloseds.topology : TopologicalSpace (FellCloseds (OnePoint α)))
      = .induced (↑) (TopologicalSpace.vietoris (OnePoint α)) :=
  topology_eq_vietoris

/-- On a compact ambient the hyperspace citizens are exactly the
compact sets — the `𝒦(Y⁺)` reading of the collapse dictionary's
codomain. -/
theorem isCompact_coe [CompactSpace α] (F : FellCloseds α) :
    IsCompact (F : Set α) :=
  F.isClosed.isCompact

end FellCloseds

end SuFunctor.Universe

#print axioms SuFunctor.Universe.fellCloseds_homeoOnePoint
#print axioms SuFunctor.Universe.FellCloseds.isClosed_setOf_infty_mem
#print axioms SuFunctor.Universe.FellCloseds.topology_onePoint_eq_vietoris
