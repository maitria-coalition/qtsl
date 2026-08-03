import SuFunctor.Universe.FellTopology
import Mathlib.Topology.Maps.Proper.Basic

/-! # Fell restriction: clip-to-open and proper pushforward are continuous

The two continuity keystones of the temporal-sheaf carrier (the
design's §3.1, Lean rungs A/B): the sheaf carrier's restriction maps
factor as clip-to-open composed with pushforward along a proper map,
and each factor is Fell-continuous by a two-line subbasis argument.

* **Rung A** (`continuous_restrictOpen`, §3.1(a)): restriction of the
  Fell hyperspace along an open inclusion is continuous — the hit face
  by openness of the inclusion (open subsets of an open set are open
  upstairs), the miss face by compactness transport (compact in the
  subspace is compact upstairs).
* **Rung B** (`continuous_image_of_isProperMap`, §3.1(b), the memo's
  `fell.continuous_map_proper`): pushforward `F ↦ f '' F` along a
  proper map is continuous — the hit face by continuity (preimages of
  opens are open), the miss face by properness (preimages of compacts
  are compact).  The two subbasis families split the work perfectly:
  continuity feeds the hit face, properness feeds the miss face.

Each subbasic preimage is again subbasic — the Fell subbasis is closed
under precisely these two operations.

The clip is stated subtype-style: `fell.restrictOpen U : Set α → Set U`,
`s ↦ (↑) ⁻¹' s`, which on closed sets is "intersect with `U`, viewed
inside `U`" — the clipping leg of the sheaf carrier's restriction.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace

variable {α : Type*} [TopologicalSpace α]

attribute [local instance] SuFunctor.Universe.fell

namespace fell

variable {U : Set α}

/-- Clip a subset of the ambient to (the subtype of) a distinguished
set `U`. -/
def restrictOpen (U : Set α) (s : Set α) : Set U := (↑) ⁻¹' s

/-- Hit classes pull back to hit classes along clipping: hitting `V`
inside `U` is hitting the image of `V` upstairs. -/
theorem preimage_restrictOpen_hit (V : Set U) :
    restrictOpen U ⁻¹' {t : Set U | (t ∩ V).Nonempty}
      = {s : Set α | (s ∩ (↑) '' V).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq]
  constructor
  · rintro ⟨x, hxs, hxV⟩
    exact ⟨↑x, hxs, x, hxV, rfl⟩
  · rintro ⟨y, hys, x, hxV, rfl⟩
    exact ⟨x, hys, hxV⟩

/-- Miss classes pull back to miss classes along clipping: missing `K`
inside `U` is missing the image of `K` upstairs. -/
theorem preimage_restrictOpen_miss (K : Set U) :
    restrictOpen U ⁻¹' {t : Set U | Disjoint t K}
      = {s : Set α | Disjoint s ((↑) '' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, Set.disjoint_left]
  constructor
  · intro h y hys hy
    obtain ⟨x, hxK, rfl⟩ := hy
    exact h hys hxK
  · intro h x hxs hxK
    exact h hxs ⟨x, hxK, rfl⟩

/-- **Clipping to an open set is Fell-continuous** (temporal-sheaf memo
§3.1(a), rung A): the hit face rides openness of the inclusion, the
miss face rides compactness of the image — one subbasic preimage each.
This is the continuity of the sheaf carrier's restriction maps in
their clipping leg; the open-ness hypothesis is load-bearing exactly
on the hit face (the seam witness of memo §3.2 is the closed-clip
refutation). -/
theorem continuous_restrictOpen (hU : IsOpen U) :
    Continuous (restrictOpen U) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · rw [preimage_restrictOpen_miss]
    exact isOpen_disjoint_of_isCompact (hK.image continuous_subtype_val)
  · rw [preimage_restrictOpen_hit]
    exact isOpen_inter_nonempty_of_isOpen (hU.isOpenMap_subtype_val V hV)

section Pushforward

variable {β : Type*} [TopologicalSpace β] {f : α → β}

/-- Hit classes pull back to hit classes along pushforward: the image
hits `V` iff the set hits `f ⁻¹' V`.  Pure set algebra — no topology
enters until the continuity theorem below. -/
theorem preimage_image_hit (f : α → β) (V : Set β) :
    Set.image f ⁻¹' {t : Set β | (t ∩ V).Nonempty}
      = {s : Set α | (s ∩ f ⁻¹' V).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨x, hxs, rfl⟩, hyV⟩
    exact ⟨x, hxs, hyV⟩
  · rintro ⟨x, hxs, hxV⟩
    exact ⟨f x, ⟨x, hxs, rfl⟩, hxV⟩

/-- Miss classes pull back to miss classes along pushforward: the image
misses `K` iff the set misses `f ⁻¹' K`.  Pure set algebra. -/
theorem preimage_image_miss (f : α → β) (K : Set β) :
    Set.image f ⁻¹' {t : Set β | Disjoint t K}
      = {s : Set α | Disjoint s (f ⁻¹' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, Set.disjoint_left]
  constructor
  · intro h x hxs hxK
    exact h ⟨x, hxs, rfl⟩ hxK
  · rintro h y ⟨x, hxs, rfl⟩ hyK
    exact h hxs hyK

/-- **Pushforward along a proper map is Fell-continuous** (temporal-sheaf
memo §3.1(b), rung B — the memo's `fell.continuous_map_proper`): the hit
face rides continuity (preimages of opens are open), the miss face rides
properness (preimages of compacts are compact) — one subbasic preimage
each.  This is the state leg of the sheaf carrier's restriction maps;
properness is exactly where the state sheaf's third commitment (proper
restriction maps, memo §2) cashes.  No separation or local compactness
is consumed at the powerset stratum: mathlib's
`IsProperMap.isCompact_preimage` is unconditional. -/
theorem continuous_image_of_isProperMap (hf : IsProperMap f) :
    Continuous (Set.image f : Set α → Set β) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · rw [preimage_image_miss]
    exact isOpen_disjoint_of_isCompact (hf.isCompact_preimage hK)
  · rw [preimage_image_hit]
    exact isOpen_inter_nonempty_of_isOpen (hV.preimage hf.continuous)

end Pushforward

end fell

end SuFunctor.Universe

#print axioms SuFunctor.Universe.fell.continuous_restrictOpen
#print axioms SuFunctor.Universe.fell.continuous_image_of_isProperMap
