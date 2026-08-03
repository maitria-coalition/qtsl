import SuFunctor.Universe.FellTopology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The measurable face of the Fell carrier

Two small pieces of infrastructure the window assembly over the Fell
carrier consumes:

* **The preimage rung** (`fell.continuous_preimage`): taking preimages
  along a continuous open map is Fell-continuous — the hit face rides
  openness (images of opens are open), the miss face rides continuity
  (images of compacts are compact).  This is the mirror of the
  pushforward rung of `SuFunctor.Universe.FellRestrict`
  (`fell.continuous_image_of_isProperMap`: hit face by continuity,
  miss face by properness), and it generalizes the clipping rung
  (`fell.continuous_restrictOpen` is the case `e := Subtype.val` with
  open range, via `IsOpen.isOpenMap_subtype_val`).  No injectivity is
  consumed anywhere.

* **The Borel structure** (`FellCloseds.instMeasurableSpace`): the
  closed-sets carrier is equipped, globally, with the Borel σ-algebra
  of its own Fell topology — the Effros Borel structure, the canonical
  measurable structure on closed sets.  The capacity development
  (`SuFunctor.Universe.FellCapacity`) states its determination theorems
  with `[MeasurableSpace (FellCloseds Y)] [BorelSpace (FellCloseds Y)]`
  as hypotheses; these instances satisfy them definitionally.  With
  this structure, measurability of every carrier map downstream is
  derived from Fell continuity rather than assumed.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

attribute [local instance] SuFunctor.Universe.fell

namespace fell

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- Hit classes pull back to hit classes along preimage: the preimage
hits `V` iff the set hits `e '' V`.  Pure set algebra. -/
theorem preimage_preimage_hit (e : β → α) (V : Set β) :
    Set.preimage e ⁻¹' {t : Set β | (t ∩ V).Nonempty}
      = {s : Set α | (s ∩ e '' V).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq]
  constructor
  · rintro ⟨b, hbs, hbV⟩
    exact ⟨e b, hbs, b, hbV, rfl⟩
  · rintro ⟨y, hys, b, hbV, rfl⟩
    exact ⟨b, hys, hbV⟩

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- Miss classes pull back to miss classes along preimage: the preimage
misses `K` iff the set misses `e '' K`.  Pure set algebra. -/
theorem preimage_preimage_miss (e : β → α) (K : Set β) :
    Set.preimage e ⁻¹' {t : Set β | Disjoint t K}
      = {s : Set α | Disjoint s (e '' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, Set.disjoint_left]
  constructor
  · rintro h y hys ⟨b, hbK, rfl⟩
    exact h hys hbK
  · intro h b hbs hbK
    exact h hbs ⟨b, hbK, rfl⟩

/-- **Preimage along a continuous open map is Fell-continuous**: the
hit face rides openness (images of opens are open), the miss face rides
continuity (images of compacts are compact) — one subbasic preimage
each, mirroring the pushforward rung
(`fell.continuous_image_of_isProperMap`), whose faces ride continuity
and properness respectively.  No injectivity is consumed: `e` need not
be an embedding.  The clipping rung `fell.continuous_restrictOpen` is
the case `e := Subtype.val` of this theorem, with `IsOpenMap` supplied
by `IsOpen.isOpenMap_subtype_val`. -/
theorem continuous_preimage {e : β → α} (hc : Continuous e)
    (ho : IsOpenMap e) : Continuous (Set.preimage e : Set α → Set β) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · rw [preimage_preimage_miss]
    exact isOpen_disjoint_of_isCompact (hK.image hc)
  · rw [preimage_preimage_hit]
    exact isOpen_inter_nonempty_of_isOpen (ho V hV)

end fell

namespace FellCloseds

/-- The closed-sets carrier is measurable via the Borel σ-algebra of
its own Fell topology: the **Effros Borel structure**, the canonical
measurable structure on closed sets.  Global on purpose — `FellCloseds`
is this development's own carrier (deliberately separate from the
library's `Closeds`), and no competing σ-algebra reaches it. -/
instance instMeasurableSpace : MeasurableSpace (FellCloseds α) := borel _

instance instBorelSpace : BorelSpace (FellCloseds α) := ⟨rfl⟩

end FellCloseds

end SuFunctor.Universe

#print axioms SuFunctor.Universe.fell.continuous_preimage
