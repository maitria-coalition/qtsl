import SuFunctor.Universe.FellDescent
import SuFunctor.Universe.LocallyClosedLayer
import Mathlib.Topology.LocallyClosed

/-! # Class descent: constructible fibre classes over the window system

The topological face of the site-indexed fibre stratum, at the
hyperspace where the descent theorem lives.  Penalty functions extend
along windows (`SuFunctor.Site.WindowPenalty`); their **bodies** —
points of the Fell hyperspace — restrict, along the clip maps of the
descent development.  This module supplies the class stratum over those
restrictions and consumes the landed descent theorem
(`SuFunctor.Universe.FellCloseds.projLimHomeomorph`), never re-proving
any part of it:

* **transition continuity** (`continuous_clipLE`): the clip between two
  open windows is Fell-continuous — the same two-subbasic-preimages
  argument as the ambient clip, with the window inclusion supplying an
  open embedding; this is what makes the window system's transition
  maps a continuous diagram rather than a bare one;
* **free class transport** (`classExt`): the preimage of a fibre class
  along a transition clip — a class over a subwindow read over a
  superwindow ("the citizens whose clip satisfies it") — preserves
  local closedness and constructibility for free, by continuity;
* **class descent** (`classDescent`, `isConstructibleUnion_classDescent_iff`):
  over a directed open cover, the landed descent homeomorphism induces
  an order isomorphism between fibre classes over the glued ambient and
  fibre classes over the projective limit, carrying constructible
  classes to constructible classes in both directions — the class-level
  face of "any fibrewise construction commuting with clipping
  globalizes";
* **ideal points are global citizens** (`bijective_toProjLim`): the
  compatible singleton-sections of the window system — per window the
  clip of one closed citizen, compatibly (`clipLE_clip`, landed) — are
  in bijection with the closed citizens of the glued ambient, again by
  the landed homeomorphism; and the judgment against a transported
  class is window-local (`clip_mem_classExt_iff`).

The hypotheses of the descent-consuming statements are exactly the
landed theorem's (open members, directedness, covering), and the landed
refuting fixtures delimit them: dropping directedness already breaks
surjectivity of the section map
(`FellCloseds.not_surjective_toProjLim_nondirectedPair`), and the
closed-miss face cannot descend at all
(`FellCloseds.not_iInf_induced_le_vietoris`) — cited as the mutants of
this module, not duplicated.

Everything here is fibre-class-blind: the ambient is an arbitrary
topological space, so any state-class dial upstream (semialgebraic,
countably-pieced, or wider) rides through with zero contact.
-/

namespace SuFunctor

namespace Site

open Set Topology TopologicalSpace
open SuFunctor.Universe SuFunctor.Universe.FellCloseds

variable {α : Type*} [TopologicalSpace α]

attribute [local instance] SuFunctor.Universe.fell

/-! ## Transition continuity -/

section Transition

variable {V W : Set α}

/-- The window inclusion is an open map into the superwindow's subspace
whenever the subwindow is open: its image is the trace of an open set. -/
theorem isOpenMap_inclusion (hV : IsOpen V) (hVW : V ⊆ W) :
    IsOpenMap (Set.inclusion hVW) := by
  intro O hO
  have himg : Set.inclusion hVW '' O
      = ((↑) : ↥W → α) ⁻¹' (((↑) : ↥V → α) '' O) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      exact ⟨v, hv, Subtype.ext hvx⟩
  rw [himg]
  exact (hV.isOpenMap_subtype_val O hO).preimage continuous_subtype_val

omit [TopologicalSpace α] in
/-- Hit classes pull back to hit classes along preimage-by-inclusion:
pure set algebra. -/
theorem preimage_inclusion_hit (hVW : V ⊆ W) (O : Set ↥V) :
    (fun s : Set ↥W => Set.inclusion hVW ⁻¹' s) ⁻¹'
        {t : Set ↥V | (t ∩ O).Nonempty}
      = {s : Set ↥W | (s ∩ Set.inclusion hVW '' O).Nonempty} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq]
  constructor
  · rintro ⟨x, hxs, hxO⟩
    exact ⟨Set.inclusion hVW x, hxs, x, hxO, rfl⟩
  · rintro ⟨y, hys, x, hxO, rfl⟩
    exact ⟨x, hys, hxO⟩

omit [TopologicalSpace α] in
/-- Miss classes pull back to miss classes along preimage-by-inclusion:
pure set algebra. -/
theorem preimage_inclusion_miss (hVW : V ⊆ W) (K : Set ↥V) :
    (fun s : Set ↥W => Set.inclusion hVW ⁻¹' s) ⁻¹'
        {t : Set ↥V | Disjoint t K}
      = {s : Set ↥W | Disjoint s (Set.inclusion hVW '' K)} := by
  ext s
  simp only [mem_preimage, mem_setOf_eq, Set.disjoint_left]
  constructor
  · intro h y hys hy
    obtain ⟨x, hxK, rfl⟩ := hy
    exact h hys hxK
  · intro h x hxs hxK
    exact h hxs ⟨x, hxK, rfl⟩

/-- Preimage along the window inclusion is Fell-continuous at the
powerset stratum: hits ride openness of the inclusion's image, misses
ride compactness of the image — one subbasic preimage each, exactly the
ambient-clip argument with the inclusion in place of the coercion. -/
theorem continuous_preimage_inclusion (hV : IsOpen V) (hVW : V ⊆ W) :
    Continuous (fun s : Set ↥W => Set.inclusion hVW ⁻¹' s) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro t (⟨K, hK, rfl⟩ | ⟨O, hO, rfl⟩)
  · rw [preimage_inclusion_miss]
    exact fell.isOpen_disjoint_of_isCompact
      (hK.image (continuous_inclusion hVW))
  · rw [preimage_inclusion_hit]
    exact fell.isOpen_inter_nonempty_of_isOpen
      (isOpenMap_inclusion hV hVW O hO)

/-- **Transition clips are Fell-continuous** between open windows: the
window system's diagram of hyperspaces is a continuous diagram, which
is what the free class transport below and the descent theorem's
compatible-family space both consume. -/
theorem continuous_clipLE (hV : IsOpen V) (hVW : V ⊆ W) :
    Continuous (clipLE hVW : FellCloseds ↥W → FellCloseds ↥V) :=
  isEmbedding_coe.isInducing.continuous_iff.mpr
    ((continuous_preimage_inclusion hV hVW).comp continuous_coe)

/-! ## Free class transport -/

/-- Read a fibre class over a subwindow as a fibre class over a
superwindow: the citizens whose clip lies in the class.  (The semantic
transport of fibre classes along the site — preimage along the
transition clip.) -/
def classExt (hVW : V ⊆ W) (Φ : Set (FellCloseds ↥V)) :
    Set (FellCloseds ↥W) :=
  clipLE hVW ⁻¹' Φ

@[simp] theorem mem_classExt {hVW : V ⊆ W} {Φ : Set (FellCloseds ↥V)}
    {F : FellCloseds ↥W} : F ∈ classExt hVW Φ ↔ clipLE hVW F ∈ Φ :=
  Iff.rfl

/-- **The judgment is window-local along class transport**: a global
citizen's superwindow face satisfies the transported class iff its
subwindow face satisfies the original.  (The landed `clipLE_clip` is
the whole proof.) -/
theorem clip_mem_classExt_iff (hVW : V ⊆ W) {Φ : Set (FellCloseds ↥V)}
    (F : FellCloseds α) :
    clip W F ∈ classExt hVW Φ ↔ clip V F ∈ Φ := by
  rw [mem_classExt, clipLE_clip]

/-- Class transport preserves local closedness — the interface
contract's "for free" clause, mechanized: preimage under a continuous
map. -/
theorem IsLocallyClosed.classExt (hV : IsOpen V) (hVW : V ⊆ W)
    {Φ : Set (FellCloseds ↥V)} (hΦ : IsLocallyClosed Φ) :
    IsLocallyClosed (classExt hVW Φ) :=
  hΦ.preimage (continuous_clipLE hV hVW)

/-- Class transport preserves constructibility: preimages commute with
finite unions. -/
theorem IsConstructibleUnion.classExt (hV : IsOpen V) (hVW : V ⊆ W)
    {Φ : Set (FellCloseds ↥V)} (hΦ : IsConstructibleUnion Φ) :
    IsConstructibleUnion (Site.classExt hVW Φ) := by
  obtain ⟨n, C, hC, rfl⟩ := hΦ
  refine ⟨n, fun k => Site.classExt hVW (C k),
    fun k => IsLocallyClosed.classExt hV hVW (hC k), ?_⟩
  simp only [Site.classExt, preimage_iUnion]

end Transition

/-! ## Constructibility transports along homeomorphisms -/

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local closedness transports along a homeomorphism, both ways. -/
theorem isLocallyClosed_image_homeomorph (e : X ≃ₜ Y) {s : Set X} :
    IsLocallyClosed (e '' s) ↔ IsLocallyClosed s := by
  have himg : e '' s = e.symm ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  constructor
  · intro h
    have hpre : e ⁻¹' (e '' s) = s := by
      ext x
      constructor
      · rintro ⟨x', hx', hxx⟩
        rw [← e.injective hxx]
        exact hx'
      · intro hx
        exact ⟨x, hx, rfl⟩
    have h' := h.preimage e.continuous
    rwa [hpre] at h'
  · intro h
    rw [himg]
    exact h.preimage e.symm.continuous

/-- Constructibility transports along a homeomorphism, both ways. -/
theorem isConstructibleUnion_image_homeomorph (e : X ≃ₜ Y) {s : Set X} :
    IsConstructibleUnion (e '' s) ↔ IsConstructibleUnion s := by
  constructor
  · rintro ⟨n, C, hC, hs⟩
    refine ⟨n, fun k => e.symm '' C k,
      fun k => (isLocallyClosed_image_homeomorph e.symm).mpr (hC k), ?_⟩
    have hrec : s = e.symm '' (e '' s) := by
      rw [← Set.image_comp, Homeomorph.symm_comp_self, Set.image_id]
    rw [hrec, hs, Set.image_iUnion]
  · rintro ⟨n, C, hC, hs⟩
    exact ⟨n, fun k => e '' C k,
      fun k => (isLocallyClosed_image_homeomorph e).mpr (hC k),
      by rw [hs, Set.image_iUnion]⟩

end Homeomorph

/-! ## Class descent along directed open covers -/

section Descent

variable {ι : Type*} {U : ι → Set α}

/-- **Class descent**: over a directed open cover, fibre classes over
the glued ambient correspond order-isomorphically to fibre classes over
the projective limit of the window hyperspaces — the image under the
**landed** descent homeomorphism, consumed and not re-proven. -/
def classDescent (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) :
    Set (FellCloseds α) ≃o Set (ProjLim U) where
  toFun Φ := projLimHomeomorph U hUo hdir hcov '' Φ
  invFun Ψ := (projLimHomeomorph U hUo hdir hcov).symm '' Ψ
  left_inv Φ := by
    show (projLimHomeomorph U hUo hdir hcov).symm ''
        ((projLimHomeomorph U hUo hdir hcov) '' Φ) = Φ
    rw [← Set.image_comp, Homeomorph.symm_comp_self, Set.image_id]
  right_inv Ψ := by
    show (projLimHomeomorph U hUo hdir hcov) ''
        ((projLimHomeomorph U hUo hdir hcov).symm '' Ψ) = Ψ
    rw [← Set.image_comp, Homeomorph.self_comp_symm, Set.image_id]
  map_rel_iff' {Φ Ψ} :=
    Set.image_subset_image_iff (projLimHomeomorph U hUo hdir hcov).injective

@[simp] theorem classDescent_apply (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    (Φ : Set (FellCloseds α)) :
    classDescent hUo hdir hcov Φ
      = projLimHomeomorph U hUo hdir hcov '' Φ := rfl

/-- Class descent carries constructible classes to constructible
classes, in both directions: the site's fibre stratum and the glued
fibre stratum have the same constructible layer. -/
theorem isConstructibleUnion_classDescent_iff (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    {Φ : Set (FellCloseds α)} :
    IsConstructibleUnion (classDescent hUo hdir hcov Φ)
      ↔ IsConstructibleUnion Φ := by
  rw [classDescent_apply]
  exact isConstructibleUnion_image_homeomorph _

/-- **Ideal points of the fibre sheaf are global citizens**: the
compatible singleton-sections — per window the clip of one citizen,
compatible by the landed `clipLE_clip` — biject with the closed
citizens of the glued ambient.  This is the landed descent
homeomorphism's underlying bijection, cited whole. -/
theorem bijective_toProjLim (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) :
    Function.Bijective (toProjLim U) :=
  (projLimHomeomorph U hUo hdir hcov).bijective

end Descent

end Site

end SuFunctor
