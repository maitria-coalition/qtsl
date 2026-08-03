import SuFunctor.Plain.SpecFunctor

/-! # Window carriers: the site direction of the spec-class tier

The temporal direction of the spec-class decoration tier, at the exact
stratum: trajectories over a window family in an instantaneous state
space, the penalty calculus over them, and the two transport directions
a site-indexed fibre assignment needs.

* **Along states** (`trajMap`): a wire map or cell acts on trajectories
  pointwise in time; penalties pull back along the induced trajectory
  transport exactly as in the plain tier.  Every coherence core of the
  plain compositor replays over trajectory carriers with the same proof
  scripts, because `trajMap` is definitionally functorial and each
  landed `Tot`-calculus identity is a `rfl`.
* **Along windows** (`trajRes`/`penExt`): trajectories clip to
  subwindows; penalty *functions* do not restrict (there is no canonical
  extension of a trajectory), but they **extend** — a subwindow demand
  is read over a superwindow by evaluating on the clip.  This is the
  variance the design's compile trade is about: bodies restrict,
  functionals extend, and the two meet at the hyperspace stratum
  (`SuFunctor.Site.ClassDescent`).

The single fact the whole upgrade rides is the definitional exchange
`trajMap h ∘ trajRes hVW = trajRes hVW ∘ trajMap h` (both are
composition on opposite sides), which makes the window-extension of
penalties commute with state transport and with the compositor
(`penExt_pull_trajMap`, `penExt_boxplusW`) — the site-direction
naturality that the fibre functor's persistence proofs consume.

Fibre-side vocabulary: a window-indexed family of penalty classes is
**persistent** when extension carries each window's classes into every
superwindow's (`IsPersistent` — the lax sections of the window
presheaf, i.e. families closed under reading-small-demands-large), and
**matching** when each window's class is exactly the restriction of
every superwindow's (`IsMatching` — the strict sections).  Matching
implies persistent; the converse fails, and the strict form is not
closed under the compositor (`SuFunctor.Site.MatchingFork`), which is
why the fibre functor takes the persistent form.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain
open scoped NNReal ENNReal

universe u

variable {T : Type u}

/-- Trajectories over a window: functions from the window into an
instantaneous carrier.  (The stage type `T` carries no topology at this
stratum; the topological face of the site lives with the hyperspace,
not with the decoration calculus.) -/
abbrev Traj (W : Set T) (X : Type u) : Type u := ↥W → X

/-- Clip a trajectory to a subwindow. -/
abbrev trajRes {V W : Set T} (hVW : V ⊆ W) {X : Type u} :
    Traj W X → Traj V X :=
  fun x => x ∘ Set.inclusion hVW

/-- Transport a trajectory along a state map, pointwise in time. -/
abbrev trajMap {W : Set T} {X Y : Type u} (h : X → Y) :
    Traj W X → Traj W Y :=
  fun x => h ∘ x

/-- Read a subwindow penalty over a superwindow: evaluate on the clip.
The window direction of penalty transport — extension, not restriction
(a penalty function reads whole-window joints, so only the small-to-big
direction is canonical). -/
abbrev penExt {V W : Set T} (hVW : V ⊆ W) {X : Type u} :
    Pen (Traj V X) → Pen (Traj W X) :=
  Pen.pull (trajRes hVW)

/-- Extension along the reflexive inclusion is the identity. -/
theorem penExt_refl {W : Set T} {X : Type u} (u : Pen (Traj W X)) :
    penExt (Set.Subset.rfl : W ⊆ W) u = u := by
  have h : trajRes (Set.Subset.rfl : W ⊆ W) (X := X) = id :=
    funext fun x =>
      (congrArg (fun g => x ∘ g) (Set.inclusion_eq_id _)).trans
        (Function.comp_id x)
  show Pen.pull (trajRes Set.Subset.rfl) u = u
  rw [h, Pen.pull_id]

/-- Extension is transitive: reading a demand over a superwindow of a
superwindow is reading it over the composite inclusion.  (The window
presheaf's functoriality, penalty-point form.) -/
theorem penExt_penExt {V W Z : Set T} (hVW : V ⊆ W) (hWZ : W ⊆ Z)
    {X : Type u} (u : Pen (Traj V X)) :
    penExt hWZ (penExt hVW u) = penExt (hVW.trans hWZ) u := by
  refine (Pen.pull_pull (trajRes hVW) (trajRes hWZ) u).trans ?_
  refine congrArg (fun g => Pen.pull g u) ?_
  funext x
  show x ∘ (Set.inclusion hWZ ∘ Set.inclusion hVW) = x ∘ Set.inclusion _
  rw [Set.inclusion_comp_inclusion]

/-- **The state–window exchange**: window-extension commutes with
state-side penalty transport.  Both routes pull back along the same
trajectory map, because pre- and post-composition commute
definitionally. -/
theorem penExt_pull_trajMap {V W : Set T} (hVW : V ⊆ W) {X Y : Type u}
    (g : Y → X) (u : Pen (Traj V X)) :
    penExt hVW (Pen.pull (trajMap g) u) =
      Pen.pull (trajMap g) (penExt hVW u) :=
  (Pen.pull_pull (trajMap g) (trajRes hVW) u).trans
    (Pen.pull_pull (trajRes hVW) (trajMap g) u).symm

/-! ## The window compositor and its coherence cores

The plain compositor over trajectory carriers: marginalize a joint over
the glued apex's trajectories to each component's trajectories
(pointwise in time), evaluate, add.  Each plain coherence core replays
with its proof script unchanged: `trajMap` preserves composition and
identities definitionally, so the landed (definitional) `Tot`-calculus
identities lift along `congrArg`-free `rfl`s. -/

variable {El : Type u}

/-- Pushforward-then-add over a window: the plain compositor at
trajectory carriers. -/
def boxplusW {W : Set T} {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    (u₁ : Pen (Traj W (Pat.Tot M))) (u₂ : Pen (Traj W (Pat.Tot N))) :
    Pen (Traj W (Pat.Tot (Pat.comp M N))) :=
  fun ν => u₁ (ν.push (trajMap (Pat.compFst M N)))
    + u₂ (ν.push (trajMap (Pat.compSnd M N)))

@[simp] theorem boxplusW_apply {W : Set T} {A B C : WireSpan El}
    {M : Pat A B} {N : Pat B C} (u₁ : Pen (Traj W (Pat.Tot M)))
    (u₂ : Pen (Traj W (Pat.Tot N)))
    (ν : Joint (Traj W (Pat.Tot (Pat.comp M N)))) :
    boxplusW u₁ u₂ ν = u₁ (ν.push (trajMap (Pat.compFst M N)))
      + u₂ (ν.push (trajMap (Pat.compSnd M N))) := rfl

/-- The austere unit over a window: the zero penalty on identity-pattern
trajectories. -/
def unitPenW (A : WireSpan El) (W : Set T) :
    Pen (Traj W (Pat.Tot (Pat.id A))) := fun _ => 0

@[simp] theorem unitPenW_apply (A : WireSpan El) (W : Set T)
    (ν : Joint (Traj W (Pat.Tot (Pat.id A)))) : unitPenW A W ν = 0 := rfl

/-- **The window–compositor exchange**: window-extension is a
homomorphism for the compositor.  With `penExt_pull_trajMap`, this is
the entire site-direction naturality the fibre functor consumes. -/
theorem penExt_boxplusW {V W : Set T} (hVW : V ⊆ W) {A B C : WireSpan El}
    {M : Pat A B} {N : Pat B C} (u₁ : Pen (Traj V (Pat.Tot M)))
    (u₂ : Pen (Traj V (Pat.Tot N))) :
    penExt hVW (boxplusW u₁ u₂) =
      boxplusW (penExt hVW u₁) (penExt hVW u₂) := by
  funext ν
  simp only [Pen.pull_apply, boxplusW_apply, Joint.push_push]
  rfl

/-- Window-extension fixes the unit. -/
theorem penExt_unitPenW {V W : Set T} (hVW : V ⊆ W) (A : WireSpan El) :
    penExt hVW (unitPenW A V) = unitPenW A W := rfl

section Cores

variable {W : Set T} {A B C D A' B' C' : WireSpan El}

/-- Naturality core over a window (the plain
`pull_tot_hComp_boxplus`, trajectory carriers). -/
theorem pullW_tot_hComp_boxplusW {M₁ : Pat A B} {M₂ : Pat B C}
    {N₁ : Pat A' B'} {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'}
    {ψ : C ⟶ C'} (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ)
    (u₁ : Pen (Traj W (Pat.Tot M₁))) (u₂ : Pen (Traj W (Pat.Tot M₂))) :
    Pen.pull (trajMap (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)))
        (boxplusW u₁ u₂) =
      boxplusW (Pen.pull (trajMap (PatCell.tot α)) u₁)
        (Pen.pull (trajMap (PatCell.tot β)) u₂) := by
  funext ν
  simp only [Pen.pull_apply, boxplusW_apply, Joint.push_push]
  rfl

/-- Associativity core over a window. -/
theorem pullW_tot_lAssoc_boxplusW (M : Pat A B) (N : Pat B C) (P : Pat C D)
    (u₁ : Pen (Traj W (Pat.Tot M))) (u₂ : Pen (Traj W (Pat.Tot N)))
    (u₃ : Pen (Traj W (Pat.Tot P))) :
    Pen.pull (trajMap (PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P)))
        (boxplusW (boxplusW u₁ u₂) u₃) =
      boxplusW u₁ (boxplusW u₂ u₃) := by
  funext ν
  simp only [Pen.pull_apply, boxplusW_apply, Joint.push_push]
  rw [add_assoc]
  rfl

/-- Left unit core over a window: unit transparency without tax, at
trajectory carriers. -/
theorem pullW_tot_lLeftUnitor_boxplusW (M : Pat A B)
    (u : Pen (Traj W (Pat.Tot M))) :
    Pen.pull (trajMap (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)))
        (boxplusW (unitPenW A W) u) = u := by
  funext ν
  simp only [Pen.pull_apply, boxplusW_apply, Joint.push_push,
    unitPenW_apply, zero_add]
  show u (ν.push (trajMap id)) = u ν
  rw [show trajMap (W := W) (id : Pat.Tot M → Pat.Tot M) = id from rfl,
    Joint.push_id]

/-- Right unit core over a window, dually. -/
theorem pullW_tot_lRightUnitor_boxplusW (M : Pat A B)
    (u : Pen (Traj W (Pat.Tot M))) :
    Pen.pull (trajMap (PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)))
        (boxplusW u (unitPenW B W)) = u := by
  funext ν
  simp only [Pen.pull_apply, boxplusW_apply, Joint.push_push,
    unitPenW_apply, add_zero]
  show u (ν.push (trajMap id)) = u ν
  rw [show trajMap (W := W) (id : Pat.Tot M → Pat.Tot M) = id from rfl,
    Joint.push_id]

end Cores

/-! ## Window-indexed spec classes: persistent and matching families -/

variable {ι : Type u}

/-- A window-indexed family of penalty classes is **persistent** when
extension carries each window's members into every superwindow's class:
the family is closed under reading-small-demands-large.  These are the
lax sections of the window presheaf of classes (equivalently:
`Φ i ⊆ penExt hij ⁻¹' Φ j`), and they are the fibre objects of the
site-indexed decoration functor. -/
def IsPersistent (U : ι → Set T) {X : Type u}
    (Φ : ∀ i, Set (Pen (Traj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), penExt hij '' Φ i ⊆ Φ j

/-- A window-indexed family of penalty classes is **matching** when each
window's class is exactly the restriction of every superwindow's — the
strict sections of the window presheaf of classes. -/
def IsMatching (U : ι → Set T) {X : Type u}
    (Φ : ∀ i, Set (Pen (Traj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), Φ i = penExt hij ⁻¹' Φ j

/-- Strict sections are lax sections. -/
theorem IsMatching.isPersistent {U : ι → Set T} {X : Type u}
    {Φ : ∀ i, Set (Pen (Traj (U i) X))} (h : IsMatching U Φ) :
    IsPersistent U Φ := by
  intro i j hij
  rw [h hij]
  exact Set.image_preimage_subset _ _

/-- Persistence is preserved by state-side transport (the image of a
persistent family along `Pen.pull (trajMap g)` is persistent), by the
state–window exchange. -/
theorem IsPersistent.image_pull_trajMap {U : ι → Set T} {X Y : Type u}
    {Φ : ∀ i, Set (Pen (Traj (U i) X))} (hΦ : IsPersistent U Φ)
    (g : Y → X) :
    IsPersistent U (fun i => Pen.pull (trajMap g) '' Φ i) := by
  intro i j hij
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  rw [penExt_pull_trajMap]
  exact Set.mem_image_of_mem _ (hΦ hij (Set.mem_image_of_mem _ hu))

/-- Persistence is preserved by the componentwise compositor, by the
window–compositor exchange.  (The matching form is **not** — see
`SuFunctor.Site.MatchingFork` — which is why the fibre functor's
objects are the persistent families.) -/
theorem IsPersistent.image2_boxplusW {U : ι → Set T}
    {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    {Φ : ∀ i, Set (Pen (Traj (U i) (Pat.Tot M)))}
    {Ψ : ∀ i, Set (Pen (Traj (U i) (Pat.Tot N)))}
    (hΦ : IsPersistent U Φ) (hΨ : IsPersistent U Ψ) :
    IsPersistent U (fun i => Set.image2 boxplusW (Φ i) (Ψ i)) := by
  intro i j hij
  rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  rw [penExt_boxplusW]
  exact Set.mem_image2_of_mem (hΦ hij (Set.mem_image_of_mem _ hu))
    (hΨ hij (Set.mem_image_of_mem _ hv))

/-- The componentwise unit family is persistent (extension fixes the
unit). -/
theorem isPersistent_unitPenW (U : ι → Set T) (A : WireSpan El) :
    IsPersistent U (fun i => ({unitPenW A (U i)} :
      Set (Pen (Traj (U i) (Pat.Tot (Pat.id A)))))) := by
  intro i j hij
  rintro _ ⟨u, hu, rfl⟩
  rw [Set.mem_singleton_iff.mp hu, penExt_unitPenW]
  exact Set.mem_singleton _

end

end Site

end SuFunctor
