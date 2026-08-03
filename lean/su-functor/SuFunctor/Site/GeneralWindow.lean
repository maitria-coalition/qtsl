import SuFunctor.Plain.GeneralSeam
import SuFunctor.Site.WindowPenalty

/-! # Window carriers at the general stratum

The site direction of the spec-class decoration tier over subprobability
Borel joints: the window-extension calculus of `SuFunctor.Site.WindowPenalty`,
transposed from finitely supported joints (`Pen`) to subprobability Borel
measures (`MeasPen`), with measurability as the morphism datum — exactly
the constitutive difference of the general stratum
(`SuFunctor.Plain.MeasJoint`): the finite stratum's transport laws hold
along arbitrary carrier maps because finite sums reindex unconditionally,
while the general stratum's hold along measurable maps.

Trajectory carriers `Traj W X = ↥W → X` carry the product σ-algebra, under
which both transport directions are measurable for free:

* `measurable_trajRes` — clipping to a subwindow is measurable (each output
  coordinate is an input coordinate);
* `measurable_trajMap` — pointwise-in-time transport along a measurable
  state map is measurable.

On that footing the whole window-extension calculus replays:
`penExtM` (read a subwindow penalty over a superwindow by evaluating on
the clip), its presheaf laws (`penExtM_refl`, `penExtM_penExtM`), the
state–window exchange (`penExtM_pull_trajMap`), the window–compositor
exchange (`penExtM_mboxplusW`, stated base-free over an arbitrary
marginalization pair, matching the base-free coherence cores of the
general composite-penalty calculus), and the unit.  The fibre-side
vocabulary transposes with it: persistent and matching window-indexed
families (`IsPersistentM`, `IsMatchingM`), persistence closed under
state transport, the componentwise compositor, and the unit family.

The seam: the general window assembly restricts to the exact one along
`Joint.toMeas` — `penExtM_comp_toMeas` at the penalty level (window
extension commutes with the seam embedding), and
`IsPersistentM.seamRestrict` at the class level (a persistent family of
general classes restricts to a persistent family of exact classes).  So
the exact-stratum site assembly is a sub-instance of this one, exactly as
the exact scalar stock is a sub-instance of the general one
(`SuFunctor.Plain.GeneralSeam`).

What deliberately stays at the exact stratum: the double-categorical
*total* of the decoration functor over a wiring base, whose comparison
squares the finite state-family presentation discharges definitionally —
a measurable wiring base owes its own transport data first (see the
design notes of `SuFunctor.Plain.MeasJoint`).
-/

namespace SuFunctor

namespace Site

noncomputable section

open SuFunctor.Plain
open scoped NNReal ENNReal

universe u

variable {T : Type u}

/-! ## Measurability of the two transport directions -/

/-- Clipping trajectories to a subwindow is measurable for the product
σ-algebras: each coordinate of the clip is a coordinate of the input. -/
theorem measurable_trajRes {V W : Set T} (hVW : V ⊆ W) {X : Type u}
    [MeasurableSpace X] :
    Measurable (trajRes hVW (X := X)) :=
  measurable_pi_lambda _ fun v => measurable_pi_apply (Set.inclusion hVW v)

/-- Pointwise-in-time state transport along a measurable map is
measurable for the product σ-algebras. -/
theorem measurable_trajMap {W : Set T} {X Y : Type u} [MeasurableSpace X]
    [MeasurableSpace Y] {h : X → Y} (hm : Measurable h) :
    Measurable (trajMap h (W := W)) :=
  measurable_pi_lambda _ fun w => hm.comp (measurable_pi_apply w)

/-! ## Window extension of general-stratum penalties -/

/-- Read a subwindow penalty over a superwindow at the general stratum:
evaluate on the clip.  The window direction of penalty transport —
extension, not restriction (a penalty functional reads whole-window
joints, so only the small-to-big direction is canonical), exactly as at
the exact stratum. -/
abbrev penExtM {V W : Set T} (hVW : V ⊆ W) {X : Type u} [MeasurableSpace X] :
    MeasPen (Traj V X) → MeasPen (Traj W X) :=
  MeasPen.pull (trajRes hVW)

/-- Extension along the reflexive inclusion is the identity. -/
theorem penExtM_refl {W : Set T} {X : Type u} [MeasurableSpace X]
    (F : MeasPen (Traj W X)) :
    penExtM (Set.Subset.rfl : W ⊆ W) F = F := by
  have h : trajRes (Set.Subset.rfl : W ⊆ W) (X := X) = id :=
    funext fun x =>
      (congrArg (fun g => x ∘ g) (Set.inclusion_eq_id _)).trans
        (Function.comp_id x)
  show MeasPen.pull (trajRes Set.Subset.rfl) F = F
  rw [h, MeasPen.pull_id]

/-- Extension is transitive: reading a demand over a superwindow of a
superwindow is reading it over the composite inclusion.  The window
presheaf's functoriality at the general stratum — and the first place
the stratum's constitutive hypothesis binds: the composite law is
`MeasPen.pull_pull` along the two clips, which holds because clipping
is measurable. -/
theorem penExtM_penExtM {V W Z : Set T} (hVW : V ⊆ W) (hWZ : W ⊆ Z)
    {X : Type u} [MeasurableSpace X] (F : MeasPen (Traj V X)) :
    penExtM hWZ (penExtM hVW F) = penExtM (hVW.trans hWZ) F := by
  refine (MeasPen.pull_pull (trajRes hVW) (trajRes hWZ)
    (measurable_trajRes hVW) (measurable_trajRes hWZ) F).trans ?_
  refine congrArg (fun g => MeasPen.pull g F) ?_
  funext x
  show x ∘ (Set.inclusion hWZ ∘ Set.inclusion hVW) = x ∘ Set.inclusion _
  rw [Set.inclusion_comp_inclusion]

/-- **The state–window exchange** at the general stratum:
window-extension commutes with state-side penalty transport along a
measurable state map.  Both routes pull back along the same (measurable)
trajectory map. -/
theorem penExtM_pull_trajMap {V W : Set T} (hVW : V ⊆ W) {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y] {g : Y → X}
    (hg : Measurable g) (F : MeasPen (Traj V X)) :
    penExtM hVW (MeasPen.pull (trajMap g) F) =
      MeasPen.pull (trajMap g) (penExtM hVW F) :=
  (MeasPen.pull_pull (trajMap g) (trajRes hVW)
      (measurable_trajMap hg) (measurable_trajRes hVW) F).trans
    (MeasPen.pull_pull (trajRes hVW) (trajMap g)
      (measurable_trajRes hVW) (measurable_trajMap hg) F).symm

/-! ## The window compositor, base-free -/

/-- The window compositor at the general stratum, base-free:
marginalize a joint over a common carrier's trajectories to each
component's trajectories (pointwise in time), evaluate, add.  The two
maps are *any* pair out of a common state carrier, of which a wiring
base's glued-apex projections are the motivating instance — matching
the base-free style of the general composite-penalty calculus
(`SuFunctor.Plain.mboxplus`). -/
def mboxplusW {W : Set T} {Z U V : Type u} [MeasurableSpace Z]
    [MeasurableSpace U] [MeasurableSpace V] (π₁ : Z → U) (π₂ : Z → V)
    (F : MeasPen (Traj W U)) (G : MeasPen (Traj W V)) :
    MeasPen (Traj W Z) :=
  mboxplus (trajMap π₁) (trajMap π₂) F G

@[simp] theorem mboxplusW_apply {W : Set T} {Z U V : Type u}
    [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]
    (π₁ : Z → U) (π₂ : Z → V) (F : MeasPen (Traj W U))
    (G : MeasPen (Traj W V)) (ν : MeasJoint (Traj W Z)) :
    mboxplusW π₁ π₂ F G ν =
      F (ν.push (trajMap π₁)) + G (ν.push (trajMap π₂)) := rfl

/-- The austere unit over a window at the general stratum: the zero
penalty. -/
def munitPenW (X : Type u) [MeasurableSpace X] (W : Set T) :
    MeasPen (Traj W X) := fun _ => 0

@[simp] theorem munitPenW_apply (X : Type u) [MeasurableSpace X]
    (W : Set T) (ν : MeasJoint (Traj W X)) : munitPenW X W ν = 0 := rfl

/-- **The window–compositor exchange** at the general stratum:
window-extension is a homomorphism for the compositor, along measurable
marginalizations.  With `penExtM_pull_trajMap`, this is the entire
site-direction naturality a general fibre assignment consumes.

The proof is one application of the base-free naturality core
`pull_mboxplus_of_comm`, with both comparison squares discharged by
`rfl` — the definitional exchange
`trajMap h ∘ trajRes hVW = trajRes hVW ∘ trajMap h` (both are
composition on opposite sides), exactly the square the finite
state-family presentation discharges definitionally. -/
theorem penExtM_mboxplusW {V W : Set T} (hVW : V ⊆ W) {Z U' V' : Type u}
    [MeasurableSpace Z] [MeasurableSpace U'] [MeasurableSpace V']
    {π₁ : Z → U'} {π₂ : Z → V'} (hπ₁ : Measurable π₁)
    (hπ₂ : Measurable π₂) (F : MeasPen (Traj V U'))
    (G : MeasPen (Traj V V')) :
    penExtM hVW (mboxplusW π₁ π₂ F G) =
      mboxplusW π₁ π₂ (penExtM hVW F) (penExtM hVW G) :=
  pull_mboxplus_of_comm (trajRes hVW) (trajMap π₁) (trajMap π₂)
    (trajMap π₁) (trajMap π₂) (trajRes hVW) (trajRes hVW)
    (measurable_trajRes hVW) (measurable_trajMap hπ₁)
    (measurable_trajMap hπ₂) (measurable_trajMap hπ₁)
    (measurable_trajMap hπ₂) (measurable_trajRes hVW)
    (measurable_trajRes hVW) rfl rfl F G

/-- Window-extension fixes the unit. -/
theorem penExtM_munitPenW {V W : Set T} (hVW : V ⊆ W) (X : Type u)
    [MeasurableSpace X] :
    penExtM hVW (munitPenW X V) = munitPenW X W := rfl

/-! ## Window-indexed spec classes at the general stratum -/

variable {ι : Type u}

/-- A window-indexed family of general-stratum penalty classes is
**persistent** when extension carries each window's members into every
superwindow's class: the family is closed under
reading-small-demands-large — the lax sections of the window presheaf
of classes, transposed from `SuFunctor.Site.IsPersistent`. -/
def IsPersistentM (U : ι → Set T) {X : Type u} [MeasurableSpace X]
    (Φ : ∀ i, Set (MeasPen (Traj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), penExtM hij '' Φ i ⊆ Φ j

/-- A window-indexed family of general-stratum penalty classes is
**matching** when each window's class is exactly the restriction of
every superwindow's — the strict sections. -/
def IsMatchingM (U : ι → Set T) {X : Type u} [MeasurableSpace X]
    (Φ : ∀ i, Set (MeasPen (Traj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), Φ i = penExtM hij ⁻¹' Φ j

/-- Strict sections are lax sections. -/
theorem IsMatchingM.isPersistentM {U : ι → Set T} {X : Type u}
    [MeasurableSpace X] {Φ : ∀ i, Set (MeasPen (Traj (U i) X))}
    (h : IsMatchingM U Φ) : IsPersistentM U Φ := by
  intro i j hij
  rw [h hij]
  exact Set.image_preimage_subset _ _

/-- Persistence is preserved by state-side transport along a measurable
state map, by the state–window exchange. -/
theorem IsPersistentM.image_pull_trajMap {U : ι → Set T} {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y]
    {Φ : ∀ i, Set (MeasPen (Traj (U i) X))} (hΦ : IsPersistentM U Φ)
    {g : Y → X} (hg : Measurable g) :
    IsPersistentM U (fun i => MeasPen.pull (trajMap g) '' Φ i) := by
  intro i j hij
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  rw [penExtM_pull_trajMap hij hg]
  exact Set.mem_image_of_mem _ (hΦ hij (Set.mem_image_of_mem _ hF))

/-- Persistence is preserved by the componentwise compositor along
measurable marginalizations, by the window–compositor exchange. -/
theorem IsPersistentM.image2_mboxplusW {U : ι → Set T} {Z U' V' : Type u}
    [MeasurableSpace Z] [MeasurableSpace U'] [MeasurableSpace V']
    {π₁ : Z → U'} {π₂ : Z → V'} (hπ₁ : Measurable π₁)
    (hπ₂ : Measurable π₂)
    {Φ : ∀ i, Set (MeasPen (Traj (U i) U'))}
    {Ψ : ∀ i, Set (MeasPen (Traj (U i) V'))}
    (hΦ : IsPersistentM U Φ) (hΨ : IsPersistentM U Ψ) :
    IsPersistentM U (fun i => Set.image2 (mboxplusW π₁ π₂) (Φ i) (Ψ i)) := by
  intro i j hij
  rintro _ ⟨_, ⟨F, hF, G, hG, rfl⟩, rfl⟩
  rw [penExtM_mboxplusW hij hπ₁ hπ₂]
  exact Set.mem_image2_of_mem (hΦ hij (Set.mem_image_of_mem _ hF))
    (hΨ hij (Set.mem_image_of_mem _ hG))

/-- The componentwise unit family is persistent (extension fixes the
unit). -/
theorem isPersistentM_munitPenW (U : ι → Set T) (X : Type u)
    [MeasurableSpace X] :
    IsPersistentM U (fun i => ({munitPenW X (U i)} :
      Set (MeasPen (Traj (U i) X)))) := by
  intro i j hij
  rintro _ ⟨F, hF, rfl⟩
  rw [Set.mem_singleton_iff.mp hF, penExtM_munitPenW]
  exact Set.mem_singleton _

/-! ## The seam: the exact assembly is a sub-instance of the general one -/

/-- Window extension commutes with the seam embedding: reading a
general-stratum subwindow penalty over a superwindow and restricting to
finitely supported joints is restricting first and extending at the
exact stratum.  (`Joint.pull_toMeas` at the clip, which is
measurable.) -/
theorem penExtM_comp_toMeas {V W : Set T} (hVW : V ⊆ W) {X : Type u}
    [MeasurableSpace X] (F : MeasPen (Traj V X)) :
    (penExtM hVW F) ∘ Joint.toMeas = penExt hVW (F ∘ Joint.toMeas) :=
  Joint.pull_toMeas (trajRes hVW) (measurable_trajRes hVW) F

/-- A persistent family of general-stratum classes restricts, along the
seam, to a persistent family of exact-stratum classes: the exact
site-indexed assembly is a sub-instance of the general one. -/
theorem IsPersistentM.seamRestrict {U : ι → Set T} {X : Type u}
    [MeasurableSpace X] {Φ : ∀ i, Set (MeasPen (Traj (U i) X))}
    (hΦ : IsPersistentM U Φ) :
    IsPersistent U (fun i => (fun F => F ∘ Joint.toMeas) '' Φ i) := by
  intro i j hij
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  rw [← penExtM_comp_toMeas hij]
  exact Set.mem_image_of_mem _ (hΦ hij (Set.mem_image_of_mem _ hF))

end

end Site

end SuFunctor
