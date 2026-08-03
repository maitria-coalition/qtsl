import SuFunctor.Site.TemporalTypeTheory
import SuFunctor.Site.SiteFunctor

/-! # Behavior types as System Specs: the spec-level leg of the inclusion

The spec-level leg of the inclusion of temporal type theory into the
double category of site-indexed spec classes: a **behavior subtype**
(a subpresheaf of the trajectory presheaf over a window family — the
window form of a temporal-type-theoretic subobject of the behavior
type of trajectories) becomes a **System Spec** — a persistent
window-indexed family of penalty classes, i.e. an object fibre of
`SuFunctor.Site.SiteSpecTotal` — by taking, at each window, all
subwindow **clip-demands**: extensions of the indicator penalties of
the behavior classes.

The inclusion is semantic, not merely formal, and functorial in every
double-categorical direction available at this tier:

* **judgment** (`satAt_specOfBehavior_iff`): a joint satisfies the
  spec of `B` at a window iff its support lies in `B` there —
  penalty satisfaction is behavior-type membership, on the nose;
* **fibre order** (`satAt_specOfBehavior_mono`): entailment between
  behavior specs is monotone in the subpresheaf order;
* **tight transport** (`wSpecMap_specOfBehavior`): transporting the
  spec of `B` along a wire map is the spec of the pullback behavior
  type — a *strict* equality, with no surjectivity hypothesis: the
  whole indicator calculus is preimage-shaped (`pull_indPen`), which
  is exactly where it is better-behaved than image-shaped class
  transport;
* **loose composition** (`boxplusW_indPen`,
  `cplOfBehavior_glue_subset_wComp`, `satAt_wComp_iff_glue`): on
  indicator penalties the compositor `⊞` *is* span composition — the
  indicator of the pullback-intersection over the glued apex; at the
  class level the spec of the glued behavior type sits inside the
  composed classes (the extra mixed-window composites are the
  laxity), and the two classes have the same models, so the laxity
  is semantically silent.

Persistence of the spec family consumes only the window calculus
(`penExt_penExt`, `penExt_refl`); the subpresheaf condition is
consumed exactly once, in the judgment bridge — the presheaf law is a
semantic fact, not an algebraic one. -/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory CategoryTheory.WireSpan
open SuFunctor.Plain
open scoped NNReal ENNReal

universe u

variable {T ι : Type u}

/-! ## Indicator penalties -/

/-- `ℝ≥0` has no nonzero additive units (absent from mathlib at the
pinned revision; the `ℝ≥0∞` instance's proof works verbatim). -/
instance : Unique (AddUnits ℝ≥0) where
  default := 0
  uniq a := AddUnits.ext <| nonpos_iff_eq_zero.1 <| by
    rw [← a.add_neg]; exact le_self_add

/-- The support of a pushforward joint is the image of the support —
with no injectivity hypothesis, because `ℝ≥0` weights cannot cancel. -/
theorem support_push_eq_image {X Y : Type u} (h : X → Y) (μ : Joint X) :
    ↑(μ.push h).wt.support = h '' ↑μ.wt.support := by
  classical
  rw [Joint.push_wt, Finsupp.mapDomain_support_of_subsingletonAddUnits,
    Finset.coe_image]

/-- The indicator penalty of a behavior class: charge nothing on
joints supported inside the class, everything on the rest. -/
def indPen {K : Type u} (S : Set K) : Pen K := fun ν =>
  @ite _ ((↑ν.wt.support : Set K) ⊆ S) (Classical.dec _) 0 ⊤

theorem indPen_apply_of_subset {K : Type u} {S : Set K} {ν : Joint K}
    (h : (↑ν.wt.support : Set K) ⊆ S) : indPen S ν = 0 := by
  unfold indPen
  exact if_pos h

theorem indPen_apply_of_not_subset {K : Type u} {S : Set K} {ν : Joint K}
    (h : ¬ (↑ν.wt.support : Set K) ⊆ S) : indPen S ν = ⊤ := by
  unfold indPen
  exact if_neg h

theorem indPen_eq_zero_iff {K : Type u} {S : Set K} {ν : Joint K} :
    indPen S ν = 0 ↔ (↑ν.wt.support : Set K) ⊆ S := by
  by_cases h : (↑ν.wt.support : Set K) ⊆ S
  · simp [indPen_apply_of_subset h, h]
  · simp [indPen_apply_of_not_subset h, h]

/-- **Indicator transport is preimage transport** — one lemma covering
both directions the site-indexed functor moves in: along `trajRes`
(window extension, `penExt`) and along `trajMap` (state transport). -/
theorem pull_indPen {K L : Type u} (h : K → L) (S : Set L) :
    Pen.pull h (indPen S) = indPen (h ⁻¹' S) := by
  funext ν
  show indPen S (ν.push h) = indPen (h ⁻¹' S) ν
  by_cases hs : (↑ν.wt.support : Set K) ⊆ h ⁻¹' S
  · rw [indPen_apply_of_subset hs, indPen_apply_of_subset (by
      rw [support_push_eq_image]
      exact Set.image_subset_iff.mpr hs)]
  · rw [indPen_apply_of_not_subset hs, indPen_apply_of_not_subset (by
      rw [support_push_eq_image]
      exact fun hc => hs (Set.image_subset_iff.mp hc))]

/-- Indicators add to the indicator of the intersection: a conjunction
of behavior constraints. -/
theorem indPen_add_indPen_apply {K : Type u} (S₁ S₂ : Set K) (ν : Joint K) :
    indPen S₁ ν + indPen S₂ ν = indPen (S₁ ∩ S₂) ν := by
  by_cases h₁ : (↑ν.wt.support : Set K) ⊆ S₁ <;>
    by_cases h₂ : (↑ν.wt.support : Set K) ⊆ S₂
  · rw [indPen_apply_of_subset h₁, indPen_apply_of_subset h₂,
      indPen_apply_of_subset (Set.subset_inter h₁ h₂), add_zero]
  · rw [indPen_apply_of_subset h₁, indPen_apply_of_not_subset h₂,
      indPen_apply_of_not_subset
        (fun hc => h₂ (hc.trans Set.inter_subset_right)), zero_add]
  · rw [indPen_apply_of_not_subset h₁, indPen_apply_of_subset h₂,
      indPen_apply_of_not_subset
        (fun hc => h₁ (hc.trans Set.inter_subset_left)), add_zero]
  · rw [indPen_apply_of_not_subset h₁,
      indPen_apply_of_not_subset
        (fun hc => h₁ (hc.trans Set.inter_subset_left)), top_add]

/-! ## Behavior subtypes over a window family -/

/-- A **behavior subtype** over the window family `U`: per-window
classes of trajectories, closed under clipping — the window form of a
subpresheaf of the trajectory presheaf (via `TTT.anchorTrajIso`, the
window form of a temporal-type-theoretic subobject of the behavior
type of trajectories of a state space). -/
structure WBehavior (U : ι → Set T) (X : Type u) : Type u where
  /-- The behavior class at each window. -/
  cls : ∀ i, Set (Traj (U i) X)
  /-- Behaviors clip to behaviors: the subpresheaf condition. -/
  restrict : ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), trajRes hij '' cls j ⊆ cls i

namespace WBehavior

variable {U : ι → Set T} {X X' : Type u}

/-- Componentwise order: the subpresheaf order on behavior subtypes. -/
def le (B B' : WBehavior U X) : Prop := ∀ i, B.cls i ⊆ B'.cls i

/-- Pullback of a behavior subtype along a state map. -/
def pull (g : X' → X) (B : WBehavior U X) : WBehavior U X' where
  cls i := trajMap g ⁻¹' B.cls i
  restrict := by
    intro i j hij
    rintro _ ⟨x, hx, rfl⟩
    exact B.restrict hij ⟨trajMap g x, hx, rfl⟩

/-- Componentwise intersection of behavior subtypes. -/
def inter (B B' : WBehavior U X) : WBehavior U X where
  cls i := B.cls i ∩ B'.cls i
  restrict := by
    intro i j hij
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨B.restrict hij ⟨x, hx.1, rfl⟩, B'.restrict hij ⟨x, hx.2, rfl⟩⟩

end WBehavior

/-! ## The spec of a behavior type -/

variable {X : Type u}

/-- The System Spec of a behavior subtype: at each window, the class
of all subwindow **clip-demands** — indicator penalties of the
behavior classes, read over the window through `penExt`. -/
def specOfBehavior (U : ι → Set T) (B : WBehavior U X) (j : ι) :
    Set (Pen (Traj (U j) X)) :=
  {p | ∃ i, ∃ hij : U i ⊆ U j, p = penExt hij (indPen (B.cls i))}

/-- The behavior class's own indicator is a member (the reflexive
clip-demand). -/
theorem indPen_mem_specOfBehavior (U : ι → Set T) (B : WBehavior U X) (j : ι) :
    indPen (B.cls j) ∈ specOfBehavior U B j :=
  ⟨j, Set.Subset.rfl, (penExt_refl _).symm⟩

/-- **Persistence**: the spec of a behavior type is a fibre object of
the site-indexed decoration functor.  Consumes only the transitivity
of window extension — never the subpresheaf condition (which is the
judgment bridge's to consume). -/
theorem isPersistent_specOfBehavior (U : ι → Set T) (B : WBehavior U X) :
    IsPersistent U (specOfBehavior U B) := by
  intro j k hjk
  rintro _ ⟨_, ⟨i, hij, rfl⟩, rfl⟩
  exact ⟨i, hij.trans hjk, penExt_penExt hij hjk _⟩

/-- Componentwise satisfaction of a penalty class: every member
vanishes on the joint. -/
abbrev SatAt {K : Type u} (ν : Joint K) (Φ : Set (Pen K)) : Prop :=
  ∀ p ∈ Φ, p ν = 0

theorem SatAt.anti {K : Type u} {ν : Joint K} {Φ Ψ : Set (Pen K)}
    (hΦΨ : Φ ⊆ Ψ) (h : SatAt ν Ψ) : SatAt ν Φ :=
  fun p hp => h p (hΦΨ hp)

/-- **The judgment bridge**: a joint satisfies the spec of `B` at a
window iff its support lies in `B` there — penalty satisfaction is
behavior-type membership.  The forward direction consumes the
reflexive clip-demand; the backward direction is where the
subpresheaf condition is consumed (exactly once in this module). -/
theorem satAt_specOfBehavior_iff (U : ι → Set T) (B : WBehavior U X) (j : ι)
    (ν : Joint (Traj (U j) X)) :
    SatAt ν (specOfBehavior U B j) ↔ (↑ν.wt.support : Set (Traj (U j) X)) ⊆ B.cls j := by
  constructor
  · intro h
    exact indPen_eq_zero_iff.mp (h _ (indPen_mem_specOfBehavior U B j))
  · rintro hsup p ⟨i, hij, rfl⟩
    rw [show penExt hij (indPen (B.cls i)) = indPen (trajRes hij ⁻¹' B.cls i) from
      pull_indPen _ _]
    exact indPen_apply_of_subset fun x hx => B.restrict hij ⟨x, hsup hx, rfl⟩

/-- **Entailment functoriality**: the inclusion is monotone from the
subpresheaf order to spec entailment. -/
theorem satAt_specOfBehavior_mono (U : ι → Set T) {B B' : WBehavior U X}
    (hBB' : B.le B') (j : ι) (ν : Joint (Traj (U j) X))
    (h : SatAt ν (specOfBehavior U B j)) : SatAt ν (specOfBehavior U B' j) := by
  rw [satAt_specOfBehavior_iff] at h ⊢
  exact h.trans (hBB' j)

/-! ## Into the double category of System Specs -/

variable {El : Type u}

/-- The spec of a behavior type over an interface's states, as a fibre
object of the site-indexed decoration functor. -/
def specOfBehaviorW (U : ι → Set T) {A : WireSpan El}
    (B : WBehavior U (states A)) : WSpec U A :=
  ⟨specOfBehavior U B, isPersistent_specOfBehavior U B⟩

/-- The spec of a behavior type over a pattern's glued apex, as a
decoration. -/
def cplOfBehavior (U : ι → Set T) {A B : WireSpan El} {M : Pat A B}
    (Bh : WBehavior U (Pat.Tot M)) : WCpl U M :=
  ⟨specOfBehavior U Bh, isPersistent_specOfBehavior U Bh⟩

/-- **The inclusion lands in the double category of System Specs**: an
interface together with the spec of a behavior type is an object of
the site-indexed total. -/
def ttObject (U : ι → Set T) {A : WireSpan El} (B : WBehavior U (states A)) :
    SiteSpecTotal U El :=
  (siteSpecFunctor U El).toFunctor.elementsMk A (specOfBehaviorW U B)

/-- **Tight-transport intertwining, strict**: transporting the spec of
a behavior type along a wire map is the spec of the pulled-back
behavior type.  No surjectivity hypothesis — where image-shaped class
transport is exact only on the surjective sub-base, the indicator
calculus is preimage-shaped on both of its axes and commutes with
everything. -/
theorem wSpecMap_specOfBehavior (U : ι → Set T) {A B : WireSpan El}
    (φ : A ⟶ B) (Bh : WBehavior U (states A)) :
    wSpecMap U φ (specOfBehaviorW U Bh) =
      specOfBehaviorW U (Bh.pull (res φ)) := by
  refine Subtype.ext (funext fun j => Set.ext fun p => ?_)
  constructor
  · rintro ⟨_, ⟨i, hij, rfl⟩, rfl⟩
    refine ⟨i, hij, ?_⟩
    rw [← penExt_pull_trajMap, pull_indPen]
    rfl
  · rintro ⟨i, hij, rfl⟩
    refine ⟨penExt hij (indPen (Bh.cls i)), ⟨i, hij, rfl⟩, ?_⟩
    rw [← penExt_pull_trajMap, pull_indPen]
    rfl

/-! ## The loose direction: the compositor is span composition -/

variable {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}

/-- The glued behavior type over a composite pattern's apex: behaviors
whose two marginals are behaviors — span composition of behavior
subtypes. -/
def WBehavior.glue (U : ι → Set T) (B₁ : WBehavior U (Pat.Tot M))
    (B₂ : WBehavior U (Pat.Tot N)) : WBehavior U (Pat.Tot (Pat.comp M N)) :=
  (B₁.pull (Pat.compFst M N)).inter (B₂.pull (Pat.compSnd M N))

/-- **The compositor on indicators is span composition**: `⊞` of two
indicator penalties is the indicator of the pullback-intersection over
the glued apex. -/
theorem boxplusW_indPen {W : Set T} (S₁ : Set (Traj W (Pat.Tot M)))
    (S₂ : Set (Traj W (Pat.Tot N))) :
    boxplusW (indPen S₁) (indPen S₂) =
      indPen (trajMap (Pat.compFst M N) ⁻¹' S₁ ∩ trajMap (Pat.compSnd M N) ⁻¹' S₂) := by
  funext ν
  rw [boxplusW_apply,
    show indPen S₁ (ν.push (trajMap (Pat.compFst M N)))
        = indPen (trajMap (Pat.compFst M N) ⁻¹' S₁) ν from
      congrFun (pull_indPen _ _) ν,
    show indPen S₂ (ν.push (trajMap (Pat.compSnd M N)))
        = indPen (trajMap (Pat.compSnd M N) ⁻¹' S₂) ν from
      congrFun (pull_indPen _ _) ν,
    indPen_add_indPen_apply]

/-- **The lax class inclusion**: the spec of the glued behavior type
sits inside the composed spec classes (the same-window composites);
the compositor's extra mixed-window composites are the laxity. -/
theorem cplOfBehavior_glue_subset_wComp (U : ι → Set T)
    (B₁ : WBehavior U (Pat.Tot M)) (B₂ : WBehavior U (Pat.Tot N)) (j : ι) :
    (cplOfBehavior U (B₁.glue U B₂)).1 j ⊆
      (wComp U (cplOfBehavior U B₁) (cplOfBehavior U B₂)).1 j := by
  rintro _ ⟨i, hij, rfl⟩
  refine ⟨penExt hij (indPen (B₁.cls i)), ⟨i, hij, rfl⟩,
    penExt hij (indPen (B₂.cls i)), ⟨i, hij, rfl⟩, ?_⟩
  rw [← penExt_boxplusW, boxplusW_indPen]
  rfl

/-- **The laxity is semantically silent**: a joint satisfies the
composed spec classes iff its support lies in the glued behavior type
— the mixed-window composites decide nothing the same-window ones do
not (a sum in `ℝ≥0∞` vanishes iff both summands do, and each summand
is a clip-demand the glue already carries). -/
theorem satAt_wComp_iff_glue (U : ι → Set T)
    (B₁ : WBehavior U (Pat.Tot M)) (B₂ : WBehavior U (Pat.Tot N)) (j : ι)
    (ν : Joint (Traj (U j) (Pat.Tot (Pat.comp M N)))) :
    SatAt ν ((wComp U (cplOfBehavior U B₁) (cplOfBehavior U B₂)).1 j) ↔
      (↑ν.wt.support : Set (Traj (U j) (Pat.Tot (Pat.comp M N)))) ⊆
        (B₁.glue U B₂).cls j := by
  constructor
  · intro h
    rw [← satAt_specOfBehavior_iff]
    exact SatAt.anti (cplOfBehavior_glue_subset_wComp U B₁ B₂ j) h
  · intro hsup
    rintro _ ⟨_, ⟨i₁, hi₁, rfl⟩, _, ⟨i₂, hi₂, rfl⟩, rfl⟩
    have hglue := (satAt_specOfBehavior_iff U (B₁.glue U B₂) j ν).mpr hsup
    have h₁ := hglue _ ⟨i₁, hi₁, rfl⟩
    have h₂ := hglue _ ⟨i₂, hi₂, rfl⟩
    rw [show penExt hi₁ (indPen ((B₁.glue U B₂).cls i₁))
        = indPen (trajRes hi₁ ⁻¹' ((B₁.glue U B₂).cls i₁)) from pull_indPen _ _,
      indPen_eq_zero_iff] at h₁
    rw [show penExt hi₂ (indPen ((B₁.glue U B₂).cls i₂))
        = indPen (trajRes hi₂ ⁻¹' ((B₁.glue U B₂).cls i₂)) from pull_indPen _ _,
      indPen_eq_zero_iff] at h₂
    rw [boxplusW_apply]
    rw [show penExt hi₁ (indPen (B₁.cls i₁)) (ν.push (trajMap (Pat.compFst M N)))
        = indPen (trajRes hi₁ ⁻¹' (trajMap (Pat.compFst M N) ⁻¹' B₁.cls i₁)) ν from by
      rw [show penExt hi₁ (indPen (B₁.cls i₁))
          = indPen (trajRes hi₁ ⁻¹' B₁.cls i₁) from pull_indPen _ _]
      exact congrFun (pull_indPen (trajMap (Pat.compFst M N)) _) ν]
    rw [show penExt hi₂ (indPen (B₂.cls i₂)) (ν.push (trajMap (Pat.compSnd M N)))
        = indPen (trajRes hi₂ ⁻¹' (trajMap (Pat.compSnd M N) ⁻¹' B₂.cls i₂)) ν from by
      rw [show penExt hi₂ (indPen (B₂.cls i₂))
          = indPen (trajRes hi₂ ⁻¹' B₂.cls i₂) from pull_indPen _ _]
      exact congrFun (pull_indPen (trajMap (Pat.compSnd M N)) _) ν]
    rw [indPen_apply_of_subset
        (S := trajRes hi₁ ⁻¹' (trajMap (Pat.compFst M N) ⁻¹' B₁.cls i₁))
        (fun x hx => (h₁ hx).1),
      indPen_apply_of_subset
        (S := trajRes hi₂ ⁻¹' (trajMap (Pat.compSnd M N) ⁻¹' B₂.cls i₂))
        (fun x hx => (h₂ hx).2), add_zero]

end

end Site

end SuFunctor
