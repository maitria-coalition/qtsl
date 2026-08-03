import SuFunctor.Site.FellAcceptance

/-! # Battery spec classes over the Fell carrier: walls, marks, persistence

The rung-4 transport: the safety / deadline /
until acceptance classes restated over the record carrier `FTraj`, as
window-indexed families of penalty classes with their persistence
instances — conclusions stated per window with the
persistence package — plus a strengthening at the seam.

The architecture transposes `SuFunctor.Site.BehaviorSpec` from the
exact stratum (`Joint`/`Pen` over the function carrier) to the general
stratum (`MeasJoint`/`MeasPen` over the Fell carrier), and the
measurability tickets that transposition costs are exactly what the
measurability leg (`SuFunctor.Site.FellAcceptance`) issues:

* **`indPenM`** — the subprobability indicator penalty of a class:
  permitted outright iff the joint's mass avoids the class's
  complement.  Its transport law `pull_indPenM` consumes measurability
  of the class and of the map — at the general stratum, the indicator
  calculus is admissible only for Borel classes, which is why the
  acceptance events' Effros measurability is the admission ticket.
* **`clipDemandsF`** — the clip-demand family of an arbitrary
  per-window base penalty, with `isPersistentMF_clipDemandsF`:
  persistence by window-calculus transitivity alone
  (`penExtMF_penExtMF`; openness of the site's windows is the only
  hypothesis).  This is the generic engine behind every battery
  family's persistence, wall and mark face alike.
* **`acceptanceSpecF`** — the spec family of a per-window acceptance
  event (deadline, until, Streett: the ∃-face **marks**).  Persistent,
  with the forward judgment lemma (`satAtM_acceptanceSpecF_ae`):
  satisfaction forces almost-sure acceptance at the window.  The
  backward direction is *deliberately absent*: liveness events do not
  clip-restrict (a record reaching its goal only in the superwindow is
  lost to the subwindow), so subwindow demands are genuinely stronger
  — a subwindow's reach demand is a deadline, and extension is exactly
  how a met deadline persists to every superwindow.  Where the graded
  face of these marks lives is the A3 leg's business, not this
  module's.
* **`WBehaviorF` / `specOfBehaviorF`** — the ∀-face **walls**:
  fellClip-closed record-class families (the Fell subpresheaf
  structure), whose specs get the full judgment bridge
  (`satAtM_specOfBehaviorF_iff`): satisfaction *equals* almost-sure
  membership, the backward direction consuming the subpresheaf
  condition, clip measurability (openness of the site's windows), and
  class measurability (A8), exactly once each.  `safetyBehaviorF` is
  the instance: per-window confinement to a safe region's cylinder,
  restriction unconditional in the region.
* **A5, the strengthening** (`graphCl_mem_confinedEvent_iff`): on the
  record carrier the wall reads the *whole* closed graph — record
  confinement of `graphCl f` to a closed wall is pointwise confinement
  of `f` at every stage, unconditional in `f`.  The skeleton route's
  segment-constancy side condition ("mid-segment visits are
  chain-invisible") is absent by construction: there is no side
  condition to delete because the carrier never introduced it, and
  jump-closure points cost nothing against a closed wall.

Horizon typing note (the memo's rung-4 rider): the deadline and until
grids of `SuFunctor.Site.FellAcceptance` are indexed by bare naturals;
at clocked continuum strata their legs are duration-typed stage cuts,
and the tick-indexed reading of `SpecPathLens` ("the horizon of a
windowed former is a natural number" — a forcing of the finitary
record site, not of the grammar) re-types to rational durations
exactly there.  This module inherits that note; it owes no theorem for
it.

Axiom probes at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx. -/

namespace SuFunctor

namespace Site

noncomputable section

open SuFunctor.Plain SuFunctor.Universe MeasureTheory
open scoped ENNReal

universe u

/-! ## The subprobability indicator penalty -/

variable {K L : Type u} [MeasurableSpace K] [MeasurableSpace L]

/-- The indicator penalty of a class at the general stratum: permitted
outright iff the joint's mass avoids the class's complement, forbidden
outright otherwise.  Total in the class (mathlib's outer-measure
evaluation); its transport law below is where measurability binds. -/
def indPenM (S : Set K) : MeasPen K := fun μ =>
  @ite _ ((μ.1 : Measure K) Sᶜ = 0) (Classical.dec _) 0 ⊤

theorem indPenM_apply_of_null {S : Set K} {μ : MeasJoint K}
    (h : (μ.1 : Measure K) Sᶜ = 0) : indPenM S μ = 0 := by
  simp [indPenM, h]

theorem indPenM_apply_of_ne_null {S : Set K} {μ : MeasJoint K}
    (h : (μ.1 : Measure K) Sᶜ ≠ 0) : indPenM S μ = ⊤ := by
  simp [indPenM, h]

theorem indPenM_eq_zero_iff {S : Set K} {μ : MeasJoint K} :
    indPenM S μ = 0 ↔ (μ.1 : Measure K) Sᶜ = 0 := by
  by_cases h : (μ.1 : Measure K) Sᶜ = 0 <;>
    simp [indPenM, h]

/-- **Transport of the indicator along a measurable map is the
indicator of the preimage** — the general-stratum form of
`pull_indPen`, with the two measurability hypotheses that stratum
charges: the map's, and the class's.  The latter is the A8 admission
ticket: only Borel acceptance events enter the indicator calculus. -/
theorem pull_indPenM (h : K → L) (hm : Measurable h) {S : Set L}
    (hS : MeasurableSet S) :
    MeasPen.pull h (indPenM S) = indPenM (h ⁻¹' S) := by
  funext μ
  have hmap : ((μ.push h).1 : Measure L) Sᶜ
      = (μ.1 : Measure K) (h ⁻¹' S)ᶜ := by
    rw [MeasJoint.push_toMeasure,
      Measure.map_apply hm hS.compl, Set.preimage_compl]
  rw [MeasPen.pull_apply]
  by_cases h0 : (μ.1 : Measure K) (h ⁻¹' S)ᶜ = 0
  · rw [indPenM_apply_of_null (hmap.trans h0), indPenM_apply_of_null h0]
  · rw [indPenM_apply_of_ne_null (fun hc => h0 (hmap.symm.trans hc)),
      indPenM_apply_of_ne_null h0]

/-- Componentwise satisfaction of a penalty class at the general
stratum: every member vanishes on the joint. -/
abbrev SatAtM (μ : MeasJoint K) (Φ : Set (MeasPen K)) : Prop :=
  ∀ p ∈ Φ, p μ = 0

/-! ## Clip demands over the Fell carrier: the persistence engine -/

variable {T ι : Type u} [TopologicalSpace T] {X : Type u}
  [TopologicalSpace X]

/-- The clip-demand family of a per-window base penalty: at each
window, all extensions of subwindow bases.  The generic engine behind
every battery family's persistence — walls and marks instantiate the
same shape. -/
def clipDemandsF (U : ι → Set T)
    (base : ∀ i, MeasPen (FTraj (U i) X)) (j : ι) :
    Set (MeasPen (FTraj (U j) X)) :=
  {p | ∃ i, ∃ hij : U i ⊆ U j, p = penExtMF hij (base i)}

/-- The window's own base is a member: the reflexive clip-demand. -/
theorem base_mem_clipDemandsF (U : ι → Set T)
    (base : ∀ i, MeasPen (FTraj (U i) X)) (j : ι) :
    base j ∈ clipDemandsF U base j :=
  ⟨j, Set.Subset.rfl, (penExtMF_refl _).symm⟩

/-- **Persistence of clip demands**: window-calculus transitivity
alone (`penExtMF_penExtMF`), with openness of the site's windows as
the only hypothesis.  No condition on the bases whatsoever. -/
theorem isPersistentMF_clipDemandsF (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i))
    (base : ∀ i, MeasPen (FTraj (U i) X)) :
    IsPersistentMF U (clipDemandsF U base) := by
  intro j k hjk
  rintro _ ⟨_, ⟨i, hij, rfl⟩, rfl⟩
  exact ⟨i, hij.trans hjk,
    penExtMF_penExtMF hij hjk (hU i) (hU j) (base i)⟩

/-! ## Marks: acceptance-event spec families (the ∃-face) -/

/-- The spec family of a per-window acceptance event (deadline, until,
Streett): clip demands of the events' indicators. -/
def acceptanceSpecF (U : ι → Set T)
    (E : ∀ i, Set (FTraj (U i) X)) (j : ι) :
    Set (MeasPen (FTraj (U j) X)) :=
  clipDemandsF U (fun i => indPenM (E i)) j

theorem isPersistentMF_acceptanceSpecF (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) (E : ∀ i, Set (FTraj (U i) X)) :
    IsPersistentMF U (acceptanceSpecF U E) :=
  isPersistentMF_clipDemandsF U hU _

/-- The forward judgment: satisfying an acceptance spec at a window
forces almost-sure acceptance there.  The backward direction is
deliberately absent — liveness events do not clip-restrict, so
subwindow demands are genuinely stronger (a reach demand within a
subwindow is a deadline); the module docstring carries the reading. -/
theorem satAtM_acceptanceSpecF_ae (U : ι → Set T)
    (E : ∀ i, Set (FTraj (U i) X)) (j : ι)
    {μ : MeasJoint (FTraj (U j) X)}
    (h : SatAtM μ (acceptanceSpecF U E j)) :
    (μ.1 : Measure (FTraj (U j) X)) (E j)ᶜ = 0 :=
  indPenM_eq_zero_iff.mp (h _ (base_mem_clipDemandsF U _ j))

/-! ## Walls: behavior subtypes over the Fell carrier (the ∀-face) -/

/-- A behavior subtype over the Fell carrier: per-window record
classes, closed under clipping — the record-carrier form of
`SuFunctor.Site.BehaviorSpec`'s `WBehavior`. -/
structure WBehaviorF (U : ι → Set T) (X : Type u)
    [TopologicalSpace X] : Type u where
  /-- The record class at each window. -/
  cls : ∀ i, Set (FTraj (U i) X)
  /-- Classes clip to classes: the subpresheaf condition. -/
  restrict : ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j),
    fellClip hij '' cls j ⊆ cls i

/-- The spec of a Fell behavior subtype: the acceptance-spec family of
its classes.  Wall polarity earns the full judgment bridge below. -/
def specOfBehaviorF (U : ι → Set T) (B : WBehaviorF U X) :
    ∀ j, Set (MeasPen (FTraj (U j) X)) :=
  acceptanceSpecF U B.cls

theorem isPersistentMF_specOfBehaviorF (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) (B : WBehaviorF U X) :
    IsPersistentMF U (specOfBehaviorF U B) :=
  isPersistentMF_acceptanceSpecF U hU B.cls

/-- **The judgment bridge at the general stratum**: a joint satisfies
the spec of a Fell behavior subtype at a window iff its mass lies in
the class there.  Forward consumes the reflexive demand; backward
consumes the subpresheaf condition, clip measurability (openness of
the site's windows), and class measurability (the A8 ticket) — each
exactly once. -/
theorem satAtM_specOfBehaviorF_iff (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) (B : WBehaviorF U X)
    (hB : ∀ i, MeasurableSet (B.cls i)) (j : ι)
    (μ : MeasJoint (FTraj (U j) X)) :
    SatAtM μ (specOfBehaviorF U B j) ↔
      (μ.1 : Measure (FTraj (U j) X)) (B.cls j)ᶜ = 0 := by
  constructor
  · intro h
    exact indPenM_eq_zero_iff.mp (h _ (base_mem_clipDemandsF U _ j))
  · rintro hnull p ⟨i, hij, rfl⟩
    rw [penExtMF_apply]
    refine indPenM_apply_of_null ?_
    rw [MeasJoint.push_toMeasure,
      Measure.map_apply (measurable_fellClip hij (hU i)) (hB i).compl]
    refine measure_mono_null (fun F hF => ?_) hnull
    intro hFj
    exact hF (B.restrict hij ⟨F, hFj, rfl⟩)

/-! ## The safety wall -/

/-- The safety behavior subtype: per-window confinement to the safe
region's cylinder.  Restriction is unconditional in the region —
clipping only removes stage–state pairs. -/
def safetyBehaviorF (U : ι → Set T) (D : Set X) : WBehaviorF U X where
  cls i := confinedEvent ((Set.univ : Set ↥(U i)) ×ˢ D)
  restrict := by
    intro i j hij
    rintro _ ⟨F, hF, rfl⟩
    intro p hp
    have hmem : inclT hij X p ∈ (F : Set (↥(U j) × X)) := hp
    exact ⟨Set.mem_univ _, (hF hmem).2⟩

/-- The safety wall's judgment bridge, with its measurability paid by
A8: for a closed safe region, satisfaction of the safety spec at a
window is almost-sure confinement there — the SU-general form of the
safety battery's acceptance reading, with the measurability pack
discharged by the topology of the site. -/
theorem satAtM_safetySpecF_iff (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {D : Set X} (hD : IsClosed D) (j : ι)
    (μ : MeasJoint (FTraj (U j) X)) :
    SatAtM μ (specOfBehaviorF U (safetyBehaviorF U D) j) ↔
      (μ.1 : Measure (FTraj (U j) X))
        (confinedEvent ((Set.univ : Set ↥(U j)) ×ˢ D))ᶜ = 0 :=
  satAtM_specOfBehaviorF_iff U hU (safetyBehaviorF U D)
    (fun _ => measurableSet_confinedEvent_cylinder hD) j μ

/-! ## A4 core: the compositor on wall demands is the glued wall demand -/

variable {Z U' V' : Type u} [TopologicalSpace Z] [TopologicalSpace U']
  [TopologicalSpace V']

/-- **The record-carrier composition seam on indicators** (the
general-stratum sibling of `boxplusW_indPen`): the window compositor
of two wall demands is the wall demand of the glued record class —
the pullback intersection along the two state transports.  Properness
feeds the transports' measurability, and the classes' measurability
is the A8 ticket again.  This is the A4 transport core: composing
wall specs along the compositor never leaves the wall fragment, so
the composed conclusion is again a per-window class demand, and
persistence survives by `IsPersistentMF.image2_mboxplusWF`.  The
per-profile grid cells of the wire-composition rule (ODE, sampled
data, gauge-form feedback) are drift-assembly content at the
presentation profiles, deliberately not restated here. -/
theorem mboxplusWF_indPenM {W : Set T} {π₁ : Z → U'} {π₂ : Z → V'}
    (hp₁ : IsProperMap π₁) (hp₂ : IsProperMap π₂)
    {S₁ : Set (FTraj W U')} {S₂ : Set (FTraj W V')}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) :
    mboxplusWF π₁ π₂ (indPenM S₁) (indPenM S₂)
      = indPenM (fellMap (W := W) π₁ ⁻¹' S₁ ∩
          fellMap (W := W) π₂ ⁻¹' S₂) := by
  funext ν
  rw [mboxplusWF_apply]
  have h₁ : ((ν.push (fellMap (W := W) π₁)).1 : Measure (FTraj W U')) S₁ᶜ
      = (ν.1 : Measure (FTraj W Z)) (fellMap (W := W) π₁ ⁻¹' S₁)ᶜ := by
    rw [MeasJoint.push_toMeasure,
      Measure.map_apply (measurable_fellMap hp₁) hS₁.compl,
      Set.preimage_compl]
  have h₂ : ((ν.push (fellMap (W := W) π₂)).1 : Measure (FTraj W V')) S₂ᶜ
      = (ν.1 : Measure (FTraj W Z)) (fellMap (W := W) π₂ ⁻¹' S₂)ᶜ := by
    rw [MeasJoint.push_toMeasure,
      Measure.map_apply (measurable_fellMap hp₂) hS₂.compl,
      Set.preimage_compl]
  have hcompl : (fellMap (W := W) π₁ ⁻¹' S₁ ∩
      fellMap (W := W) π₂ ⁻¹' S₂)ᶜ
      = (fellMap (W := W) π₁ ⁻¹' S₁)ᶜ ∪
        (fellMap (W := W) π₂ ⁻¹' S₂)ᶜ := Set.compl_inter _ _
  by_cases hz₁ : (ν.1 : Measure (FTraj W Z))
      (fellMap (W := W) π₁ ⁻¹' S₁)ᶜ = 0
  · by_cases hz₂ : (ν.1 : Measure (FTraj W Z))
        (fellMap (W := W) π₂ ⁻¹' S₂)ᶜ = 0
    · have hI : (ν.1 : Measure (FTraj W Z)) (fellMap (W := W) π₁ ⁻¹' S₁ ∩
          fellMap (W := W) π₂ ⁻¹' S₂)ᶜ = 0 := by
        rw [hcompl]; exact measure_union_null hz₁ hz₂
      rw [indPenM_apply_of_null (h₁.trans hz₁),
        indPenM_apply_of_null (h₂.trans hz₂),
        indPenM_apply_of_null hI, zero_add]
    · have hI : (ν.1 : Measure (FTraj W Z)) (fellMap (W := W) π₁ ⁻¹' S₁ ∩
          fellMap (W := W) π₂ ⁻¹' S₂)ᶜ ≠ 0 := by
        rw [hcompl]
        exact fun hc =>
          hz₂ (measure_mono_null Set.subset_union_right hc)
      rw [indPenM_apply_of_null (h₁.trans hz₁),
        indPenM_apply_of_ne_null (fun hc => hz₂ (h₂.symm.trans hc)),
        indPenM_apply_of_ne_null hI, zero_add]
  · have hI : (ν.1 : Measure (FTraj W Z)) (fellMap (W := W) π₁ ⁻¹' S₁ ∩
        fellMap (W := W) π₂ ⁻¹' S₂)ᶜ ≠ 0 := by
      rw [hcompl]
      exact fun hc => hz₁ (measure_mono_null Set.subset_union_left hc)
    rw [indPenM_apply_of_ne_null (fun hc => hz₁ (h₁.symm.trans hc)),
      indPenM_apply_of_ne_null hI]
    simp

/-! ## A5: the record wall reads the whole graph -/

variable {W : Set T}

/-- **The A5 strengthening**: record confinement of a trajectory's
closed-up graph to a closed wall is pointwise confinement at every
stage — unconditional in the trajectory.  The skeleton route's
segment-constancy side condition is absent by construction: the record
constrains every `(t, x)` of the closed graph, mid-segment stages
included, and the closure completion costs nothing against a closed
wall. -/
theorem graphCl_mem_confinedEvent_iff {D : Set X} (hD : IsClosed D)
    (f : Traj W X) :
    graphCl f ∈ confinedEvent ((Set.univ : Set ↥W) ×ˢ D) ↔
      ∀ w, f w ∈ D := by
  constructor
  · intro h w
    have hg : (w, f w) ∈ (graphCl f : Set (↥W × X)) :=
      subset_closure rfl
    exact (h hg).2
  · intro h
    rw [mem_confinedEvent_iff, coe_graphCl]
    refine closure_minimal ?_ (isClosed_univ.prod hD)
    rintro ⟨w, x⟩ hx
    have hx' : x = f w := hx
    subst hx'
    exact ⟨Set.mem_univ _, h w⟩

end

end Site

end SuFunctor

#print axioms SuFunctor.Site.pull_indPenM
#print axioms SuFunctor.Site.isPersistentMF_clipDemandsF
#print axioms SuFunctor.Site.isPersistentMF_acceptanceSpecF
#print axioms SuFunctor.Site.satAtM_acceptanceSpecF_ae
#print axioms SuFunctor.Site.satAtM_specOfBehaviorF_iff
#print axioms SuFunctor.Site.satAtM_safetySpecF_iff
#print axioms SuFunctor.Site.mboxplusWF_indPenM
#print axioms SuFunctor.Site.graphCl_mem_confinedEvent_iff
