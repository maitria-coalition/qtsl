import SuFunctor.Site.GeneralWindow
import SuFunctor.Universe.FellMeasurable
import SuFunctor.Universe.FellRestrict

/-! # Window carriers over the Fell hyperspace

The general-stratum window assembly of `SuFunctor.Site.GeneralWindow`,
restated over the record carrier: the trajectory carrier over a window
`W` is the **Fell hyperspace of closed subsets** of `↥W × X`
(`FTraj W X := FellCloseds (↥W × X)`), not the function space
`Traj W X = ↥W → X`.  Records are closed relations; functions enter
through the seam below.  The measurable structure is Borel-on-Fell (the
Effros structure of `SuFunctor.Universe.FellMeasurable`), under which
every carrier map's measurability is *derived from Fell continuity* —
the constitutive measurability hypotheses of the general stratum are
discharged by the topology of the site rather than assumed:

* **clipping** (`fellClip`) is preimage along the window inclusion
  `inclT` — the window form of `FellDescent.clipLE`.  It preserves
  closedness unconditionally, satisfies the presheaf laws
  (`fellClip_refl`, `fellClip_fellClip`) strictly at the carrier level
  with no hypotheses, and is Fell-continuous (hence Borel-measurable)
  as soon as the subwindow is open — the site's windows are open, so
  this is uniform there.
* **state transport** (`fellMap`) is closure-completed pushforward
  along `Prod.map id h` — total, like `MeasJoint.push`, with its laws
  carrying the hypotheses where the stratum binds: under a *proper*
  state map the closure completion vanishes
  (`coe_fellMap_of_isProperMap`) and the transport is Fell-continuous
  by the pushforward rung of `SuFunctor.Universe.FellRestrict`.
* the **window-extension calculus** replays: `penExtMF`, its presheaf
  laws, the state–window exchange (`penExtMF_pull_fellMap`), the
  window–compositor exchange (`penExtMF_mboxplusWF`), the unit, and
  the persistent/matching class vocabulary with its closure package.
* **the seam**: functions embed as records via
  `graphCl := closure ∘ graph`.  The closure completion is not
  optional: a jump trajectory does not have a closed graph *qua
  function* and must be upgraded to a relation to close (the witness
  module `SuFunctor.Site.FellWindowWitness` computes a jump's closure
  exactly: the two one-sided limit points are adjoined and nothing
  else — no vertical segment).  On the continuous class the completion
  vanishes (`coe_graphCl_of_continuous` — a lemma, not an assumption),
  in particular on discrete stage spaces, where the seam is injective
  (`graphCl_injective_of_discrete`); in general it is deliberately
  not injective (two functions differing only at a jump stage close to
  the same relation — the quotient the record reading wants; witness
  in the same module).  Single-valued total closed relations are
  exactly the seam's image (`graphCl_surjective_onto_functional`).
  Window extension commutes with the seam (`fellClip_graphCl` at the
  carrier level — where the openness of the subwindow is load-bearing:
  the witness module refutes the closed-window form — and
  `penExtMF_graphCl` at the penalty level, exhibiting the
  function-carrier `penExtM` as the restriction of this assembly along
  the seam).

One asymmetry is recorded rather than repaired: at the penalty level
the seam compatibility carries `Measurable graphCl` as an explicit
hypothesis.  Over uncountable stage spaces the product σ-algebra of
`Traj W X` is too coarse for the seam (graph-hitting events are the
classical non-measurable projection class), so an unconditional claim
would be wrong; discrete stages discharge the hypothesis, and the
sharper positive statements are left as owed work.

A closed record's stage-slices vary outer-semicontinuously for free —
that is just closedness read fibrewise; Fell continuity of slice
assignments adds exactly the lower (hit-face) half.  The dictionary
between Fell continuity of slice maps and the correspondence
literature's hemicontinuity vocabulary is deliberately not formalized
here.
-/

namespace SuFunctor

namespace Site

noncomputable section

open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

attribute [local instance] SuFunctor.Universe.fell

universe u

variable {T : Type u}

/-! ## The window inclusion (no topology yet) -/

/-- The window inclusion on stage–state pairs: include the stage,
leave the state. -/
def inclT {V W : Set T} (hVW : V ⊆ W) (X : Type u) : ↥V × X → ↥W × X :=
  Prod.map (Set.inclusion hVW) id

@[simp] theorem inclT_apply {V W : Set T} (hVW : V ⊆ W) {X : Type u}
    (p : ↥V × X) : inclT hVW X p = (Set.inclusion hVW p.1, p.2) := rfl

/-- The reflexive window inclusion is the identity. -/
theorem inclT_rfl (W : Set T) (X : Type u) :
    inclT (Set.Subset.rfl : W ⊆ W) X = id := by
  rw [inclT, Set.inclusion_eq_id]
  funext p
  rfl

/-- Window inclusions compose. -/
theorem inclT_comp_inclT {U V W : Set T} (hUV : U ⊆ V) (hVW : V ⊆ W)
    {X : Type u} : inclT hVW X ∘ inclT hUV X = inclT (hUV.trans hVW) X :=
  funext fun _ => rfl

/-- The bare exchange of preimage-along-inclusion with
pushforward-along-a-state-map: the two act on different factors.  Pure
set algebra — no topology, no properness, no openness. -/
theorem preimage_inclT_image_prodMap {V W : Set T} (hVW : V ⊆ W)
    {X Y : Type u} (h : X → Y) (s : Set (↥W × X)) :
    inclT hVW Y ⁻¹' (Prod.map id h '' s)
      = Prod.map id h '' (inclT hVW X ⁻¹' s) := by
  ext ⟨v, y⟩
  constructor
  · rintro ⟨⟨w, x⟩, hs, heq⟩
    have hw : w = Set.inclusion hVW v := congrArg Prod.fst heq
    have hy : h x = y := congrArg Prod.snd heq
    subst hw
    exact ⟨(v, x), hs, by rw [← hy]; rfl⟩
  · rintro ⟨⟨v', x⟩, hs, heq⟩
    have hv : v' = v := congrArg Prod.fst heq
    have hy : h x = y := congrArg Prod.snd heq
    subst hv
    exact ⟨(Set.inclusion hVW v', x), hs, by rw [← hy]; rfl⟩

/-! ## Topology enters: the carrier and the continuity rungs -/

variable [TopologicalSpace T]

/-- The inclusion of an *open* subwindow is an open map of stage
subtypes. -/
theorem isOpenMap_inclusion {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V) :
    IsOpenMap (Set.inclusion hVW) := by
  intro S hS
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hS
  have h : Set.inclusion hVW '' ((↑) ⁻¹' O) = (↑) ⁻¹' (O ∩ V) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, v.2⟩
    · rintro ⟨hwO, hwV⟩
      exact ⟨⟨↑w, hwV⟩, hwO, Subtype.ext rfl⟩
  rw [h]
  exact (hO.inter hV).preimage continuous_subtype_val

/-- The Fell trajectory carrier over a window: closed subsets of
stage × state, with the Fell topology and its Borel structure.  The
record carrier of the semantic universe's carrier section, in window
form. -/
abbrev FTraj (W : Set T) (X : Type u) [TopologicalSpace X] : Type u :=
  FellCloseds (↥W × X)

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_inclT {V W : Set T} (hVW : V ⊆ W) :
    Continuous (inclT hVW X) :=
  (continuous_inclusion hVW).prodMap continuous_id

/-- The window inclusion of an open subwindow is an open map. -/
theorem isOpenMap_inclT {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V) :
    IsOpenMap (inclT hVW X) :=
  (isOpenMap_inclusion hVW hV).prodMap IsOpenMap.id

/-- Preimage along the window inclusion of an open subwindow commutes
with closure — the inclusion is a continuous open map.  This single
exchange is what makes both the state-transport square and the seam
square close; its openness hypothesis is load-bearing
(`SuFunctor.Site.FellWindowWitness` refutes the closed-window form). -/
theorem preimage_inclT_closure {V W : Set T} (hVW : V ⊆ W)
    (hV : IsOpen V) (s : Set (↥W × X)) :
    inclT hVW X ⁻¹' closure s = closure (inclT hVW X ⁻¹' s) :=
  (isOpenMap_inclT hVW hV).preimage_closure_eq_closure_preimage
    (continuous_inclT hVW) s

/-! ## Clipping: the carrier presheaf -/

/-- Clip a record over a window to a subwindow: preimage along the
window inclusion.  The window form of `FellDescent.clipLE`.
Closedness needs only continuity of the inclusion — clipping is total
on records over arbitrary subwindows; openness enters with
Fell-continuity below. -/
def fellClip {V W : Set T} (hVW : V ⊆ W) (F : FTraj W X) : FTraj V X :=
  ⟨inclT hVW X ⁻¹' (F : Set (↥W × X)),
    F.isClosed.preimage (continuous_inclT hVW)⟩

@[simp] theorem coe_fellClip {V W : Set T} (hVW : V ⊆ W) (F : FTraj W X) :
    (fellClip hVW F : Set (↥V × X)) = inclT hVW X ⁻¹' (F : Set (↥W × X)) :=
  rfl

@[simp] theorem mem_fellClip {V W : Set T} {hVW : V ⊆ W} {F : FTraj W X}
    {p : ↥V × X} : p ∈ fellClip hVW F ↔ inclT hVW X p ∈ F := Iff.rfl

/-- Clipping along the reflexive inclusion is the identity: the
presheaf identity law, strict, no hypotheses. -/
theorem fellClip_refl {W : Set T} (F : FTraj W X) :
    fellClip (Set.Subset.rfl : W ⊆ W) F = F := by
  ext1
  rw [coe_fellClip, inclT_rfl, Set.preimage_id]

/-- Clipping is transitive: the presheaf composition law, strict, no
hypotheses — preimage is functorial on the nose. -/
theorem fellClip_fellClip {U V W : Set T} (hUV : U ⊆ V) (hVW : V ⊆ W)
    (F : FTraj W X) :
    fellClip hUV (fellClip hVW F) = fellClip (hUV.trans hVW) F := by
  ext1
  rw [coe_fellClip, coe_fellClip, coe_fellClip, ← Set.preimage_comp,
    inclT_comp_inclT]

/-- **Clipping to an open subwindow is Fell-continuous**: the preimage
rung of `SuFunctor.Universe.FellMeasurable`, transported along the
closed-sets embedding. -/
theorem continuous_fellClip {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V) :
    Continuous (fellClip (X := X) hVW) :=
  FellCloseds.isEmbedding_coe.isInducing.continuous_iff.mpr
    ((fell.continuous_preimage (continuous_inclT hVW)
      (isOpenMap_inclT hVW hV)).comp FellCloseds.continuous_coe)

/-- Clipping to an open subwindow is Borel-measurable: continuity
suffices, under the Effros Borel structure. -/
theorem measurable_fellClip {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V) :
    Measurable (fellClip (X := X) hVW) :=
  (continuous_fellClip hVW hV).measurable

/-! ## State transport, closure-completed -/

/-- Transport a record along a state map: pushforward the relation and
close.  Total, like `MeasJoint.push` — the closure completion is the
price of totality, and it vanishes exactly where the transport is
proper (`coe_fellMap_of_isProperMap`), which is where the laws below
bind. -/
def fellMap {W : Set T} (h : X → Y) (F : FTraj W X) : FTraj W Y :=
  ⟨closure (Prod.map id h '' (F : Set (↥W × X))), isClosed_closure⟩

@[simp] theorem coe_fellMap {W : Set T} (h : X → Y) (F : FTraj W X) :
    (fellMap h F : Set (↥W × Y)) =
      closure (Prod.map id h '' (F : Set (↥W × X))) := rfl

/-- Under a proper state map the closure completion vanishes: proper
maps are closed maps, and `Prod.map id h` is proper with `h`. -/
theorem coe_fellMap_of_isProperMap {W : Set T} {h : X → Y}
    (hp : IsProperMap h) (F : FTraj W X) :
    (fellMap h F : Set (↥W × Y)) = Prod.map id h '' (F : Set (↥W × X)) :=
  ((isProperMap_id.prodMap hp).isClosedMap _ F.isClosed).closure_eq

/-- **State transport along a proper map is Fell-continuous**: the
pushforward rung of `SuFunctor.Universe.FellRestrict`, transported
along the closed-sets embedding. -/
theorem continuous_fellMap {W : Set T} {h : X → Y} (hp : IsProperMap h) :
    Continuous (fellMap (W := W) h) := by
  refine FellCloseds.isEmbedding_coe.isInducing.continuous_iff.mpr ?_
  have hfun : ((↑) ∘ fellMap (W := W) h : FTraj W X → Set (↥W × Y)) =
      Set.image (Prod.map id h) ∘ (↑) :=
    funext fun F => coe_fellMap_of_isProperMap hp F
  rw [hfun]
  exact (fell.continuous_image_of_isProperMap
    (isProperMap_id.prodMap hp)).comp FellCloseds.continuous_coe

/-- State transport along a proper map is Borel-measurable. -/
theorem measurable_fellMap {W : Set T} {h : X → Y} (hp : IsProperMap h) :
    Measurable (fellMap (W := W) h) :=
  (continuous_fellMap hp).measurable

/-- **The state–window exchange square, carrier level**: clipping to an
open subwindow commutes with (closure-completed) state transport.
Openness alone — no properness: the closure completion passes through
the clip because preimage along a continuous open map commutes with
closure. -/
theorem fellClip_fellMap {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V)
    (h : X → Y) (F : FTraj W X) :
    fellClip hVW (fellMap h F) = fellMap h (fellClip hVW F) := by
  ext1
  rw [coe_fellClip, coe_fellMap, coe_fellMap, coe_fellClip,
    preimage_inclT_closure hVW hV, preimage_inclT_image_prodMap]

/-! ## Window extension of penalties over the Fell carrier -/

/-- Read a subwindow penalty over a superwindow at the Fell carrier:
evaluate on the clip.  Extension, not restriction, exactly as at the
function carrier. -/
def penExtMF {V W : Set T} (hVW : V ⊆ W) :
    MeasPen (FTraj V X) → MeasPen (FTraj W X) :=
  MeasPen.pull (fellClip hVW)

@[simp] theorem penExtMF_apply {V W : Set T} (hVW : V ⊆ W)
    (F : MeasPen (FTraj V X)) (μ : MeasJoint (FTraj W X)) :
    penExtMF hVW F μ = F (μ.push (fellClip hVW)) := rfl

/-- Extension along the reflexive inclusion is the identity. -/
theorem penExtMF_refl {W : Set T} (F : MeasPen (FTraj W X)) :
    penExtMF (Set.Subset.rfl : W ⊆ W) F = F := by
  have h : fellClip (X := X) (Set.Subset.rfl : W ⊆ W) = id :=
    funext fellClip_refl
  show MeasPen.pull (fellClip Set.Subset.rfl) F = F
  rw [h, MeasPen.pull_id]

/-- Extension is transitive: the window presheaf's functoriality at
the penalty level.  The carrier law is strict; the measurability the
composite law consumes is discharged by openness of the two
subwindows — the general stratum's constitutive hypothesis, paid by
the topology of the site. -/
theorem penExtMF_penExtMF {U V W : Set T} (hUV : U ⊆ V) (hVW : V ⊆ W)
    (hU : IsOpen U) (hV : IsOpen V) (F : MeasPen (FTraj U X)) :
    penExtMF hVW (penExtMF hUV F) = penExtMF (hUV.trans hVW) F := by
  refine (MeasPen.pull_pull (fellClip hUV) (fellClip hVW)
    (measurable_fellClip hUV hU) (measurable_fellClip hVW hV) F).trans ?_
  exact congrArg (fun g => MeasPen.pull g F)
    (funext (fellClip_fellClip hUV hVW))

/-- **The state–window exchange** at the Fell carrier:
window-extension commutes with state-side penalty transport along a
proper state map.  Openness feeds the clip's measurability, properness
feeds the transport's — both derived from continuity. -/
theorem penExtMF_pull_fellMap {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V)
    {h : X → Y} (hp : IsProperMap h) (F : MeasPen (FTraj V Y)) :
    penExtMF hVW (MeasPen.pull (fellMap h) F) =
      MeasPen.pull (fellMap (W := W) h) (penExtMF hVW F) := by
  refine (MeasPen.pull_pull (fellMap h) (fellClip hVW)
    (measurable_fellMap hp) (measurable_fellClip hVW hV) F).trans ?_
  refine Eq.trans (congrArg (fun g => MeasPen.pull g F)
    (funext fun G => (fellClip_fellMap hVW hV h G).symm)) ?_
  exact (MeasPen.pull_pull (fellClip hVW) (fellMap h)
    (measurable_fellClip hVW hV) (measurable_fellMap hp) F).symm

/-! ## The window compositor over the Fell carrier -/

variable {Z U' V' : Type u} [TopologicalSpace Z] [TopologicalSpace U']
  [TopologicalSpace V']

/-- The window compositor at the Fell carrier, base-free: transport a
joint over a common state carrier's records to each component's
records, evaluate, add. -/
def mboxplusWF {W : Set T} (π₁ : Z → U') (π₂ : Z → V')
    (F : MeasPen (FTraj W U')) (G : MeasPen (FTraj W V')) :
    MeasPen (FTraj W Z) :=
  mboxplus (fellMap π₁) (fellMap π₂) F G

@[simp] theorem mboxplusWF_apply {W : Set T} (π₁ : Z → U') (π₂ : Z → V')
    (F : MeasPen (FTraj W U')) (G : MeasPen (FTraj W V'))
    (ν : MeasJoint (FTraj W Z)) :
    mboxplusWF π₁ π₂ F G ν =
      F (ν.push (fellMap π₁)) + G (ν.push (fellMap π₂)) := rfl

/-- The austere unit over a window at the Fell carrier: the zero
penalty. -/
def munitPenWF (X : Type u) [TopologicalSpace X] (W : Set T) :
    MeasPen (FTraj W X) := fun _ => 0

@[simp] theorem munitPenWF_apply (X : Type u) [TopologicalSpace X]
    (W : Set T) (ν : MeasJoint (FTraj W X)) : munitPenWF X W ν = 0 := rfl

/-- **The window–compositor exchange** at the Fell carrier:
window-extension is a homomorphism for the compositor, along proper
marginalizations.  One application of the base-free naturality core
`pull_mboxplus_of_comm`; the comparison squares are the carrier-level
state–window exchange. -/
theorem penExtMF_mboxplusWF {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V)
    {π₁ : Z → U'} {π₂ : Z → V'} (hp₁ : IsProperMap π₁)
    (hp₂ : IsProperMap π₂) (F : MeasPen (FTraj V U'))
    (G : MeasPen (FTraj V V')) :
    penExtMF hVW (mboxplusWF π₁ π₂ F G) =
      mboxplusWF π₁ π₂ (penExtMF hVW F) (penExtMF hVW G) :=
  pull_mboxplus_of_comm (fellClip hVW) (fellMap π₁) (fellMap π₂)
    (fellMap π₁) (fellMap π₂) (fellClip hVW) (fellClip hVW)
    (measurable_fellClip hVW hV) (measurable_fellMap hp₁)
    (measurable_fellMap hp₂) (measurable_fellMap hp₁)
    (measurable_fellMap hp₂) (measurable_fellClip hVW hV)
    (measurable_fellClip hVW hV)
    (funext fun F' => (fellClip_fellMap hVW hV π₁ F').symm)
    (funext fun F' => (fellClip_fellMap hVW hV π₂ F').symm) F G

/-- Window-extension fixes the unit. -/
theorem penExtMF_munitPenWF {V W : Set T} (hVW : V ⊆ W)
    (X : Type u) [TopologicalSpace X] :
    penExtMF hVW (munitPenWF X V) = munitPenWF X W := rfl

/-! ## Window-indexed spec classes over the Fell carrier -/

variable {ι : Type u}

/-- A window-indexed family of Fell-carrier penalty classes is
**persistent** when extension carries each window's members into every
superwindow's class — the lax sections of the window presheaf of
classes, transposed from `SuFunctor.Site.IsPersistentM`. -/
def IsPersistentMF (U : ι → Set T) {X : Type u} [TopologicalSpace X]
    (Φ : ∀ i, Set (MeasPen (FTraj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), penExtMF hij '' Φ i ⊆ Φ j

/-- A window-indexed family of Fell-carrier penalty classes is
**matching** when each window's class is exactly the restriction of
every superwindow's — the strict sections. -/
def IsMatchingMF (U : ι → Set T) {X : Type u} [TopologicalSpace X]
    (Φ : ∀ i, Set (MeasPen (FTraj (U i) X))) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), Φ i = penExtMF hij ⁻¹' Φ j

/-- Strict sections are lax sections. -/
theorem IsMatchingMF.isPersistentMF {U : ι → Set T} {X : Type u}
    [TopologicalSpace X] {Φ : ∀ i, Set (MeasPen (FTraj (U i) X))}
    (h : IsMatchingMF U Φ) : IsPersistentMF U Φ := by
  intro i j hij
  rw [h hij]
  exact Set.image_preimage_subset _ _

/-- Persistence is preserved by state-side transport along a proper
state map, by the state–window exchange.  Openness of the windows is
the site-uniform hypothesis. -/
theorem IsPersistentMF.image_pull_fellMap {U : ι → Set T}
    (hUo : ∀ i, IsOpen (U i))
    {Φ : ∀ i, Set (MeasPen (FTraj (U i) X))} (hΦ : IsPersistentMF U Φ)
    {h : Y → X} (hp : IsProperMap h) :
    IsPersistentMF U (fun i => MeasPen.pull (fellMap h) '' Φ i) := by
  intro i j hij
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  rw [penExtMF_pull_fellMap hij (hUo i) hp]
  exact Set.mem_image_of_mem _ (hΦ hij (Set.mem_image_of_mem _ hF))

/-- Persistence is preserved by the componentwise compositor along
proper marginalizations, by the window–compositor exchange. -/
theorem IsPersistentMF.image2_mboxplusWF {U : ι → Set T}
    (hUo : ∀ i, IsOpen (U i)) {π₁ : Z → U'} {π₂ : Z → V'}
    (hp₁ : IsProperMap π₁) (hp₂ : IsProperMap π₂)
    {Φ : ∀ i, Set (MeasPen (FTraj (U i) U'))}
    {Ψ : ∀ i, Set (MeasPen (FTraj (U i) V'))}
    (hΦ : IsPersistentMF U Φ) (hΨ : IsPersistentMF U Ψ) :
    IsPersistentMF U
      (fun i => Set.image2 (mboxplusWF π₁ π₂) (Φ i) (Ψ i)) := by
  intro i j hij
  rintro _ ⟨_, ⟨F, hF, G, hG, rfl⟩, rfl⟩
  rw [penExtMF_mboxplusWF hij (hUo i) hp₁ hp₂]
  exact Set.mem_image2_of_mem (hΦ hij (Set.mem_image_of_mem _ hF))
    (hΨ hij (Set.mem_image_of_mem _ hG))

/-- The componentwise unit family is persistent. -/
theorem isPersistentMF_munitPenWF (U : ι → Set T) (X : Type u)
    [TopologicalSpace X] :
    IsPersistentMF U (fun i => ({munitPenWF X (U i)} :
      Set (MeasPen (FTraj (U i) X)))) := by
  intro i j hij
  rintro _ ⟨F, hF, rfl⟩
  rw [Set.mem_singleton_iff.mp hF, penExtMF_munitPenWF]
  exact Set.mem_singleton _

/-! ## The seam: functions embed as records via closure of graph -/

/-- The seam from the function carrier to the Fell carrier: a
trajectory's graph, **closed up**.  The closure completion is
constitutive, not cosmetic: a jump trajectory's bare graph is not
closed (`SuFunctor.Site.FellWindowWitness.not_isClosed_graph_jlT`), so
graphs must be upgraded to closed relations to enter the record
carrier at all. -/
def graphCl {W : Set T} (f : Traj W X) : FTraj W X :=
  ⟨closure {p : ↥W × X | p.2 = f p.1}, isClosed_closure⟩

@[simp] theorem coe_graphCl {W : Set T} (f : Traj W X) :
    (graphCl f : Set (↥W × X)) = closure {p : ↥W × X | p.2 = f p.1} := rfl

/-- On the continuous class the closure completion vanishes: a
continuous trajectory into a Hausdorff state space already has a
closed graph.  A lemma, not an assumption — the landed record-locus
closedness results are the case where the closure is invisible. -/
theorem coe_graphCl_of_continuous {W : Set T} [T2Space X] {f : Traj W X}
    (hf : Continuous f) :
    (graphCl f : Set (↥W × X)) = {p : ↥W × X | p.2 = f p.1} :=
  (isClosed_eq continuous_snd (hf.comp continuous_fst)).closure_eq

/-- **The seam square**: clipping to an open subwindow commutes with
the seam.  The openness hypothesis is load-bearing — closure and
restriction exchange along the (continuous, open) window inclusion,
and the witness module refutes the closed-window form. -/
theorem fellClip_graphCl {V W : Set T} (hVW : V ⊆ W) (hV : IsOpen V)
    (f : Traj W X) :
    fellClip hVW (graphCl f) = graphCl (trajRes hVW f) := by
  ext1
  rw [coe_fellClip, coe_graphCl, coe_graphCl,
    preimage_inclT_closure hVW hV]
  rfl

/-- **The seam compatibility at the penalty level**: the
function-carrier window extension `penExtM` is the restriction of the
Fell-carrier `penExtMF` along the seam.  Measurability of the seam
itself is an explicit hypothesis: over uncountable stage spaces the
product σ-algebra of the function carrier cannot see graph-hitting
events, so no unconditional claim is available (discrete stages
discharge both hypotheses).  The clip legs' measurability is derived —
openness on the Fell side, the landed `measurable_trajRes` on the
function side. -/
theorem penExtMF_graphCl {V W : Set T} [MeasurableSpace X]
    (hVW : V ⊆ W) (hV : IsOpen V)
    (hgW : Measurable (graphCl : Traj W X → FTraj W X))
    (hgV : Measurable (graphCl : Traj V X → FTraj V X))
    (F : MeasPen (FTraj V X)) :
    MeasPen.pull graphCl (penExtMF hVW F) =
      penExtM hVW (MeasPen.pull graphCl F) := by
  refine (MeasPen.pull_pull (fellClip hVW) graphCl
    (measurable_fellClip hVW hV) hgW F).trans ?_
  refine Eq.trans (congrArg (fun g => MeasPen.pull g F)
    (funext fun f => fellClip_graphCl hVW hV f)) ?_
  exact (MeasPen.pull_pull graphCl (trajRes hVW) hgV
    (measurable_trajRes hVW) F).symm

/-- On a discrete stage space the closure completion vanishes for
*every* trajectory: all functions from a discrete space are
continuous.  The honest general form of the exact stratum's
finite-carrier coincidence. -/
theorem coe_graphCl_of_discrete {W : Set T} [DiscreteTopology ↥W]
    [T2Space X] (f : Traj W X) :
    (graphCl f : Set (↥W × X)) = {p : ↥W × X | p.2 = f p.1} :=
  coe_graphCl_of_continuous continuous_of_discreteTopology

/-- On a discrete stage space the seam is injective: closures vanish,
and graphs determine functions.  (In general the seam is deliberately
*not* injective — see the witness module's ghost pair — which is the
quotient the record reading wants.) -/
theorem graphCl_injective_of_discrete {W : Set T} [DiscreteTopology ↥W]
    [T2Space X] :
    Function.Injective (graphCl : Traj W X → FTraj W X) := by
  intro f g h
  have hc : ({p : ↥W × X | p.2 = f p.1} : Set (↥W × X))
      = {p : ↥W × X | p.2 = g p.1} := by
    rw [← coe_graphCl_of_discrete f, ← coe_graphCl_of_discrete g, h]
  funext w
  have hm := Set.ext_iff.mp hc (w, f w)
  exact hm.mp rfl

/-- Single-valued total closed relations are exactly the seam's image,
at every stratum: a record every stage of which carries a unique state
is the closed-up graph of the function it determines. -/
theorem graphCl_surjective_onto_functional {W : Set T} (F : FTraj W X)
    (hF : ∀ w : ↥W, ∃! x : X, (w, x) ∈ (F : Set (↥W × X))) :
    ∃ f : Traj W X, graphCl f = F := by
  refine ⟨fun w => (hF w).exists.choose, ?_⟩
  ext1
  rw [coe_graphCl]
  have hgraph : {p : ↥W × X | p.2 = (hF p.1).exists.choose}
      = (F : Set (↥W × X)) := by
    ext ⟨w, x⟩
    constructor
    · intro hx
      have hx' : x = (hF w).exists.choose := hx
      rw [hx']
      exact (hF w).exists.choose_spec
    · intro hx
      exact (hF w).unique hx (hF w).exists.choose_spec
  rw [hgraph, F.isClosed.closure_eq]

end

end Site

end SuFunctor

#print axioms SuFunctor.Site.fellClip_fellClip
#print axioms SuFunctor.Site.continuous_fellClip
#print axioms SuFunctor.Site.fellClip_fellMap
#print axioms SuFunctor.Site.penExtMF_penExtMF
#print axioms SuFunctor.Site.penExtMF_pull_fellMap
#print axioms SuFunctor.Site.penExtMF_mboxplusWF
#print axioms SuFunctor.Site.fellClip_graphCl
#print axioms SuFunctor.Site.penExtMF_graphCl
#print axioms SuFunctor.Site.graphCl_surjective_onto_functional
