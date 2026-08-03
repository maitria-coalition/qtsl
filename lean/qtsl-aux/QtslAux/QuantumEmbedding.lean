import QtslAux.QuantumFunctoriality

/-! # Subregion embeddings: the fragment map beyond isomorphisms

The morphism class of locally covariant QFT (Brunetti–Fredenhagen–
Verch, arXiv:math-ph/0112041, Definition 2.1) is isometric embeddings
with *causally convex* image: any causal curve with endpoints in the
image stays in the image.  The transport modules
(`QtslAux.QuantumCovariance`, `QtslAux.QuantumFunctoriality`) mechanized
the groupoid part — order isomorphisms of event carriers — where every
component of the kinematic fragment rides the map for free.  This
module mechanizes the *embedding* part: non-surjective maps between
different carriers, where the free ride ends.

**The morphism class at order grade.**  `CausalEmbedding X Y` is an
order embedding (`f a ≤ f b ↔ a ≤ b`) whose image is interval-convex
(`f a ≤ y ≤ f b → y` is an image point) — the diamond condition,
exactly BFV's causal-convexity requirement with causal curves replaced
by the causal order itself.  Order isomorphisms embed
(`OrderIso.toCausalEmbedding`), and the canonical non-invertible family
is `Diamond.inclusionEmbedding`: every diamond of the site, viewed as a
spacetime in its own right, includes causally-convexly into its ambient
carrier — the sub-spacetimes `M|_O ↪ M` of the locally covariant
category, realized site-natively.  The diamond condition is consumed at
exactly two places, and they are the textbook reasons BFV demands it:
the image-diamond characterization `inDiamond_push_exists` (whence
Einstein causality transports: causal separation of image diamonds is
checked at arbitrary points of the image diamonds, and convexity is
what makes those points images), and chronological interpolation in the
pulled-back kit (`MixingKit.pullback`: interpolants must not escape the
region).

**Direction.**  At this finite-dimensional grade the
algebra-isomorphism component of a full locally covariant morphism is
the identity, so the entire morphism content is the coherence
`(restricted net).alg D = (ambient net).alg (image of D)` — which the
pullback construction `ObservableNet.restrict` satisfies by `rfl`
(`restrict_alg`): the subregion arrows ι_{M,O} at the fragment level.
The fragment map therefore runs contravariantly, `G ↦ G.restrict f`,
and the assignment is functorial on the nose (`restrict_id`,
`restrict_comp` close definitionally); restriction along an
isomorphism inverts the landed pushforward at net and kit grade
(`ObservableNet.map_restrict`, `MixingKit.map_pullback`).

**Where the free ride ends.**  Along an isomorphism, matter, records,
and certificates ride unchanged.  Along an embedding they become
*stated obligations* of `LCQFTFragment.restrict`:

* **matter locality** — the worldlines must ride inside the image,
  through a time re-indexing `θ : T' → T`.  The re-indexing is forced,
  not stylistic: the causal hull of an inextendible worldline pair is
  the whole carrier, so no proper convex region contains a full matter
  history — the restricted theory sees the matter only during its
  sojourn.  (The morphism data of this module is accordingly a
  spacetime embedding *together with* a time re-indexing; the
  two-tier coherence `restrict_mechanismNet` holds when the
  re-indexing exhausts the sojourn.)
* **region certificates** — the restricted ambient diamond needs its
  own interiority witness and attainment certificate (the ambient
  carrier's witness lives outside the image in general).
* **the record-transport obligation** — the record family must be
  local to the embedded region: `G.records α ∈ G.net.alg (A.push f)`.
  The ambient fragment's own `records_mem` does *not* discharge it,
  and the gap is semantic, not bureaucratic: the zz record family of
  the two-qubit fragment lies outside `leftFactor`
  (`zzRecord_not_mem_leftFactor`), so the restriction to the left
  sub-diamond has no discharge (`record_obligation_fails_at_D₁`) —
  measurement records of a Bell experiment do not restrict to one
  wing.  When the obligation *is* discharged, the Born rows ride
  untouched: the restricted two-qubit fragment's record shadow
  separates the Bell and maximally-mixed classes by the *same proof
  term* as the ambient one (`isingSub_shadow_separates_bell_mixed`) —
  restriction moves the site, never the shadow.

**Scope, stated deliberately.**  Both carriers here live over the same
geometry (a Minkowski sub-diamond into Minkowski space — a genuine
non-invertible morphism of the locally covariant category, since
sub-spacetimes are objects of it).  Embeddings between *different*
geometries need a second exact-order spacetime carrier, which does not
yet exist in this development; nothing here claims "the same physics in
all spacetimes" (Fewster–Verch, arXiv:1106.4785). -/

namespace Qtsl
namespace QuantumEmbedding

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates
open QuantumCovariance QuantumDeterminacy QuantumAssembly
open scoped ComplexOrder Kronecker

variable {X Y Z : Type*} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]

/-! ## The morphism class: order embeddings with the diamond condition -/

/-- An order embedding with interval-convex image — the
Brunetti–Fredenhagen–Verch morphism condition (causally convex
isometric embedding) at order grade: any event causally between two
image events is itself an image event.  The convexity field is the
diamond condition; it is consumed at exactly two places below
(`inDiamond_push_exists` and `MixingKit.pullback`'s interpolation),
each a textbook reason for the requirement. -/
structure CausalEmbedding (X Y : Type*) [PartialOrder X]
    [PartialOrder Y] where
  /-- The underlying event map. -/
  toFun : X → Y
  /-- Order embedding: the map preserves and reflects causal order. -/
  le_iff_le : ∀ {a b : X}, toFun a ≤ toFun b ↔ a ≤ b
  /-- The diamond condition: the image is interval-convex. -/
  convex : ∀ {a b : X} {y : Y}, toFun a ≤ y → y ≤ toFun b →
    ∃ x, toFun x = y

instance : CoeFun (CausalEmbedding X Y) (fun _ => X → Y) :=
  ⟨CausalEmbedding.toFun⟩

namespace CausalEmbedding

/-- A causal embedding is monotone. -/
theorem mono (f : CausalEmbedding X Y) {a b : X} (h : a ≤ b) :
    f a ≤ f b :=
  f.le_iff_le.mpr h

/-- A causal embedding is injective. -/
theorem injective (f : CausalEmbedding X Y) {a b : X}
    (h : f a = f b) : a = b :=
  le_antisymm (f.le_iff_le.mp h.le) (f.le_iff_le.mp h.ge)

/-- The identity causal embedding. -/
def id (X : Type*) [PartialOrder X] : CausalEmbedding X X where
  toFun x := x
  le_iff_le := Iff.rfl
  convex {_ _ y} _ _ := ⟨y, rfl⟩

/-- Composition of causal embeddings (diagrammatically: `f` then `g`).
Convexity composes by two-step descent: the interpolant descends
through `g`'s convexity, then through `f`'s. -/
def comp (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y) :
    CausalEmbedding X Z where
  toFun x := g (f x)
  le_iff_le := g.le_iff_le.trans f.le_iff_le
  convex {a b z} h₁ h₂ := by
    obtain ⟨y, rfl⟩ := g.convex h₁ h₂
    obtain ⟨x, rfl⟩ := f.convex (g.le_iff_le.mp h₁) (g.le_iff_le.mp h₂)
    exact ⟨x, rfl⟩

@[simp] theorem comp_id (f : CausalEmbedding X Y) :
    f.comp (CausalEmbedding.id X) = f := rfl

@[simp] theorem id_comp (f : CausalEmbedding X Y) :
    (CausalEmbedding.id Y).comp f = f := rfl

theorem comp_assoc {W : Type*} [PartialOrder W]
    (h : CausalEmbedding Z W) (g : CausalEmbedding Y Z)
    (f : CausalEmbedding X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end CausalEmbedding

/-- Every order isomorphism is a causal embedding (convexity witnessed
by the inverse) — the groupoid part of the morphism class. -/
def _root_.OrderIso.toCausalEmbedding (f : X ≃o Y) :
    CausalEmbedding X Y where
  toFun := f
  le_iff_le := f.le_iff_le
  convex {_ _ y} _ _ := ⟨f.symm y, f.apply_symm_apply y⟩

/-! ## Diamond transport along a causal embedding -/

/-- The image diamond under a causal embedding. -/
def _root_.Qtsl.DiamondSite.Diamond.push (f : CausalEmbedding X Y)
    (D : Diamond X) : Diamond Y :=
  ⟨f D.lo, f D.hi, f.mono D.le⟩

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.push_lo
    (f : CausalEmbedding X Y) (D : Diamond X) :
    (D.push f).lo = f D.lo := rfl

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.push_hi
    (f : CausalEmbedding X Y) (D : Diamond X) :
    (D.push f).hi = f D.hi := rfl

/-- Diamond containment transports along a causal embedding in both
directions — order-reflection at work. -/
theorem _root_.Qtsl.DiamondSite.Diamond.push_le_push_iff
    (f : CausalEmbedding X Y) {E D : Diamond X} :
    E.push f ≤ D.push f ↔ E ≤ D := by
  show (f D.lo ≤ f E.lo ∧ f E.hi ≤ f D.hi) ↔ (D.lo ≤ E.lo ∧ E.hi ≤ D.hi)
  exact and_congr f.le_iff_le f.le_iff_le

/-- On the groupoid part, `push` is the landed iso pushforward. -/
theorem _root_.Qtsl.DiamondSite.Diamond.push_toCausalEmbedding
    (f : X ≃o Y) (D : Diamond X) :
    D.push f.toCausalEmbedding = D.map f := rfl

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.push_id (D : Diamond X) :
    D.push (CausalEmbedding.id X) = D := rfl

theorem _root_.Qtsl.DiamondSite.Diamond.push_comp
    (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y) (D : Diamond X) :
    D.push (g.comp f) = (D.push f).push g := rfl

/-- Point membership of an *image* point transports along a causal
embedding — pure order embedding, no convexity. -/
theorem inDiamond_push_iff (f : CausalEmbedding X Y) {x : X}
    {D : Diamond X} : inDiamond (f x) (D.push f) ↔ inDiamond x D := by
  show (f D.lo ≤ f x ∧ f x ≤ f D.hi) ↔ (D.lo ≤ x ∧ x ≤ D.hi)
  exact and_congr f.le_iff_le f.le_iff_le

/-- **The diamond condition, kernel-visible**: the points of an image
diamond are exactly the images of the diamond's points.  The forward
direction is convexity on the nose; without it an image diamond
contains events of undetermined causal relation to the region, and
Einstein-causality transport genuinely fails. -/
theorem inDiamond_push_exists (f : CausalEmbedding X Y) {y : Y}
    {D : Diamond X} :
    inDiamond y (D.push f) ↔ ∃ x, f x = y ∧ inDiamond x D := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := f.convex h.1 h.2
    exact ⟨x, rfl, (inDiamond_push_iff f).mp h⟩
  · rintro ⟨x, rfl, hx⟩
    exact (inDiamond_push_iff f).mpr hx

/-! ## The canonical family: a diamond as a spacetime in its own right -/

/-- The inclusion of a diamond's point set, as a causal embedding — the
sub-spacetime arrows `M|_O ↪ M` of the locally covariant category,
site-natively.  Convexity is interval-convexity of diamond membership:
the diamond condition names itself. -/
def _root_.Qtsl.DiamondSite.Diamond.inclusionEmbedding (D : Diamond X) :
    CausalEmbedding {r : X // inDiamond r D} X where
  toFun := Subtype.val
  le_iff_le := Subtype.coe_le_coe
  convex {a b y} h₁ h₂ := ⟨⟨y, a.2.1.trans h₁, h₂.trans b.2.2⟩, rfl⟩

/-- A point of a subdiamond is a point of the diamond (lower
endpoint). -/
theorem inDiamond_lo_of_le {E D : Diamond X} (h : E ≤ D) :
    inDiamond E.lo D :=
  ⟨h.1, E.le.trans h.2⟩

/-- A point of a subdiamond is a point of the diamond (upper
endpoint). -/
theorem inDiamond_hi_of_le {E D : Diamond X} (h : E ≤ D) :
    inDiamond E.hi D :=
  ⟨h.1.trans E.le, h.2⟩

/-- A subdiamond, lifted to the sub-spacetime carrier of its ambient
diamond. -/
def _root_.Qtsl.DiamondSite.Diamond.liftOfLe {E D : Diamond X}
    (h : E ≤ D) : Diamond {r : X // inDiamond r D} :=
  ⟨⟨E.lo, inDiamond_lo_of_le h⟩, ⟨E.hi, inDiamond_hi_of_le h⟩,
    Subtype.mk_le_mk.mpr E.le⟩

/-- Pushing a lifted subdiamond back along the inclusion recovers
it. -/
@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.liftOfLe_push
    {E D : Diamond X} (h : E ≤ D) :
    (Diamond.liftOfLe h).push D.inclusionEmbedding = E := rfl

/-- The diamond itself, as the top diamond of its own carrier. -/
def _root_.Qtsl.DiamondSite.Diamond.selfDiamond (D : Diamond X) :
    Diamond {r : X // inDiamond r D} :=
  Diamond.liftOfLe (le_refl D)

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.selfDiamond_push
    (D : Diamond X) : (D.selfDiamond).push D.inclusionEmbedding = D :=
  rfl

/-- A lifted subdiamond is contained in the self diamond. -/
theorem _root_.Qtsl.DiamondSite.Diamond.liftOfLe_le_selfDiamond
    {E D : Diamond X} (h : E ≤ D) :
    Diamond.liftOfLe h ≤ D.selfDiamond :=
  ⟨Subtype.mk_le_mk.mpr h.1, Subtype.mk_le_mk.mpr h.2⟩

/-! ## Kit pullback: chronology restricted to a causally convex region -/

/-- Pullback of a mixing kit along a causal embedding: the chronology
read through the map.  Interpolation consumes the diamond condition —
a chronological interpolant lies causally between image points, so
convexity is exactly what keeps it inside the region. -/
def _root_.Qtsl.QuantumDescent.MixingKit.pullback
    (f : CausalEmbedding X Y) (M : MixingKit Y) : MixingKit X where
  chron a b := M.chron (f a) (f b)
  le_of_chron {_ _} h := f.le_iff_le.mp (M.le_of_chron h)
  chron_of_le_chron {_ _ _} hab hbc :=
    M.chron_of_le_chron (f.mono hab) hbc
  chron_of_chron_le {_ _ _} hab hbc :=
    M.chron_of_chron_le hab (f.mono hbc)
  interpolate {_ _} h := by
    obtain ⟨c', h₁, h₂⟩ := M.interpolate h
    obtain ⟨c, rfl⟩ := f.convex (M.le_of_chron h₁) (M.le_of_chron h₂)
    exact ⟨c, h₁, h₂⟩

/-- The pulled-back chronology, unfolded. -/
theorem _root_.Qtsl.QuantumDescent.MixingKit.pullback_chron_iff
    (f : CausalEmbedding X Y) (M : MixingKit Y) (a b : X) :
    (M.pullback f).chron a b ↔ M.chron (f a) (f b) := Iff.rfl

/-- Interiority in the pulled-back kit is interiority of the image
diamonds. -/
theorem _root_.Qtsl.QuantumDescent.MixingKit.pullback_interiorMem_iff
    (f : CausalEmbedding X Y) (M : MixingKit Y) {A W : Diamond X} :
    (M.pullback f).interiorMem A W ↔
      M.interiorMem (A.push f) (W.push f) := Iff.rfl

@[simp] theorem _root_.Qtsl.QuantumDescent.MixingKit.pullback_id
    (M : MixingKit X) : M.pullback (CausalEmbedding.id X) = M := rfl

theorem _root_.Qtsl.QuantumDescent.MixingKit.pullback_comp
    (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y)
    (M : MixingKit Z) :
    M.pullback (g.comp f) = (M.pullback g).pullback f := rfl

/-! ## Net restriction: the ι_{M,O} coherence, definitional -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Restriction of an observable net along a causal embedding: a
diamond of the region reads the ambient net at its image.  This is the
Brunetti–Fredenhagen–Verch coherence `α_ψ(A(M,O)) = A(N, ψ(O))` at
identity algebra component, arranged to hold by `rfl`
(`restrict_alg`). -/
def _root_.Qtsl.QuantumDescent.ObservableNet.restrict
    (f : CausalEmbedding X Y) (N : ObservableNet Y n) :
    ObservableNet X n where
  alg D := N.alg (D.push f)
  isotone {_ _} h := N.isotone ((Diamond.push_le_push_iff f).mpr h)

/-- The restriction coherence, kernel-visible. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.restrict_alg
    (f : CausalEmbedding X Y) (N : ObservableNet Y n) (D : Diamond X) :
    (N.restrict f).alg D = N.alg (D.push f) := rfl

@[simp] theorem _root_.Qtsl.QuantumDescent.ObservableNet.restrict_id
    (N : ObservableNet X n) : N.restrict (CausalEmbedding.id X) = N :=
  rfl

theorem _root_.Qtsl.QuantumDescent.ObservableNet.restrict_comp
    (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y)
    (N : ObservableNet Z n) :
    N.restrict (g.comp f) = (N.restrict g).restrict f := rfl

/-- Restriction along an isomorphism inverts the landed pushforward at
net grade. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.map_restrict
    (f : X ≃o Y) (N : ObservableNet X n) :
    (N.map f).restrict f.toCausalEmbedding = N :=
  ObservableNet.ext fun D => by
    show N.alg ((D.push f.toCausalEmbedding).map f.symm) = N.alg D
    rw [Diamond.push_toCausalEmbedding, Diamond.map_symm_map]

/-- Restriction along an isomorphism inverts the landed pushforward at
kit grade. -/
theorem _root_.Qtsl.QuantumDescent.MixingKit.map_pullback (f : X ≃o Y)
    (M : MixingKit X) : (M.map f).pullback f.toCausalEmbedding = M :=
  MixingKit.ext fun a b => by
    show M.chron (f.symm (f a)) (f.symm (f b)) ↔ M.chron a b
    simp

/-! ## The Heisenberg tier: the embedding-case commute lemma -/

variable {ι T T' κ : Type*} [Fintype κ]

/-- **The Heisenberg net commutes with restriction when the time
re-indexing exhausts the sojourn**: restricting the net of a mechanism
along a causal embedding is the same as rebuilding the net from the
region-valued worldlines with the re-indexed mechanism.  The
exhaustion hypothesis `hexh` — every moment the ambient matter spends
inside the region is hit by the re-indexing — is load-bearing: without
it the restricted side misses crossings and only the `≤` inequality
survives.  Convexity and injectivity are consumed in the forward leg
(an ambient crossing inside an image diamond *is* an image point, and
it is the region worldline's point). -/
theorem heisenbergNet_restrict_of_exhaustive (f : CausalEmbedding X Y)
    (θ : T' → T) (w : ι → T' → X) (wY : ι → T → Y)
    (hw : ∀ i t', f (w i t') = wY i (θ t'))
    (hexh : ∀ i t, (∃ x, f x = wY i t) → ∃ t', θ t' = t)
    (B : ι → Subalgebra ℂ (Matrix n n ℂ))
    (τ : T → (Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)) :
    (heisenbergNet wY B τ).restrict f =
      heisenbergNet w B (fun t' => τ (θ t')) :=
  ObservableNet.ext fun D => by
    refine le_antisymm (iSup_le fun pc => ?_) (iSup_le fun pc => ?_)
    · obtain ⟨⟨i, t⟩, hmem⟩ := pc
      obtain ⟨x, hfx, hxD⟩ := (inDiamond_push_exists f).mp hmem
      obtain ⟨t', rfl⟩ := hexh i t ⟨x, hfx⟩
      have hx : w i t' = x := f.injective (by rw [hw i t']; exact hfx.symm)
      exact factor_le_heisenbergNet_alg (w := w)
        (τ := fun t' => τ (θ t')) (i := i) (t := t') (hx ▸ hxD)
    · obtain ⟨⟨i, t'⟩, hmem⟩ := pc
      have hmem' : inDiamond (wY i (θ t')) (D.push f) := by
        rw [← hw i t']
        exact (inDiamond_push_iff f).mpr hmem
      exact factor_le_heisenbergNet_alg (w := wY) (τ := τ) (i := i)
        (t := θ t') hmem'

/-! ## The fragment map along an embedding

The free rides that end become stated obligations: matter locality
(through a time re-indexing), region certificates, and the
record-transport obligation.  Everything else transports by the
theorems above. -/

variable (G : LCQFTFragment Y n ι T κ)

/-- **A kinematic fragment restricts along a causal embedding** — the
fragment map beyond isomorphisms.  The inputs after the embedding are
the obligations that the iso case discharged for free:

* matter locality: worldlines `w` and sites `s` valued in the region,
  riding over a time re-indexing `θ` (`hw`, `hs`, `hsw`) — forced,
  since no proper convex region contains an inextendible matter
  history;
* region certificates: an ambient diamond `A` with interiority
  witness `W`, interior in the pulled-back kit (`hint`), and
  attainment (`hatt`);
* **the record-transport obligation** (`hrec`): the record family is
  local to the region's ambient image.  The ambient fragment's own
  `records_mem` does not discharge it (`record_obligation_fails_at_D₁`
  is the kernel-checked counterexample).

The kinematic net is the pullback (`restrict_alg` is `rfl` — the
ι_{M,O} coherence); Einstein causality transports through the diamond
condition; the frozen-shadow tie is preserved by re-indexing the
constant-worldline net on both sides. -/
def _root_.Qtsl.QuantumAssembly.LCQFTFragment.restrict
    (f : CausalEmbedding X Y) [Nonempty T'] (θ : T' → T)
    (w : ι → T' → X) (_hw : ∀ i t', f (w i t') = G.worldlines i (θ t'))
    (s : ι → X) (hs : ∀ i, f (s i) = G.sites i)
    (hsw : ∀ i, ∃ t', w i t' = s i)
    (A W : Diamond X)
    (hint : (G.kit.pullback f).interiorMem A W)
    (hatt : G.net.alg (A.push f) ≤ G.net.alg (W.push f))
    (hrec : ∀ α, G.records α ∈ G.net.alg (A.push f)) :
    LCQFTFragment X n ι T' κ where
  net := G.net.restrict f
  sites := s
  worldlines := w
  factors := G.factors
  mechanism := fun t' => G.mechanism (θ t')
  sites_on_worldlines := hsw
  factors_exhaustive := G.factors_exhaustive
  frozen_shadow := fun D => by
    have hT : Nonempty T := ⟨θ (Classical.arbitrary T')⟩
    show (heisenbergNet (fun i (_ : T') => s i) G.factors
        (fun _ => AlgEquiv.refl)).alg D = G.net.alg (D.push f)
    rw [heisenbergNet_const_alg, ← G.frozen_shadow (D.push f),
      heisenbergNet_const_alg]
    exact iSup_congr fun i => iSup_congr_Prop
      (by rw [← hs i, inDiamond_push_iff]) (fun _ => rfl)
  einstein_causality := by
    intro D₁ D₂ hsp a ha b hb
    refine G.einstein_causality (D₁ := D₁.push f) (D₂ := D₂.push f)
      ?_ a ha b hb
    intro y z hy hz
    obtain ⟨r, rfl, hr⟩ := (inDiamond_push_exists f).mp hy
    obtain ⟨u, rfl, hu⟩ := (inDiamond_push_exists f).mp hz
    have h := hsp hr hu
    exact ⟨fun hle => h.1 (f.le_iff_le.mp hle),
      fun hle => h.2 (f.le_iff_le.mp hle)⟩
  timeslice_surrogate := by
    intro E D hle hsit
    show G.net.alg (E.push f) = G.net.alg (D.push f)
    refine G.timeslice_surrogate ((Diamond.push_le_push_iff f).mpr hle) ?_
    intro i hi
    rw [← hs i, inDiamond_push_iff] at hi ⊢
    exact hsit i hi
  kit := G.kit.pullback f
  ambient := A
  interior_witness := W
  interior_mem := hint
  interior_attained := hatt
  records := G.records
  records_mem := hrec
  records_posSemidef := G.records_posSemidef
  records_exhaustive := G.records_exhaustive

section RestrictProjections

variable (f : CausalEmbedding X Y) [Nonempty T'] (θ : T' → T)
  (w : ι → T' → X) (hw : ∀ i t', f (w i t') = G.worldlines i (θ t'))
  (s : ι → X) (hs : ∀ i, f (s i) = G.sites i)
  (hsw : ∀ i, ∃ t', w i t' = s i)
  (A W : Diamond X)
  (hint : (G.kit.pullback f).interiorMem A W)
  (hatt : G.net.alg (A.push f) ≤ G.net.alg (W.push f))
  (hrec : ∀ α, G.records α ∈ G.net.alg (A.push f))

/-- The restricted net reads the ambient net at image diamonds —
`rfl`. -/
theorem restrict_net_alg (D : Diamond X) :
    (G.restrict f θ w hw s hs hsw A W hint hatt hrec).net.alg D =
      G.net.alg (D.push f) := rfl

/-- The record family rides restriction unchanged as matrices —
`rfl`; what does NOT ride free is its locality, which is the
obligation `hrec`. -/
theorem restrict_records :
    (G.restrict f θ w hw s hs hsw A W hint hatt hrec).records =
      G.records := rfl

/-- **The two tiers restrict coherently** when the time re-indexing
exhausts the sojourn: the mechanism net of the restricted fragment is
the restriction of the ambient mechanism net — the embedding-case
analogue of the landed `LCQFTFragment.map_mechanismNet`. -/
theorem restrict_mechanismNet
    (hexh : ∀ i t, (∃ x, f x = G.worldlines i t) → ∃ t', θ t' = t) :
    (G.restrict f θ w hw s hs hsw A W hint hatt hrec).mechanismNet =
      G.mechanismNet.restrict f :=
  (heisenbergNet_restrict_of_exhaustive f θ w G.worldlines hw hexh
    G.factors G.mechanism).symm

end RestrictProjections

/-- **Identity law**: restricting along the identity embedding, with
the ambient fragment's own data and certificates, is the identity —
definitionally. -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.restrict_id
    [Nonempty T] (F : LCQFTFragment X n ι T κ) :
    F.restrict (CausalEmbedding.id X) (fun t => t) F.worldlines
      (fun _ _ => rfl) F.sites (fun _ => rfl) F.sites_on_worldlines
      F.ambient F.interior_witness F.interior_mem F.interior_attained
      F.records_mem = F := rfl

/-- **Composition law**: the composite of two restrictions is the
restriction along the composite embedding, with the same data and
certificates (which typecheck on both sides definitionally) —
definitionally.  Together with `restrict_id` this is contravariant
functoriality of the fragment assignment on causal embeddings, on the
nose. -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.restrict_comp
    {T'' : Type*} [Nonempty T'] [Nonempty T'']
    (G : LCQFTFragment Z n ι T κ)
    (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y)
    (θ₁ : T' → T) (θ₂ : T'' → T')
    (w₁ : ι → T' → Y) (hw₁ : ∀ i t', g (w₁ i t') = G.worldlines i (θ₁ t'))
    (s₁ : ι → Y) (hs₁ : ∀ i, g (s₁ i) = G.sites i)
    (hsw₁ : ∀ i, ∃ t', w₁ i t' = s₁ i)
    (A₁ W₁ : Diamond Y) (hint₁ : (G.kit.pullback g).interiorMem A₁ W₁)
    (hatt₁ : G.net.alg (A₁.push g) ≤ G.net.alg (W₁.push g))
    (hrec₁ : ∀ α, G.records α ∈ G.net.alg (A₁.push g))
    (w₂ : ι → T'' → X) (hw₂ : ∀ i t'', f (w₂ i t'') = w₁ i (θ₂ t''))
    (s₂ : ι → X) (hs₂ : ∀ i, f (s₂ i) = s₁ i)
    (hsw₂ : ∀ i, ∃ t'', w₂ i t'' = s₂ i)
    (A₂ W₂ : Diamond X)
    (hint₂ : ((G.kit.pullback g).pullback f).interiorMem A₂ W₂)
    (hatt₂ : (G.net.restrict g).alg (A₂.push f) ≤
      (G.net.restrict g).alg (W₂.push f))
    (hrec₂ : ∀ α, G.records α ∈ (G.net.restrict g).alg (A₂.push f)) :
    (G.restrict g θ₁ w₁ hw₁ s₁ hs₁ hsw₁ A₁ W₁ hint₁ hatt₁
        hrec₁).restrict f θ₂ w₂ hw₂ s₂ hs₂ hsw₂ A₂ W₂ hint₂ hatt₂
        hrec₂ =
      G.restrict (g.comp f) (fun t'' => θ₁ (θ₂ t'')) w₂
        (fun i t'' => by
          show g (f (w₂ i t'')) = _
          rw [hw₂ i t'', hw₁ i (θ₂ t'')])
        s₂
        (fun i => by
          show g (f (s₂ i)) = _
          rw [hs₂ i, hs₁ i])
        hsw₂ A₂ W₂ hint₂ hatt₂ hrec₂ := rfl

/-! ## The Minkowski sub-diamond instance

The two-qubit fragment, restricted to the sub-spacetime carved out by
its own ambient diamond: a genuine non-invertible morphism of the
locally covariant category (sub-spacetimes are objects of it),
non-surjective and between different carriers.  The static worldlines
sojourn in `Dstar` exactly during `[-2, 2]`, so the time re-indexing
is the subtype inclusion of that interval. -/

/-- The two-qubit matter's sojourn interval in `Dstar`. -/
abbrev DstarSojourn := {t : ℝ // -2 ≤ t ∧ t ≤ 2}

instance : Nonempty DstarSojourn := ⟨⟨0, by norm_num⟩⟩

/-- The qubit worldlines' sojourn in the ambient diamond: both static
worldlines lie in `Dstar` for `t ∈ [-2, 2]`. -/
theorem qubitWorldline_mem_Dstar {t : ℝ} (h₁ : -2 ≤ t) (h₂ : t ≤ 2)
    (i : Fin 2) : inDiamond (qubitWorldline i t) Dstar := by
  fin_cases i
  · constructor
    · show ‖(-1 : ℝ) - 0‖ ≤ t - (-3)
      rw [Real.norm_eq_abs]
      rw [show |(-1 : ℝ) - 0| = 1 by norm_num]
      linarith
    · show ‖(0 : ℝ) - (-1)‖ ≤ 3 - t
      rw [Real.norm_eq_abs]
      rw [show |(0 : ℝ) - (-1)| = 1 by norm_num]
      linarith
  · constructor
    · show ‖(1 : ℝ) - 0‖ ≤ t - (-3)
      rw [Real.norm_eq_abs]
      rw [show |(1 : ℝ) - 0| = 1 by norm_num]
      linarith
    · show ‖(0 : ℝ) - 1‖ ≤ 3 - t
      rw [Real.norm_eq_abs]
      rw [show |(0 : ℝ) - 1| = 1 by norm_num]
      linarith

/-- The sojourn bound, converse direction: a worldline point inside
`Dstar` has its time in `[-2, 2]` — the exhaustion witness for the
two-tier coherence. -/
theorem sojourn_of_qubitWorldline_mem_Dstar {t : ℝ} {i : Fin 2}
    (h : inDiamond (qubitWorldline i t) Dstar) : -2 ≤ t ∧ t ≤ 2 := by
  fin_cases i
  · obtain ⟨h₁, h₂⟩ := h
    have e₁ : ‖(-1 : ℝ) - 0‖ ≤ t - (-3) := h₁
    have e₂ : ‖(0 : ℝ) - (-1)‖ ≤ 3 - t := h₂
    rw [Real.norm_eq_abs, show |(-1 : ℝ) - 0| = 1 by norm_num] at e₁
    rw [Real.norm_eq_abs, show |(0 : ℝ) - (-1)| = 1 by norm_num] at e₂
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h₁, h₂⟩ := h
    have e₁ : ‖(1 : ℝ) - 0‖ ≤ t - (-3) := h₁
    have e₂ : ‖(0 : ℝ) - 1‖ ≤ 3 - t := h₂
    rw [Real.norm_eq_abs, show |(1 : ℝ) - 0| = 1 by norm_num] at e₁
    rw [Real.norm_eq_abs, show |(0 : ℝ) - 1| = 1 by norm_num] at e₂
    exact ⟨by linarith, by linarith⟩

/-- The qubit worldlines, valued in the `Dstar` sub-spacetime. -/
def dstarWorldlines (i : Fin 2) (t' : DstarSojourn) :
    {r : Mink ℝ // inDiamond r Dstar} :=
  ⟨qubitWorldline i t'.1, qubitWorldline_mem_Dstar t'.2.1 t'.2.2 i⟩

/-- The qubit sites, valued in the `Dstar` sub-spacetime. -/
def dstarSites : Fin 2 → {r : Mink ℝ // inDiamond r Dstar} :=
  ![⟨p, p_mem_Dstar⟩, ⟨q, q_mem_Dstar⟩]

/-- The region-valued sites map to the ambient sites. -/
theorem dstarSites_map (i : Fin 2) :
    Dstar.inclusionEmbedding (dstarSites i) =
      isingQubitFragment.sites i := by
  fin_cases i <;> rfl

/-- Each region-valued site lies on its region-valued worldline. -/
theorem dstarSites_on_worldlines (i : Fin 2) :
    ∃ t', dstarWorldlines i t' = dstarSites i :=
  ⟨⟨0, by norm_num⟩, by fin_cases i <;> rfl⟩

/-- The ambient attainment certificate, at the region's image
diamonds. -/
theorem dstar_attained : qubitNet.alg Dstar ≤ qubitNet.alg E₃ := by
  rw [qubitNet_E₃]
  exact le_top

/-- The subtype inclusion of `[-2, 2]` exhausts the matter's sojourn
in `Dstar` — the exhaustion witness for the two-tier coherence. -/
theorem dstarSojourn_exhaustive (i : Fin 2) (t : ℝ)
    (hx : ∃ x : {r : Mink ℝ // inDiamond r Dstar},
      x.1 = qubitWorldline i t) :
    ∃ t' : DstarSojourn, t'.1 = t := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨h₁, h₂⟩ := sojourn_of_qubitWorldline_mem_Dstar (hfx ▸ x.2)
  exact ⟨⟨t, h₁, h₂⟩, rfl⟩

/-- **The two-qubit fragment, restricted to its own ambient
sub-spacetime.**  All three obligation families are discharged: the
matter sojourns in `[-2, 2]`; the region inherits `E₃` as interiority
witness with attainment; and the zz record family is local to the
region's image (`zzRecord_mem_top`) — the record-transport obligation,
satisfied here and refused at the left sub-diamond
(`record_obligation_fails_at_D₁`). -/
noncomputable def isingQubitFragmentOnDstar :
    LCQFTFragment {r : Mink ℝ // inDiamond r Dstar} (Fin 2 × Fin 2)
      (Fin 2) DstarSojourn (Fin 2 × Fin 2) :=
  isingQubitFragment.restrict Dstar.inclusionEmbedding
    (fun t' : DstarSojourn => t'.1) dstarWorldlines (fun _ _ => rfl)
    dstarSites dstarSites_map dstarSites_on_worldlines
    Dstar.selfDiamond (Diamond.liftOfLe E₃_le_Dstar)
    E₃_interior dstar_attained (fun α => zzRecord_mem_top α)

/-- The restricted fragment's net reads the ambient algebra at the
region's own top diamond — the coherence, `rfl` at the instance. -/
theorem isingSub_net_alg_self :
    isingQubitFragmentOnDstar.net.alg Dstar.selfDiamond =
      qubitNet.alg Dstar := rfl

/-- **The record thesis survives passage to the sub-spacetime**: the
restricted fragment's record shadow separates the Bell and
maximally-mixed classes at the region's own ambient diamond, by the
*same proof term* as the ambient theorem — records and representatives
are global, so restriction moves the site, never the shadow. -/
theorem isingSub_shadow_separates_bell_mixed :
    isingQubitFragmentOnDstar.shadow
        (stateClassMk isingQubitFragmentOnDstar.net Dstar.selfDiamond
          ⟨bell, bell_isState⟩) ≠
      isingQubitFragmentOnDstar.shadow
        (stateClassMk isingQubitFragmentOnDstar.net Dstar.selfDiamond
          ⟨mixed, mixed_isState⟩) :=
  recordShadowQ_separates_bell_mixed

/-- The lifted slice diamond covers the restricted worldlines' common
slice at time `1` — the sub-spacetime's own Cauchy-surface shadow. -/
theorem isingSub_commonSlice :
    CommonSlice isingQubitFragmentOnDstar.worldlines
      (⟨1, by norm_num⟩ : DstarSojourn)
      (Diamond.liftOfLe Eslice_le_Dstar) :=
  fun i => ⟨Subtype.mk_le_mk.mpr (qubitWorldline_commonSlice_Eslice i).1,
    Subtype.mk_le_mk.mpr (qubitWorldline_commonSlice_Eslice i).2⟩

/-- **Genuine Cauchy-determinacy inside the sub-spacetime**: the
restricted fragment's mechanism net is determined on the lifted slice
diamond — pure consumption of the generic time-slice theorem at the
restricted object. -/
theorem isingSub_slice_determinacy :
    isingQubitFragmentOnDstar.mechanismNet.alg
        (Diamond.liftOfLe Eslice_le_Dstar) =
      isingQubitFragmentOnDstar.mechanismNet.alg Dstar.selfDiamond :=
  isingQubitFragmentOnDstar.timeslice_genuine_alg
    (Diamond.liftOfLe_le_selfDiamond Eslice_le_Dstar)
    isingSub_commonSlice

/-- **The two tiers restrict coherently at the instance**: the
sub-spacetime's Heisenberg net is the restriction of the global one —
the sojourn interval `[-2, 2]` is exactly what the subtype inclusion
exhausts. -/
theorem isingSub_mechanismNet_restrict :
    isingQubitFragmentOnDstar.mechanismNet =
      isingQubitFragment.mechanismNet.restrict
        Dstar.inclusionEmbedding :=
  restrict_mechanismNet isingQubitFragment Dstar.inclusionEmbedding
    (fun t' : DstarSojourn => t'.1) dstarWorldlines (fun _ _ => rfl)
    dstarSites dstarSites_map dstarSites_on_worldlines
    Dstar.selfDiamond (Diamond.liftOfLe E₃_le_Dstar)
    E₃_interior dstar_attained (fun α => zzRecord_mem_top α)
    dstarSojourn_exhaustive

/-! ## The negation pair: the free ride ends, kernel-checked -/

/-- **The zz record family is not left-local**: the correlation
projector at outcome `(0,0)` does not factor as `x ⊗ 1`.  Two matrix
entries refute the factorization: it would force `x 0 0 = 1` at entry
`((0,0),(0,0))` and `x 0 0 = 0` at entry `((0,1),(0,1))`. -/
theorem zzRecord_not_mem_leftFactor :
    zzRecord ((0 : Fin 2), (0 : Fin 2)) ∉ leftFactor := by
  intro h
  obtain ⟨x, hx⟩ := mem_leftFactor.mp h
  have key : ∀ jl : Fin 2,
      (x ⊗ₖ (1 : Qubit)) ((0 : Fin 2), jl) ((0 : Fin 2), jl) =
        x 0 0 := fun jl => by
    rw [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
  have h₁ : zzRecord ((0 : Fin 2), (0 : Fin 2))
      ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (0 : Fin 2)) = 1 := by
    simp [zzRecord]
  have h₂ : zzRecord ((0 : Fin 2), (0 : Fin 2))
      ((0 : Fin 2), (1 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) = 0 := by
    simp [zzRecord]
  rw [← hx, key] at h₁ h₂
  exact one_ne_zero (h₁.symm.trans h₂)

/-- **The record-transport obligation is refused at the left
sub-diamond**: the restriction of the two-qubit fragment to the
sub-spacetime carved out by `D₁` has no record-locality discharge —
the region's ambient image reads `leftFactor`, and the zz family is
not in it.  Measurement records of a Bell experiment do not restrict
to one wing; this is where the iso case's free ride ends. -/
theorem record_obligation_fails_at_D₁ :
    ¬ ∀ α, zzRecord α ∈
      qubitNet.alg ((D₁.selfDiamond).push D₁.inclusionEmbedding) := by
  intro h
  have h₀ := h ((0 : Fin 2), (0 : Fin 2))
  rw [Diamond.selfDiamond_push, qubitNet_D₁] at h₀
  exact zzRecord_not_mem_leftFactor h₀

end QuantumEmbedding
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.mono
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.injective
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.comp_assoc
#print axioms OrderIso.toCausalEmbedding
#print axioms Qtsl.DiamondSite.Diamond.push_le_push_iff
#print axioms Qtsl.DiamondSite.Diamond.push_toCausalEmbedding
#print axioms Qtsl.DiamondSite.Diamond.push_id
#print axioms Qtsl.DiamondSite.Diamond.push_comp
#print axioms Qtsl.QuantumEmbedding.inDiamond_push_iff
#print axioms Qtsl.QuantumEmbedding.inDiamond_push_exists
#print axioms Qtsl.DiamondSite.Diamond.inclusionEmbedding
#print axioms Qtsl.DiamondSite.Diamond.liftOfLe_push
#print axioms Qtsl.DiamondSite.Diamond.selfDiamond_push
#print axioms Qtsl.DiamondSite.Diamond.liftOfLe_le_selfDiamond
#print axioms Qtsl.QuantumDescent.MixingKit.pullback
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_interiorMem_iff
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_id
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_comp
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_alg
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_id
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_comp
#print axioms Qtsl.QuantumDescent.ObservableNet.map_restrict
#print axioms Qtsl.QuantumDescent.MixingKit.map_pullback
#print axioms Qtsl.QuantumEmbedding.heisenbergNet_restrict_of_exhaustive
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict
#print axioms Qtsl.QuantumEmbedding.restrict_net_alg
#print axioms Qtsl.QuantumEmbedding.restrict_records
#print axioms Qtsl.QuantumEmbedding.restrict_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_id
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_comp
#print axioms Qtsl.QuantumEmbedding.qubitWorldline_mem_Dstar
#print axioms Qtsl.QuantumEmbedding.sojourn_of_qubitWorldline_mem_Dstar
#print axioms Qtsl.QuantumEmbedding.dstarSites_map
#print axioms Qtsl.QuantumEmbedding.dstarSites_on_worldlines
#print axioms Qtsl.QuantumEmbedding.dstar_attained
#print axioms Qtsl.QuantumEmbedding.dstarSojourn_exhaustive
#print axioms Qtsl.QuantumEmbedding.isingQubitFragmentOnDstar
#print axioms Qtsl.QuantumEmbedding.isingSub_net_alg_self
#print axioms Qtsl.QuantumEmbedding.isingSub_shadow_separates_bell_mixed
#print axioms Qtsl.QuantumEmbedding.isingSub_commonSlice
#print axioms Qtsl.QuantumEmbedding.isingSub_slice_determinacy
#print axioms Qtsl.QuantumEmbedding.isingSub_mechanismNet_restrict
#print axioms Qtsl.QuantumEmbedding.zzRecord_not_mem_leftFactor
#print axioms Qtsl.QuantumEmbedding.record_obligation_fails_at_D₁
