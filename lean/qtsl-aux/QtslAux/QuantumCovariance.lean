import QtslAux.QuantumDescent
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Covariance transport on the derived diamond site

Locally covariant quantum field theory (Brunetti–Fredenhagen–Verch,
arXiv:math-ph/0112041, Definition 2.1) formulates covariance as
functoriality over a category of spacetimes whose morphisms are
isometric embeddings with causally convex image.  On the derived
diamond site of a fixed causal order (`QtslAux.DiamondSite`,
`QtslAux.DiamondTopology`), the *inclusion* part of that category is
already present — the subdiamond arrows play exactly the role of the
subregion embeddings ι_{M,O} — and what is missing is the *groupoid*
part: how the site, its derived topology, an observable net, and the
separation-grade descent theorems move along an isomorphism of the
underlying causal orders.  This module supplies that transport.

**What this module proves.**

* **Diamond transport** (`Diamond.map`, `Diamond.congr`): an order
  isomorphism `f : X ≃o Y` of event carriers induces an order
  isomorphism of the diamond posets — inclusions go to inclusions in
  both directions.
* **Interiority and topology transport** (`interiorMem_map_iff`,
  `sieveCongr`, `mem_diamondTopology_congr`): when `f` respects the
  chronologies (`M.chron a b ↔ M'.chron (f a) (f b)`), chronological
  interiority transports, and a sieve covers in the derived topology
  iff its transport covers the image diamond.  The degenerate case of
  this statement — same carrier, identity map, two kits sharing a
  chronology — is `diamondTopology_eq_of_chron_eq`; the present form
  is its groupoid generalization.  The mathlib-facing corollary
  `coverPreserving_diamondTopology` packages the forward direction as
  a `CoverPreserving` functor between the two sites.  Contrast
  `ClockMap.cover_cofinal`: a non-invertible monotone map has to *earn*
  cover-preservation from density and approximation hypotheses
  (cofinality of the image family); an order isomorphism gets both
  directions by pure transport.
* **Kit pushforward** (`ChronologyKit.map`, `MixingKit.map`): a
  chronology kit moves along `f` (chronology read through `f.symm`),
  giving the canonical chronology-respecting target when none is
  given; the pushforward commutes with forgetting the
  filtered/directed fields (`toMixingKit_map`).
* **Net transport** (`ObservableNet.map`, `separatesSieve_map_iff`,
  `map_separates_derived_of_interior_attained`): an observable net
  pushes forward along `f`, separation-grade descent transports, and
  the interior-attainment repair theorem
  (`separates_of_interior_attained`) composes with the transport: an
  interior-attained net's pushforward separates every derived cover of
  the image diamond.
* **The special-relativity dress** (`minkTranslate`,
  `qubitNet_map_translate_separates_derived`): translations of
  Minkowski space are order automorphisms respecting the strict-cone
  chronology — so the derived Minkowski topology is
  translation-invariant, and the two-qubit net's separation theorem
  transports to every translate of its diamond without re-proving any
  matrix fact.

**Scope, stated deliberately.**

* The transport here is *kinematic*.  Order isomorphisms are the
  order-theoretic shadow of the conformal isometries: a bijection
  between (past and future distinguishing) spacetimes preserving the
  chronological relation in both directions is automatically a smooth
  conformal isometry (Hawking–King–McCarthy, J. Math. Phys. 17 (1976)
  174; Malament, J. Math. Phys. 18 (1977) 1399).  That reconstruction
  theorem is cited as motivation only; nothing manifold-level is
  formalized.
* Nothing here claims "the same physics in all spacetimes": Fewster
  and Verch (arXiv:1106.4785) show that property (SPASs) *fails* for
  the full class of locally covariant theories.  What transports is
  the kinematic fragment — nets, covers, separation — not dynamics.
* At this finite-dimensional grade the net takes values in subalgebras
  of one fixed matrix algebra, so the algebra-isomorphism component of
  a full locally covariant morphism is the identity here; only the
  geometry moves.  Non-surjective embeddings between *different*
  carriers (the full Brunetti–Fredenhagen–Verch morphism class) are
  deliberately out of scope.
-/

namespace Qtsl
namespace QuantumCovariance

open CategoryTheory DiamondSite QuantumDescent

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

/-! ## Diamond transport along an order isomorphism -/

/-- The image diamond under an order isomorphism of event carriers. -/
def _root_.Qtsl.DiamondSite.Diamond.map (f : X ≃o Y) (D : Diamond X) :
    Diamond Y :=
  ⟨f D.lo, f D.hi, f.monotone D.le⟩

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.map_lo (f : X ≃o Y)
    (D : Diamond X) : (D.map f).lo = f D.lo := rfl

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.map_hi (f : X ≃o Y)
    (D : Diamond X) : (D.map f).hi = f D.hi := rfl

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.map_symm_map (f : X ≃o Y)
    (D : Diamond X) : (D.map f).map f.symm = D := by
  cases D with
  | mk lo hi le => simp [Diamond.map]

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.map_map_symm (f : X ≃o Y)
    (D : Diamond Y) : (D.map f.symm).map f = D := by
  cases D with
  | mk lo hi le => simp [Diamond.map]

/-- Diamond containment transports along an order isomorphism, in both
directions — the reflection half is where invertibility is
load-bearing. -/
theorem _root_.Qtsl.DiamondSite.Diamond.map_le_map_iff (f : X ≃o Y)
    {E D : Diamond X} : E.map f ≤ D.map f ↔ E ≤ D := by
  show (f D.lo ≤ f E.lo ∧ f E.hi ≤ f D.hi) ↔ (D.lo ≤ E.lo ∧ E.hi ≤ D.hi)
  exact and_congr f.le_iff_le f.le_iff_le

/-- **Diamond congruence**: an order isomorphism of event carriers
induces an order isomorphism of the diamond posets (hence an
equivalence of the diamond categories, via the preorder-category
machinery). -/
def _root_.Qtsl.DiamondSite.Diamond.congr (f : X ≃o Y) :
    Diamond X ≃o Diamond Y where
  toFun := Diamond.map f
  invFun := Diamond.map f.symm
  left_inv D := D.map_symm_map f
  right_inv D := D.map_map_symm f
  map_rel_iff' := Diamond.map_le_map_iff f

/-- An inclusion into an image diamond pulls back along the inverse:
the workhorse for sieve transport. -/
theorem map_symm_le_of_le_map (f : X ≃o Y) {E' : Diamond Y}
    {D : Diamond X} (h : E' ≤ D.map f) : E'.map f.symm ≤ D := by
  show D.lo ≤ f.symm E'.lo ∧ f.symm E'.hi ≤ D.hi
  exact ⟨f.le_symm_apply.mpr h.1, f.symm_apply_le.mpr h.2⟩

/-- Sieve membership only depends on the source object (arrows in the
diamond poset are subsingletons); stated as an equality-transport
helper so no dependent rewriting is ever needed downstream. -/
theorem sieve_mem_of_source_eq {D : Diamond X} (S : Sieve D)
    {E E' : Diamond X} (hEE : E = E') {h : E ≤ D} {h' : E' ≤ D}
    (hS : S (homOfLE h)) : S (homOfLE h') := by
  subst hEE
  exact hS

/-! ## Interiority transport -/

/-- **Chronological interiority transports** along a
chronology-respecting order isomorphism.  The iff-shaped respect
hypothesis is load-bearing: a merely monotone map with forward-only
chronology respect (for instance the identity from a strict chronology
to the degenerate one, where every diamond is interior to itself) does
not reflect interiority. -/
theorem interiorMem_map_iff (f : X ≃o Y) {M : MixingKit X}
    {M' : MixingKit Y}
    (hchron : ∀ a b : X, M.chron a b ↔ M'.chron (f a) (f b))
    {D E : Diamond X} :
    M'.interiorMem (D.map f) (E.map f) ↔ M.interiorMem D E := by
  show (M'.chron (f D.lo) (f E.lo) ∧ M'.chron (f E.hi) (f D.hi)) ↔
    (M.chron D.lo E.lo ∧ M.chron E.hi D.hi)
  exact and_congr (hchron D.lo E.lo).symm (hchron E.hi D.hi).symm

/-! ## Kit pushforward: the canonical chronology-respecting target -/

/-- Pushforward of a chronology kit along an order isomorphism: the
chronology is read through `f.symm`.  All seven bicontinuity fields
transport. -/
def _root_.Qtsl.DiamondSite.ChronologyKit.map (f : X ≃o Y)
    (K : ChronologyKit X) : ChronologyKit Y where
  chron a b := K.chron (f.symm a) (f.symm b)
  le_of_chron {a b} h := f.symm.le_iff_le.mp (K.le_of_chron h)
  chron_of_le_chron {a b c} hab hbc :=
    K.chron_of_le_chron (f.symm.monotone hab) hbc
  chron_of_chron_le {a b c} hab hbc :=
    K.chron_of_chron_le hab (f.symm.monotone hbc)
  interpolate {a b} h := by
    obtain ⟨c, h₁, h₂⟩ := K.interpolate h
    exact ⟨f c, by simpa using h₁, by simpa using h₂⟩
  up_filtered {a c c'} h h' := by
    obtain ⟨c'', hc, h₁, h₂⟩ := K.up_filtered h h'
    exact ⟨f c'', by simpa using hc, f.le_symm_apply.mp h₁,
      f.le_symm_apply.mp h₂⟩
  down_directed {b d d'} h h' := by
    obtain ⟨d'', hd, h₁, h₂⟩ := K.down_directed h h'
    exact ⟨f d'', by simpa using hd, f.symm_apply_le.mp h₁,
      f.symm_apply_le.mp h₂⟩

/-- Pushforward of the interpolative-mixing fragment. -/
def _root_.Qtsl.QuantumDescent.MixingKit.map (f : X ≃o Y)
    (M : MixingKit X) : MixingKit Y where
  chron a b := M.chron (f.symm a) (f.symm b)
  le_of_chron {a b} h := f.symm.le_iff_le.mp (M.le_of_chron h)
  chron_of_le_chron {a b c} hab hbc :=
    M.chron_of_le_chron (f.symm.monotone hab) hbc
  chron_of_chron_le {a b c} hab hbc :=
    M.chron_of_chron_le hab (f.symm.monotone hbc)
  interpolate {a b} h := by
    obtain ⟨c, h₁, h₂⟩ := M.interpolate h
    exact ⟨f c, by simpa using h₁, by simpa using h₂⟩

/-- The kit pushforward commutes with forgetting the filtered/directed
fields. -/
theorem toMixingKit_map (f : X ≃o Y) (K : ChronologyKit X) :
    (K.map f).toMixingKit = K.toMixingKit.map f := rfl

/-- The pushforward kit respects the chronology through `f` — the
canonical witness for the transport theorems' hypothesis when no
target kit is given in advance. -/
theorem _root_.Qtsl.DiamondSite.ChronologyKit.map_chron_iff (f : X ≃o Y)
    (K : ChronologyKit X) (a b : X) :
    K.chron a b ↔ (K.map f).chron (f a) (f b) := by
  show K.chron a b ↔ K.chron (f.symm (f a)) (f.symm (f b))
  simp

/-- The mixing-fragment version of `ChronologyKit.map_chron_iff`. -/
theorem _root_.Qtsl.QuantumDescent.MixingKit.map_chron_iff (f : X ≃o Y)
    (M : MixingKit X) (a b : X) :
    M.chron a b ↔ (M.map f).chron (f a) (f b) := by
  show M.chron a b ↔ M.chron (f.symm (f a)) (f.symm (f b))
  simp

/-- Chronological thickness transports along a chronology-respecting
order isomorphism. -/
theorem thick_map_iff (f : X ≃o Y) {K : ChronologyKit X}
    {L : ChronologyKit Y}
    (hchron : ∀ a b : X, K.chron a b ↔ L.chron (f a) (f b))
    {D : Diamond X} : Thick L (D.map f) ↔ Thick K D :=
  (hchron D.lo D.hi).symm

/-! ## Topology transport -/

/-- Transport of a sieve along an order isomorphism of event carriers:
the transported sieve holds at an inclusion iff the original holds at
its pullback along `f.symm`.  Invertibility is load-bearing — for a
merely monotone map the pullback of the source is not available, and
cover-preservation genuinely requires cofinality hypotheses
(`ClockMap.cover_cofinal`). -/
def sieveCongr (f : X ≃o Y) {D : Diamond X} (S : Sieve D) :
    Sieve (D.map f) where
  arrows E' g := S (homOfLE (map_symm_le_of_le_map f (leOfHom g)))
  downward_closed := by
    intro E' F' g hg g'
    have h1 : F'.map f.symm ≤ E'.map f.symm :=
      (Diamond.map_le_map_iff f.symm).mpr (leOfHom g')
    have h2 := S.downward_closed hg (homOfLE h1)
    rwa [Subsingleton.elim
      (homOfLE h1 ≫ homOfLE (map_symm_le_of_le_map f (leOfHom g)))
      (homOfLE (map_symm_le_of_le_map f (leOfHom (g' ≫ g))))] at h2

/-- **The derived topology transports**: a sieve covers a diamond iff
its transport covers the image diamond.  The degenerate case (same
carrier, identity isomorphism, two kits sharing a chronology) is
`diamondTopology_eq_of_chron_eq`. -/
theorem mem_diamondTopology_congr (f : X ≃o Y) {M : MixingKit X}
    {M' : MixingKit Y}
    (hchron : ∀ a b : X, M.chron a b ↔ M'.chron (f a) (f b))
    {D : Diamond X} {S : Sieve D} :
    sieveCongr f S ∈ M'.diamondTopology (D.map f) ↔
      S ∈ M.diamondTopology D := by
  constructor
  · intro hS E hE hint
    have hint' : M'.interiorMem (D.map f) (E.map f) :=
      (interiorMem_map_iff f hchron).mpr hint
    have hle' : E.map f ≤ D.map f := (Diamond.map_le_map_iff f).mpr hE
    exact sieve_mem_of_source_eq S (Diamond.map_symm_map f E)
      (hS hle' hint')
  · intro hS E' hE' hint'
    show S (homOfLE (map_symm_le_of_le_map f hE'))
    have hint'' : M.interiorMem D (E'.map f.symm) := by
      refine (interiorMem_map_iff f hchron).mp ?_
      rwa [Diamond.map_map_symm]
    exact hS (map_symm_le_of_le_map f hE') hint''

/-- The chronology-kit form of `mem_diamondTopology_congr`, through the
mixing-fragment factoring. -/
theorem mem_diamondTopology_congr_kit (f : X ≃o Y)
    {K : ChronologyKit X} {L : ChronologyKit Y}
    (hchron : ∀ a b : X, K.chron a b ↔ L.chron (f a) (f b))
    {D : Diamond X} {S : Sieve D} :
    sieveCongr f S ∈ diamondTopology L (D.map f) ↔
      S ∈ diamondTopology K D := by
  rw [diamondTopology_factors, diamondTopology_factors]
  exact mem_diamondTopology_congr f hchron

/-- The forward direction of the transport, in mathlib's site
vocabulary: the induced functor of the diamond congruence is
cover-preserving for the derived topologies. -/
theorem coverPreserving_diamondTopology (f : X ≃o Y) {M : MixingKit X}
    {M' : MixingKit Y}
    (hchron : ∀ a b : X, M.chron a b ↔ M'.chron (f a) (f b)) :
    CoverPreserving M.diamondTopology M'.diamondTopology
      (Diamond.congr f).monotone.functor := by
  constructor
  intro D S hS E' hle' hint'
  refine ⟨E'.map f.symm, homOfLE (map_symm_le_of_le_map f hle'),
    homOfLE (le_of_eq (Diamond.map_map_symm f E').symm), ?_,
    Subsingleton.elim _ _⟩
  refine hS (map_symm_le_of_le_map f hle')
    ((interiorMem_map_iff f hchron).mp ?_)
  rwa [Diamond.map_map_symm]

/-! ## Net transport and separation-grade descent -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pushforward of an observable net along an order isomorphism of the
event carriers: the image diamond reads the original's algebra at its
pullback.  At this finite-dimensional grade the net takes values in one
fixed matrix algebra, so only the geometry moves — the
algebra-isomorphism component of a full locally covariant morphism is
the identity here. -/
def _root_.Qtsl.QuantumDescent.ObservableNet.map (f : X ≃o Y)
    (N : ObservableNet X n) : ObservableNet Y n where
  alg D' := N.alg (D'.map f.symm)
  isotone h := N.isotone ((Diamond.map_le_map_iff f.symm).mpr h)

@[simp] theorem _root_.Qtsl.QuantumDescent.ObservableNet.map_alg_map
    (f : X ≃o Y) (N : ObservableNet X n) (D : Diamond X) :
    (N.map f).alg (D.map f) = N.alg D := by
  show N.alg ((D.map f).map f.symm) = N.alg D
  rw [Diamond.map_symm_map]

/-- **Separation-grade descent transports**: a sieve separates the net
iff its transport separates the pushforward net at the image diamond.
No chronology enters — this is pure order and algebra. -/
theorem separatesSieve_map_iff (f : X ≃o Y) (N : ObservableNet X n)
    {D : Diamond X} {S : Sieve D} :
    SeparatesSieve (N.map f) (D.map f) (sieveCongr f S) ↔
      SeparatesSieve N D S := by
  constructor
  · intro hT ρ σ hagree a ha
    have ha' : a ∈ (N.map f).alg (D.map f) := by
      rw [ObservableNet.map_alg_map]
      exact ha
    refine hT ρ σ ?_ a ha'
    intro E' hE' hs b hb
    exact hagree (map_symm_le_of_le_map f hE') hs b hb
  · intro hSep ρ σ hagree' a ha
    have ha' : a ∈ N.alg D := by
      rwa [ObservableNet.map_alg_map] at ha
    refine hSep ρ σ ?_ a ha'
    intro E hE hs b hb
    have hle' : E.map f ≤ D.map f := (Diamond.map_le_map_iff f).mpr hE
    have hs' : sieveCongr f S (homOfLE hle') := by
      show S (homOfLE (map_symm_le_of_le_map f (leOfHom (homOfLE hle'))))
      exact sieve_mem_of_source_eq S (Diamond.map_symm_map f E).symm hs
    have hb' : b ∈ (N.map f).alg (E.map f) := by
      rw [ObservableNet.map_alg_map]
      exact hb
    exact hagree' hle' hs' b hb'

/-- **The interior-attainment repair composes with the transport**: an
interior-attained net's pushforward separates every derived cover of
the image diamond.  The proof is `separates_of_interior_attained`
applied to transported hypotheses — no sieve round-trip is needed. -/
theorem map_separates_derived_of_interior_attained (f : X ≃o Y)
    {M : MixingKit X} {M' : MixingKit Y}
    (hchron : ∀ a b : X, M.chron a b ↔ M'.chron (f a) (f b))
    (N : ObservableNet X n) {D E₀ : Diamond X}
    (hE : M.interiorMem D E₀) (halg : N.alg D ≤ N.alg E₀) :
    ∀ S' ∈ M'.diamondTopology (D.map f),
      SeparatesSieve (N.map f) (D.map f) S' := by
  refine separates_of_interior_attained M' (N.map f)
    ((interiorMem_map_iff f hchron).mpr hE) ?_
  show (N.map f).alg (D.map f) ≤ (N.map f).alg (E₀.map f)
  rw [ObservableNet.map_alg_map, ObservableNet.map_alg_map]
  exact halg

/-! ## The special-relativity dress: translations -/

section Minkowski

variable {V : Type*} [NormedAddCommGroup V]

/-- Translation of Minkowski space by a time shift and a spatial
displacement, as an order automorphism of the cone order. -/
def minkTranslate (a : ℝ) (w : V) : Mink V ≃o Mink V where
  toFun p := ⟨p.t + a, p.x + w⟩
  invFun p := ⟨p.t - a, p.x - w⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_rel_iff' {p q} := by
    show ‖(q.x + w) - (p.x + w)‖ ≤ (q.t + a) - (p.t + a) ↔
      ‖q.x - p.x‖ ≤ q.t - p.t
    rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]

@[simp] theorem minkTranslate_apply_t (a : ℝ) (w : V) (p : Mink V) :
    (minkTranslate a w p).t = p.t + a := rfl

@[simp] theorem minkTranslate_apply_x (a : ℝ) (w : V) (p : Mink V) :
    (minkTranslate a w p).x = p.x + w := rfl

/-- Translations respect the strict-cone chronology — with
`diamondTopology_eq_of_chron_eq`'s vocabulary, the derived Minkowski
topology is translation-invariant. -/
theorem minkTranslate_chron_iff (a : ℝ) (w : V) (p q : Mink V) :
    Mink.chron p q ↔
      Mink.chron (minkTranslate a w p) (minkTranslate a w q) := by
  show ‖q.x - p.x‖ < q.t - p.t ↔
    ‖(q.x + w) - (p.x + w)‖ < (q.t + a) - (p.t + a)
  rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]

/-- A translation with a nonzero time shift moves every event: the
dress is not the identity. -/
theorem minkTranslate_ne_self {a : ℝ} (ha : a ≠ 0) (w : V)
    (p : Mink V) : minkTranslate a w p ≠ p := by
  intro h
  have ht : p.t + a = p.t := congrArg Mink.t h
  exact ha (by linarith)

/-- **The two-qubit separation theorem transports to every translate**:
each covering sieve of the derived topology at the translated ambient
diamond separates the translated net.  The proof re-derives nothing —
it is the interior-attainment repair applied to the transported
interior witness and the transported attainment; no matrix fact is
re-proven. -/
theorem qubitNet_map_translate_separates_derived (a : ℝ) (w : ℝ) :
    ∀ S ∈ ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology
        (Dstar.map (minkTranslate a w)),
      SeparatesSieve (qubitNet.map (minkTranslate a w))
        (Dstar.map (minkTranslate a w)) S :=
  map_separates_derived_of_interior_attained (minkTranslate a w)
    (fun p q => minkTranslate_chron_iff a w p q) qubitNet E₃_interior
    (by rw [qubitNet_E₃]; exact le_top)

/-- Concretely: the translated net reads the left qubit's algebra at
the translated left diamond. -/
theorem qubitNet_map_translate_alg_D₁ (a : ℝ) (w : ℝ) :
    (qubitNet.map (minkTranslate a w)).alg
      (D₁.map (minkTranslate a w)) = leftFactor := by
  rw [ObservableNet.map_alg_map, qubitNet_D₁]

end Minkowski

end QuantumCovariance
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.DiamondSite.Diamond.map_symm_map
#print axioms Qtsl.DiamondSite.Diamond.map_le_map_iff
#print axioms Qtsl.QuantumCovariance.interiorMem_map_iff
#print axioms Qtsl.DiamondSite.ChronologyKit.map_chron_iff
#print axioms Qtsl.QuantumCovariance.toMixingKit_map
#print axioms Qtsl.QuantumCovariance.thick_map_iff
#print axioms Qtsl.QuantumCovariance.mem_diamondTopology_congr
#print axioms Qtsl.QuantumCovariance.mem_diamondTopology_congr_kit
#print axioms Qtsl.QuantumCovariance.coverPreserving_diamondTopology
#print axioms Qtsl.QuantumCovariance.separatesSieve_map_iff
#print axioms Qtsl.QuantumCovariance.map_separates_derived_of_interior_attained
#print axioms Qtsl.QuantumCovariance.minkTranslate_chron_iff
#print axioms Qtsl.QuantumCovariance.minkTranslate_ne_self
#print axioms Qtsl.QuantumCovariance.qubitNet_map_translate_separates_derived
#print axioms Qtsl.QuantumCovariance.qubitNet_map_translate_alg_D₁
