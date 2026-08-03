import QtslAux.QuantumAssembly

/-! # Functoriality of the kinematic fragment

Local covariance in the sense of Brunetti–Fredenhagen–Verch
(arXiv:math-ph/0112041, Definition 2.1) is functoriality: a locally
covariant theory is a functor from a category of spacetimes to a
category of algebras, and its covariance is the statement that the
assignment respects identities and composition.  The transport module
(`QtslAux.QuantumCovariance`) moved each *clause* of the kinematic
package along an order isomorphism of event carriers, one theorem at a
time.  This module moves the assembled *object*: `LCQFTFragment.map`
pushes a whole kinematic fragment forward along an order isomorphism,
and the assignment is functorial on the nose — identity and
composition laws hold definitionally.  Once the object has moved, every
clause of the recovery checklist is read off the image fragment by the
generic theorems of `QtslAux.QuantumAssembly`; no per-clause transport
remains to be proven.

**The commute lemma.**  The one genuinely new equation is
`heisenbergNet_map`: the pushforward of the Heisenberg net of a
mechanism is the Heisenberg net of the pushed-forward worldlines, with
the same factors and the same mechanism —

`(heisenbergNet w B τ).map f = heisenbergNet (fun i t => f (w i t)) B τ`.

Geometry moves; matter content and dynamics do not.  Its proof is an
index transport: a worldline crossing lies in the pulled-back diamond
iff its image lies in the original, so the two generating families
coincide.  The lemma is what makes the fragment map cohere across its
two tiers (`LCQFTFragment.map_mechanismNet`): the mechanism net of the
transported fragment is the transport of the mechanism net, and the
frozen-shadow tie is preserved by exactly this equation.

**What transports and what does not.**  At this finite-dimensional
grade the net takes values in subalgebras of one fixed matrix algebra,
so the algebra-isomorphism component of a full locally covariant
morphism is the identity: `factors`, `mechanism`, and the record family
ride the map unchanged, and only the geometry (sites, worldlines,
diamonds, chronology) moves.  Two consequences are exhibited on the
two-qubit instance: the strict-cone chronology kit of Minkowski space
is translation-*invariant* as an object
(`minkowskiKit_toMixingKit_map_translate`), and the record shadow is
transport-invariant on representatives — the separation of the Bell
and maximally mixed classes at every translate is definitionally the
separation at the origin
(`isingQubitFragment_map_shadow_separates_bell_mixed`).

**Scope, inherited deliberately.**  Only the groupoid part of local
covariance appears: order isomorphisms are the order-theoretic shadow
of the conformal isometries (Hawking–King–McCarthy, J. Math. Phys. 17
(1976) 174; Malament, J. Math. Phys. 18 (1977) 1399), the site's own
inclusions play the subregion-embedding role, and non-surjective
embeddings between different carriers remain out of scope, as in the
transport module.  Nothing here claims "the same physics in all
spacetimes" (Fewster–Verch, arXiv:1106.4785). -/

namespace Qtsl
namespace QuantumFunctoriality

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates
open QuantumCovariance QuantumDeterminacy QuantumAssembly
open scoped ComplexOrder

variable {X Y Z : Type*} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]

/-! ## Membership transport -/

/-- Point membership transports along an order isomorphism: the image
of a point lies in the image diamond iff the point lies in the
diamond. -/
theorem inDiamond_map_iff (f : X ≃o Y) {r : X} {D : Diamond X} :
    inDiamond (f r) (D.map f) ↔ inDiamond r D := by
  show (f D.lo ≤ f r ∧ f r ≤ f D.hi) ↔ (D.lo ≤ r ∧ r ≤ D.hi)
  exact and_congr f.le_iff_le f.le_iff_le

/-- Membership in an image diamond is membership of the preimage. -/
theorem inDiamond_map_iff' (f : X ≃o Y) {r' : Y} {D : Diamond X} :
    inDiamond r' (D.map f) ↔ inDiamond (f.symm r') D := by
  show (f D.lo ≤ r' ∧ r' ≤ f D.hi) ↔ (D.lo ≤ f.symm r' ∧ f.symm r' ≤ D.hi)
  exact and_congr f.le_symm_apply.symm f.symm_apply_le.symm

/-- Membership in a pulled-back diamond is membership of the image —
the index-transport workhorse for the Heisenberg-net commute lemma. -/
theorem inDiamond_map_symm_iff (f : X ≃o Y) {r : X} {D' : Diamond Y} :
    inDiamond r (D'.map f.symm) ↔ inDiamond (f r) D' := by
  show (f.symm D'.lo ≤ r ∧ r ≤ f.symm D'.hi) ↔ (D'.lo ≤ f r ∧ f r ≤ D'.hi)
  exact and_congr f.symm_apply_le f.le_symm_apply

/-! ## Extensionality for the transported structures -/

/-- An observable net is determined by its algebra assignment. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.ext
    {n : Type*} [Fintype n] [DecidableEq n]
    {N M : ObservableNet X n} (h : ∀ D, N.alg D = M.alg D) : N = M := by
  cases N with
  | mk algN isoN =>
    cases M with
    | mk algM isoM =>
      have halg : algN = algM := funext h
      subst halg
      rfl

/-- A mixing kit is determined by its chronology. -/
theorem _root_.Qtsl.QuantumDescent.MixingKit.ext
    {M M' : MixingKit X} (h : ∀ a b, M.chron a b ↔ M'.chron a b) :
    M = M' := by
  cases M with
  | mk c₁ h₁ h₂ h₃ h₄ =>
    cases M' with
    | mk c₂ g₁ g₂ g₃ g₄ =>
      have hc : c₁ = c₂ := funext fun a => funext fun b => propext (h a b)
      subst hc
      rfl

/-! ## Functor laws for the transported pieces

Identity and composition hold definitionally: the pushforwards were
defined by pure pullback bookkeeping, so `OrderIso.refl` unfolds to the
identity on every field and `OrderIso.trans` unfolds to consecutive
pullbacks. -/

@[simp] theorem _root_.Qtsl.DiamondSite.Diamond.map_refl (D : Diamond X) :
    D.map (OrderIso.refl X) = D := rfl

theorem _root_.Qtsl.DiamondSite.Diamond.map_trans (f : X ≃o Y) (g : Y ≃o Z)
    (D : Diamond X) : D.map (f.trans g) = (D.map f).map g := rfl

@[simp] theorem _root_.Qtsl.QuantumDescent.ObservableNet.map_refl
    {n : Type*} [Fintype n] [DecidableEq n] (N : ObservableNet X n) :
    N.map (OrderIso.refl X) = N := rfl

theorem _root_.Qtsl.QuantumDescent.ObservableNet.map_trans
    {n : Type*} [Fintype n] [DecidableEq n] (f : X ≃o Y) (g : Y ≃o Z)
    (N : ObservableNet X n) : N.map (f.trans g) = (N.map f).map g := rfl

@[simp] theorem _root_.Qtsl.QuantumDescent.MixingKit.map_refl
    (M : MixingKit X) : M.map (OrderIso.refl X) = M := rfl

theorem _root_.Qtsl.QuantumDescent.MixingKit.map_trans (f : X ≃o Y)
    (g : Y ≃o Z) (M : MixingKit X) :
    M.map (f.trans g) = (M.map f).map g := rfl

/-! ## The Heisenberg-net commute lemma -/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι T κ : Type*} [Fintype κ]

/-- Pointwise form of the commute lemma: the Heisenberg net of the
pushed-forward worldlines reads, at an image diamond, exactly what the
original Heisenberg net reads at the preimage diamond.  The proof is
index transport: a crossing of the moved matter lies in `D'` iff the
original crossing lies in the pullback of `D'`. -/
theorem heisenbergNet_map_alg (f : X ≃o Y) (w : ι → T → X)
    (B : ι → Subalgebra ℂ (Matrix n n ℂ))
    (τ : T → (Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)) (D' : Diamond Y) :
    (heisenbergNet (fun i t => f (w i t)) B τ).alg D' =
      (heisenbergNet w B τ).alg (D'.map f.symm) := by
  refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun p => ?_)
  · exact factor_le_heisenbergNet_alg ((inDiamond_map_symm_iff f).mpr p.2)
  · exact factor_le_heisenbergNet_alg ((inDiamond_map_symm_iff f).mp p.2)

/-- **The Heisenberg net commutes with pushforward**: transporting the
net of a mechanism along an order isomorphism of event carriers is the
same as transporting the worldlines and rebuilding the net — with the
same factors and the same mechanism.  Geometry moves; matter content
and dynamics do not. -/
theorem heisenbergNet_map (f : X ≃o Y) (w : ι → T → X)
    (B : ι → Subalgebra ℂ (Matrix n n ℂ))
    (τ : T → (Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)) :
    (heisenbergNet w B τ).map f = heisenbergNet (fun i t => f (w i t)) B τ :=
  ObservableNet.ext fun D' => (heisenbergNet_map_alg f w B τ D').symm

/-- A common slice of the worldline family transports to a common slice
of the pushed-forward family at the image diamond. -/
theorem _root_.Qtsl.QuantumDeterminacy.CommonSlice.map (f : X ≃o Y)
    {w : ι → T → X} {t₀ : T} {E : Diamond X}
    (hsl : CommonSlice w t₀ E) :
    CommonSlice (fun i t => f (w i t)) t₀ (E.map f) :=
  fun i => (inDiamond_map_iff f).mpr (hsl i)

/-- Pointwise causal separation of diamonds transports along an order
isomorphism — the Einstein-causality hypothesis moves with the
geometry. -/
theorem pointwise_spacelike_map (f : X ≃o Y) {D₁ D₂ : Diamond X}
    (hsp : ∀ ⦃r s : X⦄, inDiamond r D₁ → inDiamond s D₂ →
      ¬ r ≤ s ∧ ¬ s ≤ r) :
    ∀ ⦃r' s' : Y⦄, inDiamond r' (D₁.map f) → inDiamond s' (D₂.map f) →
      ¬ r' ≤ s' ∧ ¬ s' ≤ r' := by
  intro r' s' hr' hs'
  have h := hsp ((inDiamond_map_iff' f).mp hr') ((inDiamond_map_iff' f).mp hs')
  exact ⟨fun hle => h.1 (f.symm.le_iff_le.mpr hle),
    fun hle => h.2 (f.symm.le_iff_le.mpr hle)⟩

/-! ## The fragment pushforward -/

/-- **A kinematic fragment pushes forward along an order isomorphism
of event carriers.**  The geometry (sites, worldlines, diamonds,
chronology kit) moves through `f`; the matter content (factors,
mechanism, records) rides unchanged, since at this grade only the
geometry distinguishes the two carriers; every axiom field transports
by the corresponding landed theorem.  The frozen-shadow tie is
preserved by the Heisenberg-net commute lemma — this is where the new
equation is consumed on the nose. -/
def _root_.Qtsl.QuantumAssembly.LCQFTFragment.map (f : X ≃o Y)
    (F : LCQFTFragment X n ι T κ) : LCQFTFragment Y n ι T κ where
  net := F.net.map f
  sites := fun i => f (F.sites i)
  worldlines := fun i t => f (F.worldlines i t)
  factors := F.factors
  mechanism := F.mechanism
  sites_on_worldlines := fun i =>
    (F.sites_on_worldlines i).imp fun _t ht => congrArg (⇑f) ht
  factors_exhaustive := F.factors_exhaustive
  frozen_shadow := fun D' => by
    have h := heisenbergNet_map_alg f (fun i (_ : T) => F.sites i) F.factors
      (fun _ => AlgEquiv.refl) D'
    exact h.trans (F.frozen_shadow (D'.map f.symm))
  einstein_causality := by
    intro D₁' D₂' hsp
    exact F.einstein_causality (D₁ := D₁'.map f.symm) (D₂ := D₂'.map f.symm)
      (fun r s hr hs => by
        have h := hsp ((inDiamond_map_symm_iff f).mp hr)
          ((inDiamond_map_symm_iff f).mp hs)
        exact ⟨fun hrs => h.1 (f.le_iff_le.mpr hrs),
          fun hsr => h.2 (f.le_iff_le.mpr hsr)⟩)
  timeslice_surrogate := by
    intro E' D' hle hs
    show F.net.alg (E'.map f.symm) = F.net.alg (D'.map f.symm)
    exact F.timeslice_surrogate ((Diamond.map_le_map_iff f.symm).mpr hle)
      (fun i hi => (inDiamond_map_symm_iff f).mpr
        (hs i ((inDiamond_map_symm_iff f).mp hi)))
  kit := F.kit.map f
  ambient := F.ambient.map f
  interior_witness := F.interior_witness.map f
  interior_mem :=
    (interiorMem_map_iff f (MixingKit.map_chron_iff f F.kit)).mpr
      F.interior_mem
  interior_attained := by
    rw [ObservableNet.map_alg_map, ObservableNet.map_alg_map]
    exact F.interior_attained
  records := F.records
  records_mem := fun α => by
    rw [ObservableNet.map_alg_map]
    exact F.records_mem α
  records_posSemidef := F.records_posSemidef
  records_exhaustive := F.records_exhaustive

/-- **Identity law**: pushing forward along the identity isomorphism
is the identity — definitionally. -/
@[simp] theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.map_refl
    (F : LCQFTFragment X n ι T κ) : F.map (OrderIso.refl X) = F := rfl

/-- **Composition law**: pushing forward along a composite is the
composite of the pushforwards — definitionally.  Together with
`map_refl` this is functoriality of the fragment assignment on the
groupoid of event carriers. -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.map_trans
    (F : LCQFTFragment X n ι T κ) (f : X ≃o Y) (g : Y ≃o Z) :
    F.map (f.trans g) = (F.map f).map g := rfl

/-- **The two tiers transport coherently**: the mechanism net of the
transported fragment is the transport of the mechanism net.  This is
the Heisenberg-net commute lemma read at the fragment level. -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.map_mechanismNet
    (F : LCQFTFragment X n ι T κ) (f : X ≃o Y) :
    (F.map f).mechanismNet = F.mechanismNet.map f :=
  (heisenbergNet_map f F.worldlines F.factors F.mechanism).symm

/-- Genuine Cauchy-determinacy at algebra grade, read off the image
fragment: transport the object once, and the time-slice theorem at the
image is an instance of the generic theorem — no per-clause transport
remains.  (The same proposition as the per-clause
`alg_eq_transport` route, by `map_mechanismNet`.) -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_alg
    (F : LCQFTFragment X n ι T κ) (f : X ≃o Y) {E D : Diamond X}
    (hle : E ≤ D) {t₀ : T} (hsl : CommonSlice F.worldlines t₀ E) :
    (F.map f).mechanismNet.alg (E.map f) =
      (F.map f).mechanismNet.alg (D.map f) :=
  (F.map f).timeslice_genuine_alg ((Diamond.map_le_map_iff f).mpr hle)
    (hsl.map f)

/-- Genuine Cauchy-determinacy at state grade, read off the image
fragment. -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_state
    (F : LCQFTFragment X n ι T κ) (f : X ≃o Y) {E D : Diamond X}
    (hle : E ≤ D) {t₀ : T} (hsl : CommonSlice F.worldlines t₀ E) :
    Function.Bijective (fun x =>
      (StatePresheaf (F.map f).mechanismNet).map
        (homOfLE ((Diamond.map_le_map_iff f).mpr hle)).op x) :=
  (F.map f).timeslice_genuine_state ((Diamond.map_le_map_iff f).mpr hle)
    (hsl.map f)

/-! ## The Minkowski dress: the two-qubit fragment at every translate

The strict-cone chronology is translation-invariant, so the canonical
pushforward kit is the original kit and every exhibit of the assembled
two-qubit fragment reappears at every translate as a projection of the
transported object. -/

/-- The Minkowski mixing kit is translation-invariant as an object:
its pushforward along any translation is itself. -/
theorem minkowskiKit_toMixingKit_map_translate (a v : ℝ) :
    ((minkowskiKit (E := ℝ)).toMixingKit).map (minkTranslate a v) =
      (minkowskiKit (E := ℝ)).toMixingKit :=
  MixingKit.ext fun x y => by
    show Mink.chron ((minkTranslate a v).symm x)
        ((minkTranslate a v).symm y) ↔ Mink.chron x y
    rw [minkTranslate_chron_iff a v]
    simp

/-- Genuine Cauchy-determinacy at every Minkowski translate, read
through the transported fragment object. -/
theorem isingQubitFragment_map_slice_determinacy (a v : ℝ) :
    (isingQubitFragment.map (minkTranslate a v)).mechanismNet.alg
        (Eslice.map (minkTranslate a v)) =
      (isingQubitFragment.map (minkTranslate a v)).mechanismNet.alg
        (Dstar.map (minkTranslate a v)) :=
  LCQFTFragment.map_timeslice_genuine_alg isingQubitFragment
    (minkTranslate a v) Eslice_le_Dstar qubitWorldline_commonSlice_Eslice

/-- Derived-cover separation at every translate, as a projection of
the transported fragment (the translation-invariance of the kit turns
the object's own separation clause into a statement at the original
Minkowski topology). -/
theorem isingQubitFragment_map_separation (a v : ℝ) :
    ∀ S ∈ ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology
        (Dstar.map (minkTranslate a v)),
      SeparatesSieve (qubitNet.map (minkTranslate a v))
        (Dstar.map (minkTranslate a v)) S := by
  rw [← minkowskiKit_toMixingKit_map_translate a v]
  exact (isingQubitFragment.map (minkTranslate a v)).separation

/-- Class-level Einstein causality at the translated site diamonds:
the causality clause of the transported fragment, at the transported
witness pair. -/
theorem isingQubitFragment_map_causality_point_pair (a v : ℝ) :
    ∀ x ∈ (qubitNet.map (minkTranslate a v)).alg
        (Dp.map (minkTranslate a v)),
      ∀ y ∈ (qubitNet.map (minkTranslate a v)).alg
          (Dq.map (minkTranslate a v)), Commute x y :=
  (isingQubitFragment.map (minkTranslate a v)).einstein_causality
    (pointwise_spacelike_map (minkTranslate a v) Dp_Dq_pointwise_spacelike)

/-- **The record thesis at every translate**: the transported
fragment's record shadow separates the Bell and maximally mixed
classes.  The proof term is the landed separation itself — records and
states ride the pushforward unchanged, so the transported shadow is
definitionally the original shadow on representatives. -/
theorem isingQubitFragment_map_shadow_separates_bell_mixed (a v : ℝ) :
    (isingQubitFragment.map (minkTranslate a v)).shadow
        (stateClassMk (qubitNet.map (minkTranslate a v))
          (Dstar.map (minkTranslate a v)) ⟨bell, bell_isState⟩) ≠
      (isingQubitFragment.map (minkTranslate a v)).shadow
        (stateClassMk (qubitNet.map (minkTranslate a v))
          (Dstar.map (minkTranslate a v)) ⟨mixed, mixed_isState⟩) :=
  recordShadowQ_separates_bell_mixed

end QuantumFunctoriality
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_iff
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_iff'
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_symm_iff
#print axioms Qtsl.QuantumDescent.ObservableNet.ext
#print axioms Qtsl.QuantumDescent.MixingKit.ext
#print axioms Qtsl.DiamondSite.Diamond.map_refl
#print axioms Qtsl.DiamondSite.Diamond.map_trans
#print axioms Qtsl.QuantumDescent.ObservableNet.map_refl
#print axioms Qtsl.QuantumDescent.ObservableNet.map_trans
#print axioms Qtsl.QuantumDescent.MixingKit.map_refl
#print axioms Qtsl.QuantumDescent.MixingKit.map_trans
#print axioms Qtsl.QuantumFunctoriality.heisenbergNet_map_alg
#print axioms Qtsl.QuantumFunctoriality.heisenbergNet_map
#print axioms Qtsl.QuantumDeterminacy.CommonSlice.map
#print axioms Qtsl.QuantumFunctoriality.pointwise_spacelike_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_refl
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_trans
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_alg
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_state
#print axioms Qtsl.QuantumFunctoriality.minkowskiKit_toMixingKit_map_translate
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_slice_determinacy
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_separation
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_causality_point_pair
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_shadow_separates_bell_mixed
