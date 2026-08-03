import QtslAux.QuantumEmbedding

/-! # Subregion extension: the covariant fragment map

`QtslAux.QuantumEmbedding` mechanized the contravariant fragment map
along a causally convex embedding — restriction, where the record
family can no longer ride unchanged.  This module mechanizes the
covariant direction: *extending* a subregion fragment's data to the
larger carrier along the same morphism class.

**The extension is a pointwise left Kan extension.**  For an
observable net `N` on the region, the extended algebra at an ambient
diamond `E` is the join of the region's algebras over every region
diamond whose image sits inside `E`:

`(N.extend f).alg E = ⨆ D : {D // D.push f ≤ E}, N.alg D`

— the colimit formula for a left Kan extension over the diamond image
functor, with the colimit computed in the complete lattice of
subalgebras.  The name is earned by theorems, not analogy:
`extend_alg_le_iff` is the adjunction (extension is left adjoint to
restriction, stated pointwise), and `restrict_extend` is the
*invertible unit* — extension followed by restriction is the identity
on the nose, exactly because the diamond image functor is fully
faithful (`Diamond.push_le_push_iff`, order reflection).  The counit
stays an inequality at net grade (`extend_restrict_alg_le`: a general
ambient net holds information outside the region) and upgrades to an
equality precisely on fragment nets (`extend_restrict_net`): the
frozen-shadow tie pins the kinematic tier to the matter sites, and all
the matter sites lie in the region — **the kinematic tier of a
restricted fragment regenerates the ambient net exactly.**

**The mirror asymmetry.**  Restriction demanded three obligation
families (matter locality through a forced time re-indexing, region
certificates, record transport).  Extension demands exactly one: a
chronology `M'` on the larger carrier restricting to the region's
(`hkit`).  Everything else rides or derives —

* matter pushes forward with its own time index (no sojourn problem:
  the larger carrier contains the whole image history, so the
  Heisenberg-net commute lemma `heisenbergNet_extend` needs *no*
  exhaustion hypothesis, in contrast to its restriction-side twin);
* the region's ambient and witness diamonds ride as image diamonds,
  with attainment derived from the invertible unit;
* **the record obligation of the restriction is discharged by theorem
  here**: records are local to the image ambient because they were
  local to the region's — records restrict only under obligation
  (`record_obligation_fails_at_D₁`) but extend for free.  Measurement
  outcomes remain accessible in any larger region.

The one obligation is genuine: the region's chronology says nothing
about events outside its image, so the ambient chronology is new data,
and the compatibility certificate cannot be dropped
(`emptyMixingKit_pullback_ne` witnesses ambient kits whose pullback
differs — the chronology cannot ride unchanged into the larger
carrier).  It is also a genuine *choice*: two distinct lawful ambient
chronologies restrict to the same region kit
(`exists_distinct_kits_same_pullback`), and the two fragment
extensions along them share one net definitionally while remaining
distinct fragments — extension is canonical at net grade and
underdetermined at kit grade.

**Einstein causality descends through centralizers.**  Membership in a
join of subalgebras does not destructure to membership in one summand,
so class-level causality lifts to the extension by a double descent
through `Subalgebra.centralizer` (`commute_of_mem_iSup`), with the
spacelike hypothesis transported to preimage diamonds by order
reflection.  Notably, no proof in this module consumes the diamond
condition (`convex`): at this grade the covariant direction uses only
the order embedding, and causal convexity is a restriction-side
phenomenon.

**Scope, stated deliberately.**  The extension takes the *minimal*
canonical certificates — its ambient diamond is the image of the
region's, so it certifies separation and records exactly where the
region did, no further.  The mechanism tier does not round-trip in the
extend-after-restrict order: a worldline exiting the region carries
dynamics the region never saw (the sojourn problem), and the
fragment-grade statement is not even well-typed once the restriction
re-indexes time — `extend_restrict_net` (kinematic tier only) is the
maximal honest form, the kinematic/dynamic split of the restriction
module reproduced in the Kan round trip.  Embeddings between
different geometries remain fenced on the missing second exact-order
carrier. -/

namespace Qtsl
namespace QuantumExtension

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates
open QuantumCovariance QuantumDeterminacy QuantumAssembly
open QuantumEmbedding
open scoped ComplexOrder Kronecker

variable {X Y Z : Type*} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Kan extension at net grade -/

/-- Extension of an observable net along a causal embedding: an
ambient diamond reads the join of the region's algebras over every
region diamond whose image it contains — the pointwise left Kan
extension over the diamond image functor, computed in the complete
lattice of subalgebras.  Isotony is monotonicity of the index set. -/
noncomputable def _root_.Qtsl.QuantumDescent.ObservableNet.extend
    (f : CausalEmbedding X Y) (N : ObservableNet X n) :
    ObservableNet Y n where
  alg E := ⨆ p : {D : Diamond X // D.push f ≤ E}, N.alg p.1
  isotone {_E E'} h := iSup_le fun p =>
    le_iSup (fun q : {D : Diamond X // D.push f ≤ E'} => N.alg q.1)
      ⟨p.1, p.2.trans h⟩

/-- The pointwise-colimit formula, kernel-visible. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_alg
    (f : CausalEmbedding X Y) (N : ObservableNet X n) (E : Diamond Y) :
    (N.extend f).alg E =
      ⨆ p : {D : Diamond X // D.push f ≤ E}, N.alg p.1 := rfl

/-- **The invertible unit, algebra form**: at an image diamond the
extension reads exactly the region's algebra.  The `≤` leg consumes
order reflection (`Diamond.push_le_push_iff`) — full faithfulness of
the diamond image functor, the textbook condition for a Kan extension
along a fully faithful functor to restrict back to the original. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_alg_push
    (f : CausalEmbedding X Y) (N : ObservableNet X n) (D : Diamond X) :
    (N.extend f).alg (D.push f) = N.alg D := by
  refine le_antisymm (iSup_le fun p => ?_) ?_
  · exact N.isotone ((Diamond.push_le_push_iff f).mp p.2)
  · exact le_iSup
      (fun q : {D' : Diamond X // D'.push f ≤ D.push f} => N.alg q.1)
      ⟨D, le_rfl⟩

/-- **The invertible unit**: extension followed by restriction is the
identity on observable nets. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.restrict_extend
    (f : CausalEmbedding X Y) (N : ObservableNet X n) :
    (N.extend f).restrict f = N :=
  ObservableNet.ext fun D => N.extend_alg_push f D

/-- The counit inequality: restricting and re-extending recovers at
most the original — a general ambient net holds information outside
the region. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_restrict_alg_le
    (f : CausalEmbedding X Y) (N : ObservableNet Y n) (E : Diamond Y) :
    ((N.restrict f).extend f).alg E ≤ N.alg E :=
  iSup_le fun p => N.isotone p.2

/-- **The adjunction**: extension is left adjoint to restriction, in
the pointwise order on algebra assignments — the universal property
that earns `extend` the name "Kan extension". -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_alg_le_iff
    (f : CausalEmbedding X Y) (N : ObservableNet X n)
    (N' : ObservableNet Y n) :
    (∀ E, (N.extend f).alg E ≤ N'.alg E) ↔
      ∀ D, N.alg D ≤ (N'.restrict f).alg D := by
  constructor
  · intro h D
    exact le_trans
      (le_iSup
        (fun q : {D' : Diamond X // D'.push f ≤ D.push f} => N.alg q.1)
        ⟨D, le_rfl⟩)
      (h (D.push f))
  · intro h E
    exact iSup_le fun p => le_trans (h p.1) (N'.isotone p.2)

/-- Identity law.  Not definitional — the extension is a genuine
join, collapsed by antisymmetry. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_id
    (N : ObservableNet X n) : N.extend (CausalEmbedding.id X) = N :=
  ObservableNet.ext fun D =>
    le_antisymm (iSup_le fun p => N.isotone p.2)
      (le_iSup
        (fun q : {D' : Diamond X //
          D'.push (CausalEmbedding.id X) ≤ D} => N.alg q.1)
        ⟨D, le_rfl⟩)

/-- Composition law, covariant: extending along a composite is
extending in stages. -/
theorem _root_.Qtsl.QuantumDescent.ObservableNet.extend_comp
    (g : CausalEmbedding Y Z) (f : CausalEmbedding X Y)
    (N : ObservableNet X n) :
    N.extend (g.comp f) = (N.extend f).extend g := by
  refine ObservableNet.ext fun E =>
    le_antisymm (iSup_le fun p => ?_) (iSup_le fun q => iSup_le fun r => ?_)
  · refine le_trans ?_
      (le_iSup
        (fun q : {D' : Diamond Y // D'.push g ≤ E} =>
          (N.extend f).alg q.1)
        ⟨p.1.push f, p.2⟩)
    exact le_iSup
      (fun r : {D' : Diamond X // D'.push f ≤ p.1.push f} => N.alg r.1)
      ⟨p.1, le_rfl⟩
  · exact le_iSup
      (fun s : {D : Diamond X // D.push (g.comp f) ≤ E} => N.alg s.1)
      ⟨r.1, le_trans ((Diamond.push_le_push_iff g).mpr r.2) q.2⟩

/-! ## The Heisenberg tier: the extension commute lemma

Unconditional, in contrast to the restriction-side twin
(`heisenbergNet_restrict_of_exhaustive`): the covariant direction has
no sojourn problem, because the larger carrier contains every crossing
of the image worldlines. -/

variable {ι T κ : Type*} [Fintype κ]

/-- **The Heisenberg net commutes with extension** — no exhaustion
hypothesis: extending the net of a mechanism is rebuilding the net
from the pushed-forward worldlines, with the same time index.  The
`≥` leg is the degenerate diamond at each crossing. -/
theorem heisenbergNet_extend (f : CausalEmbedding X Y) (w : ι → T → X)
    (B : ι → Subalgebra ℂ (Matrix n n ℂ))
    (τ : T → (Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)) :
    (heisenbergNet w B τ).extend f =
      heisenbergNet (fun i t => f (w i t)) B τ :=
  ObservableNet.ext fun E => by
    refine le_antisymm (iSup_le fun p => iSup_le fun pc => ?_)
      (iSup_le fun pc => ?_)
    · exact factor_le_heisenbergNet_alg (w := fun i t => f (w i t))
        (B := B) (τ := τ) (i := pc.1.1) (t := pc.1.2)
        (inDiamond_mono p.2 ((inDiamond_push_iff f).mpr pc.2))
    · refine le_trans (factor_le_heisenbergNet_alg (w := w) (B := B)
        (τ := τ) (D := ⟨w pc.1.1 pc.1.2, w pc.1.1 pc.1.2, le_rfl⟩)
        (i := pc.1.1) (t := pc.1.2) ⟨le_rfl, le_rfl⟩) ?_
      exact le_iSup
        (fun q : {D : Diamond X // D.push f ≤ E} =>
          (heisenbergNet w B τ).alg q.1)
        ⟨⟨w pc.1.1 pc.1.2, w pc.1.1 pc.1.2, le_rfl⟩, pc.2⟩

/-! ## Commutation descends through joins of subalgebras -/

/-- The commutant of a fixed matrix, as a subalgebra — self-contained,
so that the double descent below can apply `iSup_le` to
"commutes-with-`b`". -/
def commutant (b : Matrix n n ℂ) : Subalgebra ℂ (Matrix n n ℂ) where
  carrier := {z | b * z = z * b}
  mul_mem' := fun {x y} hx hy => by
    have hx' : b * x = x * b := hx
    have hy' : b * y = y * b := hy
    show b * (x * y) = x * y * b
    rw [← mul_assoc, hx', mul_assoc, hy', mul_assoc]
  one_mem' := by show b * 1 = 1 * b; rw [mul_one, one_mul]
  add_mem' := fun {x y} hx hy => by
    have hx' : b * x = x * b := hx
    have hy' : b * y = y * b := hy
    show b * (x + y) = (x + y) * b
    rw [mul_add, add_mul, hx', hy']
  zero_mem' := by show b * 0 = 0 * b; rw [mul_zero, zero_mul]
  algebraMap_mem' := fun r => (Algebra.commutes r b).symm

/-- Commutant membership, unfolded. -/
theorem mem_commutant {b z : Matrix n n ℂ} :
    z ∈ commutant b ↔ b * z = z * b := Iff.rfl

/-- **Double commutant descent**: elementwise commutation between two
families of subalgebras lifts to their joins.  Membership in a join
does not destructure to membership in a summand; the descent routes
through the commutant subalgebra twice — once to place the second
join inside the commutant of each first-family element, once to place
the first join inside the commutant of the fixed element of the
second. -/
theorem commute_of_mem_iSup {ι₁ ι₂ : Sort*}
    {S : ι₁ → Subalgebra ℂ (Matrix n n ℂ)}
    {T' : ι₂ → Subalgebra ℂ (Matrix n n ℂ)}
    (h : ∀ j k, ∀ a ∈ S j, ∀ b ∈ T' k, Commute a b)
    {a b : Matrix n n ℂ} (ha : a ∈ ⨆ j, S j) (hb : b ∈ ⨆ k, T' k) :
    Commute a b := by
  have hstep : ∀ j, ∀ x ∈ S j, x * b = b * x := by
    intro j x hx
    have hT : (⨆ k, T' k) ≤ commutant x := by
      refine iSup_le fun k => ?_
      intro y hy
      exact mem_commutant.mpr (h j k x hx y hy)
    exact mem_commutant.mp (hT hb)
  have hS : (⨆ j, S j) ≤ commutant b := by
    refine iSup_le fun j => ?_
    intro x hx
    exact mem_commutant.mpr (hstep j x hx).symm
  exact (mem_commutant.mp (hS ha)).symm

/-! ## The fragment extension

One obligation — the ambient chronology with its compatibility
certificate.  Everything else rides or derives. -/

/-- **The sites formula** — the degenerate-diamond mechanism: the
extension of a fragment's net computes to conditional factor joins
over the *pushed sites*.  The `≥` leg extends each in-region site
through its degenerate diamond, whose image lies in `E` exactly when
the pushed site does; the `≤` leg is the frozen shadow of the region
read through membership transport.  This one lemma discharges both
the frozen-shadow and the time-slice fields of the extension. -/
theorem extend_alg_eq_sites [Nonempty T] (f : CausalEmbedding X Y)
    (F : LCQFTFragment X n ι T κ) (E : Diamond Y) :
    (F.net.extend f).alg E =
      ⨆ i, ⨆ _ : inDiamond (f (F.sites i)) E, F.factors i := by
  refine le_antisymm (iSup_le fun p => ?_) (iSup₂_le fun i h => ?_)
  · rw [← F.frozen_shadow p.1, heisenbergNet_const_alg]
    exact iSup₂_le fun i h => le_iSup₂
      (f := fun i' (_ : inDiamond (f (F.sites i')) E) => F.factors i') i
      (inDiamond_mono p.2 ((inDiamond_push_iff f).mpr h))
  · have hfac : F.factors i ≤
        F.net.alg ⟨F.sites i, F.sites i, le_rfl⟩ := by
      rw [← F.frozen_shadow ⟨F.sites i, F.sites i, le_rfl⟩,
        heisenbergNet_const_alg]
      exact le_iSup₂
        (f := fun i' (_ : inDiamond (F.sites i')
          (⟨F.sites i, F.sites i, le_rfl⟩ : Diamond X)) => F.factors i')
        i ⟨le_rfl, le_rfl⟩
    exact le_trans hfac (le_iSup
      (fun q : {D : Diamond X // D.push f ≤ E} => F.net.alg q.1)
      ⟨⟨F.sites i, F.sites i, le_rfl⟩, h⟩)

/-- **A kinematic fragment extends along a causal embedding** — the
covariant fragment map.  After the embedding, the single obligation:
an ambient chronology `M'` restricting to the region's (`hkit`).  The
matter pushes forward with its own time index; the region's ambient
and witness ride as image diamonds with attainment derived from the
invertible unit; and the record family is local to the image ambient
*by theorem* — the restriction module's record-transport obligation,
discharged for free in the covariant direction. -/
noncomputable def _root_.Qtsl.QuantumAssembly.LCQFTFragment.extend
    (F : LCQFTFragment X n ι T κ) (f : CausalEmbedding X Y) [Nonempty T]
    (M' : MixingKit Y) (hkit : M'.pullback f = F.kit) :
    LCQFTFragment Y n ι T κ where
  net := F.net.extend f
  sites := fun i => f (F.sites i)
  worldlines := fun i t => f (F.worldlines i t)
  factors := F.factors
  mechanism := F.mechanism
  sites_on_worldlines := fun i =>
    (F.sites_on_worldlines i).imp fun _ ht => congrArg f ht
  factors_exhaustive := F.factors_exhaustive
  frozen_shadow := fun E => by
    show (heisenbergNet (fun i (_ : T) => f (F.sites i)) F.factors
        (fun _ => AlgEquiv.refl)).alg E = (F.net.extend f).alg E
    rw [heisenbergNet_const_alg, extend_alg_eq_sites f F E]
  einstein_causality := fun {E₁ E₂} hsp a ha b hb =>
    commute_of_mem_iSup
      (S := fun p : {D : Diamond X // D.push f ≤ E₁} => F.net.alg p.1)
      (T' := fun q : {D : Diamond X // D.push f ≤ E₂} => F.net.alg q.1)
      (fun p q => F.einstein_causality (fun r s hr hs => by
        have hsep := hsp (inDiamond_mono p.2 ((inDiamond_push_iff f).mpr hr))
          (inDiamond_mono q.2 ((inDiamond_push_iff f).mpr hs))
        exact ⟨fun hle => hsep.1 (f.mono hle),
          fun hle => hsep.2 (f.mono hle)⟩))
      ha hb
  timeslice_surrogate := fun {E D} hle hsit => by
    show (F.net.extend f).alg E = (F.net.extend f).alg D
    rw [extend_alg_eq_sites f F E, extend_alg_eq_sites f F D]
    exact iSup_congr fun i => iSup_congr_Prop
      ⟨inDiamond_mono hle, hsit i⟩ (fun _ => rfl)
  kit := M'
  ambient := F.ambient.push f
  interior_witness := F.interior_witness.push f
  interior_mem :=
    (MixingKit.pullback_interiorMem_iff f M').mp (hkit.symm ▸ F.interior_mem)
  interior_attained := by
    rw [ObservableNet.extend_alg_push, ObservableNet.extend_alg_push]
    exact F.interior_attained
  records := F.records
  records_mem := fun α => by
    rw [ObservableNet.extend_alg_push]
    exact F.records_mem α
  records_posSemidef := F.records_posSemidef
  records_exhaustive := F.records_exhaustive

section ExtendProjections

variable (F : LCQFTFragment X n ι T κ) (f : CausalEmbedding X Y)
  [Nonempty T] (M' : MixingKit Y) (hkit : M'.pullback f = F.kit)

/-- The extended net's algebra is the pointwise colimit — `rfl`. -/
theorem extend_net_alg (E : Diamond Y) :
    (F.extend f M' hkit).net.alg E =
      ⨆ p : {D : Diamond X // D.push f ≤ E}, F.net.alg p.1 := rfl

/-- The record family rides extension unchanged as matrices — `rfl`;
its locality at the image ambient is a theorem, not an obligation. -/
theorem extend_records : (F.extend f M' hkit).records = F.records := rfl

/-- The extended sites are the pushed sites — `rfl`. -/
theorem extend_sites :
    (F.extend f M' hkit).sites = fun i => f (F.sites i) := rfl

/-- The extended ambient is the image of the region's — `rfl`: the
extension certifies exactly where the region did. -/
theorem extend_ambient :
    (F.extend f M' hkit).ambient = F.ambient.push f := rfl

/-- **The two tiers extend coherently, unconditionally**: the
mechanism net of the extended fragment is the extension of the
region's mechanism net — no sojourn-exhaustion hypothesis, in
contrast to the restriction-side `restrict_mechanismNet`. -/
theorem extend_mechanismNet :
    (F.extend f M' hkit).mechanismNet = F.mechanismNet.extend f :=
  (heisenbergNet_extend f F.worldlines F.factors F.mechanism).symm

end ExtendProjections

/-! ## Fragment extensionality and the round trip -/

/-- A kinematic fragment is determined by its data fields: the nine
non-propositional fields fix the object (the certificate fields are
proof-irrelevant). -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.ext
    {F G : LCQFTFragment X n ι T κ}
    (hnet : F.net = G.net) (hsites : F.sites = G.sites)
    (hworldlines : F.worldlines = G.worldlines)
    (hfactors : F.factors = G.factors)
    (hmechanism : F.mechanism = G.mechanism)
    (hkit : F.kit = G.kit) (hambient : F.ambient = G.ambient)
    (hwitness : F.interior_witness = G.interior_witness)
    (hrecords : F.records = G.records) : F = G := by
  cases F
  cases G
  dsimp only at hnet hsites hworldlines hfactors hmechanism hkit hambient hwitness hrecords
  subst hnet hsites hworldlines hfactors hmechanism hkit hambient hwitness hrecords
  rfl

section RoundTrip

variable (F : LCQFTFragment X n ι T κ) (f : CausalEmbedding X Y)
  [Nonempty T] (M' : MixingKit Y) (hkit : M'.pullback f = F.kit)

/-- The extension's kit pulls back to the region's — the restriction
obligation slot, discharged at the extension. -/
theorem extend_pullback_interiorMem :
    (((F.extend f M' hkit).kit).pullback f).interiorMem
      F.ambient F.interior_witness :=
  hkit.symm ▸ F.interior_mem

/-- The extension attains its interior witness at the image diamonds —
the restriction obligation slot, discharged at the extension. -/
theorem extend_push_attained :
    (F.extend f M' hkit).net.alg (F.ambient.push f) ≤
      (F.extend f M' hkit).net.alg (F.interior_witness.push f) := by
  show (F.net.extend f).alg _ ≤ (F.net.extend f).alg _
  rw [ObservableNet.extend_alg_push, ObservableNet.extend_alg_push]
  exact F.interior_attained

/-- The extension's records are local to the image ambient — the
record-transport obligation of the restriction module, discharged by
theorem in the covariant direction. -/
theorem extend_push_records :
    ∀ α, (F.extend f M' hkit).records α ∈
      (F.extend f M' hkit).net.alg (F.ambient.push f) := fun α => by
  show F.records α ∈ (F.net.extend f).alg _
  rw [ObservableNet.extend_alg_push]
  exact F.records_mem α

/-- **The round trip is the identity at full fragment grade**:
extending a fragment and restricting back along the same embedding —
with the region's own matter, certificates, and the discharged
obligation slots — recovers the fragment on the nose.  The only
non-definitional components are the net (the invertible unit) and the
kit (the compatibility certificate). -/
theorem _root_.Qtsl.QuantumAssembly.LCQFTFragment.restrict_extend :
    (F.extend f M' hkit).restrict f (fun t => t) F.worldlines
      (fun _ _ => rfl) F.sites (fun _ => rfl) F.sites_on_worldlines
      F.ambient F.interior_witness
      (extend_pullback_interiorMem F f M' hkit)
      (extend_push_attained F f M' hkit)
      (extend_push_records F f M' hkit) = F :=
  LCQFTFragment.ext (ObservableNet.restrict_extend f F.net)
    rfl rfl rfl rfl hkit rfl rfl rfl

end RoundTrip

/-- Identity law at fragment grade: extending along the identity
embedding, with the region's own kit, is the identity. -/
theorem extend_id_frag [Nonempty T] (F : LCQFTFragment X n ι T κ) :
    F.extend (CausalEmbedding.id X) F.kit (MixingKit.pullback_id F.kit)
      = F :=
  LCQFTFragment.ext (ObservableNet.extend_id F.net)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- Composition law at fragment grade: extending in stages is
extending along the composite, with the composite compatibility
certificate. -/
theorem extend_comp_frag [Nonempty T] (F : LCQFTFragment X n ι T κ)
    (f : CausalEmbedding X Y) (g : CausalEmbedding Y Z)
    (M₁ : MixingKit Y) (h₁ : M₁.pullback f = F.kit)
    (M₂ : MixingKit Z) (h₂ : M₂.pullback g = M₁) :
    (F.extend f M₁ h₁).extend g M₂ h₂ =
      F.extend (g.comp f) M₂
        (by rw [MixingKit.pullback_comp, h₂, h₁]) :=
  LCQFTFragment.ext (ObservableNet.extend_comp g f F.net).symm
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- **The counit upgrades to an equality on fragment nets**: the
extension of a restricted fragment's net is the ambient net, exactly —
the frozen-shadow tie pins the kinematic tier to the matter sites, and
the restriction's matter-locality data places every site in the
region.  (The mechanism tier does not round-trip this way: dynamics
outside the region is unrecoverable — the kinematic/dynamic split,
reproduced in the Kan round trip.) -/
theorem extend_restrict_net {T' : Type*} [Nonempty T']
    (G : LCQFTFragment Y n ι T κ) (f : CausalEmbedding X Y) (θ : T' → T)
    (w : ι → T' → X) (hw : ∀ i t', f (w i t') = G.worldlines i (θ t'))
    (s : ι → X) (hs : ∀ i, f (s i) = G.sites i)
    (hsw : ∀ i, ∃ t', w i t' = s i) (A W : Diamond X)
    (hint : (G.kit.pullback f).interiorMem A W)
    (hatt : G.net.alg (A.push f) ≤ G.net.alg (W.push f))
    (hrec : ∀ α, G.records α ∈ G.net.alg (A.push f)) :
    ((G.restrict f θ w hw s hs hsw A W hint hatt hrec).net).extend f =
      G.net :=
  ObservableNet.ext fun E => by
    have hT : Nonempty T := ⟨θ (Classical.arbitrary T')⟩
    rw [extend_alg_eq_sites f
        (G.restrict f θ w hw s hs hsw A W hint hatt hrec) E,
      ← G.frozen_shadow E, heisenbergNet_const_alg]
    exact iSup_congr fun i => iSup_congr_Prop
      (by rw [← hs i]; exact Iff.rfl) (fun _ => rfl)

/-! ## The Minkowski instance: the sub-diamond fragment, extended back

The two-qubit fragment restricted to its own ambient sub-diamond
(`isingQubitFragmentOnDstar`), extended back into Minkowski space
along the inclusion.  The kit obligation is discharged by the
Minkowski chronology itself — the restricted kit is definitionally its
pullback — and the kinematic net regenerates `qubitNet` exactly. -/

/-- The sub-diamond fragment, extended back into Minkowski space. -/
noncomputable def isingExtendedFragment :
    LCQFTFragment (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) DstarSojourn
      (Fin 2 × Fin 2) :=
  isingQubitFragmentOnDstar.extend Dstar.inclusionEmbedding
    ((minkowskiKit (E := ℝ)).toMixingKit) rfl

/-- **The sub-spacetime fragment regenerates the ambient kinematic net
on the nose**: extending the restricted net recovers `qubitNet` — the
matter sites pin the kinematic tier, and both live in the region. -/
theorem isingExtended_net : isingExtendedFragment.net = qubitNet :=
  extend_restrict_net isingQubitFragment Dstar.inclusionEmbedding
    (fun t' : DstarSojourn => t'.1) dstarWorldlines (fun _ _ => rfl)
    dstarSites dstarSites_map dstarSites_on_worldlines
    Dstar.selfDiamond (Diamond.liftOfLe E₃_le_Dstar)
    E₃_interior dstar_attained (fun α => zzRecord_mem_top α)

/-- The round trip at the instance: restricting the extended fragment
back to the sub-diamond recovers the restricted fragment exactly. -/
theorem isingExtended_restrict :
    isingExtendedFragment.restrict Dstar.inclusionEmbedding
      (fun t => t) isingQubitFragmentOnDstar.worldlines (fun _ _ => rfl)
      isingQubitFragmentOnDstar.sites (fun _ => rfl)
      isingQubitFragmentOnDstar.sites_on_worldlines
      isingQubitFragmentOnDstar.ambient
      isingQubitFragmentOnDstar.interior_witness
      (extend_pullback_interiorMem isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding
        ((minkowskiKit (E := ℝ)).toMixingKit) rfl)
      (extend_push_attained isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding
        ((minkowskiKit (E := ℝ)).toMixingKit) rfl)
      (extend_push_records isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding
        ((minkowskiKit (E := ℝ)).toMixingKit) rfl) =
      isingQubitFragmentOnDstar :=
  LCQFTFragment.restrict_extend isingQubitFragmentOnDstar
    Dstar.inclusionEmbedding ((minkowskiKit (E := ℝ)).toMixingKit) rfl

/-- **The record thesis survives extension**: the extended fragment's
record shadow separates the Bell and maximally-mixed classes at the
ambient diamond, by the *same proof term* as the original theorem —
the Born row sees neither the carrier (the restriction module's
finding) nor the net's Kan dressing: records and representatives are
global, and the shadow reduces through the quotient before the net is
ever consulted. -/
theorem isingExtended_shadow_separates_bell_mixed :
    isingExtendedFragment.shadow
        (stateClassMk isingExtendedFragment.net Dstar
          ⟨bell, bell_isState⟩) ≠
      isingExtendedFragment.shadow
        (stateClassMk isingExtendedFragment.net Dstar
          ⟨mixed, mixed_isState⟩) :=
  recordShadowQ_separates_bell_mixed

/-- **Genuine Cauchy determinacy of the extended fragment** at the
ambient carrier's own slice diamond: pure consumption of the generic
time-slice theorem — the extended matter carries its sojourn time
index, and the slice at time `1` covers it. -/
theorem isingExtended_slice_determinacy :
    isingExtendedFragment.mechanismNet.alg Eslice =
      isingExtendedFragment.mechanismNet.alg Dstar :=
  isingExtendedFragment.timeslice_genuine_alg Eslice_le_Dstar
    (t₀ := ⟨1, by norm_num⟩)
    (fun i => qubitWorldline_commonSlice_Eslice i)

/-! ## The obligation is genuine: chronology does not ride -/

/-- The empty chronology: a mixing kit with no chronological pairs —
every law holds vacuously. -/
def emptyMixingKit (X : Type*) [PartialOrder X] : MixingKit X where
  chron _ _ := False
  le_of_chron h := h.elim
  chron_of_le_chron _ h := h
  chron_of_chron_le h _ := h
  interpolate h := h.elim

/-- **The kit obligation is non-vacuous**: ambient chronologies whose
pullback differs from the region's exist — the empty chronology on
Minkowski space pulls back without the region's interiority pair, so
the compatibility certificate `hkit` is genuine data.  The chronology
cannot ride unchanged into the larger carrier. -/
theorem emptyMixingKit_pullback_ne :
    (emptyMixingKit (Mink ℝ)).pullback Dstar.inclusionEmbedding ≠
      isingQubitFragmentOnDstar.kit := fun h => by
  have hchron : isingQubitFragmentOnDstar.kit.chron
      ⟨Dstar.lo, le_rfl, Dstar.le⟩
      ⟨E₃.lo, inDiamond_lo_of_le E₃_le_Dstar⟩ :=
    E₃_interior.1
  rw [← h] at hchron
  exact hchron

/-! ## The obligation is underdetermined: two chronologies, one region

`emptyMixingKit_pullback_ne` showed the compatibility certificate is
non-vacuous — ambient kits with the *wrong* pullback exist.  This
section shows the certificate is a genuine *choice*: two distinct
lawful ambient chronologies with the *same* pullback exist, so the
region's kit does not determine its ambient extension.  The witness is
the **future-restricted Minkowski kit**: the Minkowski chronology
conditioned to pairs whose upper event lies in the strict future of a
base event `z`.  For `z` strictly below the region the condition holds
throughout the region (absorption from the lower endpoint), so the
restriction is invisible from inside — yet the kits differ at
deep-past pairs outside the future of `z`.

Contrast the net: the extension's net field never consults the ambient
kit, so the two extensions of the sub-diamond fragment have
definitionally equal nets — and regenerate the ambient net by the same
proof term — while the fragments themselves are distinct.  **Extension
is canonical at net grade (a left Kan extension with invertible unit)
and non-canonical at kit grade: the coverage half of the extension is
genuinely new data.**

Structurally, the future-restriction must condition the *upper*
argument: the mixing laws make a chronology a two-sided ideal
(down-closed in the lower argument, up-closed in the upper), and the
strict future of `z` is up-closed only.  Interpolation is the one
field that costs geometry — a mixing kit deliberately has no
past-directedness (the filtered/directed fields feed sheaf descent,
never the coverage), so the interpolant cannot be assembled from kit
laws alone; it is built from concrete Minkowski arithmetic, as a
time-shifted copy of the upper event displaced by half the smaller
chronological slack. -/

section FutureKit

variable {E : Type*} [NormedAddCommGroup E]

/-- The Minkowski absorb law, weak-then-strict — self-contained at
`NormedAddCommGroup` (the packaged `minkowskiKit` carries a
`NormedSpace ℝ E` requirement its absorb laws never use). -/
theorem mink_chron_of_le_chron {a b c : Mink E} (h : a ≤ b)
    (h' : Mink.chron b c) : Mink.chron a c := by
  have h₁ : ‖b.x - a.x‖ ≤ b.t - a.t := h
  have h₂ : ‖c.x - b.x‖ < c.t - b.t := h'
  have htri : ‖c.x - a.x‖ ≤ ‖c.x - b.x‖ + ‖b.x - a.x‖ := by
    simpa using norm_add_le (c.x - b.x) (b.x - a.x)
  show ‖c.x - a.x‖ < c.t - a.t
  linarith

/-- The Minkowski absorb law, strict-then-weak — self-contained at
`NormedAddCommGroup`. -/
theorem mink_chron_of_chron_le {a b c : Mink E} (h : Mink.chron a b)
    (h' : b ≤ c) : Mink.chron a c := by
  have h₁ : ‖b.x - a.x‖ < b.t - a.t := h
  have h₂ : ‖c.x - b.x‖ ≤ c.t - b.t := h'
  have htri : ‖c.x - a.x‖ ≤ ‖c.x - b.x‖ + ‖b.x - a.x‖ := by
    simpa using norm_add_le (c.x - b.x) (b.x - a.x)
  show ‖c.x - a.x‖ < c.t - a.t
  linarith

/-- The **future-restricted Minkowski kit**: the Minkowski chronology
conditioned to pairs whose upper event lies in the strict
chronological future of a base event `z`.  A lawful mixing kit — the
absorb laws are triangle inequalities, and the interpolant is a
time-shifted copy of the upper event.  Note the instance economy: the
time shift never scales a spatial vector, so no `NormedSpace ℝ E` is
needed (contrast `minkowskiKit`'s midpoint interpolant). -/
def minkowskiFutureKit (z : Mink E) : MixingKit (Mink E) where
  chron p q := Mink.chron p q ∧ Mink.chron z q
  le_of_chron h := h.1.le
  chron_of_le_chron {_ _ _} hab hbc :=
    ⟨mink_chron_of_le_chron hab hbc.1, hbc.2⟩
  chron_of_chron_le {_ _ _} hab hbc :=
    ⟨mink_chron_of_chron_le hab.1 hbc,
      mink_chron_of_chron_le hab.2 hbc⟩
  interpolate {a b} h := by
    obtain ⟨hab, hzb⟩ := h
    have h₁ : ‖b.x - a.x‖ < b.t - a.t := hab
    have h₂ : ‖b.x - z.x‖ < b.t - z.t := hzb
    have hle₁ := min_le_left ((b.t - a.t) - ‖b.x - a.x‖)
      ((b.t - z.t) - ‖b.x - z.x‖)
    have hle₂ := min_le_right ((b.t - a.t) - ‖b.x - a.x‖)
      ((b.t - z.t) - ‖b.x - z.x‖)
    have hm : 0 < min ((b.t - a.t) - ‖b.x - a.x‖)
        ((b.t - z.t) - ‖b.x - z.x‖) :=
      lt_min (by linarith) (by linarith)
    refine ⟨⟨b.t - min ((b.t - a.t) - ‖b.x - a.x‖)
        ((b.t - z.t) - ‖b.x - z.x‖) / 2, b.x⟩,
      ⟨?_, ?_⟩, ?_, hzb⟩
    · show ‖b.x - a.x‖ < b.t - min ((b.t - a.t) - ‖b.x - a.x‖)
        ((b.t - z.t) - ‖b.x - z.x‖) / 2 - a.t
      linarith
    · show ‖b.x - z.x‖ < b.t - min ((b.t - a.t) - ‖b.x - a.x‖)
        ((b.t - z.t) - ‖b.x - z.x‖) / 2 - z.t
      linarith
    · show ‖b.x - b.x‖ < b.t - (b.t - min ((b.t - a.t) - ‖b.x - a.x‖)
        ((b.t - z.t) - ‖b.x - z.x‖) / 2)
      rw [sub_self, norm_zero]
      linarith

/-- The future-restricted chronology, unfolded. -/
theorem minkowskiFutureKit_chron_iff (z p q : Mink E) :
    (minkowskiFutureKit z).chron p q ↔
      Mink.chron p q ∧ Mink.chron z q := Iff.rfl

end FutureKit

/-- A base event strictly below the region: the deep-past anchor of
the future-restricted kit. -/
def zPast : Mink ℝ := ⟨-4, 0⟩

/-- The base event lies strictly below the region's lower endpoint. -/
theorem zPast_chron_lo : Mink.chron zPast Dstar.lo := by
  show ‖(0 : ℝ) - 0‖ < (-3 : ℝ) - (-4)
  rw [Real.norm_eq_abs]
  norm_num

/-- **Two chronologies, one region kit**: the future-restricted kit at
`zPast` pulls back to exactly the sub-diamond fragment's kit — the
future of `zPast` contains the whole region (absorption from the lower
endpoint), so the restriction is invisible from inside the region. -/
theorem minkowskiFutureKit_pullback_eq :
    (minkowskiFutureKit zPast).pullback Dstar.inclusionEmbedding =
      isingQubitFragmentOnDstar.kit :=
  MixingKit.ext fun a b => by
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, mink_chron_of_chron_le zPast_chron_lo b.2.1⟩

/-- **The two kits are distinct**: the deep-past pair
`⟨-10,0⟩ ≪ ⟨-9,0⟩` is chronological for the Minkowski kit but lies
outside the future of `zPast`, so the future-restricted kit refuses
it. -/
theorem minkowskiFutureKit_ne :
    minkowskiFutureKit zPast ≠ (minkowskiKit (E := ℝ)).toMixingKit :=
  fun h => by
    have hchron : (minkowskiFutureKit zPast).chron ⟨-10, 0⟩ ⟨-9, 0⟩ := by
      rw [h]
      show ‖(0 : ℝ) - 0‖ < (-9 : ℝ) - (-10)
      rw [Real.norm_eq_abs]
      norm_num
    have h₂ : ‖(0 : ℝ) - 0‖ < (-9 : ℝ) - (-4) := hchron.2
    rw [Real.norm_eq_abs] at h₂
    norm_num at h₂

/-- **The kit obligation is genuinely underdetermined**: two distinct
lawful ambient chronologies with the same pullback — the region's kit
does not determine its ambient extension.  (Contrast the net, whose
extension is canonical: the pointwise left Kan extension, with
invertible unit.) -/
theorem exists_distinct_kits_same_pullback :
    ∃ M₁ M₂ : MixingKit (Mink ℝ), M₁ ≠ M₂ ∧
      M₁.pullback Dstar.inclusionEmbedding =
        isingQubitFragmentOnDstar.kit ∧
      M₂.pullback Dstar.inclusionEmbedding =
        isingQubitFragmentOnDstar.kit :=
  ⟨minkowskiFutureKit zPast, (minkowskiKit (E := ℝ)).toMixingKit,
    minkowskiFutureKit_ne, minkowskiFutureKit_pullback_eq, rfl⟩

/-- The extension's kit is the supplied ambient kit — `rfl` (the
projection the non-uniqueness pair inspects). -/
theorem extend_kit [Nonempty T] (F : LCQFTFragment X n ι T κ)
    (f : CausalEmbedding X Y) (M' : MixingKit Y)
    (hkit : M'.pullback f = F.kit) :
    (F.extend f M' hkit).kit = M' := rfl

/-- The sub-diamond fragment, extended along the *other* compatible
chronology: same region data, different ambient kit. -/
noncomputable def isingExtendedFragmentPast :
    LCQFTFragment (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) DstarSojourn
      (Fin 2 × Fin 2) :=
  isingQubitFragmentOnDstar.extend Dstar.inclusionEmbedding
    (minkowskiFutureKit zPast) minkowskiFutureKit_pullback_eq

/-- **The two extensions have the same net, definitionally**: the net
field of the extension never consults the ambient kit — extension is
canonical at net grade. -/
theorem isingExtendedPast_net_eq :
    isingExtendedFragmentPast.net = isingExtendedFragment.net := rfl

/-- Both extensions regenerate the ambient kinematic net — by the same
proof term: the regeneration theorem never reads the kit. -/
theorem isingExtendedPast_net :
    isingExtendedFragmentPast.net = qubitNet := isingExtended_net

/-- **The two extensions are distinct fragments**: they differ at
exactly the kit.  Together with `isingExtendedPast_net_eq`: extension
along a causal embedding is canonical on nets and non-canonical on
kits. -/
theorem isingExtendedPast_ne :
    isingExtendedFragmentPast ≠ isingExtendedFragment :=
  fun h => minkowskiFutureKit_ne (congrArg LCQFTFragment.kit h)

/-- Both extensions restrict back to the same fragment on the nose —
the round trip cannot see the choice the extension made. -/
theorem isingExtendedPast_restrict :
    isingExtendedFragmentPast.restrict Dstar.inclusionEmbedding
      (fun t => t) isingQubitFragmentOnDstar.worldlines (fun _ _ => rfl)
      isingQubitFragmentOnDstar.sites (fun _ => rfl)
      isingQubitFragmentOnDstar.sites_on_worldlines
      isingQubitFragmentOnDstar.ambient
      isingQubitFragmentOnDstar.interior_witness
      (extend_pullback_interiorMem isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding (minkowskiFutureKit zPast)
        minkowskiFutureKit_pullback_eq)
      (extend_push_attained isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding (minkowskiFutureKit zPast)
        minkowskiFutureKit_pullback_eq)
      (extend_push_records isingQubitFragmentOnDstar
        Dstar.inclusionEmbedding (minkowskiFutureKit zPast)
        minkowskiFutureKit_pullback_eq) =
      isingQubitFragmentOnDstar :=
  LCQFTFragment.restrict_extend isingQubitFragmentOnDstar
    Dstar.inclusionEmbedding (minkowskiFutureKit zPast)
    minkowskiFutureKit_pullback_eq

end QuantumExtension
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumDescent.ObservableNet.extend
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg_push
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_extend
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_restrict_alg_le
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg_le_iff
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_id
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_comp
#print axioms Qtsl.QuantumExtension.heisenbergNet_extend
#print axioms Qtsl.QuantumExtension.commute_of_mem_iSup
#print axioms Qtsl.QuantumExtension.extend_alg_eq_sites
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.extend
#print axioms Qtsl.QuantumExtension.extend_net_alg
#print axioms Qtsl.QuantumExtension.extend_records
#print axioms Qtsl.QuantumExtension.extend_sites
#print axioms Qtsl.QuantumExtension.extend_ambient
#print axioms Qtsl.QuantumExtension.extend_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.ext
#print axioms Qtsl.QuantumExtension.extend_pullback_interiorMem
#print axioms Qtsl.QuantumExtension.extend_push_attained
#print axioms Qtsl.QuantumExtension.extend_push_records
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_extend
#print axioms Qtsl.QuantumExtension.extend_id_frag
#print axioms Qtsl.QuantumExtension.extend_comp_frag
#print axioms Qtsl.QuantumExtension.extend_restrict_net
#print axioms Qtsl.QuantumExtension.isingExtendedFragment
#print axioms Qtsl.QuantumExtension.isingExtended_net
#print axioms Qtsl.QuantumExtension.isingExtended_restrict
#print axioms Qtsl.QuantumExtension.isingExtended_shadow_separates_bell_mixed
#print axioms Qtsl.QuantumExtension.isingExtended_slice_determinacy
#print axioms Qtsl.QuantumExtension.emptyMixingKit
#print axioms Qtsl.QuantumExtension.emptyMixingKit_pullback_ne
#print axioms Qtsl.QuantumExtension.mink_chron_of_le_chron
#print axioms Qtsl.QuantumExtension.mink_chron_of_chron_le
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_chron_iff
#print axioms Qtsl.QuantumExtension.zPast
#print axioms Qtsl.QuantumExtension.zPast_chron_lo
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_pullback_eq
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_ne
#print axioms Qtsl.QuantumExtension.exists_distinct_kits_same_pullback
#print axioms Qtsl.QuantumExtension.extend_kit
#print axioms Qtsl.QuantumExtension.isingExtendedFragmentPast
#print axioms Qtsl.QuantumExtension.isingExtendedPast_net_eq
#print axioms Qtsl.QuantumExtension.isingExtendedPast_net
#print axioms Qtsl.QuantumExtension.isingExtendedPast_ne
#print axioms Qtsl.QuantumExtension.isingExtendedPast_restrict
