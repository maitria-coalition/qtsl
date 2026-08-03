import SuFunctor.Universe.FellDescent
import Mathlib.Topology.Separation.Basic

/-! # Fell descent along arbitrary open covers: the equalizer form (rung C′)

The sheaf condition proper for the Fell hyperspace: over an open
cover of the ambient space — **no directedness**, and, it turns out,
no finiteness either — the clip maps induce a homeomorphism

  `CL(α) ≃ₜ {(Fᵢ) ∈ Πᵢ CL(Uᵢ) : Fᵢ ∩ Uⱼ = Fⱼ ∩ Uᵢ ∀ i j}`

onto the **equalizer** of the cell-hyperspace product over the
overlap-compatibility constraints, with the subspace-of-product
topology (`equalizerHomeomorph`, `isHomeomorph_toEqualizer`).  This is
the sibling of `FellDescent.lean`'s rung C, never its replacement: for
directed covers the projective-limit form remains the fast path; the
equalizer form is what a mesh of cells (a cover that *cuts* the stage
space) consumes.

Where the directed proof leaned on directedness, this one splits:

* **bijectivity** is directedness-free sheaf bookkeeping — the
  glue-trace identity (`preimage_glueSet_overlap`) collects a stray
  point through the *overlap* rather than through a common refinement
  (a point of `F ∩ Uᵢ` lies in some `Fⱼ`, hence in
  `Fⱼ ∩ Uᵢ = Fᵢ ∩ Uⱼ ⊆ Fᵢ`), and closedness of the glue is locality
  of closedness over arbitrary open covers;
* **hits are local** (`isOpen_glueEqualizer_hit`) — verbatim the
  directed argument, which never consumed directedness;
* **misses are compactly supported** (`isOpen_glueEqualizer_miss`) —
  the one real move: a compact miss parameter need not land in a
  single member, so directedness's job is done by the **compact
  splitting lemma** (mathlib's `IsCompact.finite_compact_cover`,
  shrinking-lemma stock): `K` takes a finite subcover and
  splits as a union of compacts `Kᵢ ⊆ Uᵢ` along it, so the miss
  demand is a *finite* intersection of levelwise miss demands.

Two deltas against rung C, both honest fees of the non-directed
setting and both confined to the miss face:

* **`R1Space α`** — the splitting lemma separates disjoint compacts
  inside `K`; rung C needed no separation anywhere.
* nothing else: in particular **finiteness of the index is not a
  hypothesis** — the finite-cover statement is the instance of
  this one at a finite index type.  Compactness of the miss parameter
  manufactures its own finite subcover, which is also exactly why the
  miss face fails for closed noncompact parameters
  (`not_isOpen_iInf_induced_singleton_bot`, unchanged from rung C's
  battery).

Positive controls, per the mesh brief: over rung C's nondirected
fixture cover `{Iic 1, Ici 1}` of `ℕ` — where the projective-limit
form is *not even surjective*
(`not_surjective_toProjLim_nondirectedPair`) — the equalizer form
descends (`isHomeomorph_toEqualizer_nondirectedPair`), and the fixture
family `(∅, {1})` that witnessed the failure is correctly *excluded*
from the equalizer (`not_isOverlapCompat_nondirectedFamily`): its
incompatibility lives on the overlap `{1}`, which inclusion-indexed
compatibility could not see, and its glued set fails the trace
identity (`preimage_glueSet_nondirectedFamily_ne`) — so pairwise
compatibility is load-bearing at statement level, not merely in this
proof.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

attribute [local instance] SuFunctor.Universe.fell

namespace FellCloseds

section Equalizer

variable {ι : Type*}

/-! ## Overlap compatibility and the equalizer -/

/-- A family of closed subsets of the members of a system of subsets
is *overlap-compatible* when for every pair of levels the two clips to
the overlap agree: `Fᵢ ∩ Uⱼ = Fⱼ ∩ Uᵢ`, stated at the subspace
carrier of `U i ∩ U j`.  This is the sheaf condition's equalizer leg —
strictly stronger than `IsCompatFamily` on non-directed systems, where
inclusion-indexed compatibility can degenerate (the members may admit
no inclusions at all). -/
def IsOverlapCompat (U : ι → Set α) (f : ∀ i, FellCloseds ↥(U i)) : Prop :=
  ∀ i j : ι,
    clipLE (inter_subset_left : U i ∩ U j ⊆ U i) (f i)
      = clipLE (inter_subset_right : U i ∩ U j ⊆ U j) (f j)

/-- The equalizer of the cell-hyperspace product over the overlap
constraints: overlap-compatible families, carrying the subspace
topology of the product. -/
abbrev Equalizer (U : ι → Set α) : Type _ :=
  {f : ∀ i, FellCloseds ↥(U i) // IsOverlapCompat U f}

/-- The canonical map into the equalizer: clip to every level.  The
compatibility is definitional: both clips to an overlap compute the
ambient clip there (`clipLE_clip`). -/
def toEqualizer (U : ι → Set α) (F : FellCloseds α) : Equalizer U :=
  ⟨fun i => clip (U i) F, fun _ _ => rfl⟩

@[simp]
theorem toEqualizer_apply (U : ι → Set α) (F : FellCloseds α) (i : ι) :
    (toEqualizer U F).1 i = clip (U i) F := rfl

/-- The canonical map is continuous: componentwise it is clipping,
which is Fell-continuous on open members. -/
theorem continuous_toEqualizer (U : ι → Set α) (hUo : ∀ i, IsOpen (U i)) :
    Continuous (toEqualizer U) :=
  Continuous.subtype_mk (continuous_pi fun i => continuous_clip (hUo i)) _

/-! ## Gluing, directedness-free -/

/-- The glue-trace identity from pairwise compatibility alone: an
overlap-compatible family's glued set traces back to the family, with
**no directedness, no finiteness, no separation** — a stray point of
`(f j)`'s image lying in `U i` is collected through the overlap
`U i ∩ U j`, where compatibility identifies both members' traces (the
pairwise condition does what directedness did in
`preimage_glueSet`). -/
theorem preimage_glueSet_overlap {U : ι → Set α}
    {f : ∀ i, FellCloseds ↥(U i)} (hf : IsOverlapCompat U f) (i : ι) :
    ((↑) ⁻¹' glueSet f : Set ↥(U i)) = (f i : Set ↥(U i)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, hy, hyx⟩ : ∃ j, ∃ y ∈ (f j : Set ↥(U j)), (y : α) = (x : α) := by
      simpa [glueSet, mem_iUnion] using hx
    have hxj : (x : α) ∈ U j := hyx ▸ y.2
    set z : ↥(U i ∩ U j) := ⟨(x : α), ⟨x.2, hxj⟩⟩ with hzdef
    have hzy : Set.inclusion (inter_subset_right : U i ∩ U j ⊆ U j) z = y :=
      Subtype.ext hyx.symm
    have hz : z ∈ clipLE (inter_subset_right : U i ∩ U j ⊆ U j) (f j) := by
      rw [mem_clipLE, hzy]
      exact hy
    rw [← hf i j] at hz
    have hzx : Set.inclusion (inter_subset_left : U i ∩ U j ⊆ U i) z = x :=
      Subtype.ext rfl
    rw [mem_clipLE, hzx] at hz
    exact hz
  · intro hx
    exact mem_preimage.mpr (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hx⟩)

/-- Over any open cover, an overlap-compatible family's glued set is
closed: closedness is local on arbitrary open covers, and the
glue-trace identity exhibits the glued set's trace on each member as
that member's relatively closed entry. -/
theorem isClosed_glueSet_overlap {U : ι → Set α} (hUo : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ)
    {f : ∀ i, FellCloseds ↥(U i)} (hf : IsOverlapCompat U f) :
    IsClosed (glueSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := mem_iUnion.mp (hcov ▸ mem_univ x)
  obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.mp (f i).isClosed
  refine ⟨U i ∩ Cᶜ, fun y hy hyG => hy.2 ?_, (hUo i).inter hC.isOpen_compl, hxi,
    fun hxC => hx ?_⟩
  · -- a point of `U i ∩ Cᶜ` cannot lie in the glued set
    have htr : (⟨y, hy.1⟩ : ↥(U i)) ∈ ((↑) ⁻¹' glueSet f : Set ↥(U i)) := hyG
    rw [preimage_glueSet_overlap hf, ← hCeq] at htr
    exact htr
  · -- `x ∈ C` would place `x` in the glued set
    have htr : (⟨x, hxi⟩ : ↥(U i)) ∈ ((↑) ⁻¹' C : Set ↥(U i)) := hxC
    rw [hCeq] at htr
    exact mem_iUnion.mpr ⟨i, mem_image_of_mem _ htr⟩

/-- Glue an overlap-compatible family over an open cover into a closed
subset of the ambient. -/
def glueEqualizer (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (p : Equalizer U) : FellCloseds α :=
  ⟨glueSet p.1, isClosed_glueSet_overlap hUo hcov p.2⟩

/-- A closed set is recovered from its clips: the cover exhausts it. -/
theorem glueEqualizer_toEqualizer (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (F : FellCloseds α) :
    glueEqualizer U hUo hcov (toEqualizer U F) = F := by
  apply FellCloseds.ext
  show glueSet (toEqualizer U F).1 = (F : Set α)
  ext x
  simp only [glueSet, toEqualizer_apply, coe_clip, Subtype.image_preimage_coe,
    mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, -, hxF⟩
    exact hxF
  · intro hxF
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcov ▸ mem_univ x)
    exact ⟨i, hxi, hxF⟩

/-- An overlap-compatible family is recovered from its glue: the
glue-trace identity, packaged. -/
theorem toEqualizer_glueEqualizer (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (p : Equalizer U) :
    toEqualizer U (glueEqualizer U hUo hcov p) = p := by
  apply Subtype.ext
  funext i
  apply FellCloseds.ext
  show ((↑) ⁻¹' glueSet p.1 : Set ↥(U i)) = (p.1 i : Set ↥(U i))
  exact preimage_glueSet_overlap p.2 i

/-! ## The two subbasis faces of inverse continuity -/

/-- **Hits are local**: the glued set meets an open `V` iff some level
meets `V`'s trace — verbatim the directed argument, which never
consumed directedness, now at the equalizer carrier. -/
theorem isOpen_glueEqualizer_hit (U : ι → Set α) {V : Set α} (hV : IsOpen V) :
    IsOpen {p : Equalizer U | (glueSet p.1 ∩ V).Nonempty} := by
  have hset : {p : Equalizer U | (glueSet p.1 ∩ V).Nonempty}
      = ⋃ i, (fun p : Equalizer U => p.1 i) ⁻¹'
          {G : FellCloseds ↥(U i) | ((G : Set ↥(U i)) ∩ (↑) ⁻¹' V).Nonempty} := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, mem_preimage, glueSet, iUnion_inter,
      nonempty_iUnion]
    refine exists_congr fun i => ?_
    rw [← image_inter_preimage, image_nonempty]
  rw [hset]
  exact isOpen_iUnion fun i =>
    (isOpen_inter_nonempty_of_isOpen (hV.preimage continuous_subtype_val)).preimage
      ((continuous_apply i).comp continuous_subtype_val)

/-- **Misses are compactly split**: a compact miss parameter takes a
finite subcover and splits as a union of compact subsets `Kᵢ ⊆ Uᵢ`
along it (`IsCompact.finite_compact_cover` — the compact splitting
lemma, directedness's replacement and the one real move of the
non-directed setting), so the miss demand is a *finite* intersection
of levelwise miss demands.  `R1Space` is the splitting lemma's fee —
the one hypothesis rung C did not pay — and index-finiteness is *not*
consumed: the finiteness in the intersection is the subcover's,
supplied by `K`'s own compactness. -/
theorem isOpen_glueEqualizer_miss [R1Space α] (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    {K : Set α} (hK : IsCompact K) :
    IsOpen {p : Equalizer U | Disjoint (glueSet p.1) K} := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo (hcov ▸ subset_univ K)
  obtain ⟨C, hCc, hCU, hKC⟩ := hK.finite_compact_cover t U (fun i _ => hUo i) ht
  have hC' : ∀ i, IsCompact ((↑) ⁻¹' C i : Set ↥(U i)) := fun i =>
    Topology.IsInducing.subtypeVal.isCompact_preimage' (hCc i)
      (by rw [Subtype.range_coe]; exact hCU i)
  have hset : {p : Equalizer U | Disjoint (glueSet p.1) K}
      = ⋂ i ∈ t, (fun p : Equalizer U => p.1 i) ⁻¹'
          {G : FellCloseds ↥(U i) | Disjoint (G : Set ↥(U i)) ((↑) ⁻¹' C i)} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter, mem_preimage]
    constructor
    · intro h i hi
      rw [Set.disjoint_left]
      intro x hxG hxC
      exact (Set.disjoint_left.mp h)
        (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hxG⟩)
        (hKC ▸ mem_biUnion hi hxC)
    · intro h
      rw [Set.disjoint_left]
      intro x hxglue hxK
      rw [hKC] at hxK
      obtain ⟨j, hjt, hxj⟩ := mem_iUnion₂.mp hxK
      have hxUj : x ∈ U j := hCU j hxj
      have hmem : (⟨x, hxUj⟩ : ↥(U j)) ∈ ((↑) ⁻¹' glueSet p.1 : Set ↥(U j)) := hxglue
      rw [preimage_glueSet_overlap p.2] at hmem
      exact (Set.disjoint_left.mp (h j hjt)) hmem hxj
  rw [hset]
  exact isOpen_biInter_finset fun i _ =>
    (isOpen_disjoint_of_isCompact (hC' i)).preimage
      ((continuous_apply i).comp continuous_subtype_val)

/-- Gluing is continuous: per Fell subbasic, the hit face by locality,
the miss face by compact splitting over the finite subcover. -/
theorem continuous_glueEqualizer [R1Space α] (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    Continuous (glueEqualizer U hUo hcov) := by
  apply isEmbedding_coe.isInducing.continuous_iff.mpr
  apply continuous_generateFrom_iff.mpr
  rintro s (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · exact isOpen_glueEqualizer_miss U hUo hcov hK
  · exact isOpen_glueEqualizer_hit U hV

/-! ## The descent theorem, equalizer form -/

/-- **Fell descent along arbitrary open covers**: over any open cover of
an R1 ambient — directedness and index-finiteness both dropped — the
clip maps are the components of a homeomorphism from the Fell
hyperspace of the ambient onto the equalizer of the members' Fell
hyperspaces over the overlap constraints.  The finite-cover statement
is the finite-index instance; rung C's directed statement remains the
projective-limit fast path where directedness is available. -/
def equalizerHomeomorph [R1Space α] (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) :
    FellCloseds α ≃ₜ Equalizer U where
  toFun := toEqualizer U
  invFun := glueEqualizer U hUo hcov
  left_inv := glueEqualizer_toEqualizer U hUo hcov
  right_inv := toEqualizer_glueEqualizer U hUo hcov
  continuous_toFun := continuous_toEqualizer U hUo
  continuous_invFun := continuous_glueEqualizer U hUo hcov

/-- The descent theorem in predicate form: over any open cover of an
R1 ambient, the canonical clip-family map is a homeomorphism onto the
equalizer. -/
theorem isHomeomorph_toEqualizer [R1Space α] (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    IsHomeomorph (toEqualizer U) :=
  (equalizerHomeomorph U hUo hcov).isHomeomorph

end Equalizer

/-! ## Positive controls: the nondirected fixture, revisited

Rung C's refuting fixture I (`FellDescent.lean`) showed the
projective-limit form failing over the nondirected cover
`{Iic 1, Ici 1}` of `ℕ`: the family `(∅, {1})` was
`IsCompatFamily`-compatible (vacuously — the members admit no
inclusions) yet had no preimage.  The equalizer form must succeed
exactly where that witness failed, and it does, in both halves: the
cover descends, and the witness family is excluded. -/

section NondirectedControl

/-- **The equalizer condition sees what inclusion-indexed
compatibility could not**: fixture I's family `(∅, {1})` is *not*
overlap-compatible — its incompatibility lives on the overlap
`Iic 1 ∩ Ici 1 = {1}`, which the nondirected pair's (empty) inclusion
structure never inspects. -/
theorem not_isOverlapCompat_nondirectedFamily :
    ¬ IsOverlapCompat nondirectedPair nondirectedFamily := by
  intro h
  have h1 : (1 : ℕ) ∈ nondirectedPair true ∩ nondirectedPair false :=
    ⟨mem_Ici.mpr le_rfl, mem_Iic.mpr le_rfl⟩
  set z : ↥(nondirectedPair true ∩ nondirectedPair false) := ⟨1, h1⟩ with hzdef
  have hz : z ∈ clipLE
      (inter_subset_left : nondirectedPair true ∩ nondirectedPair false ⊆ _)
      (nondirectedFamily true) := by
    rw [mem_clipLE]
    show ((Set.inclusion _ z : ↥(nondirectedPair true)) : ℕ) ∈ ({1} : Set ℕ)
    rfl
  rw [h true false, mem_clipLE] at hz
  exact notMem_empty _ hz

/-- **Pairwise compatibility is load-bearing at statement level**: the
incompatible fixture family's glued set (`{1}`) fails the glue-trace
identity at level `false` — so no proof of `preimage_glueSet_overlap`
could avoid the compatibility hypothesis; the identity is false
without it. -/
theorem preimage_glueSet_nondirectedFamily_ne :
    ((↑) ⁻¹' glueSet nondirectedFamily : Set ↥(nondirectedPair false))
      ≠ (nondirectedFamily false : Set ↥(nondirectedPair false)) := by
  intro h
  have h1 : (⟨1, mem_Iic.mpr le_rfl⟩ : ↥(nondirectedPair false))
      ∈ ((↑) ⁻¹' glueSet nondirectedFamily : Set ↥(nondirectedPair false)) := by
    show (1 : ℕ) ∈ glueSet nondirectedFamily
    exact mem_iUnion.mpr
      ⟨true, mem_image_of_mem _ (show (⟨1, mem_Ici.mpr le_rfl⟩ :
        ↥(nondirectedPair true)) ∈ nondirectedFamily true from rfl)⟩
  rw [h] at h1
  exact notMem_empty _ h1

/-- **The equalizer form descends over the nondirected fixture cover**
— the cover over which the projective-limit form is not even
surjective (`not_surjective_toProjLim_nondirectedPair`).  Instance of
the descent theorem at `ℕ` discrete. -/
theorem isHomeomorph_toEqualizer_nondirectedPair :
    IsHomeomorph (toEqualizer nondirectedPair) :=
  isHomeomorph_toEqualizer nondirectedPair isOpen_nondirectedPair
    iUnion_nondirectedPair

end NondirectedControl

end FellCloseds

end SuFunctor.Universe

#print axioms SuFunctor.Universe.FellCloseds.equalizerHomeomorph
#print axioms SuFunctor.Universe.FellCloseds.isHomeomorph_toEqualizer
#print axioms SuFunctor.Universe.FellCloseds.not_isOverlapCompat_nondirectedFamily
#print axioms SuFunctor.Universe.FellCloseds.preimage_glueSet_nondirectedFamily_ne
#print axioms SuFunctor.Universe.FellCloseds.isHomeomorph_toEqualizer_nondirectedPair
