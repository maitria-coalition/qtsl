import SuFunctor.Universe.FellRestrict

/-! # Fell descent along directed open covers

The descent theorem for the Fell hyperspace (rung C of the
temporal-sheaf-carrier design): over a **directed** family of open
sets covering
the ambient space, the clip maps induce a homeomorphism

  `CL(α) ≃ₜ lim_i CL(U i)`

onto the space of compatible families, carrying the limit (initial)
topology as a subspace of the product (`projLimHomeomorph`,
`isHomeomorph_toProjLim_of_directed`).  The projective limit is taken
in explicit form — the subtype of the product on the transition-clip
compatibility condition — which is the form the sheaf condition
consumes; the ambient plays the role of the cover's union (the
subspace form of the statement is the instantiation of this one at the
union's subtype).

The proof splits along the two Fell subbasis families, and the split
is the theorem:

* **bijectivity** — a closed set is recovered from its clips
  (`glue_toProjLim`), and a compatible family glues to the union of
  its members' images, closed because closedness is local on an open
  cover (`isClosed_glueSet`), with the glue-trace identity
  `preimage_glueSet` collecting stray points through a
  directedness-supplied common refinement;
* **hits are local** (`isOpen_glue_hit`) — the glued set meets an open
  `V` iff some level's member meets `V`'s trace, so hit demands are
  unions of levelwise hit demands;
* **misses are compactly supported** (`isOpen_glue_miss`) — a compact
  miss parameter lands inside a single cover member
  (`IsCompact.elim_directed_cover`), so miss demands are levelwise
  miss demands there.

Two refuting fixtures delimit the theorem's hypotheses, failure
exhibited rather than asserted:

* **directedness is load-bearing at statement level**
  (`not_surjective_toProjLim_nondirectedPair`): over the nondirected
  two-member open cover `{Iic 1, Ici 1}` of `ℕ`, compatibility
  degenerates (the members admit no inclusions), and the compatible
  family `(∅, {1})` has no preimage — the canonical map is not even
  surjective.
* **the Vietoris upper face cannot descend**
  (`not_isOpen_iInf_induced_singleton_bot`,
  `not_iInf_induced_le_vietoris`): over the directed cover `Iic` of
  `ℕ`, the miss class `{⊥}` of the **closed noncompact** parameter
  `univ` — Vietoris-open unconditionally, since `{∅}` is the powerset
  of an open set — is not open in the limit topology: a closed set's
  tail straddles every cover member, so its miss demand is not
  finitely supported.  Together with the descent theorem this is the
  memo's dichotomy: hit-of-open and miss-of-compact are exactly the
  faces that descend, and the compact-miss trade is what
  `isOpen_glue_miss` runs on.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

attribute [local instance] SuFunctor.Universe.fell

namespace FellCloseds

/-! ## Clip maps at the closeds carrier -/

section Clip

variable {U : Set α}

/-- Clip a closed subset of the ambient to a distinguished subset `U`,
as a closed subset of the subspace: the carrier-level form of
`fell.restrictOpen`. -/
def clip (U : Set α) (F : FellCloseds α) : FellCloseds ↥U :=
  ⟨(↑) ⁻¹' (F : Set α), F.isClosed.preimage continuous_subtype_val⟩

@[simp]
theorem coe_clip (U : Set α) (F : FellCloseds α) :
    (clip U F : Set ↥U) = (↑) ⁻¹' (F : Set α) := rfl

@[simp]
theorem mem_clip {U : Set α} {F : FellCloseds α} {x : ↥U} :
    x ∈ clip U F ↔ (x : α) ∈ F := Iff.rfl

/-- **Clipping to an open set is Fell-continuous** at the closeds
carrier: rung A's `fell.continuous_restrictOpen`, transported along the
induced topologies. -/
theorem continuous_clip (hU : IsOpen U) : Continuous (clip (α := α) U) :=
  isEmbedding_coe.isInducing.continuous_iff.mpr
    ((fell.continuous_restrictOpen hU).comp continuous_coe)

/-- The transition clip of a system of subsets: for `s ⊆ t`, clip a
closed subset of (the subspace) `t` to one of `s`. -/
def clipLE {s t : Set α} (hst : s ⊆ t) (F : FellCloseds ↥t) : FellCloseds ↥s :=
  ⟨Set.inclusion hst ⁻¹' (F : Set ↥t), F.isClosed.preimage (continuous_inclusion hst)⟩

@[simp]
theorem mem_clipLE {s t : Set α} {hst : s ⊆ t} {F : FellCloseds ↥t} {x : ↥s} :
    x ∈ clipLE hst F ↔ Set.inclusion hst x ∈ F := Iff.rfl

/-- Transition clips absorb ambient clips: clipping to `t` and then to
`s ⊆ t` is clipping to `s`. -/
theorem clipLE_clip {s t : Set α} (hst : s ⊆ t) (F : FellCloseds α) :
    clipLE hst (clip t F) = clip s F := rfl

end Clip

/-! ## The projective system of a family of subsets -/

section Descent

variable {ι : Type*}

/-- A family of closed subsets of the members of a system of subsets
is *compatible* when every transition clip carries the level-`j`
member to the level-`i` member. -/
def IsCompatFamily (U : ι → Set α) (f : ∀ i, FellCloseds ↥(U i)) : Prop :=
  ∀ ⦃i j : ι⦄ (hij : U i ⊆ U j), clipLE hij (f j) = f i

/-- The projective limit of the Fell hyperspaces of a system of
subsets: compatible families, carrying the limit (initial) topology as
a subspace of the product. -/
abbrev ProjLim (U : ι → Set α) : Type _ :=
  {f : ∀ i, FellCloseds ↥(U i) // IsCompatFamily U f}

/-- The canonical map into the projective limit: clip to every level. -/
def toProjLim (U : ι → Set α) (F : FellCloseds α) : ProjLim U :=
  ⟨fun i => clip (U i) F, fun _ _ hij => clipLE_clip hij F⟩

@[simp]
theorem toProjLim_apply (U : ι → Set α) (F : FellCloseds α) (i : ι) :
    (toProjLim U F).1 i = clip (U i) F := rfl

/-- The canonical map is continuous: componentwise it is clipping,
which is Fell-continuous on open members. -/
theorem continuous_toProjLim (U : ι → Set α) (hUo : ∀ i, IsOpen (U i)) :
    Continuous (toProjLim U) :=
  Continuous.subtype_mk (continuous_pi fun i => continuous_clip (hUo i)) _

/-! ## Gluing -/

/-- The glued set of a family: the union of the members' images in the
ambient. -/
def glueSet {U : ι → Set α} (f : ∀ i, FellCloseds ↥(U i)) : Set α :=
  ⋃ i, (↑) '' (f i : Set ↥(U i))

/-- The glue-trace identity: over a directed system, a compatible
family's glued set traces back to the family — the preimage of the
union at level `i` is the level-`i` member.  Directedness collects a
point of `(f j)`'s image lying in `U i` into a common refinement, where
compatibility identifies both members' traces. -/
theorem preimage_glueSet {U : ι → Set α} (hdir : Directed (· ⊆ ·) U)
    {f : ∀ i, FellCloseds ↥(U i)} (hf : IsCompatFamily U f) (i : ι) :
    ((↑) ⁻¹' glueSet f : Set ↥(U i)) = (f i : Set ↥(U i)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, hy, hyx⟩ : ∃ j, ∃ y ∈ (f j : Set ↥(U j)), (y : α) = (x : α) := by
      simpa [glueSet, mem_iUnion] using hx
    obtain ⟨k, hik, hjk⟩ := hdir i j
    have hyk : Set.inclusion hjk y ∈ (f k : Set ↥(U k)) := by
      rw [← hf hjk] at hy
      exact hy
    have hxk : Set.inclusion hik x ∈ (f k : Set ↥(U k)) := by
      have heq : Set.inclusion hjk y = Set.inclusion hik x :=
        Subtype.ext (by simp [hyx])
      rwa [heq] at hyk
    rw [← hf hik]
    exact hxk
  · intro hx
    exact mem_preimage.mpr (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hx⟩)

/-- Over a directed open cover, a compatible family's glued set is
closed: closedness is local, and the glue-trace identity exhibits the
glued set's trace on each member as that member's relatively closed
entry. -/
theorem isClosed_glueSet {U : ι → Set α} (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    {f : ∀ i, FellCloseds ↥(U i)} (hf : IsCompatFamily U f) :
    IsClosed (glueSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := mem_iUnion.mp (hcov ▸ mem_univ x)
  obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.mp (f i).isClosed
  refine ⟨U i ∩ Cᶜ, fun y hy hyG => hy.2 ?_, (hUo i).inter hC.isOpen_compl, hxi,
    fun hxC => hx ?_⟩
  · -- a point of `U i ∩ Cᶜ` cannot lie in the glued set
    have htr : (⟨y, hy.1⟩ : ↥(U i)) ∈ ((↑) ⁻¹' glueSet f : Set ↥(U i)) := hyG
    rw [preimage_glueSet hdir hf, ← hCeq] at htr
    exact htr
  · -- `x ∈ C` would place `x` in the glued set
    have htr : (⟨x, hxi⟩ : ↥(U i)) ∈ ((↑) ⁻¹' C : Set ↥(U i)) := hxC
    rw [hCeq] at htr
    exact mem_iUnion.mpr ⟨i, mem_image_of_mem _ htr⟩

/-- Glue a compatible family over a directed open cover into a closed
subset of the ambient. -/
def glue (U : ι → Set α) (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) (p : ProjLim U) : FellCloseds α :=
  ⟨glueSet p.1, isClosed_glueSet hUo hdir hcov p.2⟩

/-- A closed set is recovered from its clips: the cover exhausts it. -/
theorem glue_toProjLim (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) (F : FellCloseds α) :
    glue U hUo hdir hcov (toProjLim U F) = F := by
  apply FellCloseds.ext
  show glueSet (toProjLim U F).1 = (F : Set α)
  ext x
  simp only [glueSet, toProjLim_apply, coe_clip, Subtype.image_preimage_coe,
    mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, -, hxF⟩
    exact hxF
  · intro hxF
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcov ▸ mem_univ x)
    exact ⟨i, hxi, hxF⟩

/-- A compatible family is recovered from its glue: the glue-trace
identity, packaged. -/
theorem toProjLim_glue (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) (p : ProjLim U) :
    toProjLim U (glue U hUo hdir hcov p) = p := by
  apply Subtype.ext
  funext i
  apply FellCloseds.ext
  show ((↑) ⁻¹' glueSet p.1 : Set ↥(U i)) = (p.1 i : Set ↥(U i))
  exact preimage_glueSet hdir p.2 i

/-! ## The two subbasis faces of inverse continuity -/

/-- **Hits are local**: the glued set meets an open `V` iff some level
meets `V`'s trace, so the hit demand is a union of levelwise hit
demands — open in the limit topology with no hypotheses at all. -/
theorem isOpen_glue_hit (U : ι → Set α) {V : Set α} (hV : IsOpen V) :
    IsOpen {p : ProjLim U | (glueSet p.1 ∩ V).Nonempty} := by
  have hset : {p : ProjLim U | (glueSet p.1 ∩ V).Nonempty}
      = ⋃ i, (fun p : ProjLim U => p.1 i) ⁻¹'
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

/-- **Misses are compactly supported**: a compact miss parameter lands
inside one member of the directed cover, and the miss demand is
exactly the levelwise miss demand there.  This is the step Vietoris's
closed-miss face cannot make (`not_isOpen_iInf_induced_singleton_bot`):
a closed parameter's tail can straddle every member. -/
theorem isOpen_glue_miss (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    {K : Set α} (hK : IsCompact K) :
    IsOpen {p : ProjLim U | Disjoint (glueSet p.1) K} := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- an empty system covers only the empty ambient: the demand is vacuous
    have hKe : K = ∅ := by
      have huniv : (univ : Set α) = ∅ := by
        rw [← hcov]
        exact iUnion_of_empty U
      exact eq_empty_of_subset_empty (huniv ▸ subset_univ K)
    have htriv : {p : ProjLim U | Disjoint (glueSet p.1) K} = univ := by
      ext p
      simp [hKe]
    rw [htriv]
    exact isOpen_univ
  · obtain ⟨i, hKi⟩ := hK.elim_directed_cover U hUo (hcov ▸ subset_univ K) hdir
    have hK' : IsCompact ((↑) ⁻¹' K : Set ↥(U i)) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK
        (by rwa [Subtype.range_coe])
    have hset : {p : ProjLim U | Disjoint (glueSet p.1) K}
        = (fun p : ProjLim U => p.1 i) ⁻¹'
            {G : FellCloseds ↥(U i) | Disjoint (G : Set ↥(U i)) ((↑) ⁻¹' K)} := by
      ext p
      simp only [mem_setOf_eq, mem_preimage, Set.disjoint_left]
      constructor
      · intro h y hy hyK
        exact h (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hy⟩) hyK
      · intro h x hxG hxK
        have hxglue : (⟨x, hKi hxK⟩ : ↥(U i)) ∈ ((↑) ⁻¹' glueSet p.1 : Set ↥(U i)) := hxG
        rw [preimage_glueSet hdir p.2] at hxglue
        exact h hxglue hxK
    rw [hset]
    exact (isOpen_disjoint_of_isCompact hK').preimage
      ((continuous_apply i).comp continuous_subtype_val)

/-- Gluing is continuous: per Fell subbasic, the hit face by locality,
the miss face by compact support over the directed cover. -/
theorem continuous_glue (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) :
    Continuous (glue U hUo hdir hcov) := by
  apply isEmbedding_coe.isInducing.continuous_iff.mpr
  apply continuous_generateFrom_iff.mpr
  rintro t (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩)
  · exact isOpen_glue_miss U hUo hdir hcov hK
  · exact isOpen_glue_hit U hV

/-! ## The descent theorem -/

/-- **Fell descent along directed open covers** (the temporal-sheaf
memo's §4.1): over a directed open cover of the ambient, the clip maps
are the components of a homeomorphism from the Fell hyperspace of the
ambient onto the projective limit of the members' Fell hyperspaces.
Hit-of-open and miss-of-compact are respectively the local-character
and finite-support halves of the proof; the refuting fixtures below
show each is sharp. -/
def projLimHomeomorph (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) :
    FellCloseds α ≃ₜ ProjLim U where
  toFun := toProjLim U
  invFun := glue U hUo hdir hcov
  left_inv := glue_toProjLim U hUo hdir hcov
  right_inv := toProjLim_glue U hUo hdir hcov
  continuous_toFun := continuous_toProjLim U hUo
  continuous_invFun := continuous_glue U hUo hdir hcov

/-- The descent theorem in predicate form: over a directed open cover,
the canonical clip-family map is a homeomorphism onto the projective
limit. -/
theorem isHomeomorph_toProjLim_of_directed (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) : IsHomeomorph (toProjLim U) :=
  (projLimHomeomorph U hUo hdir hcov).isHomeomorph

end Descent

/-! ## Refuting fixture I: directedness is load-bearing

The two-member open cover `{Iic 1, Ici 1}` of `ℕ` is not directed, and
descent fails for it already at the bijection: compatibility along
inclusions degenerates (the members admit none), so the family
`(∅, {1})` is compatible — but a preimage would have to omit `1` at
level `false` and contain it at level `true`. -/

section NondirectedWitness

/-- The nondirected witness cover: `Iic 1` and `Ici 1` in `ℕ`. -/
def nondirectedPair : Bool → Set ℕ
  | false => Iic 1
  | true => Ici 1

@[simp] theorem nondirectedPair_false : nondirectedPair false = Iic 1 := rfl

@[simp] theorem nondirectedPair_true : nondirectedPair true = Ici 1 := rfl

theorem isOpen_nondirectedPair (b : Bool) : IsOpen (nondirectedPair b) :=
  isOpen_discrete _

theorem iUnion_nondirectedPair : ⋃ b, nondirectedPair b = univ := by
  ext n
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases h : n ≤ 1
  · exact ⟨false, h⟩
  · exact ⟨true, mem_Ici.mpr (by omega)⟩

theorem not_directed_nondirectedPair : ¬ Directed (· ⊆ ·) nondirectedPair := by
  intro h
  obtain ⟨z, h0, h1⟩ := h false true
  cases z
  · have h2 : (2 : ℕ) ∈ nondirectedPair false :=
      h1 (show (2 : ℕ) ∈ nondirectedPair true from mem_Ici.mpr (by omega))
    exact absurd (mem_Iic.mp h2) (by omega)
  · have h0' : (0 : ℕ) ∈ nondirectedPair true :=
      h0 (show (0 : ℕ) ∈ nondirectedPair false from mem_Iic.mpr (by omega))
    exact absurd (mem_Ici.mp h0') (by omega)

/-- The compatible family `(∅, {1})` over the nondirected pair. -/
def nondirectedFamily : ∀ b, FellCloseds ↥(nondirectedPair b)
  | false => ⊥
  | true => ⟨(↑) ⁻¹' {1}, isClosed_singleton.preimage continuous_subtype_val⟩

theorem isCompatFamily_nondirectedFamily :
    IsCompatFamily nondirectedPair nondirectedFamily := by
  rintro (_ | _) (_ | _) hij
  · rfl
  · exact absurd
      (mem_Ici.mp (hij (show (0 : ℕ) ∈ nondirectedPair false from mem_Iic.mpr (by omega))))
      (by omega)
  · exact absurd
      (mem_Iic.mp (hij (show (2 : ℕ) ∈ nondirectedPair true from mem_Ici.mpr (by omega))))
      (by omega)
  · rfl

/-- **Directedness is load-bearing at statement level**: over the
nondirected pair — an open cover of `ℕ` failing only directedness —
the canonical map into the projective limit is not surjective.  The
memo's glue step ("directedness gives `U k ⊇ U i ∪ U j`") is not a
proof convenience but a hypothesis the statement itself needs. -/
theorem not_surjective_toProjLim_nondirectedPair :
    ¬ Function.Surjective (toProjLim nondirectedPair) := by
  intro hsurj
  obtain ⟨F, hF⟩ := hsurj ⟨nondirectedFamily, isCompatFamily_nondirectedFamily⟩
  have htrue : clip (nondirectedPair true) F = nondirectedFamily true :=
    congrFun (congrArg Subtype.val hF) true
  have hfalse : clip (nondirectedPair false) F = nondirectedFamily false :=
    congrFun (congrArg Subtype.val hF) false
  have h1F : (1 : ℕ) ∈ F := by
    have e1 : (⟨1, mem_Ici.mpr le_rfl⟩ : ↥(nondirectedPair true)) ∈ nondirectedFamily true :=
      rfl
    rw [← htrue] at e1
    exact mem_clip.mp e1
  have e0 : (⟨1, mem_Iic.mpr le_rfl⟩ : ↥(nondirectedPair false)) ∈ nondirectedFamily false := by
    rw [← hfalse]
    exact mem_clip.mpr h1F
  exact notMem_empty _ e0

end NondirectedWitness

/-! ## Refuting fixture II: the Vietoris upper face cannot descend

Over the directed cover `Iic` of `ℕ`, the singleton `{⊥}` is the miss
class of the closed noncompact parameter `univ` — Vietoris-open
unconditionally — yet not open in the limit topology: every finite
conjunction of clip constraints is satisfied by a far-enough singleton
`{n}`, whose clips agree with `⊥`'s on every constrained level.  So no
hyperspace topology with the closed-miss upper face satisfies descent,
while the descent theorem above shows the compact-miss one does: the
Fell trade is load-bearing, not aesthetic. -/

section VietorisMissWitness

/-- Misses of closed noncompact parameters are not limit-detectable:
`{⊥}` fails to be open in the limit topology of the `Iic` system. -/
theorem not_isOpen_iInf_induced_singleton_bot :
    ¬ IsOpen[⨅ i : ℕ, TopologicalSpace.induced (clip (Iic i)) FellCloseds.topology]
      {(⊥ : FellCloseds ℕ)} := by
  intro hopen
  have hmem : {(⊥ : FellCloseds ℕ)}
      ∈ @nhds _ (⨅ i : ℕ, TopologicalSpace.induced (clip (Iic i)) FellCloseds.topology) ⊥ := by
    letI : TopologicalSpace (FellCloseds ℕ) :=
      ⨅ i : ℕ, TopologicalSpace.induced (clip (Iic i)) FellCloseds.topology
    exact hopen.mem_nhds rfl
  rw [nhds_iInf] at hmem
  obtain ⟨I, hIfin, V, hV, hVeq⟩ := Filter.mem_iInf.mp hmem
  obtain ⟨m, hm⟩ := hIfin.bddAbove
  set G : FellCloseds ℕ := ⟨{m + 1}, isClosed_singleton⟩ with hGdef
  have hGclip : ∀ i ∈ I, clip (Iic i) G = clip (Iic i) (⊥ : FellCloseds ℕ) := by
    intro i hi
    apply FellCloseds.ext
    ext x
    simp only [coe_clip, hGdef, coe_mk, coe_bot, mem_preimage, mem_singleton_iff,
      mem_empty_iff_false, iff_false]
    intro hxm
    have hxi : (x : ℕ) ≤ i := x.2
    have him : i ≤ m := hm hi
    omega
  have hGmem : G ∈ ⋂ i, V i := by
    rw [mem_iInter]
    intro i
    obtain ⟨u, hu, husub⟩ := (mem_nhds_induced (clip (Iic (i : ℕ))) ⊥ (V i)).mp (hV i)
    apply husub
    show clip (Iic (i : ℕ)) G ∈ u
    rw [hGclip (i : ℕ) i.2]
    exact mem_of_mem_nhds hu
  rw [← hVeq] at hGmem
  have hcoe : ({m + 1} : Set ℕ) = ∅ :=
    congrArg (fun F : FellCloseds ℕ => (F : Set ℕ)) (mem_singleton_iff.mp hGmem)
  exact singleton_ne_empty (m + 1) hcoe

/-- At the powerset stratum the corresponding Vietoris class is open
unconditionally: `{∅}` is the powerset of the open set `∅`. -/
theorem isOpen_vietoris_singleton_empty :
    IsOpen[TopologicalSpace.vietoris ℕ] {(∅ : Set ℕ)} := by
  rw [← Set.powerset_empty]
  exact isOpen_empty.powerset_vietoris

/-- **The Vietoris upper face fails descent**: the limit topology of
the `Iic` system does not refine the closeds-restricted Vietoris
topology — while by the descent theorem it coincides with the Fell
topology.  A hyperspace topology descends along directed open covers
only if its miss face is compactly indexed. -/
theorem not_iInf_induced_le_vietoris :
    ¬ (⨅ i : ℕ, TopologicalSpace.induced (clip (Iic i)) FellCloseds.topology)
        ≤ TopologicalSpace.induced ((↑) : FellCloseds ℕ → Set ℕ)
            (TopologicalSpace.vietoris ℕ) := by
  intro hle
  have hpre : ((↑) : FellCloseds ℕ → Set ℕ) ⁻¹' {(∅ : Set ℕ)} = {(⊥ : FellCloseds ℕ)} := by
    ext F
    constructor
    · intro hF
      exact FellCloseds.ext ((mem_singleton_iff.mp hF).trans coe_bot.symm)
    · intro hF
      have hFbot : F = ⊥ := hF
      rw [hFbot]
      exact coe_bot
  have hopen : IsOpen[TopologicalSpace.induced ((↑) : FellCloseds ℕ → Set ℕ)
      (TopologicalSpace.vietoris ℕ)] {(⊥ : FellCloseds ℕ)} :=
    (isOpen_induced_iff (t := TopologicalSpace.vietoris ℕ)).mpr
      ⟨{(∅ : Set ℕ)}, isOpen_vietoris_singleton_empty, hpre⟩
  exact not_isOpen_iInf_induced_singleton_bot (hopen.mono hle)

end VietorisMissWitness

end FellCloseds

end SuFunctor.Universe

#print axioms SuFunctor.Universe.FellCloseds.projLimHomeomorph
#print axioms SuFunctor.Universe.FellCloseds.isHomeomorph_toProjLim_of_directed
#print axioms SuFunctor.Universe.FellCloseds.not_surjective_toProjLim_nondirectedPair
#print axioms SuFunctor.Universe.FellCloseds.not_isOpen_iInf_induced_singleton_bot
#print axioms SuFunctor.Universe.FellCloseds.not_iInf_induced_le_vietoris
