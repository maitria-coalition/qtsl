import SuFunctor.Universe.FellTopology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Sets.Opens

/-! # Capacity presentation: hit-and-miss generators determine laws

Classically (Choquet; Matheron; see Molchanov, *Theory of Random
Sets*), the law of a random closed set is determined by its capacity
functional on a generating class of hit-and-miss events.  This module
proves the point-set shadow of that determination principle for the
Fell hyperspace `FellCloseds Y` of a locally compact Hausdorff ambient
`Y`, from a countable generator family indexed by *formal data*: given
a basis `B : ι → Set Y` whose members have compact closures, the
**∇-generators**

`nablaGen B hits misses
  = {F | (∀ i ∈ hits, F ∩ B i ≠ ∅) ∧ ∀ j ∈ misses, F ∩ closure (B j) = ∅}`

(finitely many hit demands and finitely many miss demands, each named
by a basis index) form a topological **basis** of the Fell hyperspace
(`isTopologicalBasis_nablaGen`).  Three consequences:

* **second countability** — for countable `ι` the hyperspace is second
  countable (`secondCountableTopology_of_basis`), hence compact
  Hausdorff second countable, i.e. metrizable, over any locally
  compact second-countable Hausdorff ambient (the `instance`);
* **determination of Borel laws** (`measure_ext_of_nablaGen`): two
  finite Borel measures on the hyperspace agreeing on every
  ∇-generator are equal — the generators form a π-system containing
  the empty crescent `univ`, so total-mass agreement is part of the
  generator agreement and the π-λ machinery applies; the separating
  corollary (`exists_nablaGen_measure_ne`) certifies distinctness of
  two laws by a *single* generator, i.e. by finite formal data;
* **determination of Scott-continuous functionals**
  (`scottContinuous_ext_of_nablaGen`): two Scott-continuous maps on
  the frame of opens agreeing on finite joins of ∇-generators are
  equal — the frame-level determination, with no measure theory and no
  countability.

Two boundary theorems keep the design honest:

* `not_isOpen_disjoint_univ` — the miss face's compactness constraint
  is not removable: over a noncompact ambient, the miss class of a
  noncompact closed set fails to be Fell-open (via the escape
  specimen of `FellTopology`);
* `exists_scottContinuous_eq_on_lower_ne` — the hit face alone does
  not determine: two Scott-continuous functionals can agree on the
  entire lower (hit-generated) topology yet differ on a compact-miss
  open.  The witness pair is the Dirac functional of the empty set
  against the indicator of the full open: escape mass is exactly what
  hit events cannot see.  (Classically, hit-only determination
  survives at the σ-algebra level because σ-algebras grant
  complements; the frame of opens does not, and this theorem is that
  difference made precise.)
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace

open scoped ENNReal

attribute [local instance] SuFunctor.Universe.fell

namespace FellCloseds

variable {Y : Type*} [TopologicalSpace Y] {ι : Type*}

/-- The ∇-generator of the Fell hyperspace over formal data: finitely
many hit demands and finitely many miss demands, each named by an
index into the basis family `B`.  Misses are taken against closures so
that a compact-closure basis yields Fell-open generators. -/
def nablaGen (B : ι → Set Y) (hits misses : Finset ι) : Set (FellCloseds Y) :=
  {F | (∀ i ∈ hits, ((F : Set Y) ∩ B i).Nonempty) ∧
    ∀ j ∈ misses, Disjoint (F : Set Y) (closure (B j))}

theorem mem_nablaGen_iff {B : ι → Set Y} {hits misses : Finset ι} {F : FellCloseds Y} :
    F ∈ nablaGen B hits misses ↔
      (∀ i ∈ hits, ((F : Set Y) ∩ B i).Nonempty) ∧
        ∀ j ∈ misses, Disjoint (F : Set Y) (closure (B j)) :=
  Iff.rfl

@[simp]
theorem nablaGen_empty_empty {B : ι → Set Y} : nablaGen B ∅ ∅ = univ := by
  ext F
  simp [nablaGen]

/-- Intersecting two ∇-generators unions their formal data: the
generator family is a π-system by construction. -/
theorem nablaGen_inter_nablaGen [DecidableEq ι] {B : ι → Set Y}
    {h₁ h₂ m₁ m₂ : Finset ι} :
    nablaGen B (h₁ ∪ h₂) (m₁ ∪ m₂) = nablaGen B h₁ m₁ ∩ nablaGen B h₂ m₂ := by
  ext F
  simp only [mem_nablaGen_iff, Set.mem_inter_iff, Finset.forall_mem_union]
  constructor
  · rintro ⟨⟨hh₁, hh₂⟩, hm₁, hm₂⟩
    exact ⟨⟨hh₁, hm₁⟩, hh₂, hm₂⟩
  · rintro ⟨⟨hh₁, hm₁⟩, hh₂, hm₂⟩
    exact ⟨⟨hh₁, hh₂⟩, hm₁, hm₂⟩

/-- Enlarging the formal data shrinks the generator. -/
theorem nablaGen_anti {B : ι → Set Y} {h₁ h₂ m₁ m₂ : Finset ι}
    (hh : h₁ ⊆ h₂) (hm : m₁ ⊆ m₂) :
    nablaGen B h₂ m₂ ⊆ nablaGen B h₁ m₁ := by
  rintro F ⟨hhit, hmiss⟩
  exact ⟨fun i hi => hhit i (hh hi), fun j hj => hmiss j (hm hj)⟩

theorem nablaGen_eq_biInter {B : ι → Set Y} {hits misses : Finset ι} :
    nablaGen B hits misses
      = (⋂ i ∈ hits, {F : FellCloseds Y | ((F : Set Y) ∩ B i).Nonempty})
        ∩ ⋂ j ∈ misses, {F : FellCloseds Y | Disjoint (F : Set Y) (closure (B j))} := by
  ext F
  simp [nablaGen, Set.mem_iInter]

/-- ∇-generators over an open family with compact closures are
Fell-open: the hit demands by openness, the miss demands by
compactness of the closures. -/
theorem isOpen_nablaGen {B : ι → Set Y} (hBo : ∀ i, IsOpen (B i))
    (hBcl : ∀ i, IsCompact (closure (B i))) (hits misses : Finset ι) :
    IsOpen (nablaGen B hits misses) := by
  rw [nablaGen_eq_biInter]
  exact (isOpen_biInter_finset fun i _ =>
      isOpen_inter_nonempty_of_isOpen (hBo i)).inter
    (isOpen_biInter_finset fun j _ =>
      isOpen_disjoint_of_isCompact (hBcl j))

/-- **The ∇-basis theorem.**  Over a locally compact Hausdorff
ambient, the ∇-generators of any basis with compact closures form a
topological basis of the Fell hyperspace.  The hit face is immediate
from the basis property; the miss face interpolates a compact set
between a compact miss parameter and the complement of a closed set,
then covers it by finitely many basis members whose closures stay
inside the interpolant. -/
theorem isTopologicalBasis_nablaGen [LocallyCompactSpace Y] [T2Space Y]
    {B : ι → Set Y} (hB : IsTopologicalBasis (Set.range B))
    (hBcl : ∀ i, IsCompact (closure (B i))) :
    IsTopologicalBasis
      (Set.range fun p : Finset ι × Finset ι => nablaGen B p.1 p.2) := by
  classical
  have hBo : ∀ i, IsOpen (B i) := fun i => hB.isOpen ⟨i, rfl⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact isOpen_nablaGen hBo hBcl p.1 p.2
  · intro F U hFU hU
    -- the ambient basis of the hyperspace: finite intersections of the
    -- Fell subbasis, pulled back along the (inducing) coercion
    have hbasis :=
      (TopologicalSpace.isTopologicalBasis_of_subbasis
        (rfl : SuFunctor.Universe.fell Y = _)).isInducing isEmbedding_coe.isInducing
    obtain ⟨b, hb, hFb, hbU⟩ := hbasis.exists_subset_of_mem_open hFU hU
    obtain ⟨t, ⟨f, ⟨hffin, hfsub⟩, rfl⟩, rfl⟩ := hb
    have hFf : ∀ s ∈ f, (F : Set Y) ∈ s := fun s hsf =>
      mem_sInter.mp (mem_preimage.mp hFb) s hsf
    -- each subbasic member of the cell refines to a ∇-generator around `F`
    have href : ∀ s ∈ f, ∃ p : Finset ι × Finset ι,
        F ∈ nablaGen B p.1 p.2 ∧ nablaGen B p.1 p.2 ⊆ (↑) ⁻¹' s := by
      intro s hsf
      rcases hfsub hsf with ⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩
      · -- miss case: `s = {u | Disjoint u K}` with `K` compact
        have hFK : Disjoint (F : Set Y) K := hFf _ hsf
        have hKF : K ⊆ ((F : Set Y))ᶜ := fun x hxK =>
          Set.disjoint_right.mp hFK hxK
        have hcover : ∀ x ∈ K, ∃ i : ι, x ∈ B i ∧ closure (B i) ⊆ ((F : Set Y))ᶜ := by
          intro x hxK
          obtain ⟨L, hL, hxL, hLF⟩ :=
            exists_compact_between isCompact_singleton
              F.isClosed.isOpen_compl (singleton_subset_iff.mpr (hKF hxK))
          obtain ⟨w, ⟨i, rfl⟩, hxw, hwL⟩ :=
            hB.exists_subset_of_mem_open (singleton_subset_iff.mp hxL)
              isOpen_interior
          refine ⟨i, hxw, subset_trans ?_ hLF⟩
          exact (closure_mono hwL).trans
            ((closure_mono interior_subset).trans hL.isClosed.closure_eq.subset)
        obtain ⟨tσ, htσ⟩ :=
          hK.elim_finite_subcover
            (fun j : {i : ι // closure (B i) ⊆ ((F : Set Y))ᶜ} => B j.1)
            (fun j => hBo j.1)
            (fun x hxK => by
              obtain ⟨i, hxi, hicl⟩ := hcover x hxK
              exact mem_iUnion.mpr ⟨⟨i, hicl⟩, hxi⟩)
        refine ⟨(∅, tσ.image Subtype.val), ⟨?_, ?_⟩, ?_⟩
        · intro i hi
          exact absurd hi (Finset.notMem_empty i)
        · intro j hj
          obtain ⟨jσ, -, rfl⟩ := Finset.mem_image.mp hj
          exact Set.disjoint_left.mpr fun a haF hacl => jσ.2 hacl haF
        · rintro G ⟨-, gmiss⟩
          refine mem_preimage.mpr (Set.disjoint_right.mpr fun x hxK hxG => ?_)
          obtain ⟨jσ, hjσ, hxBj⟩ := mem_iUnion₂.mp (htσ hxK)
          exact Set.disjoint_right.mp
            (gmiss jσ.1 (Finset.mem_image_of_mem _ hjσ))
            (subset_closure hxBj) hxG
      · -- hit case: `s = {u | (u ∩ V).Nonempty}` with `V` open
        obtain ⟨y, hyF, hyV⟩ := hFf _ hsf
        obtain ⟨w, ⟨i, rfl⟩, hyw, hwV⟩ := hB.exists_subset_of_mem_open hyV hV
        refine ⟨({i}, ∅), ⟨?_, ?_⟩, ?_⟩
        · intro j hj
          rw [Finset.mem_singleton] at hj
          exact hj ▸ ⟨y, hyF, hyw⟩
        · intro j hj
          exact absurd hj (Finset.notMem_empty j)
        · rintro G ⟨ghit, -⟩
          obtain ⟨z, hzG, hzB⟩ := ghit i (Finset.mem_singleton_self i)
          exact mem_preimage.mpr ⟨z, hzG, hwV hzB⟩
    choose! p hpmem hpsub using href
    set H : Finset ι := hffin.toFinset.biUnion fun s => (p s).1 with hH
    set M : Finset ι := hffin.toFinset.biUnion fun s => (p s).2 with hM
    refine ⟨nablaGen B H M, ⟨(H, M), rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨s, hs, his⟩ := Finset.mem_biUnion.mp hi
      exact (hpmem s (hffin.mem_toFinset.mp hs)).1 i his
    · intro j hj
      obtain ⟨s, hs, hjs⟩ := Finset.mem_biUnion.mp hj
      exact (hpmem s (hffin.mem_toFinset.mp hs)).2 j hjs
    · intro G hG
      refine hbU (mem_preimage.mpr (mem_sInter.mpr fun s hsf => ?_))
      exact mem_preimage.mp
        (hpsub s hsf
          (nablaGen_anti
            (Finset.subset_biUnion_of_mem _ (hffin.mem_toFinset.mpr hsf))
            (Finset.subset_biUnion_of_mem _ (hffin.mem_toFinset.mpr hsf)) hG))

/-- Countable formal data gives a second-countable hyperspace. -/
theorem secondCountableTopology_of_basis [LocallyCompactSpace Y] [T2Space Y]
    [Countable ι] {B : ι → Set Y} (hB : IsTopologicalBasis (Set.range B))
    (hBcl : ∀ i, IsCompact (closure (B i))) :
    SecondCountableTopology (FellCloseds Y) :=
  (isTopologicalBasis_nablaGen hB hBcl).secondCountableTopology
    (Set.countable_range _)

/-- A locally compact Hausdorff second-countable space has a countable
basis whose members have compact closures. -/
theorem exists_countable_basis_isCompact_closure
    (Y : Type*) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] :
    ∃ b : Set (Set Y), b.Countable ∧ IsTopologicalBasis b ∧
      ∀ U ∈ b, IsCompact (closure U) := by
  refine ⟨{U ∈ countableBasis Y | IsCompact (closure U)},
    (countable_countableBasis Y).mono (Set.sep_subset _ _),
    isTopologicalBasis_of_isOpen_of_nhds ?_ ?_, fun U hU => hU.2⟩
  · rintro u ⟨hu, -⟩
    exact (isBasis_countableBasis Y).isOpen hu
  · intro y V hyV hV
    obtain ⟨L, hL, hyL, hLV⟩ :=
      exists_compact_between isCompact_singleton hV (singleton_subset_iff.mpr hyV)
    obtain ⟨U, hUb, hyU, hUL⟩ :=
      (isBasis_countableBasis Y).exists_subset_of_mem_open
        (singleton_subset_iff.mp hyL) isOpen_interior
    refine ⟨U, ⟨hUb, ?_⟩, hyU, hUL.trans (interior_subset.trans hLV)⟩
    exact hL.of_isClosed_subset isClosed_closure
      ((closure_mono hUL).trans
        ((closure_mono interior_subset).trans hL.isClosed.closure_eq.subset))

/-- Over a locally compact second-countable Hausdorff ambient, the
Fell hyperspace is second countable — hence, with the unconditional
`compactSpace` and `t2Space`, compact metrizable. -/
instance instSecondCountableTopology
    [LocallyCompactSpace Y] [T2Space Y] [SecondCountableTopology Y] :
    SecondCountableTopology (FellCloseds Y) := by
  obtain ⟨b, hbc, hbB, hbcl⟩ := exists_countable_basis_isCompact_closure Y
  haveI : Countable ↥b := hbc.to_subtype
  exact secondCountableTopology_of_basis
    (B := fun U : ↥b => (U : Set Y)) (by rwa [Subtype.range_coe])
    fun U => hbcl U U.2

section Measure

open MeasureTheory

/-- **The capacity-presentation lemma** (determination half of
Choquet–Matheron, on the Fell hyperspace): two finite Borel measures
on `FellCloseds Y` that agree on every ∇-generator are equal.  The
generator family is a countable π-system containing `univ` (the empty
crescent), and it generates the Borel σ-algebra because the
∇-generators form a countable basis. -/
theorem measure_ext_of_nablaGen [LocallyCompactSpace Y] [T2Space Y] [Countable ι]
    {B : ι → Set Y} (hB : IsTopologicalBasis (Set.range B))
    (hBcl : ∀ i, IsCompact (closure (B i)))
    [MeasurableSpace (FellCloseds Y)] [BorelSpace (FellCloseds Y)]
    {μ ν : Measure (FellCloseds Y)} [IsFiniteMeasure μ]
    (h : ∀ hits misses : Finset ι,
      μ (nablaGen B hits misses) = ν (nablaGen B hits misses)) :
    μ = ν := by
  classical
  haveI := secondCountableTopology_of_basis hB hBcl
  refine ext_of_generate_finite
    (Set.range fun p : Finset ι × Finset ι => nablaGen B p.1 p.2)
    (BorelSpace.measurable_eq.trans
      (isTopologicalBasis_nablaGen hB hBcl).borel_eq_generateFrom)
    ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ -
    exact ⟨(p.1 ∪ q.1, p.2 ∪ q.2), nablaGen_inter_nablaGen⟩
  · rintro _ ⟨p, rfl⟩
    exact h p.1 p.2
  · simpa using h ∅ ∅

/-- The separating form: two distinct finite Borel laws on the
hyperspace are separated by a single ∇-generator — finite formal data
(two finite sets of basis indices) certifies distinctness. -/
theorem exists_nablaGen_measure_ne [LocallyCompactSpace Y] [T2Space Y] [Countable ι]
    {B : ι → Set Y} (hB : IsTopologicalBasis (Set.range B))
    (hBcl : ∀ i, IsCompact (closure (B i)))
    [MeasurableSpace (FellCloseds Y)] [BorelSpace (FellCloseds Y)]
    {μ ν : Measure (FellCloseds Y)} [IsFiniteMeasure μ]
    (hμν : μ ≠ ν) :
    ∃ hits misses : Finset ι,
      μ (nablaGen B hits misses) ≠ ν (nablaGen B hits misses) := by
  by_contra hcon
  push Not at hcon
  exact hμν (measure_ext_of_nablaGen hB hBcl fun hits misses => hcon hits misses)

end Measure

section Frame

open TopologicalSpace (Opens)

/-- **Frame-level determination**: two Scott-continuous maps on the
frame of opens of the Fell hyperspace that agree on all finite joins
of ∇-generators are equal.  This is the pointfree shadow of the
capacity presentation: no measures, no σ-algebra, no countability —
the join-closure of the ∇-basis is directed below every open, with
that open as least upper bound. -/
theorem scottContinuous_ext_of_nablaGen [LocallyCompactSpace Y] [T2Space Y]
    {B : ι → Set Y} (hB : IsTopologicalBasis (Set.range B))
    (hBcl : ∀ i, IsCompact (closure (B i)))
    {β : Type*} [PartialOrder β] {f g : Opens (FellCloseds Y) → β}
    (hf : ScottContinuous f) (hg : ScottContinuous g)
    (h : ∀ U : Opens (FellCloseds Y),
      (∃ s : Finset (Finset ι × Finset ι),
        (U : Set (FellCloseds Y)) = ⋃ p ∈ s, nablaGen B p.1 p.2) →
      f U = g U) :
    f = g := by
  classical
  have hBo : ∀ i, IsOpen (B i) := fun i => hB.isOpen ⟨i, rfl⟩
  funext U
  set D : Set (Opens (FellCloseds Y)) :=
    {V | (∃ s : Finset (Finset ι × Finset ι),
      (V : Set (FellCloseds Y)) = ⋃ p ∈ s, nablaGen B p.1 p.2) ∧ V ≤ U} with hD
  have hDne : D.Nonempty := by
    refine ⟨⊥, ⟨∅, ?_⟩, bot_le⟩
    rw [Opens.coe_bot]
    ext x
    simp
  have hDdir : DirectedOn (· ≤ ·) D := by
    rintro V₁ ⟨⟨s₁, hs₁⟩, hV₁U⟩ V₂ ⟨⟨s₂, hs₂⟩, hV₂U⟩
    refine ⟨V₁ ⊔ V₂, ⟨⟨s₁ ∪ s₂, ?_⟩, sup_le hV₁U hV₂U⟩, le_sup_left, le_sup_right⟩
    rw [Opens.coe_sup, hs₁, hs₂, Finset.set_biUnion_union]
  have hlub : IsLUB D U := by
    constructor
    · rintro V ⟨-, hVU⟩
      exact hVU
    · intro W hW
      rw [SetLike.le_def]
      intro x hxU
      obtain ⟨v, ⟨p, rfl⟩, hxv, hvU⟩ :=
        (isTopologicalBasis_nablaGen hB hBcl).exists_subset_of_mem_open hxU U.isOpen
      have hmem : (⟨nablaGen B p.1 p.2, isOpen_nablaGen hBo hBcl p.1 p.2⟩ :
          Opens (FellCloseds Y)) ∈ D := by
        refine ⟨⟨{p}, ?_⟩, SetLike.coe_subset_coe.mp hvU⟩
        simp
      exact SetLike.le_def.mp (hW hmem) hxv
  have himg : f '' D = g '' D :=
    Set.image_congr fun V hV => h V hV.1
  exact (hf hDne hDdir hlub).unique (himg.symm ▸ hg hDne hDdir hlub)

/-- **The miss face is load-bearing**: over a noncompact T1 ambient,
the miss class of the (noncompact, closed) full ambient is not
Fell-open — it is the singleton of the escape point, which the escape
specimen shows is open only over a compact ambient.  A generator
family whose misses ranged over arbitrary closed sets would therefore
leave the Fell topology. -/
theorem not_isOpen_disjoint_univ [T1Space Y] (hY : ¬CompactSpace Y) :
    ¬IsOpen {F : FellCloseds Y | Disjoint (F : Set Y) univ} := by
  have heq : {F : FellCloseds Y | Disjoint (F : Set Y) univ} = {⊥} := by
    ext F
    simp only [mem_setOf_eq, Set.disjoint_iff_inter_eq_empty, Set.inter_univ,
      Set.mem_singleton_iff]
    constructor
    · intro hF
      exact FellCloseds.ext (hF.trans coe_bot.symm)
    · intro hF
      rw [hF, coe_bot]
  rw [heq]
  intro hopen
  exact hY (isOpen_singleton_bot_iff_compactSpace.mp hopen)

/-- **The hit face alone does not determine**: there are two
Scott-continuous functionals on the frame of opens of the Fell
hyperspace that agree on every open of the lower (hit-generated)
topology yet differ.  The pair is the Dirac functional of the escape
point `⊥` against the indicator of the full open: a hit-generated open
containing the empty set is already the whole hyperspace, so the two
agree on the entire lower topology, while a compact-miss open
separates them.  Escape mass is exactly what hit events cannot see.
Scott continuity of the second functional uses compactness of the
hyperspace: a directed family of opens with join the whole space has a
member equal to the whole space. -/
theorem exists_scottContinuous_eq_on_lower_ne [T1Space Y] [Nonempty Y] :
    ∃ f g : Opens (FellCloseds Y) → ℝ≥0∞,
      ScottContinuous f ∧ ScottContinuous g ∧
      (∀ U : Opens (FellCloseds Y),
        IsOpen[TopologicalSpace.generateFrom
          ((fun V => {F : FellCloseds Y | ((F : Set Y) ∩ V).Nonempty})
            '' {V : Set Y | IsOpen V})]
          (U : Set (FellCloseds Y)) → f U = g U) ∧
      f ≠ g := by
  classical
  refine ⟨fun U => if (⊥ : FellCloseds Y) ∈ U then 1 else 0,
    fun U => if U = ⊤ then 1 else 0, ?_, ?_, ?_, ?_⟩
  · -- Scott continuity of the Dirac functional of the escape point
    intro d hdne hddir a hlub
    have ha : sSup d = a := hlub.sSup_eq
    by_cases hbot : (⊥ : FellCloseds Y) ∈ a
    · have hfa : (fun U => if (⊥ : FellCloseds Y) ∈ U then (1 : ℝ≥0∞) else 0) a
          = 1 := if_pos hbot
      rw [hfa]
      have hbot' : (⊥ : FellCloseds Y) ∈ sSup d := by rw [ha]; exact hbot
      obtain ⟨V, hVd, hbotV⟩ := Opens.mem_sSup.mp hbot'
      constructor
      · rintro _ ⟨W, -, rfl⟩
        by_cases hW : (⊥ : FellCloseds Y) ∈ W <;> simp [hW]
      · intro b hb
        have h1 : (1 : ℝ≥0∞) ∈
            (fun U => if (⊥ : FellCloseds Y) ∈ U then 1 else 0) '' d :=
          ⟨V, hVd, if_pos hbotV⟩
        exact hb h1
    · have hfa : (fun U => if (⊥ : FellCloseds Y) ∈ U then (1 : ℝ≥0∞) else 0) a
          = 0 := if_neg hbot
      have himg : (fun U => if (⊥ : FellCloseds Y) ∈ U then (1 : ℝ≥0∞) else 0) '' d
          = {0} := by
        refine Set.eq_singleton_iff_nonempty_unique_mem.mpr
          ⟨hdne.image _, ?_⟩
        rintro _ ⟨W, hWd, rfl⟩
        exact if_neg fun hbotW => hbot (SetLike.le_def.mp (hlub.1 hWd) hbotW)
      rw [hfa, himg]
      exact isLUB_singleton
  · -- Scott continuity of the indicator of the full open: uses
    -- compactness of the hyperspace
    intro d hdne hddir a hlub
    have ha : sSup d = a := hlub.sSup_eq
    by_cases htop : a = ⊤
    · have hga : (fun U => if U = ⊤ then (1 : ℝ≥0∞) else 0) a = 1 :=
        if_pos htop
      rw [hga]
      -- a directed open cover of the compact hyperspace has a member
      -- equal to the whole space
      obtain ⟨t, ht⟩ :=
        isCompact_univ.elim_finite_subcover
          (fun V : ↥d => ((V : Opens (FellCloseds Y)) : Set (FellCloseds Y)))
          (fun V => (V : Opens (FellCloseds Y)).isOpen)
          (by
            intro x _
            have hx : x ∈ sSup d := by
              rw [ha, htop]
              trivial
            obtain ⟨V, hVd, hxV⟩ := Opens.mem_sSup.mp hx
            exact mem_iUnion.mpr ⟨⟨V, hVd⟩, hxV⟩)
      haveI : Nonempty ↥d := hdne.to_subtype
      obtain ⟨z, hz⟩ := (directedOn_iff_directed.mp hddir).finset_le t
      have hztop : (z : Opens (FellCloseds Y)) = ⊤ := by
        refine top_unique (SetLike.le_def.mpr fun x _ => ?_)
        obtain ⟨V, hVt, hxV⟩ := mem_iUnion₂.mp (ht (mem_univ x))
        exact SetLike.le_def.mp (hz V hVt) hxV
      constructor
      · rintro _ ⟨W, -, rfl⟩
        by_cases hW : W = ⊤ <;> simp [hW]
      · intro b hb
        exact hb ⟨z, z.2, if_pos hztop⟩
    · have hga : (fun U => if U = ⊤ then (1 : ℝ≥0∞) else 0) a = 0 :=
        if_neg htop
      have himg : (fun U => if U = ⊤ then (1 : ℝ≥0∞) else 0) '' d
          = ({0} : Set ℝ≥0∞) := by
        refine Set.eq_singleton_iff_nonempty_unique_mem.mpr
          ⟨hdne.image _, ?_⟩
        rintro _ ⟨W, hWd, rfl⟩
        refine if_neg fun hWtop => htop ?_
        exact top_unique (hWtop ▸ hlub.1 hWd)
      rw [hga, himg]
      exact isLUB_singleton
  · -- agreement on the lower (hit-generated) topology
    intro U hUlow
    have key : ∀ s : Set (FellCloseds Y),
        IsOpen[TopologicalSpace.generateFrom
          ((fun V => {F : FellCloseds Y | ((F : Set Y) ∩ V).Nonempty})
            '' {V : Set Y | IsOpen V})] s →
        (⊥ : FellCloseds Y) ∈ s → s = univ := by
      intro s hs
      induction hs with
      | basic v hv =>
        intro hbot
        obtain ⟨W, -, rfl⟩ := hv
        simp only [mem_setOf_eq, coe_bot, Set.empty_inter] at hbot
        exact absurd hbot Set.not_nonempty_empty
      | univ => exact fun _ => rfl
      | inter s₁ s₂ h₁ h₂ ih₁ ih₂ =>
        rintro ⟨hb₁, hb₂⟩
        rw [ih₁ hb₁, ih₂ hb₂, Set.univ_inter]
      | sUnion S hS ih =>
        rintro ⟨w, hwS, hbw⟩
        exact Set.eq_univ_of_univ_subset
          ((ih w hwS hbw) ▸ Set.subset_sUnion_of_mem hwS)
    have hiff : (⊥ : FellCloseds Y) ∈ U ↔ U = ⊤ := by
      constructor
      · intro hbot
        exact Opens.ext ((key (U : Set (FellCloseds Y)) hUlow hbot).trans rfl)
      · rintro rfl
        trivial
    show (if (⊥ : FellCloseds Y) ∈ U then (1 : ℝ≥0∞) else 0)
      = if U = ⊤ then (1 : ℝ≥0∞) else 0
    exact if_congr hiff rfl rfl
  · -- the two functionals differ on a compact-miss open
    intro hfg
    set y := Classical.arbitrary Y
    have hU₀open : IsOpen {F : FellCloseds Y | Disjoint (F : Set Y) {y}} :=
      isOpen_disjoint_of_isCompact isCompact_singleton
    set U₀ : Opens (FellCloseds Y) := ⟨_, hU₀open⟩ with hU₀
    have hbot : (⊥ : FellCloseds Y) ∈ U₀ := by
      show Disjoint ((⊥ : FellCloseds Y) : Set Y) {y}
      rw [coe_bot]
      exact Set.empty_disjoint _
    have hne : U₀ ≠ ⊤ := by
      intro htop
      have hmem : (⟨{y}, isClosed_singleton⟩ : FellCloseds Y) ∈ U₀ := by
        rw [htop]
        trivial
      have hdisj : Disjoint ({y} : Set Y) {y} := hmem
      have hnd : ¬Disjoint ({y} : Set Y) {y} :=
        Set.not_disjoint_iff.mpr ⟨y, rfl, rfl⟩
      exact hnd hdisj
    have h := congrFun hfg U₀
    simp [hbot, hne] at h

end Frame

end FellCloseds

end SuFunctor.Universe
