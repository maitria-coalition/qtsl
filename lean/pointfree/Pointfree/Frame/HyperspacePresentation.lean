import Pointfree.Frame.Presentation
import Pointfree.Valuation.Determination

/-! # The hyperspace frame, presented — and localic Choquet–Matheron

The hyperspace locale of hit-and-miss observations, presented by
generators and relations, with continuous valuations determined by
generator values.  No points, no spatial model, no countability.

**Generators.** Formal hit-and-miss data over an index type of basic
observations: finitely many hit demands and finitely many miss
demands (`NablaData`).  Data meet by union and the empty datum is the
top — exactly the π-law and unit of the spatial ∇-generators, carried
as *structure of the generator semilattice* rather than as relations.
In cover-modality terms (Venema–Vickers–Vosmaer, *Generalized
powerlocales via relation lifting*, 2012): the hit-and-miss data are
the ◇/□-decomposition of the ∇-basics, and presenting over their
meet-closure absorbs the slim-redistribution meet law (their (∇2))
into the site; their data-monotonicity (∇1) is likewise free, since
principal lower sets embed monotonically.

**Relations.** The base geometry enters as abstract relational data
on indices (`FellGeometry`) — which basic observations refine which
families, which miss-closures are covered, which differences refine —
and each geometry fact induces one inequality of the Fell/Vietoris
genre (`fellRelations`): hit-refinement, miss-covering,
miss-monotonicity, hit-miss refinement.  Each is spatially true of
the hit-and-miss generators of a Fell hyperspace under its geometric
reading (stated field by field below).  The adequacy-grade laws (the
way-below interpolation of the compact miss face, Scott continuity of
the miss face) are deliberately not encoded: they belong to the
localic reading of the fibre column, which remains argued design; the
determination theorem below is proven for the presented frame at an
**arbitrary** relation set, so no relation-set choice can gate it.

**The theorem.** `Pointfree.Valuation.ext_of_nabla`: two
Scott-continuous valuations on the presented hyperspace frame with
finite generator values, agreeing on every ∇-generator, are equal —
with `exists_nabla_ne` the single-generator separation corollary.
This is the determination half of the localic Choquet–Matheron
statement; the existence half (capacity functional to law) is
deliberately not claimed.
-/

namespace Pointfree

open LowerSet

/-- Formal hit-and-miss data: finitely many hit demands and finitely
many miss demands, each named by an index into a family of basic
observations.  The spatial reading of `⟨hits, misses⟩` over a basis
`B` is the ∇-generator
`{F | (∀ i ∈ hits, F ∩ B i ≠ ∅) ∧ ∀ j ∈ misses, F ∩ closure (B j) = ∅}`. -/
@[ext] structure NablaData (ι : Type*) where
  /-- The indices of the basic observations the record must hit. -/
  hits : Finset ι
  /-- The indices of the basic observations whose closures the record
  must miss. -/
  misses : Finset ι

namespace NablaData

variable {ι : Type*}

/-- A single hit demand. -/
def hit (i : ι) : NablaData ι := ⟨{i}, ∅⟩

/-- A single miss demand. -/
def miss (j : ι) : NablaData ι := ⟨∅, {j}⟩

/-- One hit demand beside one miss demand. -/
def hitMiss (i j : ι) : NablaData ι := ⟨{i}, {j}⟩

section Lattice

variable [DecidableEq ι]

/-- Hit-and-miss data form a meet-semilattice: meets accumulate the
formal data (the spatial π-law `∇p ∩ ∇q = ∇(p ∪ q)`, as structure). -/
instance : SemilatticeInf (NablaData ι) where
  le p q := q.hits ⊆ p.hits ∧ q.misses ⊆ p.misses
  le_refl _ := ⟨subset_rfl, subset_rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hqr.1.trans hpq.1, hqr.2.trans hpq.2⟩
  le_antisymm p q hpq hqp :=
    NablaData.ext (Finset.Subset.antisymm hqp.1 hpq.1)
      (Finset.Subset.antisymm hqp.2 hpq.2)
  inf p q := ⟨p.hits ∪ q.hits, p.misses ∪ q.misses⟩
  inf_le_left _ _ := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  inf_le_right _ _ := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
  le_inf _ _ _ hpq hpr :=
    ⟨Finset.union_subset hpq.1 hpr.1, Finset.union_subset hpq.2 hpr.2⟩

theorem le_def {p q : NablaData ι} :
    p ≤ q ↔ q.hits ⊆ p.hits ∧ q.misses ⊆ p.misses := Iff.rfl

@[simp] theorem inf_hits (p q : NablaData ι) :
    (p ⊓ q).hits = p.hits ∪ q.hits := rfl

@[simp] theorem inf_misses (p q : NablaData ι) :
    (p ⊓ q).misses = p.misses ∪ q.misses := rfl

/-- The empty datum is the top: no demands. -/
instance : OrderTop (NablaData ι) where
  top := ⟨∅, ∅⟩
  le_top _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

@[simp] theorem top_hits : (⊤ : NablaData ι).hits = ∅ := rfl

@[simp] theorem top_misses : (⊤ : NablaData ι).misses = ∅ := rfl

@[simp] theorem hit_inf_miss (i j : ι) : hit i ⊓ miss j = hitMiss i j := by
  ext1 <;> simp [hit, miss, hitMiss]

end Lattice

end NablaData

/-- The base geometry, as abstract relational data on indices: the
facts about a basis of observations that the presentation's relations
transpose.  Spatial readings (over a basis `B` with compact closures):

* `refines i T` — `B i ⊆ ⋃ k ∈ T, B k`;
* `missCovers j T` — `closure (B j) ⊆ ⋃ k ∈ T, B k`;
* `missMono j' j` — `closure (B j') ⊆ closure (B j)`;
* `diffCovers i j T` — `B i \ closure (B j) ⊆ ⋃ k ∈ T, B k`.

No topology is consumed here: a geometry is pure formal data, and any
actual basis realizes one. -/
structure FellGeometry (ι : Type*) where
  /-- Hit-refinement data: the observation `i` is covered by the
  family `T`. -/
  refines : ι → Set ι → Prop
  /-- Miss-covering data: the closure of observation `j` is covered by
  the family `T`. -/
  missCovers : ι → Set ι → Prop
  /-- Miss-monotonicity data: the closure of `j'` sits inside the
  closure of `j`. -/
  missMono : ι → ι → Prop
  /-- Hit-miss refinement data: what remains of observation `i` after
  removing the closure of `j` is covered by the family `T`. -/
  diffCovers : ι → ι → Set ι → Prop

variable {ι : Type*} [DecidableEq ι]

/-- The Fell/Vietoris relation set over a geometry, on the free frame
of the hit-and-miss data.  Four inequality families, each the
transposition of a spatially true fact about ∇-generators:

* **hit-refinement** — a hit demand refines along a cover of its
  observation (a record hitting `B i ⊆ ⋃ B k` hits some `B k`);
* **miss-covering** — every record either misses `closure (B j)` or
  hits a member of any family covering it;
* **miss-monotonicity** — missing a larger closure implies missing a
  smaller one;
* **hit-miss refinement** — a hit beside a miss refines along a cover
  of the difference (with the empty cover: a hit demand inside a miss
  closure annihilates, `∇ ≤ ⊥`). -/
def fellRelations (geom : FellGeometry ι) :
    Set (LowerSet (NablaData ι) × LowerSet (NablaData ι)) :=
  {r | (∃ i T, geom.refines i T ∧
        r = (Iic (NablaData.hit i), ⨆ k ∈ T, Iic (NablaData.hit k)))
    ∨ (∃ j T, geom.missCovers j T ∧
        r = (⊤, Iic (NablaData.miss j) ⊔ ⨆ k ∈ T, Iic (NablaData.hit k)))
    ∨ (∃ j' j, geom.missMono j' j ∧
        r = (Iic (NablaData.miss j), Iic (NablaData.miss j')))
    ∨ (∃ i j T, geom.diffCovers i j T ∧
        r = (Iic (NablaData.hitMiss i j), ⨆ k ∈ T, Iic (NablaData.hitMiss k j)))}

/-- The presented hyperspace frame: the free frame on the hit-and-miss
data, quotiented by the least nucleus forcing the Fell/Vietoris
relations over the geometry. -/
abbrev FellPresented (geom : FellGeometry ι) : Set (LowerSet (NablaData ι)) :=
  Presented (fellRelations geom)

/-- The ∇-generator of the presented hyperspace frame. -/
def nabla (geom : FellGeometry ι) (p : NablaData ι) : FellPresented geom :=
  gen (fellRelations geom) p

/-- The π-law, in the presented frame: intersecting ∇-generators
unions their formal data.  Free — no relation is spent on it. -/
theorem nabla_inf (geom : FellGeometry ι) (p q : NablaData ι) :
    nabla geom (p ⊓ q) = nabla geom p ⊓ nabla geom q :=
  gen_inf _ p q

/-- The empty datum is the whole hyperspace. -/
theorem nabla_top (geom : FellGeometry ι) : nabla geom ⊤ = ⊤ :=
  gen_top _

/-- Enlarging the formal data shrinks the generator. -/
theorem nabla_anti (geom : FellGeometry ι) {p q : NablaData ι}
    (hh : p.hits ⊆ q.hits) (hm : p.misses ⊆ q.misses) :
    nabla geom q ≤ nabla geom p :=
  gen_mono _ ⟨hh, hm⟩

/-- Every element of the presented hyperspace frame is a join of
∇-generators. -/
theorem eq_iSup_nabla (geom : FellGeometry ι) (x : FellPresented geom) :
    x = ⨆ p ∈ (x : LowerSet (NablaData ι)), nabla geom p :=
  eq_iSup_gen _ x

section Relations

variable {geom : FellGeometry ι}

/-- Hit-refinement holds in the presented frame. -/
theorem nabla_hit_le_of_refines {i : ι} {T : Set ι} (h : geom.refines i T) :
    nabla geom (.hit i) ≤ ⨆ k ∈ T, nabla geom (.hit k) := by
  have hle := restrict_rel_le (fellRelations geom)
    (r := (Iic (NablaData.hit i), ⨆ k ∈ T, Iic (NablaData.hit k)))
    (Or.inl ⟨i, T, h, rfl⟩)
  rw [map_iSup₂] at hle
  exact hle

/-- Miss-covering holds in the presented frame: the whole hyperspace
is covered by the miss generator beside the hits of any covering
family. -/
theorem top_le_of_missCovers {j : ι} {T : Set ι} (h : geom.missCovers j T) :
    (⊤ : FellPresented geom) ≤
      nabla geom (.miss j) ⊔ ⨆ k ∈ T, nabla geom (.hit k) := by
  have hle := restrict_rel_le (fellRelations geom)
    (r := (⊤, Iic (NablaData.miss j) ⊔ ⨆ k ∈ T, Iic (NablaData.hit k)))
    (Or.inr (Or.inl ⟨j, T, h, rfl⟩))
  rw [map_top, map_sup, map_iSup₂] at hle
  exact hle

/-- Miss-monotonicity holds in the presented frame. -/
theorem nabla_miss_le_of_missMono {j' j : ι} (h : geom.missMono j' j) :
    nabla geom (.miss j) ≤ nabla geom (.miss j') :=
  restrict_rel_le (fellRelations geom)
    (r := (Iic (NablaData.miss j), Iic (NablaData.miss j')))
    (Or.inr (Or.inr (Or.inl ⟨j', j, h, rfl⟩)))

/-- Hit-miss refinement holds in the presented frame; with `T = ∅`,
a hit demand inside a miss closure annihilates. -/
theorem nabla_hitMiss_le_of_diffCovers {i j : ι} {T : Set ι}
    (h : geom.diffCovers i j T) :
    nabla geom (.hitMiss i j) ≤ ⨆ k ∈ T, nabla geom (.hitMiss k j) := by
  have hle := restrict_rel_le (fellRelations geom)
    (r := (Iic (NablaData.hitMiss i j), ⨆ k ∈ T, Iic (NablaData.hitMiss k j)))
    (Or.inr (Or.inr (Or.inr ⟨i, j, T, h, rfl⟩)))
  rw [map_iSup₂] at hle
  exact hle

end Relations

namespace Valuation

open scoped ENNReal

variable {geom : FellGeometry ι} {μ ν : Valuation (FellPresented geom)}

/-- **Localic Choquet–Matheron, determination half**: two
Scott-continuous valuations on the presented hyperspace frame with
finite generator values, agreeing on every ∇-generator, are equal.
The interface is the free part of the presentation — the π-law
`nabla_inf` and join-generation `eq_iSup_nabla` — so the theorem holds
at every relation set, this one included.  No points, no spatial
model, no countability, no σ-algebra. -/
theorem ext_of_nabla
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hfin : ∀ p, μ (nabla geom p) ≠ ∞)
    (h : ∀ p, μ (nabla geom p) = ν (nabla geom p)) : μ = ν :=
  ext_of_generators hμS hνS
    (fun p q => ⟨p ⊓ q, (nabla_inf geom p q).symm⟩)
    (fun x => ⟨(x : LowerSet (NablaData ι)), eq_iSup_nabla geom x⟩)
    hfin h

/-- **Separation**: two distinct Scott-continuous valuations on the
presented hyperspace frame are separated by a single ∇-generator —
finite formal data certify distinctness, as in the point-set shadow. -/
theorem exists_nabla_ne
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hfin : ∀ p, μ (nabla geom p) ≠ ∞)
    (hne : μ ≠ ν) : ∃ p, μ (nabla geom p) ≠ ν (nabla geom p) :=
  exists_generator_ne hμS hνS
    (fun p q => ⟨p ⊓ q, (nabla_inf geom p q).symm⟩)
    (fun x => ⟨(x : LowerSet (NablaData ι)), eq_iSup_nabla geom x⟩)
    hfin hne

end Valuation

end Pointfree
