import SuFunctor.StateSpace.FamCat
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-! # Countable coproducts in the completion: free, disjoint, universal

The point of the `FamObj` construction: **all** countable coproducts
exist — with no common-ambient hypothesis, no assumptions on `C`
whatsoever — because the completion takes them freely at the index
level: the coproduct of countably many countable families is the
`Sigma`-indexed family of all their components.

Beyond bare existence, the coproducts have the properties that make a
category *extensive*, and they hold here for arbitrary `C` because every
one of them is index bookkeeping:

* copairing is an equivalence (`famDescEquiv`) — the local form of the
  completion's freeness;
* every family is the coproduct of its component singletons
  (`famComponentsIsColimit`) — the completion adds no objects beyond
  formal countable coproducts of `C`-objects;
* the initial object is the empty family, and it is *strict*
  (`HasStrictInitialObjects`): anything mapping into it is empty-indexed;
* distinct coproduct injections are *disjoint* — they are monomorphisms
  and their pullback is initial (`famInjPullbackIsLimit`,
  `famCoproductDisjoint`): a point of the pullback would carry a
  `Sigma`-tag equal to two distinct tags at once;
* coproducts are *universal* in decomposition form: any morphism into a
  coproduct decomposes its source along sector preimages, with pullback
  squares (`famSectorIsPullback`) whose apexes again form a coproduct
  (`famSectorCofanIsColimit`).

Mechanization note: every construction ships with `@[simp]` projection
lemmas (`…_r`, `…_app`, `…_X`, `…_inj`) — the `Hom`-structure literals
sit behind semireducible defs, so without the lemmas the category-law
simp set cannot see the components (the transparency face of the
object-literals-carry-lemma-references lesson). -/

namespace SuFunctor.StateSpace

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace FamObj

/-! ## The coproduct of a countable family of families -/

section Sigma

variable {J : Type} [Countable J] (F : J → FamObj C)

/-- The coproduct family: all components of all members, `Sigma`-indexed. -/
@[reducible]
def famSigma : FamObj C :=
  ⟨(j : J) × (F j).ι, fun p => (F p.1).X p.2⟩

@[simp] lemma famSigma_X (p : (famSigma F).ι) :
    (famSigma F).X p = (F p.1).X p.2 := rfl

/-- The `j`-th coproduct injection: tag with `j`. -/
def famSigmaInj (j : J) : F j ⟶ famSigma F :=
  ⟨fun i => ⟨j, i⟩, fun i => 𝟙 _⟩

@[simp] lemma famSigmaInj_r (j : J) (i : (F j).ι) :
    (famSigmaInj F j).r i = ⟨j, i⟩ := rfl

@[simp] lemma famSigmaInj_app (j : J) (i : (F j).ι) :
    (famSigmaInj F j).app i = 𝟙 ((F j).X i) := rfl

/-- Copairing: dispatch on the tag. -/
def famSigmaDesc {Z : FamObj C} (t : ∀ j, F j ⟶ Z) : famSigma F ⟶ Z :=
  ⟨fun p => (t p.1).r p.2, fun p => (t p.1).app p.2⟩

@[simp] lemma famSigmaDesc_r {Z : FamObj C} (t : ∀ j, F j ⟶ Z)
    (p : (famSigma F).ι) : (famSigmaDesc F t).r p = (t p.1).r p.2 := rfl

@[simp] lemma famSigmaDesc_app {Z : FamObj C} (t : ∀ j, F j ⟶ Z)
    (p : (famSigma F).ι) : (famSigmaDesc F t).app p = (t p.1).app p.2 := rfl

@[simp] lemma famSigmaInj_comp_desc {Z : FamObj C} (t : ∀ j, F j ⟶ Z) (j : J) :
    famSigmaInj F j ≫ famSigmaDesc F t = t j :=
  Hom.ext' rfl (fun i => by simp)

/-- Copairing out of the coproduct is an equivalence: the local form of
the completion's freeness. -/
def famDescEquiv (Z : FamObj C) : (famSigma F ⟶ Z) ≃ (∀ j, F j ⟶ Z) where
  toFun f j := famSigmaInj F j ≫ f
  invFun t := famSigmaDesc F t
  left_inv f := Hom.ext' (funext fun p => rfl) (fun p => by
    obtain ⟨j, i⟩ := p
    simp)
  right_inv t := funext fun j => famSigmaInj_comp_desc F t j

/-- The coproduct cofan. -/
def famCofan : Cofan F := Cofan.mk (famSigma F) (famSigmaInj F)

@[simp] lemma famCofan_pt : (famCofan F).pt = famSigma F := rfl

@[simp] lemma famCofan_inj (j : J) : (famCofan F).inj j = famSigmaInj F j := rfl

/-- The coproduct cofan is a colimit: **all countable coproducts exist in
the completion**, freely — no common ambient, no hypothesis on `C`. -/
def famCofanIsColimit : IsColimit (famCofan F) := by
  refine Cofan.IsColimit.mk _ (fun t => famSigmaDesc F fun j => t.inj j)
    (fun t j => famSigmaInj_comp_desc F _ j) (fun t m hm => ?_)
  refine Hom.ext' (funext fun p => ?_) (fun p => ?_)
  · obtain ⟨j, i⟩ := p
    exact congrFun (congrArg Hom.r (hm j)) i
  · obtain ⟨j, i⟩ := p
    have h := Hom.congr_app (hm j) i
    simp only [famCofan_inj, comp_app, famSigmaInj_app, famSigmaInj_r] at h
    rw [comp_eqToHom_iff]
    exact (Category.id_comp _).symm.trans h

/-- Coproducts of countable families of families exist. -/
theorem hasCoproduct_fam : HasCoproduct F :=
  ⟨⟨⟨famCofan F, famCofanIsColimit F⟩⟩⟩

instance : HasCountableCoproducts (FamObj C) where
  out J :=
    { has_colimit := fun F =>
        have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
          hasCoproduct_fam _
        hasColimit_of_iso Discrete.natIsoFunctor }

end Sigma

/-! ## Every family is the coproduct of its component singletons -/

section Components

variable (A : FamObj C)

/-- The leg of the components cofan: the `i`-th component singleton into
the family. -/
def famComponentInj (i : A.ι) : ySing (A.X i) ⟶ A :=
  ⟨fun _ => i, fun _ => 𝟙 (A.X i)⟩

@[simp] lemma famComponentInj_r (i : A.ι) (p : (ySing (A.X i)).ι) :
    (famComponentInj A i).r p = i := rfl

@[simp] lemma famComponentInj_app (i : A.ι) (p : (ySing (A.X i)).ι) :
    (famComponentInj A i).app p = 𝟙 (A.X i) := rfl

/-- The cofan exhibiting a family as the coproduct of its component
singletons. -/
def famComponentsCofan : Cofan (fun i : A.ι => ySing (A.X i)) :=
  Cofan.mk A (famComponentInj A)

@[simp] lemma famComponentsCofan_pt : (famComponentsCofan A).pt = A := rfl

@[simp] lemma famComponentsCofan_inj (i : A.ι) :
    (famComponentsCofan A).inj i = famComponentInj A i := rfl

/-- Every family **is** the coproduct of its component singletons: the
completion adds nothing beyond formal countable coproducts of
`C`-objects, and every family-object decomposes canonically. -/
def famComponentsIsColimit : IsColimit (famComponentsCofan A) := by
  refine Cofan.IsColimit.mk _
    (fun t => ⟨fun i => (t.inj i).r PUnit.unit, fun i => (t.inj i).app PUnit.unit⟩)
    (fun t i => ?_) (fun t m hm => ?_)
  · refine Hom.ext' (funext fun p => rfl) (fun p => ?_)
    exact (Category.comp_id _).trans (Category.id_comp _)
  · refine Hom.ext' (funext fun i => ?_) (fun i => ?_)
    · exact congrFun (congrArg Hom.r (hm i)) PUnit.unit
    · have h := Hom.congr_app (hm i) PUnit.unit
      simp only [famComponentsCofan_inj, comp_app, famComponentInj_app,
        famComponentInj_r] at h
      rw [comp_eqToHom_iff]
      exact (Category.id_comp _).symm.trans h

end Components

/-! ## The initial object is the empty family, strictly -/

/-- The initial object: the empty family. -/
@[reducible]
def famInitial : FamObj C := ⟨PEmpty, fun e => e.elim⟩

/-- The unique morphism out of the empty family. -/
def famInitialTo (A : FamObj C) : famInitial ⟶ A :=
  ⟨fun e => e.elim, fun e => e.elim⟩

instance (A : FamObj C) : Unique (famInitial ⟶ A) where
  default := famInitialTo A
  uniq _ := Hom.ext' (funext fun e => e.elim) (fun e => e.elim)

instance : HasInitial (FamObj C) := hasInitial_of_unique famInitial

/-- The empty family is initial. -/
def famInitialIsInitial : IsInitial (famInitial (C := C)) :=
  IsInitial.ofUnique _

/-- An empty-indexed family is initial. -/
def famIsInitial_of_isEmpty {A : FamObj C} (hA : IsEmpty A.ι) : IsInitial A :=
  IsInitial.ofUniqueHom
    (fun B => ⟨fun i => (hA.false i).elim, fun i => (hA.false i).elim⟩)
    (fun B m =>
      Hom.ext' (funext fun i => (hA.false i).elim) (fun i => (hA.false i).elim))

/-- A family admitting a morphism into the empty family is itself
empty-indexed, hence initial: the initial object is **strict**. -/
def famIsInitial_of_hom_to_initial {A : FamObj C} (f : A ⟶ famInitial) :
    IsInitial A :=
  famIsInitial_of_isEmpty ⟨fun i => (f.r i).elim⟩

instance : HasStrictInitialObjects (FamObj C) := by
  refine hasStrictInitialObjects_of_initial_is_strict (fun A f => ?_)
  have hA : IsInitial A :=
    famIsInitial_of_hom_to_initial (f ≫ initialIsInitial.to famInitial)
  have hf : f = (hA.uniqueUpToIso initialIsInitial).hom := hA.hom_ext _ _
  rw [hf]
  infer_instance

/-- The singleton embedding does **not** preserve the initial object:
the singleton family over an initial object of `C` is a one-sector
family, and it admits distinct morphisms into any two-sector family —
the completion's initial object is the *empty* family.
(Presentation-grain honesty: families remember sector structure,
including empty sectors.) -/
theorem ySing_not_initial (V : C) (B : FamObj C) (j j' : B.ι)
    (hjj' : j ≠ j') (u : V ⟶ B.X j) (u' : V ⟶ B.X j') :
    ¬ Nonempty (IsInitial (ySing V)) := by
  rintro ⟨hI⟩
  have h := hI.hom_ext (⟨fun _ => j, fun _ => u⟩ : ySing V ⟶ B)
    (⟨fun _ => j', fun _ => u'⟩ : ySing V ⟶ B)
  exact hjj' (congrFun (congrArg Hom.r h) PUnit.unit)

/-! ## Disjointness: distinct injections pull back to the initial -/

section Disjoint

variable {J : Type} [Countable J] (F : J → FamObj C)

/-- Coproduct injections are monomorphisms. -/
instance famSigmaInj_mono (j : J) : Mono (famSigmaInj F j) := by
  constructor
  intro A u v huv
  have hr : u.r = v.r := by
    funext i
    have h := congrFun (congrArg Hom.r huv) i
    simp only [comp_r, famSigmaInj_r] at h
    exact eq_of_heq (Sigma.mk.injEq _ _ _ _ ▸ h).2
  refine Hom.ext' hr (fun i => ?_)
  have h := Hom.congr_app huv i
  simp only [comp_app, famSigmaInj_app, famSigmaInj_r] at h
  rw [comp_eqToHom_iff]
  exact (Category.comp_id _).symm.trans
    (h.trans (congrArg (fun k => k ≫ eqToHom _) (Category.comp_id _)))

/-- The index type of a cone over two distinct coproduct injections is
empty: its reindexing would equate two distinct `Sigma`-tags. -/
theorem famInjPullback_index_empty {j j' : J} (hjj' : j ≠ j')
    (s : PullbackCone (famSigmaInj F j) (famSigmaInj F j')) :
    IsEmpty s.pt.ι := by
  constructor
  intro i
  have h := congrFun (congrArg Hom.r s.condition) i
  simp only [comp_r, famSigmaInj_r] at h
  exact hjj' (Sigma.mk.injEq _ _ _ _ ▸ h).1

/-- The pullback cone over two distinct coproduct injections, with empty
apex. -/
def famInjPullbackCone {j j' : J} (_ : j ≠ j') :
    PullbackCone (famSigmaInj F j) (famSigmaInj F j') :=
  PullbackCone.mk (famInitialTo (F j)) (famInitialTo (F j'))
    (Hom.ext' (funext fun e => e.elim) (fun e => e.elim))

/-- Distinct coproduct injections are **disjoint**: the empty-apex cone
is a limit — a point of the pullback would carry a `Sigma`-tag equal to
`j` and `j'` at once. -/
def famInjPullbackIsLimit {j j' : J} (hjj' : j ≠ j') :
    IsLimit (famInjPullbackCone F hjj') := by
  refine PullbackCone.IsLimit.mk _
    (fun s =>
      have hE := famInjPullback_index_empty F hjj' s
      ⟨fun i => (hE.false i).elim, fun i => (hE.false i).elim⟩)
    (fun s => ?_) (fun s => ?_) (fun s m _ _ => ?_)
  · have hE := famInjPullback_index_empty F hjj' s
    exact Hom.ext' (funext fun i => (hE.false i).elim)
      (fun i => (hE.false i).elim)
  · have hE := famInjPullback_index_empty F hjj' s
    exact Hom.ext' (funext fun i => (hE.false i).elim)
      (fun i => (hE.false i).elim)
  · have hE := famInjPullback_index_empty F hjj' s
    exact Hom.ext' (funext fun i => (hE.false i).elim)
      (fun i => (hE.false i).elim)

/-- The completion's countable coproducts are disjoint, in mathlib's
packaging: for *any* colimit cofan (transported from the canonical one
along the colimit-uniqueness isomorphism), injections are mono and
distinct injections pull back to an initial object. -/
instance famCoproductDisjoint : CoproductDisjoint F where
  mono_inj {c} hc k := by
    have hcomm : c.inj k ≫
        (hc.coconePointUniqueUpToIso (famCofanIsColimit F)).hom
        = famSigmaInj F k :=
      hc.comp_coconePointUniqueUpToIso_hom (famCofanIsColimit F) ⟨k⟩
    have hck : c.inj k = famSigmaInj F k ≫
        (hc.coconePointUniqueUpToIso (famCofanIsColimit F)).inv :=
      (Category.comp_id _).symm.trans
        ((congrArg (fun m => c.inj k ≫ m) (Iso.hom_inv_id _)).symm.trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun m => m ≫ _) hcomm)))
    rw [hck]
    exact mono_comp _ _
  nonempty_isInitial_of_ne {c} hc {i j} hij s hs := by
    have hcomm : ∀ k, c.inj k ≫
        (hc.coconePointUniqueUpToIso (famCofanIsColimit F)).hom
        = famSigmaInj F k := fun k =>
      hc.comp_coconePointUniqueUpToIso_hom (famCofanIsColimit F) ⟨k⟩
    have hcond : s.fst ≫ famSigmaInj F i = s.snd ≫ famSigmaInj F j :=
      (congrArg (fun m => s.fst ≫ m) (hcomm i)).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫
              (hc.coconePointUniqueUpToIso (famCofanIsColimit F)).hom)
            s.condition).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun m => s.snd ≫ m) (hcomm j)))))
    exact ⟨famIsInitial_of_isEmpty
      (famInjPullback_index_empty F hij (PullbackCone.mk s.fst s.snd hcond))⟩

end Disjoint

/-! ## Universality: any morphism into a coproduct decomposes its source

The extensivity working content, with no assumptions on `C`: given
`f : A ⟶ famSigma F`, the `j`-th *sector preimage* is the subfamily of
`A` on the indices whose tag lands in sector `j`.  Each sector sits in a
pullback square over the `j`-th injection, and the sectors' cofan is a
colimit — `A` is the coproduct of its sector preimages.

Design note: a sector index *carries* the summand index as data,
constrained by a `Sigma`-equality (`f.r q.1 = ⟨j, q.2⟩`), rather than
transporting `(f.r i).2` along a first-component equality — this keeps
every construction transport-free (the one `eqToHom` in `famSectorMap`
has definitionally matching endpoints). -/

section Sectors

variable {J : Type} [Countable J] {F : J → FamObj C} {A : FamObj C}
  (f : A ⟶ famSigma F)

/-- The `j`-th sector preimage of a morphism into a coproduct: indices
of `A` paired with the summand index they hit. -/
@[reducible]
def famSector (j : J) : FamObj C :=
  ⟨{q : A.ι × (F j).ι // f.r q.1 = ⟨j, q.2⟩}, fun q => A.X q.1.1⟩

@[simp] lemma famSector_X (j : J) (q : (famSector f j).ι) :
    (famSector f j).X q = A.X q.1.1 := rfl

/-- The sector inclusion. -/
def famSectorIncl (j : J) : famSector f j ⟶ A :=
  ⟨fun q => q.1.1, fun q => 𝟙 _⟩

@[simp] lemma famSectorIncl_r (j : J) (q : (famSector f j).ι) :
    (famSectorIncl f j).r q = q.1.1 := rfl

@[simp] lemma famSectorIncl_app (j : J) (q : (famSector f j).ι) :
    (famSectorIncl f j).app q = 𝟙 (A.X q.1.1) := rfl

/-- The sector map into the summand. -/
def famSectorMap (j : J) : famSector f j ⟶ F j :=
  ⟨fun q => q.1.2, fun q => f.app q.1.1 ≫ eqToHom (congrArg (famSigma F).X q.2)⟩

@[simp] lemma famSectorMap_r (j : J) (q : (famSector f j).ι) :
    (famSectorMap f j).r q = q.1.2 := rfl

@[simp] lemma famSectorMap_app (j : J) (q : (famSector f j).ι) :
    (famSectorMap f j).app q =
      f.app q.1.1 ≫ eqToHom (congrArg (famSigma F).X q.2) := rfl

/-- The sector square commutes. -/
lemma famSector_comm (j : J) :
    famSectorIncl f j ≫ f = famSectorMap f j ≫ famSigmaInj F j := by
  refine Hom.ext' (funext fun q => q.2) (fun q => ?_)
  show (𝟙 _ ≫ f.app q.1.1) ≫ eqToHom _ =
    (f.app q.1.1 ≫ eqToHom (congrArg (famSigma F).X q.2)) ≫ 𝟙 _
  exact (congrArg (fun k => k ≫ eqToHom _) (Category.id_comp _)).trans
    (Category.comp_id _).symm

/-- The reindexing datum of a cone over the sector cospan: the full
`Sigma`-equality, extracted from the cone condition. -/
lemma famSector_cone_tag {j : J} (s : PullbackCone f (famSigmaInj F j))
    (t : s.pt.ι) : f.r (s.fst.r t) = ⟨j, s.snd.r t⟩ := by
  have h := congrFun (congrArg Hom.r s.condition) t
  simpa using h

/-- The sector square is a pullback: coproducts in the completion are
universal (decomposition form, first half). -/
theorem famSectorIsPullback (j : J) :
    IsPullback (famSectorIncl f j) (famSectorMap f j) f (famSigmaInj F j) := by
  refine ⟨⟨famSector_comm f j⟩, ⟨?_⟩⟩
  refine PullbackCone.IsLimit.mk _
    (fun s => ⟨fun t => ⟨(s.fst.r t, s.snd.r t), famSector_cone_tag f s t⟩,
      fun t => s.fst.app t⟩)
    (fun s => ?_) (fun s => ?_) (fun s m hfst hsnd => ?_)
  · -- fac fst
    refine Hom.ext' (funext fun t => rfl) (fun t => ?_)
    exact (congrArg (fun k => k ≫ eqToHom _) (Category.comp_id _)).trans
      (Category.comp_id _)
  · -- fac snd
    refine Hom.ext' (funext fun t => rfl) (fun t => ?_)
    have h := Hom.congr_app s.condition t
    simp only [comp_app, famSigmaInj_app, famSigmaInj_r] at h
    replace h := h.trans (congrArg (fun k => k ≫ eqToHom _) (Category.comp_id _))
    -- h : s.fst.app t ≫ f.app (s.fst.r t) = s.snd.app t ≫ eqToHom _
    show (s.fst.app t ≫ (famSectorMap f j).app
        ⟨(s.fst.r t, s.snd.r t), famSector_cone_tag f s t⟩) ≫ eqToHom _
      = s.snd.app t
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => s.fst.app t ≫ k) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (fun k => s.fst.app t ≫ (f.app (s.fst.r t) ≫ k))
      (eqToHom_trans _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ eqToHom _) h).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun k => s.snd.app t ≫ k) (eqToHom_trans _ _)).trans
      (Category.comp_id _)
  · -- uniqueness
    refine Hom.ext' (funext fun t => Subtype.ext (Prod.ext ?_ ?_)) (fun t => ?_)
    · exact congrFun (congrArg Hom.r hfst) t
    · exact congrFun (congrArg Hom.r hsnd) t
    · have h := Hom.congr_app hfst t
      simp only [comp_app, famSectorIncl_app, famSectorIncl_r] at h
      rw [comp_eqToHom_iff]
      exact (Category.comp_id _).symm.trans h

/-- The sectors' cofan. -/
def famSectorCofan : Cofan (fun j => famSector f j) :=
  Cofan.mk A (famSectorIncl f)

@[simp] lemma famSectorCofan_inj (j : J) :
    (famSectorCofan f).inj j = famSectorIncl f j := rfl

/-- Coherence of the sector copairing at a fixed tag equality: the
reindexing legs of `t.inj` agree across the two presentations of a
sector member.  Proved by eliminating the tag equality, after which
everything is proof-irrelevantly reflexive. -/
private lemma sector_desc_r (t : Cofan fun j => famSector f j) (i₀ : A.ι)
    {p : (j : J) × (F j).ι} (hp : f.r i₀ = p) :
    (t.inj (f.r i₀).1).r ⟨(i₀, (f.r i₀).2), (Sigma.eta _).symm⟩ =
      (t.inj p.1).r ⟨(i₀, p.2), by rw [hp]⟩ := by
  subst hp
  rfl

/-- The componentwise face of `sector_desc_r`. -/
private lemma sector_desc_app (t : Cofan fun j => famSector f j) (i₀ : A.ι)
    {p : (j : J) × (F j).ι} (hp : f.r i₀ = p)
    (hX : t.pt.X ((t.inj (f.r i₀).1).r ⟨(i₀, (f.r i₀).2), (Sigma.eta _).symm⟩) =
      t.pt.X ((t.inj p.1).r ⟨(i₀, p.2), by rw [hp]⟩)) :
    (t.inj (f.r i₀).1).app ⟨(i₀, (f.r i₀).2), (Sigma.eta _).symm⟩ ≫ eqToHom hX =
      (t.inj p.1).app ⟨(i₀, p.2), by rw [hp]⟩ := by
  subst hp
  exact Category.comp_id _

/-- The sectors' cofan is a colimit: **coproducts in the completion are
universal** — any morphism into a coproduct exhibits its source as the
coproduct of the sector preimages (decomposition form, second half). -/
def famSectorCofanIsColimit : IsColimit (famSectorCofan f) := by
  refine Cofan.IsColimit.mk _
    (fun t => ⟨fun i => (t.inj (f.r i).1).r ⟨(i, (f.r i).2), (Sigma.eta _).symm⟩,
      fun i => (t.inj (f.r i).1).app ⟨(i, (f.r i).2), (Sigma.eta _).symm⟩⟩)
    (fun t j => ?_) (fun t m hm => ?_)
  · refine Hom.ext' (funext fun q => ?_) (fun q => ?_)
    · exact sector_desc_r f t q.1.1 q.2
    · exact (congrArg (fun k => k ≫ eqToHom _) (Category.id_comp _)).trans
        (sector_desc_app f t q.1.1 q.2 _)
  · refine Hom.ext' (funext fun i => ?_) (fun i => ?_)
    · exact congrFun (congrArg Hom.r
        (hm (f.r i).1)) ⟨(i, (f.r i).2), (Sigma.eta _).symm⟩
    · have h := Hom.congr_app (hm (f.r i).1) ⟨(i, (f.r i).2), (Sigma.eta _).symm⟩
      simp only [famSectorCofan_inj, comp_app, famSectorIncl_app,
        famSectorIncl_r] at h
      rw [comp_eqToHom_iff]
      exact (Category.id_comp _).symm.trans h

end Sectors

end FamObj

end SuFunctor.StateSpace
