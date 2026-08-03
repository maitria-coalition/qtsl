import DoubleCat.Virtual.Grothendieck

/-!
# Discrete virtual double opfibrations

The lifting property of the projection from a virtual double category of
elements.  Following Blanco ("Bifibrations of polycategories and classical
multiplicative linear logic", PhD thesis, Birmingham, 2023, ch. 6), a
multicell of the total of a functor of virtual double categories is
*opcartesian* when every multicell lying over a substitution factoring
through its image factors through it uniquely; the codomain of an
opcartesian lift at a path is the *pushforward* of the path along the base
multicell.  Blanco's pushfibrations lift only along base multicells with
identity tight boundaries; the notion here is the tight-boundary-general
form his conclusion poses as an open direction, in its *discrete* (unique
lifts on the nose) and therefore split incarnation — the regime of the
span-valued construction, exactly as ordinary discrete (op)fibrations are
the regime of the set-valued Grothendieck construction one dimension down
(Lambert, "Discrete double fibrations", 2021, at the double level;
Hermida's and Heuts's opfibrations of multicategories at the multi level).

Discreteness is phrased as bijectivity of the projection on lifting data
(tight arrows out of a fixed source; multicells out of a fixed domain
path), which avoids stating uniqueness through heterogeneous equalities.
There is no separate clause for loose identities or loose composites —
the pseudo-level conditions "the loose unit and loose composition
functors preserve (op)cartesians" (Cruttwell–Lambert–Pronk–Szyld,
"Double fibrations", 2022; the unwound definition) have no independent
content here, being the nullary and n-ary instances of the single
arity-uniform multicell clause.

Main definitions:

* `CategoryTheory.IsDiscreteVirtualDoubleOpfibration`: the predicate on a
  functor of virtual double categories.
* `CategoryTheory.VSpanValued.pushLoose`, `pushCell`: the chosen lifts of
  the elements projection — the pushforward of a decorated path along a
  base multicell is the indexing's own cell action on the chained
  decoration, and the chosen opcartesian multicell has a *definitional*
  decoration condition.
* `CategoryTheory.VSpanValued.vproj_isDiscreteOpfibration`: the elements
  projection is a discrete virtual double opfibration (proved; the
  uniqueness legs are the rung-R1 chases of the design ladder,
  discharged below).
-/

namespace CategoryTheory

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂ w t v uB u

section Predicate

variable {E : Type u₁} [Category.{v₁} E]
  [VirtualDoubleCategoryStruct.{w₁, t₁, v₁, u₁} E]
variable {B : Type u₂} [Category.{v₂} B]
  [VirtualDoubleCategoryStruct.{w₂, t₂, v₂, u₂} B]

/-- The tight-arrow lifting data of a functor at a source object: a
codomain together with a tight arrow out of the fixed source. -/
@[reducible] def tightLiftData (Pr : VirtualDoubleFunctor E B) (e : E) :
    (Σ e' : E, e ⟶ e') → Σ X' : B, Pr.obj e ⟶ X' :=
  fun l => ⟨Pr.obj l.1, Pr.map l.2⟩

/-- The multicell lifting data of a functor at a domain path: a codomain
loose arrow, tight sides, and a multicell out of the fixed path. -/
@[reducible] def cellLiftData (Pr : VirtualDoubleFunctor E B) {a b : E}
    (Ξ : LoosePath (Loose (C := E)) a b) :
    (Σ (c : E) (d : E) (N : Loose c d) (f : a ⟶ c) (g : b ⟶ d),
        Cell Ξ N f g) →
      Σ (c' : B) (d' : B) (q : Loose c' d') (f' : Pr.obj a ⟶ c')
        (g' : Pr.obj b ⟶ d'),
        Cell (Ξ.map Pr.obj fun {_ _} e => Pr.mapLoose e) q f' g' :=
  fun l => ⟨Pr.obj l.1, Pr.obj l.2.1, Pr.mapLoose l.2.2.1, Pr.map l.2.2.2.1,
    Pr.map l.2.2.2.2.1, Pr.mapCell l.2.2.2.2.2⟩

/-- A functor of virtual double categories is a *discrete virtual double
opfibration* when tight arrows out of a fixed source and multicells out of
a fixed domain path both lift uniquely: the projections on lifting data
are bijections.  Discrete implies split (the inverse bijections are a
strictly functorial choice of lifts) implies opfibration in the
up-to-isomorphism sense of Blanco's pushfibrations. -/
structure IsDiscreteVirtualDoubleOpfibration
    (Pr : VirtualDoubleFunctor E B) : Prop where
  /-- Tight arrows lift uniquely: the underlying functor is a discrete
  opfibration. -/
  tight_bijective : ∀ e : E, Function.Bijective (tightLiftData Pr e)
  /-- Multicells lift uniquely at every domain path (nullary and n-ary
  alike, which is where the pseudo-level unit/composition clauses went). -/
  cell_bijective : ∀ {a b : E} (Ξ : LoosePath (Loose (C := E)) a b),
    Function.Bijective (cellLiftData Pr Ξ)

end Predicate

namespace VSpanValued

attribute [local instance] VirtualDoubleCategoryStruct.ofPseudo

variable {B : Type uB} [Category.{v} B]
  [VirtualDoubleCategoryStruct.{w, t, v, uB} B]
variable {P : VSpanValued.{w, t, v, uB, u} B}

/-- The pushforward of a decorated path along a base multicell: the base
codomain loose arrow, decorated by the indexing's cell action on the
chained decoration.  Its endpoints are the discrete tight pushforwards of
the path's endpoints. -/
def pushLoose {p p' : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p p') {c d : B} {q : Loose c d}
    {f' : p.1 ⟶ c} {g' : p'.1 ⟶ d} (α : Cell (basePath Ξ) q f' g') :
    VGLoose (P := P) ⟨c, P.map f' p.2⟩ ⟨d, P.map g' p'.2⟩ :=
  ⟨q, P.mapCell α p.2 p'.2 (chainDec Ξ)⟩

/-- The chosen opcartesian multicell over a base multicell at a decorated
path: the base multicell itself, with a definitional decoration
condition.  This is the split opcleavage of the elements projection. -/
def pushCell {p p' : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p p') {c d : B} {q : Loose c d}
    {f' : p.1 ⟶ c} {g' : p'.1 ⟶ d} (α : Cell (basePath Ξ) q f' g') :
    VGCell Ξ (pushLoose Ξ α) ⟨f', rfl⟩ ⟨g', rfl⟩ :=
  ⟨α, HEq.rfl⟩

@[simp] theorem pushCell_base {p p' : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p p') {c d : B} {q : Loose c d}
    {f' : p.1 ⟶ c} {g' : p'.1 ⟶ d} (α : Cell (basePath Ξ) q f' g') :
    (pushCell Ξ α).base = α := rfl

variable (P)

/-- The elements projection is a discrete virtual double opfibration: its
chosen lifts are `(f', rfl)` on tight arrows and `pushCell` on multicells,
and both are unique on the nose.  Surjectivity of the lifting-data maps is
definitional (the chosen lifts project to the given data by `rfl`);
injectivity is forced componentwise — the subtype condition of a morphism
of elements pins the codomain points, and the propositional decoration
conditions pin the decorations. -/
theorem vproj_isDiscreteOpfibration :
    IsDiscreteVirtualDoubleOpfibration (vproj P) := by
  refine ⟨fun p => ?_, fun {a b} Ξ => ?_⟩
  · -- The reassembly identity with every component a free variable, so the
    -- point and its pinning equation eliminate together; the concrete case
    -- follows by structure eta at the projections.
    have key : ∀ {X : B} (x : P.obj X) (u : p.1 ⟶ X)
        (h : (P.map u) p.2 = x),
        (⟨⟨X, (P.map u) p.2⟩, ⟨u, rfl⟩⟩ : Σ e' : Grothendieck P, p ⟶ e') =
          ⟨⟨X, x⟩, ⟨u, h⟩⟩ := by
      rintro X x u rfl
      rfl
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun l => ⟨⟨l.1, P.map l.2 p.2⟩, l.2, rfl⟩,
        fun l => key l.1.2 l.2.val l.2.property, fun _ => rfl⟩
  · have key : ∀ {X Y : B} (x : P.obj X) (y : P.obj Y) (n : Loose X Y)
        (dn : P.mapLoose n x y) (u : a.1 ⟶ X) (v : b.1 ⟶ Y)
        (hu : (P.map u) a.2 = x) (hv : (P.map v) b.2 = y)
        (w : Cell (basePath Ξ) n u v)
        (hw : P.mapCell w a.2 b.2 (chainDec Ξ) ≍ dn),
        (⟨⟨X, (P.map u) a.2⟩, ⟨Y, (P.map v) b.2⟩, pushLoose Ξ w, ⟨u, rfl⟩,
            ⟨v, rfl⟩, pushCell Ξ w⟩ :
          Σ (c : Grothendieck P) (d : Grothendieck P) (N : Loose c d)
            (f : a ⟶ c) (g : b ⟶ d), Cell Ξ N f g) =
          ⟨⟨X, x⟩, ⟨Y, y⟩, ⟨n, dn⟩, ⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := by
      rintro X Y x y n dn u v rfl rfl w hw
      obtain rfl := eq_of_heq hw
      rfl
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun l => ⟨⟨l.1, P.map l.2.2.2.1 a.2⟩, ⟨l.2.1, P.map l.2.2.2.2.1 b.2⟩,
          pushLoose Ξ l.2.2.2.2.2, ⟨l.2.2.2.1, rfl⟩, ⟨l.2.2.2.2.1, rfl⟩,
          pushCell Ξ l.2.2.2.2.2⟩,
        fun l => key l.1.2 l.2.1.2 l.2.2.1.base l.2.2.1.dec l.2.2.2.1.val
          l.2.2.2.2.1.val l.2.2.2.1.property l.2.2.2.2.1.property
          l.2.2.2.2.2.base l.2.2.2.2.2.dec,
        fun _ => rfl⟩

end VSpanValued

end CategoryTheory
