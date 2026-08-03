import DoubleCat.Grothendieck

/-!
# Discrete double opfibrations, and the elements projection

The plain-side companion of `DoubleCat.Virtual.Opfibration`: the lifting
property of the projection from a (plain) double category of elements.
Discreteness is phrased as bijectivity of the projection on lifting data
— tight arrows out of a fixed source, and cells out of a fixed loose
arrow — which avoids stating uniqueness through heterogeneous
equalities, exactly as in the virtual file.  Discrete implies split (the
inverse bijections are a strictly functorial choice of lifts) implies
double opfibration in the up-to-isomorphism sense of
Cruttwell–Lambert–Pronk–Szyld ("Double fibrations", 2022); at the
discrete stratum the split opcleavage is the canonical-lift data of the
covariant construction (Patterson, "Structured and decorated cospans
from the viewpoint of double category theory", 2023).

Main definitions:

* `CategoryTheory.IsDiscreteDoubleOpfibration`: the predicate on a lax
  double functor.
* `CategoryTheory.SpanValued.pushGLoose`, `pushGCell`: the chosen lifts
  of the elements projection — pushforward of a decorated loose arrow
  along a base cell is the indexing's own cell action on the decoration,
  and the chosen opcartesian cell has a definitional decoration
  condition.
* `CategoryTheory.SpanValued.proj_isDiscreteOpfibration`: the elements
  projection is a discrete double opfibration.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w₁ t₁ v₁ u₁' w₂ t₂ v₂ u₂' w t v u₁ u

section Predicate

variable {E : Type u₁'} [Category.{v₁} E]
  [PseudoDoubleCategoryStruct.{w₁, t₁} E] [PseudoDoubleCategory E]
variable {B : Type u₂'} [Category.{v₂} B]
  [PseudoDoubleCategoryStruct.{w₂, t₂} B] [PseudoDoubleCategory B]

/-- The tight-arrow lifting data of a lax double functor at a source
object: a codomain together with a tight arrow out of the fixed
source. -/
@[reducible] def doubleTightLiftData (F : LaxDoubleFunctor E B) (e : E) :
    (Σ e' : E, e ⟶ e') → Σ X' : B, F.obj e ⟶ X' :=
  fun l => ⟨F.obj l.1, F.map l.2⟩

/-- The cell lifting data of a lax double functor at a loose arrow: a
codomain loose arrow, tight sides, and a cell out of the fixed loose
arrow. -/
@[reducible] def doubleCellLiftData (F : LaxDoubleFunctor E B) {a b : E}
    (m : Loose a b) :
    (Σ (c : E) (d : E) (n : Loose c d) (f : a ⟶ c) (g : b ⟶ d),
        Cell m n f g) →
      Σ (c' : B) (d' : B) (q : Loose c' d') (f' : F.obj a ⟶ c')
        (g' : F.obj b ⟶ d'), Cell (F.mapLoose m) q f' g' :=
  fun l => ⟨F.obj l.1, F.obj l.2.1, F.mapLoose l.2.2.1, F.map l.2.2.2.1,
    F.map l.2.2.2.2.1, F.mapCell l.2.2.2.2.2⟩

/-- A lax double functor is a *discrete double opfibration* when tight
arrows out of a fixed source and cells out of a fixed loose arrow both
lift uniquely: the projections on lifting data are bijections.  Discrete
implies split implies double opfibration in the up-to-isomorphism
sense. -/
structure IsDiscreteDoubleOpfibration (F : LaxDoubleFunctor E B) :
    Prop where
  /-- Tight arrows lift uniquely: the underlying functor is a discrete
  opfibration. -/
  tight_bijective : ∀ e : E, Function.Bijective (doubleTightLiftData F e)
  /-- Cells out of a fixed loose arrow lift uniquely. -/
  cell_bijective : ∀ {a b : E} (m : Loose a b),
    Function.Bijective (doubleCellLiftData F m)

end Predicate

namespace SpanValued

variable {C : Type u₁} [Category.{v} C]
  [PseudoDoubleCategoryStruct.{w, t} C] [PseudoDoubleCategory C]
variable {F : SpanValued.{w, t, v, u₁, u} C}

/-- The pushforward of a decorated loose arrow along a base cell: the
base codomain loose arrow, decorated by the indexing's cell action on
the decoration.  Its endpoints are the discrete tight pushforwards of
the loose arrow's endpoints. -/
def pushGLoose {p q : Grothendieck F} (M : GLoose (F := F) p q)
    {c d : C} {n : Loose c d} {f' : p.1 ⟶ c} {g' : q.1 ⟶ d}
    (γ : Cell M.base n f' g') :
    GLoose (F := F) ⟨c, F.map f' p.2⟩ ⟨d, F.map g' q.2⟩ :=
  ⟨n, F.mapCell γ p.2 q.2 M.dec⟩

/-- The chosen opcartesian cell over a base cell at a decorated loose
arrow: the base cell itself, with a definitional decoration condition.
This is the split opcleavage of the elements projection (the
canonical-lift data of the covariant construction). -/
def pushGCell {p q : Grothendieck F} (M : GLoose (F := F) p q)
    {c d : C} {n : Loose c d} {f' : p.1 ⟶ c} {g' : q.1 ⟶ d}
    (γ : Cell M.base n f' g') :
    GCell M (pushGLoose M γ) ⟨f', rfl⟩ ⟨g', rfl⟩ :=
  ⟨γ, HEq.rfl⟩

@[simp] theorem pushGCell_base {p q : Grothendieck F}
    (M : GLoose (F := F) p q) {c d : C} {n : Loose c d} {f' : p.1 ⟶ c}
    {g' : q.1 ⟶ d} (γ : Cell M.base n f' g') :
    (pushGCell M γ).base = γ := rfl

variable (F)

/-- The elements projection of the plain construction is a discrete
double opfibration: its chosen lifts are `(f', rfl)` on tight arrows and
`pushGCell` on cells, and both are unique on the nose.  Surjectivity of
the lifting-data maps is definitional; injectivity is forced
componentwise — the subtype condition of a morphism of elements pins the
codomain points, and the propositional decoration conditions pin the
decorations. -/
theorem proj_isDiscreteOpfibration :
    IsDiscreteDoubleOpfibration (proj F) := by
  refine ⟨fun p => ?_, fun {p q} M => ?_⟩
  · have key : ∀ {X : C} (x : F.obj X) (u : p.1 ⟶ X)
        (h : (F.map u) p.2 = x),
        (⟨⟨X, (F.map u) p.2⟩, ⟨u, rfl⟩⟩ :
            Σ e' : Grothendieck F, p ⟶ e') =
          ⟨⟨X, x⟩, ⟨u, h⟩⟩ := by
      rintro X x u rfl
      rfl
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun l => ⟨⟨l.1, F.map l.2 p.2⟩, l.2, rfl⟩,
        fun l => key l.1.2 l.2.val l.2.property, fun _ => rfl⟩
  · have key : ∀ {X Y : C} (x : F.obj X) (y : F.obj Y) (n : Loose X Y)
        (dn : F.mapLoose n x y) (u : p.1 ⟶ X) (v : q.1 ⟶ Y)
        (hu : (F.map u) p.2 = x) (hv : (F.map v) q.2 = y)
        (w : Cell M.base n u v)
        (hw : F.mapCell w p.2 q.2 M.dec ≍ dn),
        (⟨⟨X, (F.map u) p.2⟩, ⟨Y, (F.map v) q.2⟩, pushGLoose M w,
            ⟨u, rfl⟩, ⟨v, rfl⟩, pushGCell M w⟩ :
          Σ (c : Grothendieck F) (d : Grothendieck F) (N : Loose c d)
            (f : p ⟶ c) (g : q ⟶ d), Cell M N f g) =
          ⟨⟨X, x⟩, ⟨Y, y⟩, ⟨n, dn⟩, ⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := by
      rintro X Y x y n dn u v rfl rfl w hw
      obtain rfl := eq_of_heq hw
      rfl
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun l => ⟨⟨l.1, F.map l.2.2.2.1 p.2⟩, ⟨l.2.1, F.map l.2.2.2.2.1 q.2⟩,
          pushGLoose M l.2.2.2.2.2, ⟨l.2.2.2.1, rfl⟩, ⟨l.2.2.2.2.1, rfl⟩,
          pushGCell M l.2.2.2.2.2⟩,
        fun l => key l.1.2 l.2.1.2 l.2.2.1.base l.2.2.1.dec l.2.2.2.1.val
          l.2.2.2.2.1.val l.2.2.2.1.property l.2.2.2.2.1.property
          l.2.2.2.2.2.base l.2.2.2.2.2.dec,
        fun _ => rfl⟩

end SpanValued

end CategoryTheory
