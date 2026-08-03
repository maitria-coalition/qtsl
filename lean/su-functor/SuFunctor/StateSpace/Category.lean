import SuFunctor.StateSpace.Maps
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

/-! # The category of ω-semialgebraic spaces

Objects are ω-semialgebraic subsets of finite-dimensional real ambients
(`OmegaSA`); morphisms are countably-piecewise-polynomial maps between
them (`IsPiecewisePolyOn`).  Composition is `IsPiecewisePolyOn.comp` —
substitution and pair-reindexing only — and the category laws hold on the
nose (morphism equality is proof-irrelevant equality of the underlying
functions).

This is the *concrete* stratum: the objects the semantic-universe carrier
consumes are subsets of an ambient, so no plot/sheaf structure is imposed
here.  The ωPAP construction of arXiv:2302.10636 §2 (spaces with plots,
quasi-topos-style) is the closure-completion of this kind of concrete
category under function spaces and lifting; at this stratum we record
instead exactly which limits and colimits exist concretely (see
`StateSpace/Limits.lean` and `StateSpace/CountableCoproducts.lean`).

Monomorphisms and epimorphisms are characterized on underlying functions
as far as the census needs (`mono_of_injective`, `epi_of_surjective`);
the category is *not* balanced — see `StateSpace/Adjudication.lean` for
the cubing witness. -/

namespace SuFunctor.StateSpace

open CategoryTheory

/-- An ω-semialgebraic space: an ω-semialgebraic subset of some `ℝⁿ`. -/
structure OmegaSA : Type where
  /-- The ambient dimension. -/
  dim : ℕ
  /-- The carrier subset of `Fin dim → ℝ`. -/
  carrier : Set (Fin dim → ℝ)
  /-- The carrier is a countable union of basic polynomial pieces. -/
  isOmegaSA : IsOmegaSA carrier

namespace OmegaSA

instance : CoeSort OmegaSA Type :=
  ⟨fun V => ↥V.carrier⟩

/-- Morphisms: functions between the carriers whose ambient-valued
coercion is countably-piecewise-polynomial on the domain. -/
@[ext]
structure Hom (V W : OmegaSA) : Type where
  /-- The underlying function on carrier subtypes. -/
  toFun : V → W
  /-- The countably-piecewise-polynomial witness. -/
  property : IsPiecewisePolyOn V.carrier fun x => (toFun x : Fin W.dim → ℝ)

instance : Category OmegaSA where
  Hom := Hom
  id V := ⟨fun x => x, IsPiecewisePolyOn.id V.carrier⟩
  comp f g := ⟨fun x => g.toFun (f.toFun x), g.property.comp f.property⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_toFun (V : OmegaSA) (x : V) : Hom.toFun (𝟙 V) x = x := rfl

@[simp] lemma comp_toFun {U V W : OmegaSA} (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    Hom.toFun (f ≫ g) x = g.toFun (f.toFun x) := rfl

lemma hom_ext' {V W : OmegaSA} {f g : V ⟶ W}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g :=
  Hom.ext (funext h)

/-- Injective-on-carriers morphisms are monomorphisms. -/
lemma mono_of_injective {V W : OmegaSA} (f : V ⟶ W)
    (hf : Function.Injective f.toFun) : Mono f := by
  constructor
  intro U g h hgh
  exact hom_ext' fun x => hf (congrArg (fun k => Hom.toFun k x) hgh)

/-- Surjective-on-carriers morphisms are epimorphisms. -/
lemma epi_of_surjective {V W : OmegaSA} (f : V ⟶ W)
    (hf : Function.Surjective f.toFun) : Epi f := by
  constructor
  intro U g h hgh
  refine hom_ext' fun y => ?_
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun k => Hom.toFun k x) hgh

/-- An isomorphism has a two-sided piecewise-polynomial inverse on
underlying functions. -/
lemma isIso_inverse {V W : OmegaSA} (f : V ⟶ W) [IsIso f] :
    ∃ g : W ⟶ V, (∀ x, g.toFun (f.toFun x) = x) ∧ ∀ y, f.toFun (g.toFun y) = y :=
  ⟨inv f,
    fun x => congrArg (fun k => Hom.toFun k x) (IsIso.hom_inv_id f),
    fun y => congrArg (fun k => Hom.toFun k y) (IsIso.inv_hom_id f)⟩

end OmegaSA

end SuFunctor.StateSpace
