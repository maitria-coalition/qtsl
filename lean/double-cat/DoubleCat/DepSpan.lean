import DoubleCat.Basic
import DoubleCat.Companion
import Mathlib.CategoryTheory.Types.Basic

/-!
# The double category of dependent spans (type-valued matrices)

This file equips `Type u` with the pseudo double category structure whose
tight arrows are functions, loose arrows `A ↛ B` are type-valued matrices
`M : A → B → Type u` (a span `A ⟵ S ⟶ B` presented by its fibres, so that
the legs are projections and leg-compatibility is definitional), and cells
are fiberwise maps.  Loose composition is matrix multiplication with `Σ`
as sum and `×` as product; the loose identity is the diagonal family.

This is the double category of sets and matrices (Bénabou's bicategory of
matrices, viewed double-categorically), equivalent to the double category
of spans of types — but presented dependently: where `Span (Type u)`
composes loose arrows by a chosen pullback and every coherence proof rides
the universal property, the matrix presentation composes by `Σ` and every
coherence law holds by `rfl` after destructuring, because the category of
types has definitional category laws (so all boundary casts vanish by
proof irrelevance) and `Σ`/`×` enjoy definitional eta.

The instance lives directly on `Type u` (the convention of
`Mathlib.CategoryTheory.Monoidal.Types.Basic`, which puts the monoidal
structure directly on `Type u`), so tight arrows are mathlib's own
`X ⟶ Y` in `types` and morphism application needs no unwrapping.  The
definitions are grouped in the `CategoryTheory.DepSpan` namespace.

## Main definitions

* `CategoryTheory.DepSpan.Fam`: type-valued matrices, the loose arrows.
* `CategoryTheory.DepSpan.FamCell`: fiberwise maps, the cells.
* `CategoryTheory.DepSpan.instPseudoDoubleCategory`: the axioms, as an
  instance on `Type u`.
* `CategoryTheory.DepSpan.instEquipment`: the equipment structure
  (companion = graph family, conjoint = cograph family).

## Implementation notes

The loose identity's fibres are `ULift (PLift (x = y))` rather than an
inductive diagonal family: the propositional core gives proof irrelevance
and structure eta, under which most of the axioms close by `rfl` — an
inductive diagonal would block those reductions on opaque elements.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe u

namespace DepSpan

/-- A type-valued matrix `A → B → Type u`: a span `A ⟵ S ⟶ B` presented by
its fibres.  These are the loose arrows of the dependent-span double category
on `Type u`. -/
abbrev Fam (A B : Type u) : Type (u + 1) := A → B → Type u

namespace Fam

@[reducible] def id (A : Type u) : Fam A A :=
  fun x y => ULift (PLift (x = y))

@[reducible] def comp {A B C : Type u} (M : Fam A B) (N : Fam B C) :
    Fam A C :=
  fun x z => Σ y : B, M x y × N y z

@[reducible] def graph {A B : Type u} (f : A ⟶ B) : Fam A B :=
  fun x y => ULift (PLift (f x = y))

@[reducible] def cograph {A B : Type u} (f : A ⟶ B) : Fam B A :=
  fun y x => ULift (PLift (f x = y))

end Fam

/-- A cell between type-valued matrices over tight boundaries `f`, `g`: a
fiberwise map `M x y → N (f x) (g y)`. -/
abbrev FamCell {A B A' B' : Type u} (M : Fam A B) (N : Fam A' B')
    (f : A ⟶ A') (g : B ⟶ B') : Type u :=
  ∀ x y, M x y → N (f x) (g y)

theorem diag_heq {A : Type u} {x y : A} (h : x = y) :
    (⟨⟨rfl⟩⟩ : ULift.{u} (PLift (x = x))) ≍
      (⟨⟨rfl⟩⟩ : ULift.{u} (PLift (y = y))) := by
  subst h; rfl

theorem comp_heq {A B C : Type u} {M : Fam A B} {N : Fam B C}
    {x x' : A} {z z' : C} (hx : x = x') (hz : z = z')
    {y y' : B} (hy : y = y')
    {m : M x y} {m' : M x' y'} (hm : m ≍ m')
    {n : N y z} {n' : N y' z'} (hn : n ≍ n') :
    (⟨y, m, n⟩ : Fam.comp M N x z) ≍
      (⟨y', m', n'⟩ : Fam.comp M N x' z') := by
  subst hx; subst hz; subst hy
  rw [eq_of_heq hm, eq_of_heq hn]

theorem comp_snd_heq {A B C : Type u} {M : Fam A B} {N : Fam B C}
    {x : A} {z : C} {p₁ p₂ : Fam.comp M N x z} (h : p₁ = p₂) :
    p₁.2.2 ≍ p₂.2.2 := by
  subst h
  rfl

namespace FamCell

/-- Cells are determined by their fiberwise action. -/
theorem ext {A B A' B' : Type u} {M : Fam A B} {N : Fam A' B'}
    {f : A ⟶ A'} {g : B ⟶ B'} {φ ψ : FamCell M N f g}
    (h : ∀ x y s, φ x y s = ψ x y s) : φ = ψ :=
  funext fun x => funext fun y => funext (h x y)

theorem heq_of_apply {A B A' B' : Type u} {M : Fam A B}
    {N : Fam A' B'} {f f' : A ⟶ A'} {g g' : B ⟶ B'}
    {φ : FamCell M N f g} {ψ : FamCell M N f' g'}
    (hf : f = f') (hg : g = g')
    (h : ∀ x y (s : M x y), φ x y s ≍ ψ x y s) : φ ≍ ψ := by
  subst hf; subst hg
  exact heq_of_eq (ext fun x y s => eq_of_heq (h x y s))

theorem heq_apply {A B A' B' : Type u} {M : Fam A B} {N : Fam A' B'}
    {f f' : A ⟶ A'} {g g' : B ⟶ B'}
    {φ : FamCell M N f g} {ψ : FamCell M N f' g'}
    (hf : f = f') (hg : g = g') (h : φ ≍ ψ)
    (x : A) (y : B) (s : M x y) : φ x y s ≍ ψ x y s := by
  subst hf; subst hg; rw [eq_of_heq h]

theorem apply_congr_heq {A B A' B' : Type u} {M : Fam A B} {N : Fam A' B'}
    {f : A ⟶ A'} {g : B ⟶ B'} (φ : FamCell M N f g)
    {x x' : A} {y y' : B} (hx : x = x') (hy : y = y')
    {s : M x y} {s' : M x' y'} (hs : s ≍ s') :
    φ x y s ≍ φ x' y' s' := by
  subst hx; subst hy; rw [eq_of_heq hs]

@[reducible] def hId {A B : Type u} (f : A ⟶ B) :
    FamCell (Fam.id A) (Fam.id B) f f :=
  fun _ _ e => ⟨⟨congrArg _ e.down.down⟩⟩

@[reducible] def graphEta {A B : Type u} (f : A ⟶ B) :
    FamCell (Fam.id A) (Fam.graph f) (𝟙 A) f :=
  fun _ _ e => ⟨⟨congrArg _ e.down.down⟩⟩

@[reducible] def graphEps {A B : Type u} (f : A ⟶ B) :
    FamCell (Fam.graph f) (Fam.id B) f (𝟙 B) :=
  fun _ _ e => e

@[reducible] def cographEta {A B : Type u} (f : A ⟶ B) :
    FamCell (Fam.id A) (Fam.cograph f) f (𝟙 A) :=
  fun _ _ e => ⟨⟨(congrArg _ e.down.down).symm⟩⟩

@[reducible] def cographEps {A B : Type u} (f : A ⟶ B) :
    FamCell (Fam.cograph f) (Fam.id B) (𝟙 B) f :=
  fun _ _ e => ⟨⟨e.down.down.symm⟩⟩

end FamCell

/-- The dependent-span double category structure on `Type u`: loose
composition is matrix multiplication with `Σ` as sum and `×` as product; the
loose identity is the propositional diagonal family. -/
instance instPseudoDoubleCategoryStruct :
    PseudoDoubleCategoryStruct (Type u) where
  Loose A B := Fam A B
  Cell M N f g := FamCell M N f g
  vId _ := fun _ _ s => s
  vComp φ ψ := fun _ _ s => ψ _ _ (φ _ _ s)
  lId A := Fam.id A
  lComp M N := Fam.comp M N
  hId f := FamCell.hId f
  hComp φ ψ := fun _ _ s => ⟨_, φ _ _ s.2.1, ψ _ _ s.2.2⟩
  lAssoc _ _ _ := fun _ _ s => ⟨s.2.1.1, s.2.1.2.1, s.1, s.2.1.2.2, s.2.2⟩
  lAssocInv _ _ _ := fun _ _ s =>
    ⟨s.2.2.1, ⟨s.1, s.2.1, s.2.2.2.1⟩, s.2.2.2.2⟩
  lLeftUnitor _ := fun _ _ s =>
    match s with | ⟨_, ⟨⟨rfl⟩⟩, m⟩ => m
  lLeftUnitorInv _ := fun _ _ s => ⟨_, ⟨⟨rfl⟩⟩, s⟩
  lRightUnitor _ := fun _ _ s =>
    match s with | ⟨_, m, ⟨⟨rfl⟩⟩⟩ => m
  lRightUnitorInv _ := fun _ _ s => ⟨_, s, ⟨⟨rfl⟩⟩⟩

@[simp]
theorem lId_def (A : Type u) : 𝟙ˡ A = Fam.id A := rfl

@[simp]
theorem lComp_def {A B C : Type u} (M : Loose A B) (N : Loose B C) :
    M ⊙ N = Fam.comp M N := rfl

theorem lRightUnitor_apply_heq {A B : Type u} (M : Fam A B) {x : A}
    {y₀ y' : B} (v : M x y₀) (w : ULift.{u} (PLift (y₀ = y'))) :
    PseudoDoubleCategoryStruct.lRightUnitor (C := Type u) M x y'
      ⟨y₀, v, w⟩ ≍ v := by
  obtain ⟨⟨e⟩⟩ := w
  subst e
  rfl

/-- The axioms hold, mostly by `rfl` after destructuring: the category of
types has definitional category laws, so all boundary casts vanish. -/
instance instPseudoDoubleCategory : PseudoDoubleCategory (Type u) where
  vId_vComp _ := rfl
  vComp_vId _ := rfl
  vComp_assoc _ _ _ := rfl
  hId_id _ := rfl
  hId_comp _ _ := rfl
  hComp_vId _ _ := rfl
  interchange _ _ _ _ := rfl
  lAssoc_natural _ _ _ := rfl
  lLeftUnitor_natural α := by
    funext x y s
    obtain ⟨_, ⟨⟨rfl⟩⟩, m⟩ := s
    rfl
  lRightUnitor_natural α := by
    funext x y s
    obtain ⟨_, m, ⟨⟨rfl⟩⟩⟩ := s
    rfl
  lAssoc_lAssocInv _ _ _ := rfl
  lAssocInv_lAssoc _ _ _ := rfl
  lLeftUnitor_lLeftUnitorInv m := by
    funext x y s
    obtain ⟨_, ⟨⟨rfl⟩⟩, m'⟩ := s
    rfl
  lLeftUnitorInv_lLeftUnitor _ := rfl
  lRightUnitor_lRightUnitorInv m := by
    funext x y s
    obtain ⟨_, m', ⟨⟨rfl⟩⟩⟩ := s
    rfl
  lRightUnitorInv_lRightUnitor _ := rfl
  pentagon _ _ _ _ := rfl
  triangle m n := by
    funext x w s
    obtain ⟨_, ⟨_, mm, ⟨⟨rfl⟩⟩⟩, nn⟩ := s
    rfl

variable {A B : Type u}

/-- The companion of a function: its graph family `fun x y => ULift (PLift (f x = y))`. -/
def companion (f : A ⟶ B) : Companion f where
  loose := Fam.graph f
  eta := FamCell.graphEta f
  eps := FamCell.graphEps f
  eta_vComp_eps := rfl
  eta_hComp_eps := by
    funext x y e
    obtain ⟨⟨rfl⟩⟩ := e
    rfl

/-- The conjoint of a function: its cograph family. -/
def conjoint (f : A ⟶ B) : Conjoint f where
  loose := Fam.cograph f
  eta := FamCell.cographEta f
  eps := FamCell.cographEps f
  eta_vComp_eps := rfl
  eps_hComp_eta := by
    funext y x e
    obtain ⟨⟨rfl⟩⟩ := e
    rfl

/-- `Type u` with dependent spans is a proarrow equipment. -/
instance instEquipment : Equipment (Type u) where
  companion := fun f => companion f
  conjoint := fun f => conjoint f

end DepSpan

end CategoryTheory
