import DoubleCat.Virtual
import DoubleCat.Virtual.Functor
import DoubleCat.Virtual.OfPseudo
import DoubleCat.DepSpan
import Mathlib.CategoryTheory.Elements

/-!
# The virtual double category of elements of a span-valued virtual functor

A span-valued *virtual* indexing on a virtual double category `B` is a
functor of virtual double categories from `B` into the underlying virtual
double category of the dependent-span pseudo double category on `Type u`
(`DoubleCat.DepSpan` through `DoubleCat.Virtual.OfPseudo`).  No new
structure is required: the value on a loose arrow is a two-sided family,
and the value on a multicell is a fiberwise map out of the Σ-chain of the
domain path's families — the tuple (pullback-composite) span, which exists
in the representable target even though the base has no loose composition.
Against a representable target the multicell action on composite-forming
multicells *is* the laxator of a lax double functor (Cruttwell–Shulman,
"A unified framework for generalized multicategories", 2010), so laxity is
absorbed by virtuality rather than postulated: no laxator, compositor, or
unit comparison appears anywhere in this file.

This file introduces `VSpanValued`, the virtual double category of
elements `∫ᵛ P` — objects and tight arrows via mathlib's category of
elements, loose arrows as decorated base looses, multicells as base
multicells whose decoration condition says the indexing's cell action
carries the chained domain decorations to the codomain decoration — and
the strict projection `vproj : ∫ᵛ P → B`.  In every data field the
decoration is a direct application or a constructor; every equation
between elements lives in a `Prop` field, so the axioms of the total
reduce to the base's through one heterogeneous extensionality lemma
(`VGCell.heq_ext`) with *no thinness hypothesis* — matching how
`DoubleCat.Grothendieck` handles the pseudo case, minus its laxator legs,
which have no virtual counterpart to need handling.

The decoration-transport chases (rungs R1/R2 of the accompanying design
ladder) are fully proven — the transport kit and the associativity kit
below are those chases; every datum and every statement is final.

References: Cruttwell–Lambert–Pronk–Szyld, "Double fibrations" (2022)
(the pseudo-level representation theorem this construction restricts to);
Lambert, "Discrete double fibrations" (2021) (the discrete regime, over
strict double bases); Blanco, "Bifibrations of polycategories and
classical multiplicative linear logic" (PhD thesis, Birmingham, 2023)
(opcartesian multicells and pushfibrations of virtual double categories:
the projection's lifting property is the tight-boundary-general form of
his pushforwards); Patterson, "Structured and decorated cospans from the
viewpoint of double category theory" (2023) (the covariant span-valued
convention this file matches, as in `DoubleCat.Grothendieck`).
-/

namespace CategoryTheory

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

universe w t v u₁ u

attribute [local instance] VirtualDoubleCategoryStruct.ofPseudo

/-- A span-valued virtual indexing: a functor of virtual double categories
from `B` to the underlying virtual double category of the dependent-span
pseudo double category on `Type u`.  The virtual counterpart of
`SpanValued` (`DoubleCat.Grothendieck`); by Cruttwell–Shulman, when `B` is
the underlying virtual double category of a pseudo double category these
are exactly the span-valued lax double functors out of it. -/
abbrev VSpanValued (B : Type u₁) [Category.{v} B]
    [VirtualDoubleCategoryStruct.{w, t, v, u₁} B] :=
  VirtualDoubleFunctor B (Type u)

namespace VSpanValued

variable {B : Type u₁} [Category.{v} B]
  [VirtualDoubleCategoryStruct.{w, t, v, u₁} B]
variable (P : VSpanValued.{w, t, v, u₁, u} B)

/-- The virtual double category of elements of a span-valued virtual
indexing: objects and tight arrows are mathlib's category of elements of
the underlying functor; loose arrows and multicells are added below. -/
def Grothendieck := P.toFunctor.Elements

instance : Category (Grothendieck P) :=
  inferInstanceAs (Category P.toFunctor.Elements)

variable {P}

/-- A loose arrow of the virtual double category of elements: a loose
arrow of the base together with a decoration — an element of the two-sided
family `P` assigns to it, indexed at the endpoints' points. -/
structure VGLoose (p q : Grothendieck P) where
  /-- The underlying loose arrow of the base. -/
  base : Loose p.1 q.1
  /-- The decoration. -/
  dec : P.mapLoose base p.2 q.2

/-- The underlying path of base loose arrows of a path of decorated loose
arrows. -/
@[reducible] def basePath {p q : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p q) :
    LoosePath (Loose (C := B)) p.1 q.1 :=
  Ξ.map (fun r => r.1) (fun {_ _} e => e.base)

/-- The chained decoration of a path of decorated loose arrows: an element
of the Σ-chain (the fold of the mapped path) over the endpoints' points.
Composability of the decorations is automatic — consecutive loose arrows
of the path share their endpoint *object of elements*, hence their
endpoint point. -/
def chainDec : ∀ {p q : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p q),
    ((basePath Ξ).map P.obj (fun {_ _} e => P.mapLoose e)).fold p.2 q.2
  | _, _, .nil => ⟨⟨rfl⟩⟩
  | _, _, .cons (b := m) e Ξ' => ⟨m.2, e.dec, chainDec Ξ'⟩

@[simp] theorem chainDec_nil {p : Grothendieck P} :
    chainDec (.nil : LoosePath (VGLoose (P := P)) p p) = ⟨⟨rfl⟩⟩ := rfl

@[simp] theorem chainDec_cons {p m q : Grothendieck P}
    (e : VGLoose (P := P) p m) (Ξ : LoosePath (VGLoose (P := P)) m q) :
    chainDec (.cons e Ξ) = ⟨m.2, e.dec, chainDec Ξ⟩ := rfl

/-- A multicell of the virtual double category of elements: a multicell of
the base whose action on decorations (via `P`'s cell action, read at
elements and at the chained domain decoration) carries the domain
decorations to the codomain decoration. -/
structure VGCell {p q r s : Grothendieck P}
    (Ξ : LoosePath (VGLoose (P := P)) p q) (N : VGLoose (P := P) r s)
    (φ : p ⟶ r) (ψ : q ⟶ s) where
  /-- The underlying multicell of the base. -/
  base : Cell (basePath Ξ) N.base φ.1 ψ.1
  /-- The decoration condition (a proposition). -/
  dec : P.mapCell base p.2 q.2 (chainDec Ξ) ≍ N.dec

namespace VGCell

/-- Multicells of `∫ᵛ P` are determined by their base multicells. -/
theorem ext {p q r s : Grothendieck P}
    {Ξ : LoosePath (VGLoose (P := P)) p q} {N : VGLoose (P := P) r s}
    {φ : p ⟶ r} {ψ : q ⟶ s} {α β : VGCell Ξ N φ ψ}
    (h : α.base = β.base) : α = β := by
  cases α; cases β; cases h; rfl

/-- Heterogeneous extensionality: multicells of `∫ᵛ P` with
heterogeneously equal base multicells (and equal boundaries) are
heterogeneously equal — the decoration condition is a proposition.  The
axioms of `VirtualDoubleCategory (∫ᵛ P)` reduce through this lemma to the
base's, with no thinness hypothesis anywhere. -/
theorem heq_ext {p q r s : Grothendieck P}
    {Ξ Ξ' : LoosePath (VGLoose (P := P)) p q} {N : VGLoose (P := P) r s}
    {φ φ' : p ⟶ r} {ψ ψ' : q ⟶ s} {α : VGCell Ξ N φ ψ}
    {β : VGCell Ξ' N φ' ψ'} (hΞ : Ξ = Ξ') (hφ : φ = φ') (hψ : ψ = ψ')
    (h : α.base ≍ β.base) : α ≍ β := by
  subst hΞ; subst hφ; subst hψ
  exact heq_of_eq (ext (eq_of_heq h))

end VGCell

/-- The loose arrows and multicells of `∫ᵛ P`, as a
`VirtualDoubleCategoryData` instance (registered so that the covering
machinery of `DoubleCat.Virtual` elaborates against the total). -/
instance instData : VirtualDoubleCategoryData (Grothendieck P) where
  Loose p q := VGLoose p q
  Cell Ξ N φ ψ := VGCell Ξ N φ ψ

/-- The underlying covering sequence of base multicells of a covering
sequence of decorated multicells (the same recursion as
`mapSeqAux` at the forgetful data, stated directly because the total's
`VirtualDoubleCategoryStruct` — which `mapSeqAux` assumes — is being
built from it). -/
def baseSeq : ∀ {a b c d : Grothendieck P}
    {qs : LoosePath (VGLoose (P := P)) c d}
    {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d},
    CellSeq (C := Grothendieck P) qs ps u v →
    CellSeq (C := B) (basePath qs) (basePath ps) u.1 v.1
  | _, _, _, _, _, _, _, _, .nil f => .nil f.1
  | _, _, _, _, _, _, _, _, .cons A V =>
      (CellSeq.cons A.base (baseSeq V)).castDom
        (LoosePath.map_comp _ _ _ _).symm

section TransportKit

/-! ### The transport kit

Substitution in the base concatenates domain strings, and the image of a
concatenated string is a concatenation of images only propositionally
(`LoosePath.map_comp`); the covering-sequence machinery records this with
`castDom` transports.  The lemmas of this section move those transports
out of the way of the decoration chases: each is a `subst`-and-`rfl`, or a
structural induction whose every step computes definitionally in
`DepSpan` (whose category laws and `Σ`/`×` eta are definitional). -/

/-- Evaluating the fold of a domain-transported covering sequence at a
correspondingly transported element. -/
private theorem seqFoldAux_castDom_apply
    {A₀ B₀ : Type u} {qs' : LoosePath (Loose (C := Type u)) A₀ B₀}
    {a' b' : Type u} {ps' ps'' : LoosePath (Loose (C := Type u)) a' b'}
    {u' : a' ⟶ A₀} {v' : b' ⟶ B₀} (hp : ps' = ps'')
    (W : CellSeq (C := Type u) qs' ps' u' v') {x : a'} {y : b'}
    {pt : ps''.fold x y} {pt' : ps'.fold x y} (hpt : pt ≍ pt') :
    seqFoldAux (W.castDom hp) x y pt ≍ seqFoldAux W x y pt' := by
  subst hp
  cases eq_of_heq hpt
  rfl

/-- Folding the image of a domain-transported covering at a
correspondingly transported element: the transport passes through
`mapSeqAux` and the fold in one step. -/
private theorem seqFold_mapSeq_castDom_apply {a b c d : B}
    {qs : LoosePath (Loose (C := B)) c d}
    {ps ps' : LoosePath (Loose (C := B)) a b} {u' : a ⟶ c} {v' : b ⟶ d}
    (hp : ps = ps') (V : CellSeq (C := B) qs ps u' v') {x : P.obj a}
    {y : P.obj b}
    {pt : ((ps'.map P.obj (fun {_ _} e => P.mapLoose e)).fold) x y}
    {pt' : ((ps.map P.obj (fun {_ _} e => P.mapLoose e)).fold) x y}
    (hpt : pt ≍ pt') :
    seqFoldAux
        (mapSeqAux P.obj (fun {_ _} k => P.map k)
          (fun {_ _} e => P.mapLoose e)
          (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) (V.castDom hp))
        x y pt
      ≍ seqFoldAux
        (mapSeqAux P.obj (fun {_ _} k => P.map k)
          (fun {_ _} e => P.mapLoose e)
          (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) V)
        x y pt' := by
  subst hp
  cases eq_of_heq hpt
  rfl

/-- Domain-string transports compose. -/
private theorem castDom_castDom {C' : Type u₁} [Category.{v} C']
    [VirtualDoubleCategoryData.{w, t, v, u₁} C'] {a b c d : C'}
    {qs : LoosePath (Loose (C := C')) c d}
    {ps ps' ps'' : LoosePath (Loose (C := C')) a b} {f : a ⟶ c} {g : b ⟶ d}
    (h₁ : ps = ps') (h₂ : ps' = ps'') (V : CellSeq qs ps f g) :
    (V.castDom h₁).castDom h₂ = V.castDom (h₁.trans h₂) := by
  subst h₁; subst h₂; rfl

/-- Substitution along a domain-transported covering. -/
private theorem ccomp_castDom {a b c d e e' : B}
    {qs : LoosePath (Loose (C := B)) c d} {s : Loose e e'} {f : c ⟶ e}
    {g : d ⟶ e'} {ps ps' : LoosePath (Loose (C := B)) a b} {u : a ⟶ c}
    {v : b ⟶ d} (α : Cell qs s f g) (hp : ps = ps')
    (V : CellSeq (C := B) qs ps u v) :
    ccomp α (V.castDom hp) ≍ ccomp α V := by
  subst hp; rfl

/-- Splitting a heterogeneous equality of composite-span elements whose
tail families agree propositionally. -/
private theorem comp_heq_split {A B C : Type u} {M : DepSpan.Fam A B}
    {N N' : DepSpan.Fam B C} (hN : N = N') {x : A} {z : C} {y y' : B}
    {m : M x y} {m' : M x y'} {n : N y z} {n' : N' y' z}
    (h : (⟨y, m, n⟩ : DepSpan.Fam.comp M N x z) ≍
        (⟨y', m', n'⟩ : DepSpan.Fam.comp M N' x z)) :
    y = y' ∧ m ≍ m' ∧ n ≍ n' := by
  subst hN
  injection eq_of_heq h with h₁ h₂
  subst h₁
  injection eq_of_heq h₂ with h₃ h₄
  exact ⟨rfl, heq_of_eq h₃, heq_of_eq h₄⟩

/-- The fold comparison of `DoubleCat.Virtual.OfPseudo`, ascribed as the
fiberwise map it is over `DepSpan` (the instance projections otherwise
block applying it to elements). -/
private abbrev fCC {A₀ M₀ B₀ : Type u}
    (X : LoosePath (Loose (C := Type u)) A₀ M₀)
    (Y : LoosePath (Loose (C := Type u)) M₀ B₀) :
    ∀ x y, (X.comp Y).fold x y → DepSpan.Fam.comp X.fold Y.fold x y :=
  LoosePath.foldCompCell X Y

/-- Splitting the chained decoration of a concatenated path: the canonical
fold comparison sends any element heterogeneously equal to it to the pair
of the two chained decorations.  Every step computes definitionally in
`DepSpan` (the boundary casts vanish because the category laws of
`Type u` are definitional). -/
private theorem foldCompCell_chainDec :
    ∀ {p m q : Grothendieck P} (Ξ₁ : LoosePath (VGLoose (P := P)) p m)
      (Ξ₂ : LoosePath (VGLoose (P := P)) m q)
      (pt : (((basePath Ξ₁).map P.obj (fun {_ _} e => P.mapLoose e)).comp
          ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))).fold
          p.2 q.2)
      (hpt : pt ≍ chainDec (Ξ₁.comp Ξ₂)),
      fCC ((basePath Ξ₁).map P.obj (fun {_ _} e => P.mapLoose e))
          ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))
          p.2 q.2 pt
        ≍ (⟨m.2, chainDec Ξ₁, chainDec Ξ₂⟩ :
            DepSpan.Fam.comp
              (((basePath Ξ₁).map P.obj
                (fun {_ _} e => P.mapLoose e)).fold)
              (((basePath Ξ₂).map P.obj
                (fun {_ _} e => P.mapLoose e)).fold) p.2 q.2)
  | _, _, _, .nil, Ξ₂, pt, hpt => by
      cases eq_of_heq hpt
      rfl
  | p, m, q, .cons (b := mid) e Ξ₁', Ξ₂, pt, hpt => by
      obtain ⟨y₀, m₀, tail⟩ := pt
      obtain ⟨hy, hm, hn⟩ :=
        comp_heq_split
          (congrArg (fun z => LoosePath.fold z)
            (((congrArg
                (fun z =>
                  LoosePath.map P.obj (fun {_ _} e => P.mapLoose e) z)
                (LoosePath.map_comp (fun r => r.1) (fun {_ _} e => e.base)
                  Ξ₁' Ξ₂)).trans
              (LoosePath.map_comp P.obj (fun {_ _} e => P.mapLoose e)
                (basePath Ξ₁') (basePath Ξ₂))).symm)) hpt
      subst hy
      cases eq_of_heq hm
      have hIH :
          fCC ((basePath Ξ₁').map P.obj (fun {_ _} e => P.mapLoose e))
              ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))
              mid.2 q.2 tail =
            ⟨m.2, chainDec Ξ₁', chainDec Ξ₂⟩ :=
        eq_of_heq (foldCompCell_chainDec Ξ₁' Ξ₂ tail hn)
      have step :
          fCC ((basePath (LoosePath.cons e Ξ₁')).map P.obj
              (fun {_ _} e => P.mapLoose e))
            ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))
            p.2 q.2 ⟨mid.2, e.dec, tail⟩ =
            ⟨(fCC ((basePath Ξ₁').map P.obj
                (fun {_ _} e => P.mapLoose e))
                ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))
                mid.2 q.2 tail).1,
              ⟨mid.2, e.dec,
                (fCC ((basePath Ξ₁').map P.obj
                  (fun {_ _} e => P.mapLoose e))
                  ((basePath Ξ₂).map P.obj
                    (fun {_ _} e => P.mapLoose e))
                  mid.2 q.2 tail).2.1⟩,
              (fCC ((basePath Ξ₁').map P.obj
                (fun {_ _} e => P.mapLoose e))
                ((basePath Ξ₂).map P.obj (fun {_ _} e => P.mapLoose e))
                mid.2 q.2 tail).2.2⟩ := rfl
      rw [step, hIH]
      rfl

/-- The `cons` step of the master decoration chase, stated separately so
that the constructor's telescope is in scope by name. -/
private theorem seqFold_chainDec_cons {a a₁ b c c₁ d : Grothendieck P}
    {ps₁ : LoosePath (VGLoose (P := P)) a a₁} {Nh : VGLoose (P := P) c c₁}
    {ut : a ⟶ c} {wt : a₁ ⟶ c₁}
    {qs' : LoosePath (VGLoose (P := P)) c₁ d}
    {rs : LoosePath (VGLoose (P := P)) a₁ b} {vt : b ⟶ d}
    (A : VGCell ps₁ Nh ut wt)
    (V' : CellSeq (C := Grothendieck P) qs' rs wt vt)
    (ih :
      seqFoldAux
          (mapSeqAux P.obj (fun {_ _} k => P.map k)
            (fun {_ _} e => P.mapLoose e)
            (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) (baseSeq V'))
          a₁.2 b.2 (chainDec rs)
        ≍ chainDec qs') :
    seqFoldAux
        (mapSeqAux P.obj (fun {_ _} k => P.map k)
          (fun {_ _} e => P.mapLoose e)
          (fun {_ _ _ _ _ _ _ _} β => P.mapCell β)
          (baseSeq (CellSeq.cons A V')))
        a.2 b.2 (chainDec (ps₁.comp rs))
      ≍ chainDec (LoosePath.cons Nh qs') := by
  have hb :
      baseSeq (CellSeq.cons A V') =
        (CellSeq.cons A.base (baseSeq V')).castDom
          (LoosePath.map_comp (fun r => r.1) (fun {_ _} e => e.base)
            ps₁ rs).symm := rfl
  rw [hb]
  have h₁ :
      (basePath ps₁).comp (basePath rs) = basePath (ps₁.comp rs) :=
    (LoosePath.map_comp (fun r => r.1) (fun {_ _} e => e.base) ps₁ rs).symm
  have hf₁ :
      ((basePath (ps₁.comp rs)).map P.obj
          (fun {_ _} e => P.mapLoose e)).fold a.2 b.2 =
        ((((basePath ps₁).comp (basePath rs)).map P.obj
          (fun {_ _} e => P.mapLoose e)).fold) a.2 b.2 :=
    (congrArg
      (fun s => ((LoosePath.map P.obj (fun {_ _} e => P.mapLoose e) s).fold)
        a.2 b.2) h₁).symm
  refine
    (seqFold_mapSeq_castDom_apply (P := P) h₁ _
      ((cast_heq hf₁ (chainDec (ps₁.comp rs))).symm)).trans ?_
  have h₃ :
      ((basePath ps₁).map P.obj (fun {_ _} e => P.mapLoose e)).comp
          ((basePath rs).map P.obj (fun {_ _} e => P.mapLoose e)) =
        (((basePath ps₁).comp (basePath rs)).map P.obj
          (fun {_ _} e => P.mapLoose e)) :=
    (LoosePath.map_comp P.obj (fun {_ _} e => P.mapLoose e)
      (basePath ps₁) (basePath rs)).symm
  have hf₃ :
      ((((basePath ps₁).comp (basePath rs)).map P.obj
          (fun {_ _} e => P.mapLoose e)).fold) a.2 b.2 =
        (((((basePath ps₁).map P.obj
              (fun {_ _} e => P.mapLoose e)).comp
            ((basePath rs).map P.obj
              (fun {_ _} e => P.mapLoose e)))).fold) a.2 b.2 :=
    (congrArg
      (fun s : LoosePath (Loose (C := Type u)) (P.obj a.1) (P.obj b.1) =>
        (LoosePath.fold s) a.2 b.2) h₃).symm
  refine
    (seqFoldAux_castDom_apply h₃ _
      ((cast_heq hf₃ (cast hf₁ (chainDec (ps₁.comp rs)))).symm)).trans ?_
  have hK3 :
      (fCC ((basePath ps₁).map P.obj (fun {_ _} e => P.mapLoose e))
          ((basePath rs).map P.obj (fun {_ _} e => P.mapLoose e))
          a.2 b.2 (cast hf₃ (cast hf₁ (chainDec (ps₁.comp rs))))) =
        ⟨a₁.2, chainDec ps₁, chainDec rs⟩ :=
    eq_of_heq
      (foldCompCell_chainDec ps₁ rs _
        ((cast_heq hf₃ (cast hf₁ (chainDec (ps₁.comp rs)))).trans
          (cast_heq hf₁ (chainDec (ps₁.comp rs)))))
  have pairEq :
      (⟨P.map wt.1 ((fCC ((basePath ps₁).map P.obj (fun {_ _} e => P.mapLoose e))
          ((basePath rs).map P.obj (fun {_ _} e => P.mapLoose e))
          a.2 b.2 (cast hf₃ (cast hf₁ (chainDec (ps₁.comp rs)))))).1,
        P.mapCell A.base a.2 _ ((fCC ((basePath ps₁).map P.obj (fun {_ _} e => P.mapLoose e))
          ((basePath rs).map P.obj (fun {_ _} e => P.mapLoose e))
          a.2 b.2 (cast hf₃ (cast hf₁ (chainDec (ps₁.comp rs)))))).2.1,
        seqFoldAux
          (mapSeqAux P.obj (fun {_ _} k => P.map k)
            (fun {_ _} e => P.mapLoose e)
            (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) (baseSeq V'))
          _ b.2 ((fCC ((basePath ps₁).map P.obj (fun {_ _} e => P.mapLoose e))
          ((basePath rs).map P.obj (fun {_ _} e => P.mapLoose e))
          a.2 b.2 (cast hf₃ (cast hf₁ (chainDec (ps₁.comp rs)))))).2.2⟩ :
        DepSpan.Fam.comp (P.mapLoose Nh.base)
          (((basePath qs').map P.obj
            (fun {_ _} e => P.mapLoose e)).fold)
          (P.map ut.1 a.2) (P.map vt.1 b.2)) =
      ⟨P.map wt.1 a₁.2,
        P.mapCell A.base a.2 a₁.2 (chainDec ps₁),
        seqFoldAux
          (mapSeqAux P.obj (fun {_ _} k => P.map k)
            (fun {_ _} e => P.mapLoose e)
            (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) (baseSeq V'))
          a₁.2 b.2 (chainDec rs)⟩ := by
    rw [hK3]
  exact (heq_of_eq pairEq).trans
    (DepSpan.comp_heq ut.2 vt.2 wt.2 A.dec ih)

/-- The master decoration chase: folding the image of a covering sequence
over the chained decoration of its domain path yields the chained
decoration of its covered path (each block contributing its own
decoration condition). -/
private theorem seqFold_chainDec :
    ∀ {a b c d : Grothendieck P} {qs : LoosePath (VGLoose (P := P)) c d}
      {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
      (V : CellSeq (C := Grothendieck P) qs ps u v),
      seqFoldAux
          (mapSeqAux P.obj (fun {_ _} k => P.map k)
            (fun {_ _} e => P.mapLoose e)
            (fun {_ _ _ _ _ _ _ _} β => P.mapCell β) (baseSeq V))
          a.2 b.2 (chainDec ps)
        ≍ chainDec qs
  | _, _, _, _, _, _, _, _, .nil f => DepSpan.diag_heq f.2
  | _, _, _, _, _, _, _, _, .cons A V' =>
      seqFold_chainDec_cons A V' (seqFold_chainDec V')

end TransportKit

/-- The virtual double category structure on `∫ᵛ P`: identities and
substitution decorate the base's, the decoration conditions riding
`mapCell_cid` (with the right-unitor evaluation of `DepSpan`) and
`mapCell_ccomp` (with the master chase `seqFold_chainDec`). -/
instance instVirtualDoubleCategoryStruct :
    VirtualDoubleCategoryStruct (Grothendieck P) where
  toVirtualDoubleCategoryData := instData
  cid N :=
    { base := cid N.base
      dec :=
        (DepSpan.FamCell.heq_apply (P.toFunctor.map_id _)
            (P.toFunctor.map_id _) (P.mapCell_cid N.base) _ _
            (chainDec (.single N))).trans
          (DepSpan.lRightUnitor_apply_heq (P.mapLoose N.base) N.dec
            ⟨⟨rfl⟩⟩) }
  ccomp := fun {a b c d e e' qs s f g ps u v} α V =>
    { base := ccomp α.base (baseSeq V)
      dec :=
        (DepSpan.FamCell.heq_apply (P.toFunctor.map_comp _ _)
            (P.toFunctor.map_comp _ _)
            (P.mapCell_ccomp α.base (baseSeq V)) _ _ (chainDec ps)).trans
          ((DepSpan.FamCell.apply_congr_heq (P.mapCell α.base)
              u.2 v.2 (seqFold_chainDec V)).trans α.dec) }


section AssocKit

/-! ### The associativity transport kit

The covering-of-covering machinery (`SeqUnder`, `flatten`, `compUnder`)
threads the same propositional string equalities as substitution itself;
this section moves those transports through the forgetful image so that
the base's associativity law can be consumed directly.  Every helper is a
`subst`-collapse; the two bridges are structural inductions whose cast
chains close by proof irrelevance (casts between definitionally equal
endpoints vanish). -/

variable {Cq : Type u₁} [Category.{v} Cq]
  [VirtualDoubleCategoryStruct.{w, t, v, u₁} Cq]

/-- Transport a covering-of-covering along an equality of its inner
string. -/
private def castOs {a b c d : Cq} {qs : LoosePath (Loose (C := Cq)) c d}
    {ps : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os os' : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (h : os = os') (W : SeqUnder V os s t) : SeqUnder V os' s t :=
  h ▸ W

/-- Transport a covering-of-covering along a domain transport of the
covering it covers. -/
private def castSeq {a b c d : Cq} {qs : LoosePath (Loose (C := Cq)) c d}
    {ps ps' : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (hp : ps = ps') (W : SeqUnder V os s t) :
    SeqUnder (V.castDom hp) os s t := by
  subst hp; exact W

/-- Codomain transports compose. -/
private theorem castCod_castCod {a b c d : Cq}
    {qs qs' qs'' : LoosePath (Loose (C := Cq)) c d}
    {ps : LoosePath (Loose (C := Cq)) a b} {f : a ⟶ c} {g : b ⟶ d}
    (h₁ : qs = qs') (h₂ : qs' = qs'')
    (V : CellSeq (C := Cq) qs ps f g) :
    (V.castCod h₁).castCod h₂ = V.castCod (h₁.trans h₂) := by
  subst h₁; subst h₂; rfl

/-- Domain and codomain transports commute. -/
private theorem castDom_castCod {a b c d : Cq}
    {qs qs' : LoosePath (Loose (C := Cq)) c d}
    {ps ps' : LoosePath (Loose (C := Cq)) a b} {f : a ⟶ c} {g : b ⟶ d}
    (hq : qs = qs') (hp : ps = ps') (V : CellSeq (C := Cq) qs ps f g) :
    (V.castCod hq).castDom hp = (V.castDom hp).castCod hq := by
  subst hq; subst hp; rfl

/-- Prepending under a domain transport of the tail. -/
private theorem cons_castDom_tail {a a₁ b c c₁ d : Cq}
    {ps₁ : LoosePath (Loose (C := Cq)) a a₁} {q : Loose c c₁}
    {u : a ⟶ c} {w : a₁ ⟶ c₁} {qs : LoosePath (Loose (C := Cq)) c₁ d}
    {rs rs' : LoosePath (Loose (C := Cq)) a₁ b} {v : b ⟶ d}
    (β : Cell ps₁ q u w) (h : rs = rs')
    (V : CellSeq (C := Cq) qs rs w v) :
    CellSeq.cons β (V.castDom h) =
      (CellSeq.cons β V).castDom (congrArg (fun z => ps₁.comp z) h) := by
  subst h; rfl

/-- Prepending under a codomain transport of the tail. -/
private theorem cons_castCod_tail {a a₁ b c c₁ d : Cq}
    {ps₁ : LoosePath (Loose (C := Cq)) a a₁} {q : Loose c c₁}
    {u : a ⟶ c} {w : a₁ ⟶ c₁} {qs qs' : LoosePath (Loose (C := Cq)) c₁ d}
    {rs : LoosePath (Loose (C := Cq)) a₁ b} {v : b ⟶ d}
    (β : Cell ps₁ q u w) (h : qs = qs')
    (V : CellSeq (C := Cq) qs rs w v) :
    CellSeq.cons β (V.castCod h) =
      (CellSeq.cons β V).castCod
        (congrArg (fun z => LoosePath.cons q z) h) := by
  subst h; rfl

/-- Appending under transports of the first covering. -/
private theorem append_castDom_left {a b b' c d d' : Cq}
    {qs₁ : LoosePath (Loose (C := Cq)) c d}
    {ps₁ ps₁' : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {w : b ⟶ d}
    {qs₂ : LoosePath (Loose (C := Cq)) d d'}
    {ps₂ : LoosePath (Loose (C := Cq)) b b'} {v : b' ⟶ d'}
    (hp : ps₁ = ps₁') (X : CellSeq (C := Cq) qs₁ ps₁ u w)
    (Y : CellSeq (C := Cq) qs₂ ps₂ w v) :
    (X.castDom hp).append Y =
      (X.append Y).castDom (congrArg (fun z => z.comp ps₂) hp) := by
  subst hp; rfl

private theorem append_castCod_left {a b b' c d d' : Cq}
    {qs₁ qs₁' : LoosePath (Loose (C := Cq)) c d}
    {ps₁ : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {w : b ⟶ d}
    {qs₂ : LoosePath (Loose (C := Cq)) d d'}
    {ps₂ : LoosePath (Loose (C := Cq)) b b'} {v : b' ⟶ d'}
    (hq : qs₁ = qs₁') (X : CellSeq (C := Cq) qs₁ ps₁ u w)
    (Y : CellSeq (C := Cq) qs₂ ps₂ w v) :
    (X.castCod hq).append Y =
      (X.append Y).castCod (congrArg (fun z => z.comp qs₂) hq) := by
  subst hq; rfl

/-- Prepending respects heterogeneous equality of tails over a
propositional equality of their domain strings. -/
private theorem cons_congr_heq {a a₁ b c c₁ d : Cq}
    {ps₁ : LoosePath (Loose (C := Cq)) a a₁} {q : Loose c c₁}
    {u : a ⟶ c} {w : a₁ ⟶ c₁} {qs qs' : LoosePath (Loose (C := Cq)) c₁ d}
    {rs rs' : LoosePath (Loose (C := Cq)) a₁ b} {v : b ⟶ d}
    (β : Cell ps₁ q u w) (Z : CellSeq (C := Cq) qs rs w v)
    (Z' : CellSeq (C := Cq) qs' rs' w v) (hZ : Z ≍ Z')
    (hqs : qs = qs') (hrs : rs = rs') :
    CellSeq.cons β Z ≍ CellSeq.cons β Z' := by
  subst hqs
  subst hrs
  rw [eq_of_heq hZ]

/-- Appending respects heterogeneous equality of the first covering over
a propositional equality of its domain string. -/
private theorem append_congr_left_heq {a b b' c d d' : Cq}
    {qs₁ qs₁' : LoosePath (Loose (C := Cq)) c d}
    {ps₁ ps₁' : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {w : b ⟶ d}
    {qs₂ : LoosePath (Loose (C := Cq)) d d'}
    {ps₂ : LoosePath (Loose (C := Cq)) b b'} {v : b' ⟶ d'}
    (X : CellSeq (C := Cq) qs₁ ps₁ u w)
    (X' : CellSeq (C := Cq) qs₁' ps₁' u w) (hX : X ≍ X')
    (hq : qs₁ = qs₁') (hp : ps₁ = ps₁')
    (Y : CellSeq (C := Cq) qs₂ ps₂ w v) :
    X.append Y ≍ X'.append Y := by
  subst hq
  subst hp
  rw [eq_of_heq hX]

private theorem flatten_castOs {a b c d : Cq}
    {qs : LoosePath (Loose (C := Cq)) c d}
    {ps : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os os' : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (h : os = os') (W : SeqUnder V os s t) :
    (castOs h W).flatten = W.flatten.castDom h := by
  subst h; rfl

private theorem flatten_castSeq {a b c d : Cq}
    {qs : LoosePath (Loose (C := Cq)) c d}
    {ps ps' : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (hp : ps = ps') (W : SeqUnder V os s t) :
    (castSeq hp W).flatten = W.flatten.castCod hp := by
  subst hp; rfl

private theorem compUnder_castOs {a b c d : Cq}
    {qs : LoosePath (Loose (C := Cq)) c d}
    {ps : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os os' : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (h : os = os') (W : SeqUnder V os s t) :
    compUnder (castOs h W) = (compUnder W).castDom h := by
  subst h; rfl

private theorem compUnder_castSeq {a b c d : Cq}
    {qs : LoosePath (Loose (C := Cq)) c d}
    {ps ps' : LoosePath (Loose (C := Cq)) a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq (C := Cq) qs ps u v} {a' b' : Cq}
    {os : LoosePath (Loose (C := Cq)) a' b'} {s : a' ⟶ a} {t : b' ⟶ b}
    (hp : ps = ps') (W : SeqUnder V os s t) :
    compUnder (castSeq hp W) = compUnder W := by
  subst hp; rfl

/-- The forgetful image of a covering-of-covering. -/
private def baseSeqUnder :
    ∀ {a b c d : Grothendieck P} {qs : LoosePath (VGLoose (P := P)) c d}
      {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
      {V : CellSeq (C := Grothendieck P) qs ps u v}
      {a' b' : Grothendieck P} {os : LoosePath (VGLoose (P := P)) a' b'}
      {s : a' ⟶ a} {t : b' ⟶ b},
      SeqUnder V os s t →
        SeqUnder (baseSeq V) (basePath os) s.1 t.1
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil f s => .nil f.1 s.1
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons β V W₁ Wr =>
      castSeq (LoosePath.map_comp _ _ _ _).symm
        (castOs (LoosePath.map_comp _ _ _ _).symm
          (SeqUnder.cons β.base (baseSeq V) (baseSeq W₁)
            (baseSeqUnder Wr)))

/-- `baseSeq` commutes with domain transports. -/
private theorem baseSeq_castDom {a b c d : Grothendieck P}
    {qs : LoosePath (VGLoose (P := P)) c d}
    {ps ps' : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
    (h : ps = ps') (Z : CellSeq (C := Grothendieck P) qs ps u v) :
    baseSeq (Z.castDom h) =
      (baseSeq Z).castDom
        (congrArg (fun z : LoosePath (VGLoose (P := P)) a b =>
          basePath z) h) := by
  subst h; rfl

/-- The forgetful image of an appended covering. -/
private theorem baseSeq_append :
    ∀ {a b b' c d d' : Grothendieck P}
      {qs₁ : LoosePath (VGLoose (P := P)) c d}
      {ps₁ : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {w : b ⟶ d}
      {qs₂ : LoosePath (VGLoose (P := P)) d d'}
      {ps₂ : LoosePath (VGLoose (P := P)) b b'} {v : b' ⟶ d'}
      (X : CellSeq (C := Grothendieck P) qs₁ ps₁ u w)
      (Y : CellSeq (C := Grothendieck P) qs₂ ps₂ w v),
      baseSeq (X.append Y) =
        (((baseSeq X).append (baseSeq Y)).castCod
            (LoosePath.map_comp _ _ qs₁ qs₂).symm).castDom
          (LoosePath.map_comp _ _ ps₁ ps₂).symm
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .nil _, Y => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .cons γ X', Y => by
      have hIH := baseSeq_append X' Y
      have hIHe : baseSeq (X'.append Y) ≍
          (baseSeq X').append (baseSeq Y) :=
        (heq_of_eq hIH).trans
          ((CellSeq.castDom_heq _ _).trans (CellSeq.castCod_heq _ _))
      have h₁ : baseSeq ((CellSeq.cons γ X').append Y) ≍
          baseSeq (CellSeq.cons γ (X'.append Y)) :=
        (heq_of_eq (baseSeq_castDom (LoosePath.comp_assoc _ _ _).symm
          (CellSeq.cons γ (X'.append Y)))).trans (CellSeq.castDom_heq _ _)
      have h₂ : baseSeq (CellSeq.cons γ (X'.append Y)) ≍
          CellSeq.cons γ.base (baseSeq (X'.append Y)) :=
        CellSeq.castDom_heq _ _
      have h₃ : CellSeq.cons γ.base (baseSeq (X'.append Y)) ≍
          CellSeq.cons γ.base ((baseSeq X').append (baseSeq Y)) := by
        refine cons_congr_heq (Cq := B) γ.base (baseSeq (X'.append Y))
          ((baseSeq X').append (baseSeq Y)) hIHe ?_ ?_
        · exact LoosePath.map_comp _ _ _ _
        · exact LoosePath.map_comp _ _ _ _
      have hcons₁ : baseSeq (CellSeq.cons γ X') ≍
          CellSeq.cons γ.base (baseSeq X') := CellSeq.castDom_heq _ _
      have h₄ : (((baseSeq (CellSeq.cons γ X')).append (baseSeq Y)).castCod
            (LoosePath.map_comp _ _ _ _).symm).castDom
            (LoosePath.map_comp _ _ _ _).symm ≍
          (baseSeq (CellSeq.cons γ X')).append (baseSeq Y) :=
        (CellSeq.castDom_heq _ _).trans (CellSeq.castCod_heq _ _)
      have h₅ : (baseSeq (CellSeq.cons γ X')).append (baseSeq Y) ≍
          (CellSeq.cons γ.base (baseSeq X')).append (baseSeq Y) := by
        refine append_congr_left_heq (Cq := B)
          (baseSeq (CellSeq.cons γ X'))
          (CellSeq.cons γ.base (baseSeq X')) hcons₁ rfl ?_ (baseSeq Y)
        exact LoosePath.map_comp _ _ _ _
      have h₆ : (CellSeq.cons γ.base (baseSeq X')).append (baseSeq Y) ≍
          CellSeq.cons γ.base ((baseSeq X').append (baseSeq Y)) :=
        CellSeq.castDom_heq _ _
      exact eq_of_heq ((h₁.trans h₂).trans
        (h₃.trans (h₄.trans (h₅.trans h₆)).symm))

/-- The forgetful image of a flattened covering-of-covering. -/
private theorem baseSeq_flatten :
    ∀ {a b c d : Grothendieck P} {qs : LoosePath (VGLoose (P := P)) c d}
      {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
      {V : CellSeq (C := Grothendieck P) qs ps u v}
      {a' b' : Grothendieck P} {os : LoosePath (VGLoose (P := P)) a' b'}
      {s : a' ⟶ a} {t : b' ⟶ b} (W : SeqUnder V os s t),
      baseSeq (SeqUnder.flatten W) = (baseSeqUnder W).flatten
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil f s => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons β V W₁ Wr => by
      have hIH := baseSeq_flatten Wr
      have hL : baseSeq ((SeqUnder.cons β V W₁ Wr).flatten) ≍
          (baseSeq W₁).append (baseSeqUnder Wr).flatten :=
        (heq_of_eq (baseSeq_append W₁ (SeqUnder.flatten Wr))).trans
          (((CellSeq.castDom_heq _ _).trans
            (CellSeq.castCod_heq _ _)).trans
            (heq_of_eq (congrArg (fun z => (baseSeq W₁).append z) hIH)))
      have hR : (baseSeqUnder (SeqUnder.cons β V W₁ Wr)).flatten ≍
          (baseSeq W₁).append (baseSeqUnder Wr).flatten := by
        refine HEq.trans (b := ((SeqUnder.cons β.base (baseSeq V)
            (baseSeq W₁) (baseSeqUnder Wr)).flatten.castDom
              (LoosePath.map_comp _ _ _ _).symm).castCod
              (LoosePath.map_comp _ _ _ _).symm) ?_ ?_
        · exact heq_of_eq
            ((congrArg (fun z => CellSeq.castCod
                (LoosePath.map_comp _ _ _ _).symm z)
              (flatten_castOs (Cq := B) _ _)).symm ▸
              (flatten_castSeq (Cq := B) _ _))
        · exact (CellSeq.castCod_heq _ _).trans (CellSeq.castDom_heq _ _)
      exact eq_of_heq (hL.trans hR.symm)

/-- The forgetful image of a blockwise substitution. -/
private theorem baseSeq_compUnder :
    ∀ {a b c d : Grothendieck P} {qs : LoosePath (VGLoose (P := P)) c d}
      {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
      {V : CellSeq (C := Grothendieck P) qs ps u v}
      {a' b' : Grothendieck P} {os : LoosePath (VGLoose (P := P)) a' b'}
      {s : a' ⟶ a} {t : b' ⟶ b} (W : SeqUnder V os s t),
      baseSeq (compUnder W) = compUnder (baseSeqUnder W)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil f s => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons β V W₁ Wr => by
      have hIH := baseSeq_compUnder Wr
      have hL : baseSeq (compUnder (SeqUnder.cons β V W₁ Wr)) ≍
          CellSeq.cons (ccomp β.base (baseSeq W₁))
            (compUnder (baseSeqUnder Wr)) :=
        (CellSeq.castDom_heq _ _).trans
          (heq_of_eq (congrArg
            (fun z => CellSeq.cons (ccomp β.base (baseSeq W₁)) z) hIH))
      have hR : compUnder (baseSeqUnder (SeqUnder.cons β V W₁ Wr)) ≍
          CellSeq.cons (ccomp β.base (baseSeq W₁))
            (compUnder (baseSeqUnder Wr)) := by
        refine HEq.trans
          (b := (compUnder (SeqUnder.cons β.base (baseSeq V) (baseSeq W₁)
            (baseSeqUnder Wr))).castDom
            (LoosePath.map_comp _ _ _ _).symm) ?_ ?_
        · exact heq_of_eq
            ((compUnder_castSeq (Cq := B) _ _).trans
              (compUnder_castOs (Cq := B) _ _))
        · exact CellSeq.castDom_heq _ _
      exact eq_of_heq (hL.trans hR.symm)

end AssocKit

/-- The image of the identity covering under `baseSeq` is the identity
covering of the image string (the transports collapse definitionally:
their endpoints are constructor-headed). -/
private theorem baseSeq_idSeq :
    ∀ {c d : Grothendieck P} (qs : LoosePath (VGLoose (P := P)) c d),
      baseSeq (idSeq qs) = idSeq (basePath qs)
  | _, _, .nil => rfl
  | _, _, .cons e rest =>
      congrArg (CellSeq.cons (cid e.base)) (baseSeq_idSeq rest)

/-- `baseSeq` is `mapSeqAux` at the forgetful data of the projection. -/
private theorem baseSeq_eq_mapSeqAux :
    ∀ {a b c d : Grothendieck P} {qs : LoosePath (VGLoose (P := P)) c d}
      {ps : LoosePath (VGLoose (P := P)) a b} {u : a ⟶ c} {v : b ⟶ d}
      (V : CellSeq (C := Grothendieck P) qs ps u v),
      baseSeq V =
        mapSeqAux (C := Grothendieck P) (D := B)
          (CategoryOfElements.π P.toFunctor).obj
          (fun {_ _} k => (CategoryOfElements.π P.toFunctor).map k)
          (fun {_ _} e => VGLoose.base e)
          (fun {_ _ _ _ _ _ _ _} A => VGCell.base A) V
  | _, _, _, _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, _, _, _, .cons A V =>
      congrArg (fun W => (CellSeq.cons A.base W).castDom
        (LoosePath.map_comp _ _ _ _).symm) (baseSeq_eq_mapSeqAux V)

/-- The axioms, componentwise from the base through `VGCell.heq_ext` (the
decoration condition is propositional, so no thinness is needed): the base
sides of each law are the base law's sides up to the `castDom` transports
of `baseSeq`, which the kit lemmas discharge.

The associativity leg threads the base law through the image of a
covering-of-covering; its transport bridge is the associativity kit above
(rung R2 of the design ladder), with the two unit laws riding the
transport kit directly. -/
instance instVirtualDoubleCategory [VirtualDoubleCategory B] :
    VirtualDoubleCategory (Grothendieck P) where
  ccomp_idSeq α :=
    VGCell.heq_ext rfl (by simp) (by simp)
      (by
        show ccomp α.base (baseSeq (idSeq _)) ≍ α.base
        rw [baseSeq_idSeq]
        exact VirtualDoubleCategory.ccomp_idSeq α.base)
  cid_ccomp α :=
    VGCell.heq_ext (LoosePath.comp_nil _) (by simp) (by simp)
      (by
        show ccomp (cid _) (baseSeq (CellSeq.singleton α)) ≍ α.base
        exact
          (ccomp_castDom (cid _) _ _).trans
            (VirtualDoubleCategory.cid_ccomp α.base))
  ccomp_assoc := fun {a b c d e e' a' b'} {qs s f g ps u v} α V {os s' t'} W =>
    VGCell.heq_ext rfl (by simp) (by simp)
      (by
        show ccomp (ccomp α.base (baseSeq V))
            (baseSeq (SeqUnder.flatten W)) ≍
          ccomp α.base (baseSeq (compUnder W))
        rw [baseSeq_flatten, baseSeq_compUnder]
        exact VirtualDoubleCategory.ccomp_assoc α.base (baseSeq V)
          (baseSeqUnder W))

variable (P)

/-- The strict projection `∫ᵛ P → B`: forget decorations.  Unlike the
pseudo-level projection (`SpanValued.proj`), there are no laxator legs —
a functor of virtual double categories has nothing to compare, which is
the point of taking the virtual presentation as primary. -/
def vproj : VirtualDoubleFunctor (Grothendieck P) B where
  toFunctor := CategoryOfElements.π P.toFunctor
  mapLoose M := M.base
  mapCell A := A.base
  mapCell_cid _ := HEq.rfl
  mapCell_ccomp α V := heq_of_eq (congrArg (ccomp α.base)
    (baseSeq_eq_mapSeqAux V))

end VSpanValued

end CategoryTheory
