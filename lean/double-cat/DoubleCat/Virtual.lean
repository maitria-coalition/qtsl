import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom

/-!
# Virtual double categories

This file defines virtual double categories, following Cruttwell–Shulman
("A unified framework for generalized multicategories", 2010, §2), where
they appear as the natural home of structures whose loose arrows do not
compose: there are objects, tight arrows, loose arrows, and *multicells*
whose loose domain is a finite composable string of loose arrows and whose
loose codomain is a single loose arrow.  The same notion appears as
Leinster's fc-multicategories ("Higher Operads, Higher Categories", 2004,
§5.1) and, earlier, as Burroni's T-categories for the free-category monad.

## Main definitions

* `CategoryTheory.LoosePath`: finite composable strings over an arbitrary
  family of edges `L : C → C → Type w` (the loose analogue of
  `Quiver.Path`, kept family-parametric because the loose arrows of a
  virtual double category are a second edge structure on a carrier that
  already has a `Category` instance for its tight direction, so a `Quiver`
  instance for them would collide with the one `Category` provides).
* `CategoryTheory.VirtualDoubleCategoryData`: loose arrows and multicells.
  A multicell `Cell ps q f g` has a composable string `ps` of loose arrows
  as its loose domain, a single loose arrow `q` as its loose codomain, and
  tight side boundaries `f`, `g`.
* `CategoryTheory.VirtualDoubleCategoryData.CellSeq`: a composable
  sequence of multicells covering a string — the shape of the "blanket" a
  multicell is substituted along.  Consecutive entries share their
  boundary tight arrow.
* `CategoryTheory.VirtualDoubleCategoryStruct`: identity multicells and
  substitution (`ccomp`): a multicell composes with a covering sequence of
  multicells, yielding a multicell over the concatenated domains.
* `CategoryTheory.VirtualDoubleCategory`: the axioms — substitution is
  associative and unital, stated in heterogeneous form because the tight
  boundaries of iterated substitutes agree only up to the category laws of
  the tight direction (the same phenomenon `Cell.cast` handles in
  `DoubleCat.Basic`, here absorbed by `HEq` since substitution also
  re-associates loose domain strings).
* `CategoryTheory.VirtualDoubleCategory.of_subsingleton`: a virtual double
  category structure whose multicells are proof-irrelevant satisfies the
  axioms outright.  All instances built in this development are of this
  thin kind, matching how `DoubleCat.Basic`'s pseudo double category
  axioms are discharged for the thin instances of the library.

## Design notes

Unlike a pseudo double category, a virtual double category has *no loose
composition* and hence no associator or unitor structure cells and no
coherence tower: the only operation is substitution of multicells into a
multicell, and the only laws are its associativity and unitality.  A
pseudo double category has an underlying virtual double category
(multicells `ps ⇒ q` are cells `fold ps ⟶ q` out of the loose composite;
see `DoubleCat.Virtual.OfPseudo`), and the virtual notion is strictly more
general: it also hosts structures whose would-be loose composite provably
forgets information, which is where multi-ary loose domains earn their
keep — a two-premise inference whose premise *pair* is strictly stronger
than any single composable summary is an ordinary multicell here, while in
a pseudo double category it must (unsoundly) factor through the composite.

Vertical (tight-wise) composition of cells is not separate data: pasting
`β : [q] ⇒ r` below `α : ps ⇒ q` is substitution of the singleton sequence
`[α]` into `β`.  Likewise, a "unit-topped" cell into `q` is simply a
multicell with the *empty* loose domain — virtual double categories do not
need chosen loose units for this purpose (units in the sense of
Cruttwell–Shulman §5 are extra structure, not required here; when loose
composites are freely added, the empty string becomes the loose unit — see
`DoubleCat.Virtual.FreePromotion`).

The associativity of substitution is stated against a *partitioned* inner
layer (`SeqUnder`, a covering-of-covering carrying its partition in its
type), so that both sides of the law are definable by structural
recursion with no splitting of sequences along concatenations; splitting
appears only propositionally, where the free promotion needs it
(`DoubleCat.Virtual.FreePromotion`).
-/

namespace CategoryTheory

universe w t v u

section LoosePath

variable {C : Type u}

/-- Finite composable strings over an arbitrary family of edges
`L : C → C → Type w`: the loose analogue of `Quiver.Path`, parametric in
the family rather than in a `Quiver` instance.  `LoosePath L a b` is the
type of strings of `L`-edges from `a` to `b`; the empty string exists at
every object, and `cons` extends a string on the left. -/
inductive LoosePath (L : C → C → Type w) : C → C → Type (max u w)
  /-- The empty string at an object. -/
  | nil {a : C} : LoosePath L a a
  /-- Prepend an edge to a string. -/
  | cons {a b c : C} (e : L a b) (p : LoosePath L b c) : LoosePath L a c

namespace LoosePath

variable {L : C → C → Type w}

/-- The singleton string. -/
abbrev single {a b : C} (e : L a b) : LoosePath L a b := .cons e .nil

/-- Concatenation of strings. -/
def comp : ∀ {a b c : C}, LoosePath L a b → LoosePath L b c → LoosePath L a c
  | _, _, _, .nil, q => q
  | _, _, _, .cons e p, q => .cons e (p.comp q)

@[simp] theorem nil_comp {a b : C} (p : LoosePath L a b) :
    LoosePath.comp .nil p = p := rfl

@[simp] theorem cons_comp {a b c d : C} (e : L a b) (p : LoosePath L b c)
    (q : LoosePath L c d) : (LoosePath.cons e p).comp q = .cons e (p.comp q) :=
  rfl

@[simp] theorem comp_nil : ∀ {a b : C} (p : LoosePath L a b),
    p.comp .nil = p
  | _, _, .nil => rfl
  | _, _, .cons e p => congrArg (LoosePath.cons e) (comp_nil p)

theorem comp_assoc : ∀ {a b c d : C} (p : LoosePath L a b)
    (q : LoosePath L b c) (r : LoosePath L c d),
    (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .cons e p, q, r => congrArg (LoosePath.cons e) (comp_assoc p q r)

universe w'' u''

/-- Map a string along a function of objects and a family map of edges. -/
def map {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) :
    ∀ {a b : C}, LoosePath L a b → LoosePath M (Fo a) (Fo b)
  | _, _, .nil => .nil
  | _, _, .cons e p => .cons (Fe e) (map Fo Fe p)

@[simp] theorem map_nil {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) {a : C} :
    (LoosePath.nil : LoosePath L a a).map Fo Fe = .nil := rfl

@[simp] theorem map_cons {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) {a b c : C} (e : L a b)
    (p : LoosePath L b c) :
    (LoosePath.cons e p).map Fo Fe = .cons (Fe e) (p.map Fo Fe) := rfl

theorem map_comp {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) :
    ∀ {a b c : C} (p : LoosePath L a b) (q : LoosePath L b c),
    (p.comp q).map Fo Fe = (p.map Fo Fe).comp (q.map Fo Fe)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons e p, q => congrArg (LoosePath.cons (Fe e)) (map_comp Fo Fe p q)

/-- Build a string from a list of loops at an object (constant-endpoint
edges).  Rule families whose premise strings arrive as a `List` enter
presentations through this builder. -/
def ofList {a : C} : List (L a a) → LoosePath L a a
  | [] => .nil
  | e :: es => .cons e (ofList es)

@[simp] theorem ofList_nil {a : C} :
    ofList ([] : List (L a a)) = .nil := rfl

@[simp] theorem ofList_cons {a : C} (e : L a a) (es : List (L a a)) :
    ofList (e :: es) = .cons e (ofList es) := rfl

/-- Build a string from a `Fin`-indexed family of loops at an object, by
direct recursion on the arity — deliberately not via `List.ofFn`, so
literal arities reduce definitionally (ground coverings over the builder
type-check by iota alone). -/
def ofFin {a : C} : ∀ {n : Nat}, (Fin n → L a a) → LoosePath L a a
  | 0, _ => .nil
  | _ + 1, f => .cons (f 0) (ofFin fun k => f k.succ)

@[simp] theorem ofFin_zero {a : C} (f : Fin 0 → L a a) :
    ofFin f = .nil := rfl

@[simp] theorem ofFin_succ {a : C} {n : Nat} (f : Fin (n + 1) → L a a) :
    ofFin f = .cons (f 0) (ofFin fun k => f k.succ) := rfl

/-- Mapping commutes with the list builder. -/
theorem map_ofList {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) {a : C} :
    ∀ (l : List (L a a)),
    (ofList l).map Fo Fe = ofList (l.map fun e => Fe e)
  | [] => rfl
  | e :: es => congrArg (LoosePath.cons (Fe e)) (map_ofList Fo Fe es)

/-- Mapping commutes with the family builder. -/
theorem map_ofFin {D : Type u''} {M : D → D → Type w''} (Fo : C → D)
    (Fe : ∀ {a b : C}, L a b → M (Fo a) (Fo b)) {a : C} :
    ∀ {n : Nat} (f : Fin n → L a a),
    (ofFin f).map Fo Fe = ofFin fun k => Fe (f k)
  | 0, _ => rfl
  | _ + 1, f =>
      congrArg (LoosePath.cons (Fe (f 0))) (map_ofFin Fo Fe fun k => f k.succ)

end LoosePath

end LoosePath

set_option linter.checkUnivs false in
/-- The data of loose arrows and multicells on a category `C`.

The morphisms of `C` are the *tight* arrows.  `Loose a b` is the type of
loose arrows from `a` to `b`, and `Cell ps q f g` is the type of multicells
with loose domain the composable string `ps : LoosePath Loose a b`, loose
codomain the single loose arrow `q : Loose c d`, tight source side
`f : a ⟶ c` and tight target side `g : b ⟶ d`:

```
        p₁      p₂            pₙ
    a = x₀ --↛ x₁ --↛ ⋯ --↛ xₙ = b
    |                            |
  f |             α              | g
    v                            v
    c --------------↛------------ d
                    q
```

The loose domain may be empty (`ps = .nil`, forcing `a = b`): nullary
multicells are how theorems with no loose premises enter a virtual double
category, with no loose unit arrow required. -/
class VirtualDoubleCategoryData.{w', t', v', u'} (C : Type u')
    [Category.{v'} C] where
  /-- Loose arrows from `a` to `b`. -/
  Loose : C → C → Type w'
  /-- Multicells: loose domain a composable string, loose codomain a single
  loose arrow, tight sides `f` and `g`. -/
  Cell : ∀ {a b c d : C}, LoosePath Loose a b → Loose c d →
    (a ⟶ c) → (b ⟶ d) → Type t'

namespace VirtualDoubleCategoryData

variable {C : Type u} [Category.{v} C] [VirtualDoubleCategoryData.{w, t, v, u} C]

/-- Transport a multicell along an equality of its loose domain strings.
Substitution concatenates domain strings, and concatenation is associative
and unital only propositionally, so iterated substitutes inhabit types
that agree up to this transport (the loose-direction analogue of
`PseudoDoubleCategoryStruct.Cell.cast`). -/
def Cell.castDom {a b c d : C} {ps ps' : LoosePath Loose a b} {q : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (hp : ps = ps') (α : Cell ps q f g) :
    Cell ps' q f g :=
  hp ▸ α

@[simp] theorem Cell.castDom_rfl {a b c d : C} {ps : LoosePath Loose a b}
    {q : Loose c d} {f : a ⟶ c} {g : b ⟶ d} (α : Cell ps q f g) :
    α.castDom rfl = α := rfl

theorem Cell.castDom_heq {a b c d : C} {ps ps' : LoosePath Loose a b}
    {q : Loose c d} {f : a ⟶ c} {g : b ⟶ d} (hp : ps = ps')
    (α : Cell ps q f g) : α.castDom hp ≍ α := by
  subst hp; rfl

set_option linter.checkUnivs false in
/-- A composable sequence of multicells covering a string: the shape along
which a multicell is substituted.  `CellSeq qs ps u v` covers the string
`qs` (one multicell per edge of `qs`, in order), with the concatenation of
the multicells' loose domains equal to `ps`, outer tight boundaries `u`
and `v`, and consecutive multicells sharing their boundary tight arrow:

```
        ps₁           ps₂                 psₙ
    a = ⋯ --↛ ⋯   ⋯ --↛ ⋯     ⋯       ⋯ --↛ ⋯ = b
    |         |         |         |         |
  u |    β₁   | w₁  β₂  | w₂  ⋯   | wₙ₋₁ βₙ | v
    v         v         v         v         v
    c ---↛--- x₁ --↛--- x₂ - ⋯ - xₙ₋₁ --↛-- d
        q₁        q₂         ⋯        qₙ
```
-/
inductive CellSeq :
    ∀ {a b c d : C}, LoosePath Loose c d → LoosePath Loose a b →
      (a ⟶ c) → (b ⟶ d) → Type (max u v w t)
  /-- The empty sequence over the empty string, at a tight arrow. -/
  | nil {a c : C} (f : a ⟶ c) : CellSeq .nil .nil f f
  /-- Prepend a multicell to a sequence, sharing the boundary tight
  arrow `w`. -/
  | cons {a a₁ b c c₁ d : C} {ps₁ : LoosePath Loose a a₁} {q : Loose c c₁}
      {u : a ⟶ c} {w : a₁ ⟶ c₁} {qs : LoosePath Loose c₁ d}
      {rs : LoosePath Loose a₁ b} {v : b ⟶ d}
      (β : Cell ps₁ q u w) (V : CellSeq qs rs w v) :
      CellSeq (.cons q qs) (ps₁.comp rs) u v

namespace CellSeq

/-- Transport a sequence along an equality of its domain strings. -/
def castDom {a b c d : C} {qs : LoosePath Loose c d}
    {ps ps' : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    (hp : ps = ps') (V : CellSeq qs ps u v) : CellSeq qs ps' u v :=
  hp ▸ V

theorem castDom_heq {a b c d : C} {qs : LoosePath Loose c d}
    {ps ps' : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    (hp : ps = ps') (V : CellSeq qs ps u v) : V.castDom hp ≍ V := by
  subst hp; rfl

/-- Transport a sequence along an equality of its covered strings. -/
def castCod {a b c d : C} {qs qs' : LoosePath Loose c d}
    {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    (hq : qs = qs') (V : CellSeq qs ps u v) : CellSeq qs' ps u v :=
  hq ▸ V

theorem castCod_heq {a b c d : C} {qs qs' : LoosePath Loose c d}
    {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    (hq : qs = qs') (V : CellSeq qs ps u v) : V.castCod hq ≍ V := by
  subst hq; rfl

/-- Concatenation of covering sequences (sharing the boundary tight
arrow).  The domain string of the result is the concatenation of the
domain strings, transported along associativity of `LoosePath.comp`. -/
def append : ∀ {a b b' c d d' : C} {qs₁ : LoosePath Loose c d}
    {ps₁ : LoosePath Loose a b} {u : a ⟶ c} {w : b ⟶ d}
    {qs₂ : LoosePath Loose d d'} {ps₂ : LoosePath Loose b b'} {v : b' ⟶ d'},
    CellSeq qs₁ ps₁ u w → CellSeq qs₂ ps₂ w v →
    CellSeq (qs₁.comp qs₂) (ps₁.comp ps₂) u v
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .nil _, W => W
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .cons β V, W =>
      (CellSeq.cons β (V.append W)).castDom (LoosePath.comp_assoc _ _ _).symm

end CellSeq

end VirtualDoubleCategoryData

set_option linter.checkUnivs false in
/-- A virtual double category structure on a category `C`: loose arrows,
multicells, identity multicells, and substitution.

This carries all data but no axioms; the axioms are in
`CategoryTheory.VirtualDoubleCategory`. -/
class VirtualDoubleCategoryStruct.{w', t', v', u'} (C : Type u')
    [Category.{v'} C] extends VirtualDoubleCategoryData.{w', t', v', u'} C where
  /-- The identity multicell on a loose arrow: a unary multicell with
  identity tight sides. -/
  cid : ∀ {a b : C} (q : Loose a b), Cell (.single q) q (𝟙 a) (𝟙 b)
  /-- Substitution: a multicell out of the string `qs` composes with a
  sequence of multicells covering `qs`, yielding a multicell out of the
  concatenated domains. -/
  ccomp : ∀ {a b c d e e' : C} {qs : LoosePath Loose c d} {s : Loose e e'}
    {f : c ⟶ e} {g : d ⟶ e'} {ps : LoosePath Loose a b} {u : a ⟶ c}
    {v : b ⟶ d},
    Cell qs s f g → VirtualDoubleCategoryData.CellSeq qs ps u v →
      Cell ps s (u ≫ f) (v ≫ g)

namespace VirtualDoubleCategoryStruct

open VirtualDoubleCategoryData

variable {C : Type u} [Category.{v} C] [VirtualDoubleCategoryStruct.{w, t, v, u} C]

/-- The identity covering sequence on a string: one identity multicell per
edge.  Its domain string is the string itself, definitionally. -/
def idSeq : ∀ {a b : C} (qs : LoosePath Loose a b),
    CellSeq qs qs (𝟙 a) (𝟙 b)
  | _, _, .nil => .nil (𝟙 _)
  | _, _, .cons q qs => .cons (cid q) (idSeq qs)

/-- The singleton covering sequence on a multicell.  Its domain string is
`ps.comp .nil`, which is the price of the left-biased string encoding; the
unit law `VirtualDoubleCategory.cid_ccomp` is stated heterogeneously for
exactly this reason. -/
def CellSeq.singleton {a b c d : C} {ps : LoosePath Loose a b}
    {q : Loose c d} {u : a ⟶ c} {v : b ⟶ d} (α : Cell ps q u v) :
    CellSeq (.single q) (ps.comp .nil) u v :=
  .cons α (.nil v)

set_option linter.checkUnivs false in
/-- A covering of a covering, block by block: for each multicell of `V`, a
covering sequence of its loose domain, with consecutive blocks sharing
their boundary tight arrow.  This is the shape of the inner layer in the
associativity of substitution, carrying its partition in its type. -/
inductive SeqUnder :
    ∀ {a b c d : C} {qs : LoosePath Loose c d} {ps : LoosePath Loose a b}
      {u : a ⟶ c} {v : b ⟶ d}, CellSeq qs ps u v →
      ∀ {a' b' : C}, LoosePath Loose a' b' → (a' ⟶ a) → (b' ⟶ b) →
        Type (max u v w t)
  /-- Under the empty sequence: the empty covering, at a tight arrow. -/
  | nil {a c : C} (f : a ⟶ c) {a' : C} (s : a' ⟶ a) :
      SeqUnder (.nil f) .nil s s
  /-- Under a `cons`: a covering sequence for the head multicell's domain,
  and a covering-of-covering for the tail, sharing the boundary tight
  arrow `w'`.  The head multicell `β` and the tail sequence `V` are
  explicit fields: a covering-of-covering names the layer it covers. -/
  | cons {a a₁ b c c₁ d : C} {ps₁ : LoosePath Loose a a₁} {q : Loose c c₁}
      {u : a ⟶ c} {w : a₁ ⟶ c₁} {qs : LoosePath Loose c₁ d}
      {rs : LoosePath Loose a₁ b} {v : b ⟶ d}
      (β : Cell ps₁ q u w) (V : CellSeq qs rs w v)
      {a' m b' : C} {os₁ : LoosePath Loose a' m} {s : a' ⟶ a} {w' : m ⟶ a₁}
      {os₂ : LoosePath Loose m b'} {t' : b' ⟶ b}
      (W₁ : CellSeq ps₁ os₁ s w') (W : SeqUnder V os₂ w' t') :
      SeqUnder (.cons β V) (os₁.comp os₂) s t'

namespace SeqUnder

/-- Flatten a covering-of-covering into a single covering sequence of the
inner domain string, forgetting the partition. -/
def flatten : ∀ {a b c d : C} {qs : LoosePath Loose c d}
    {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq qs ps u v} {a' b' : C} {os : LoosePath Loose a' b'}
    {s : a' ⟶ a} {t' : b' ⟶ b}, SeqUnder V os s t' → CellSeq ps os s t'
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil _ s => .nil s
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons _ _ W₁ W =>
      W₁.append W.flatten

end SeqUnder

/-- Substitute a covering-of-covering into a covering sequence, block by
block: each multicell of `V` composes with its block of `W`.  (The match
is on the covering-of-covering alone: its constructors force the shape of
`V` through their indices, and the blocks `β`, `V` are recovered from the
constructor's own telescope.) -/
def compUnder : ∀ {a b c d : C} {qs : LoosePath Loose c d}
    {ps : LoosePath Loose a b} {u : a ⟶ c} {v : b ⟶ d}
    {V : CellSeq qs ps u v} {a' b' : C} {os : LoosePath Loose a' b'}
    {s : a' ⟶ a} {t' : b' ⟶ b}, SeqUnder V os s t' →
    CellSeq qs os (s ≫ u) (t' ≫ v)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil f s => .nil (s ≫ f)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons β _ W₁ W =>
      .cons (ccomp β W₁) (compUnder W)

end VirtualDoubleCategoryStruct

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

/-- A virtual double category: substitution of multicells is associative
and unital (Cruttwell–Shulman, Definition 2.1).

The laws are stated heterogeneously: the two sides of each law inhabit
multicell types whose loose domain strings agree only up to the monoid
laws of `LoosePath.comp` and whose tight boundaries agree only up to the
category laws of the tight direction, so the appropriate equality is
`HEq`, exactly as the cast calculus of `DoubleCat.Basic` handles the
tight-boundary drift of iterated pseudo-double-category composites. -/
class VirtualDoubleCategory (C : Type u) [Category.{v} C]
    [VirtualDoubleCategoryStruct.{w, t, v, u} C] : Prop where

  /-- Substituting the identity covering sequence is the identity. -/
  ccomp_idSeq : ∀ {c d e e' : C} {qs : LoosePath Loose c d} {s : Loose e e'}
    {f : c ⟶ e} {g : d ⟶ e'} (α : Cell qs s f g),
    ccomp α (idSeq qs) ≍ α

  /-- Substituting a singleton covering into an identity multicell is the
  identity. -/
  cid_ccomp : ∀ {a b c d : C} {ps : LoosePath Loose a b} {q : Loose c d}
    {u : a ⟶ c} {v : b ⟶ d} (α : Cell ps q u v),
    ccomp (cid q) (CellSeq.singleton α) ≍ α

  /-- Associativity of substitution: substituting a flattened
  covering-of-covering into a composite is substituting the blockwise
  composite. -/
  ccomp_assoc : ∀ {a b c d e e' a' b' : C} {qs : LoosePath Loose c d}
    {s : Loose e e'} {f : c ⟶ e} {g : d ⟶ e'} {ps : LoosePath Loose a b}
    {u : a ⟶ c} {v : b ⟶ d} (α : Cell qs s f g) (V : CellSeq qs ps u v)
    {os : LoosePath Loose a' b'} {s' : a' ⟶ a} {t' : b' ⟶ b}
    (W : SeqUnder V os s' t'),
    ccomp (ccomp α V) W.flatten ≍ ccomp α (compUnder W)

namespace VirtualDoubleCategory

open VirtualDoubleCategoryStruct

variable {C : Type u} [Category.{v} C] [VirtualDoubleCategoryStruct.{w, t, v, u} C]

/-- Multicells with propositionally equal boundaries are heterogeneously
equal as soon as multicells are proof-irrelevant. -/
theorem heq_of_subsingleton
    (h : ∀ {a b c d : C} (ps : LoosePath Loose a b) (q : Loose c d)
      (f : a ⟶ c) (g : b ⟶ d), Subsingleton (Cell ps q f g))
    {a b c d : C} {ps ps' : LoosePath Loose a b} {q : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hp : ps = ps') (hf : f = f')
    (hg : g = g') (α : Cell ps q f g) (α' : Cell ps' q f' g') : α ≍ α' := by
  subst hp; subst hf; subst hg
  exact heq_of_eq (@Subsingleton.elim _ (h ps q f g) α α')

/-- A virtual double category structure with proof-irrelevant multicells
satisfies the axioms outright: every law equates multicells whose
boundaries agree up to the monoid laws of strings and the category laws
of tight arrows.  This is the virtual counterpart of discharging the
pseudo double category axioms by `Subsingleton.elim` for thin instances. -/
theorem of_subsingleton
    (h : ∀ {a b c d : C} (ps : LoosePath Loose a b) (q : Loose c d)
      (f : a ⟶ c) (g : b ⟶ d), Subsingleton (Cell ps q f g)) :
    VirtualDoubleCategory C where
  ccomp_idSeq := fun α => heq_of_subsingleton h rfl (Category.id_comp _)
    (Category.id_comp _) _ α
  cid_ccomp := fun α => heq_of_subsingleton h (LoosePath.comp_nil _)
    (Category.comp_id _) (Category.comp_id _) _ α
  ccomp_assoc := by
    intros
    exact heq_of_subsingleton h rfl
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _ _

end VirtualDoubleCategory

end CategoryTheory
