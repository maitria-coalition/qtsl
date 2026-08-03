import DoubleCat.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# The wiring base, in state-family presentation

This file equips interfaces-and-wirings with a pseudo double category
structure, presented at the level the decoration tier consumes: objects
are interfaces (wire sets over a fixed state type `El`), tight arrows are
wire maps, loose arrows are wiring patterns presented by the *state-space
families* they induce, and cells act on apex states contravariantly.

The presentation is chosen so that every strictness claim of the
dependent-span double category transfers: where the cospan base composes
patterns by a pushout of wire sets — associative only up to canonical
isomorphism of iterated quotients — the state functor carries that pushout
to the *agreement subspace* of a product, i.e. to the `Σ`-pullback of the
state families, and `Σ`/`×` enjoy definitional eta.  Concretely: a wiring
pattern `I → A ← J` is recorded as the family sending boundary states
`(x, y)` to the type of apex states restricting to `x` and `y`; loose
composition is then matrix multiplication with `Σ` as sum and `×` as
product, exactly as in `DoubleCat.DepSpan`, and the coherence laws hold by
`rfl` after destructuring.

The one genuine difference from `DepSpan` is the *variance of cells*: a
map of wiring patterns pushes apex wires forward, so it pulls apex states
back — a cell from `M` to `N` over wire maps `(φ, ψ)` sends `N`-apex
states to `M`-apex states over the boundary restrictions.  Tight-wise
composition of cells therefore composes the transports in the reversed
order, and the associator/unitor cells of this base are the *constructor*
directions of `DepSpan`'s (their inverses are the `match` directions).
This transposition is what lets decorations whose transport is
contravariant in apex states (penalty functionals pull back along
pushforward of joints) be *covariantly* indexed by the base, in the strict
covariant form of the double Grothendieck construction
(`DoubleCat.Grothendieck`).

The stratum is deliberately untyped (a single state type `El`): the typed
wire category is the slice over a set of wire types, and the injective
sub-base restricts the tight direction — neither refinement is consumed by
any construction on this base, so both are left to instantiation, matching
the design split of the semantic-universe chapter (nothing in the
decoration functor consumes the cocartesian universal property of tights).

## Main definitions

* `CategoryTheory.WireSpan`: interfaces over `El`, with wire maps as the
  tight category.
* `CategoryTheory.WireSpan.Pat`: wiring patterns as state families, the
  loose arrows; `Pat.Tot` is the apex state space.
* `CategoryTheory.WireSpan.PatCell`: transposed fibrewise maps, the cells;
  `PatCell.tot` is the induced (backward) map of apex state spaces.
* `CategoryTheory.WireSpan.instPseudoDoubleCategory`: the axioms.
* The `Tot`-calculus (`tot_vId`, `tot_vComp`, `compFst_tot_hComp`, …):
  the transport identities a decoration tier consumes, each definitional.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe u

/-- An interface over a fixed state type: a type of wires.  (The untyped
stratum: every wire carries states from one type `El`; the typed wire
category is the slice construction over a set of wire types and is not
needed by anything on this base.) -/
structure WireSpan (El : Type u) : Type (u + 1) where
  /-- The wires of the interface. -/
  wires : Type u

namespace WireSpan

variable {El : Type u}

/-- Tight arrows are wire maps.  Composition is composition of functions,
so the category laws are definitional. -/
instance : Category.{u} (WireSpan El) where
  Hom A B := A.wires → B.wires
  id _ := fun w => w
  comp f g := fun w => g (f w)

/-- The state space of an interface: assignments of a state to each
wire. -/
abbrev states (A : WireSpan El) : Type u := A.wires → El

/-- Restriction of states along a wire map (contravariant, and
definitionally functorial). -/
abbrev res {A B : WireSpan El} (φ : A ⟶ B) : states B → states A :=
  fun y w => y (φ w)

@[simp] theorem res_id {A : WireSpan El} : res (𝟙 A) = id := rfl

theorem res_comp {A B C : WireSpan El} (φ : A ⟶ B) (ψ : B ⟶ C) :
    res (φ ≫ ψ) = res φ ∘ res ψ := rfl

/-- A wiring pattern from `A` to `B`, presented by its state family: the
type of apex states over each pair of boundary states.  (For a cospan
`A → C ← B` of wire sets this is the family of apex states restricting to
the given boundary states; all identification of wires lives in the apex,
never in the tight direction.) -/
abbrev Pat (A B : WireSpan El) : Type (u + 1) :=
  states A → states B → Type u

namespace Pat

/-- The identity pattern: the diagonal family (the pattern that wires an
interface straight through to itself). -/
@[reducible] def id (A : WireSpan El) : Pat A A :=
  fun x y => ULift (PLift (x = y))

/-- Composition of patterns: gluing along the shared boundary.  The state
space of a glued apex is the agreement subspace, i.e. the `Σ`-pullback of
the two families. -/
@[reducible] def comp {A B C : WireSpan El} (M : Pat A B) (N : Pat B C) :
    Pat A C :=
  fun x z => Σ y : states B, M x y × N y z

/-- The apex state space of a pattern: all apex states, fibred over their
boundary restrictions. -/
@[reducible] def Tot {A B : WireSpan El} (M : Pat A B) : Type u :=
  Σ (x : states A) (y : states B), M x y

/-- The first joint-to-component projection of a glued apex. -/
@[reducible] def compFst {A B C : WireSpan El} (M : Pat A B) (N : Pat B C) :
    Tot (comp M N) → Tot M :=
  fun t => ⟨t.1, t.2.2.1, t.2.2.2.1⟩

/-- The second joint-to-component projection of a glued apex. -/
@[reducible] def compSnd {A B C : WireSpan El} (M : Pat A B) (N : Pat B C) :
    Tot (comp M N) → Tot N :=
  fun t => ⟨t.2.2.1, t.2.1, t.2.2.2.2⟩

end Pat

/-- A cell between patterns over wire maps `(φ, ψ)`: a map of apex states,
*backward* — a map of wiring patterns pushes apex wires forward, hence
pulls apex states back over the boundary restrictions. -/
abbrev PatCell {A B A' B' : WireSpan El} (M : Pat A B) (N : Pat A' B')
    (φ : A ⟶ A') (ψ : B ⟶ B') : Type u :=
  ∀ x y, N x y → M (res φ x) (res ψ y)

namespace PatCell

/-- The action of a cell on apex state spaces (backward). -/
@[reducible] def tot {A B A' B' : WireSpan El} {M : Pat A B} {N : Pat A' B'}
    {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ) : Pat.Tot N → Pat.Tot M :=
  fun t => ⟨res φ t.1, res ψ t.2.1, γ t.1 t.2.1 t.2.2⟩

end PatCell

/-- The pseudo double category of interfaces and wiring patterns: loose
composition is gluing (`Σ`-pullback of state families); cells transport
apex states backward, so tight-wise composition of cells composes the
transports in reversed order. -/
instance instPseudoDoubleCategoryStruct :
    PseudoDoubleCategoryStruct (WireSpan El) where
  Loose A B := Pat A B
  Cell M N φ ψ := PatCell M N φ ψ
  vId _ := fun _ _ s => s
  vComp α β := fun _ _ s => α _ _ (β _ _ s)
  lId A := Pat.id A
  lComp M N := Pat.comp M N
  hId φ := fun _ _ e => ⟨⟨congrArg (res φ) e.down.down⟩⟩
  hComp α β := fun _ _ s => ⟨_, α _ _ s.2.1, β _ _ s.2.2⟩
  lAssoc _ _ _ := fun _ _ s =>
    ⟨s.2.2.1, ⟨s.1, s.2.1, s.2.2.2.1⟩, s.2.2.2.2⟩
  lAssocInv _ _ _ := fun _ _ s =>
    ⟨s.2.1.1, s.2.1.2.1, s.1, s.2.1.2.2, s.2.2⟩
  lLeftUnitor _ := fun _ _ s => ⟨_, ⟨⟨rfl⟩⟩, s⟩
  lLeftUnitorInv _ := fun _ _ s =>
    match s with | ⟨_, ⟨⟨rfl⟩⟩, m⟩ => m
  lRightUnitor _ := fun _ _ s => ⟨_, s, ⟨⟨rfl⟩⟩⟩
  lRightUnitorInv _ := fun _ _ s =>
    match s with | ⟨_, m, ⟨⟨rfl⟩⟩⟩ => m

@[simp] theorem lId_def (A : WireSpan El) : 𝟙ˡ A = Pat.id A := rfl

@[simp] theorem lComp_def {A B C : WireSpan El} (M : Loose A B)
    (N : Loose B C) : M ⊙ N = Pat.comp M N := rfl

/-- The axioms hold, mostly by `rfl` after destructuring: the wire
category's laws are definitional, so all boundary casts vanish, and the
structure cells in the constructor direction reduce on opaque elements.
(Relative to `DepSpan`, the `match`-blocked cases are the unitor
*inverses*, since the cell variance is transposed.) -/
instance instPseudoDoubleCategory : PseudoDoubleCategory (WireSpan El) where
  vId_vComp _ := rfl
  vComp_vId _ := rfl
  vComp_assoc _ _ _ := rfl
  hId_id _ := rfl
  hId_comp _ _ := rfl
  hComp_vId _ _ := rfl
  interchange _ _ _ _ := rfl
  lAssoc_natural _ _ _ := rfl
  lLeftUnitor_natural _ := rfl
  lRightUnitor_natural _ := rfl
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
    obtain ⟨y, mm, nn⟩ := s
    rfl

/-! ## The `Tot`-calculus

The transport identities a decoration tier consumes.  Each is
definitional: the whole point of the state-family presentation is that
the comparison maps between iterated glued apexes are `Σ`-reshuffles, and
`Σ`/`×` eta makes those reshuffles invisible to any functional that reads
apex states only through the projections. -/

section TotCalculus

variable {A B C D A' B' C' : WireSpan El}

/-- The identity cell transports apex states by the identity. -/
theorem tot_vId (M : Pat A B) :
    PatCell.tot (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M) =
      id := rfl

/-- Tight-wise composition of cells transports apex states by the
reversed composite. -/
theorem tot_vComp {M₁ : Pat A B} {M₂ : Pat A' B'} {M₃ : Pat C D}
    {f₁ : A ⟶ A'} {g₁ : B ⟶ B'} {f₂ : A' ⟶ C} {g₂ : B' ⟶ D}
    (α : PatCell M₁ M₂ f₁ g₁) (β : PatCell M₂ M₃ f₂ g₂) :
    PatCell.tot
        (PseudoDoubleCategoryStruct.vComp (C := WireSpan El) α β) =
      PatCell.tot α ∘ PatCell.tot β := rfl

/-- The first projection intertwines a loose-wise composite cell with its
left factor. -/
theorem compFst_tot_hComp {M₁ : Pat A B} {M₂ : Pat B C} {N₁ : Pat A' B'}
    {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ) :
    Pat.compFst M₁ M₂ ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β) =
      PatCell.tot α ∘ Pat.compFst N₁ N₂ := rfl

/-- The second projection intertwines a loose-wise composite cell with its
right factor. -/
theorem compSnd_tot_hComp {M₁ : Pat A B} {M₂ : Pat B C} {N₁ : Pat A' B'}
    {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ) :
    Pat.compSnd M₁ M₂ ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β) =
      PatCell.tot β ∘ Pat.compSnd N₁ N₂ := rfl

/-- Reassociation of a glued apex is invisible to the left component:
the two routes to the leftmost factor agree definitionally. -/
theorem compFst_compFst_tot_lAssoc (M : Pat A B) (N : Pat B C)
    (P : Pat C D) :
    Pat.compFst M N ∘ Pat.compFst (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P) =
      Pat.compFst M (N.comp P) := rfl

/-- Reassociation, middle factor. -/
theorem compSnd_compFst_tot_lAssoc (M : Pat A B) (N : Pat B C)
    (P : Pat C D) :
    Pat.compSnd M N ∘ Pat.compFst (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P) =
      Pat.compFst N P ∘ Pat.compSnd M (N.comp P) := rfl

/-- Reassociation, right factor. -/
theorem compSnd_tot_lAssoc (M : Pat A B) (N : Pat B C) (P : Pat C D) :
    Pat.compSnd (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P) =
      Pat.compSnd N P ∘ Pat.compSnd M (N.comp P) := rfl

/-- Stripping the unit pattern on the left is invisible to the content:
the second projection composed with the left-unitor transport is the
identity of the apex state space. -/
theorem compSnd_tot_lLeftUnitor (M : Pat A B) :
    Pat.compSnd (Pat.id A) M ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M) =
      id := rfl

/-- Stripping the unit pattern on the right, dually. -/
theorem compFst_tot_lRightUnitor (M : Pat A B) :
    Pat.compFst M (Pat.id B) ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M) =
      id := rfl

end TotCalculus

end WireSpan

end CategoryTheory
