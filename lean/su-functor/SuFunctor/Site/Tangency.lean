import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Tangency structure — the (T4) clause, reified

The semantic-universe chapter's structured-site definition carries, at
clause (T4), a **tangency** in the sense of Capucci–Myers (arXiv
2604.03017, following Libkind–Myers' *Double Operadic Theory of
Systems*, Def. 7.1; called a "doctrine of dynamical systems" in Jaz
Myers 2021): a triple `(𝒷, π : ℰ → 𝒷, T)` — a category of state (and
observation) spaces, a cloven Grothendieck fibration of *action
bundles* over it, and a section `T` assigning to each state space `S`
its bundle `(T_s S)_{s : S}` of *admissible changes*.  A *dynamics over
the tangency* is a map INTO the bundle the tangency selects:
`u : (s, a) ↦ u(s, a) ∈ T_s S` — in fibrational terms, a vertical
morphism from a parameter bundle into the section's value (the `u`-leg
of Capucci–Myers' generalized Moore machine).

**Presentation.**  The fibration is carried by its cleavage: a
pseudofunctor `F : LocallyDiscrete 𝒷ᵒᵖ ⥤ᵖ Cat`, whose CoGrothendieck
total `∫ᶜ F` and projection `forget F` are mathlib's, together with
mathlib's proof that the projection is a fibered category
(`Pseudofunctor.CoGrothendieck.instIsFibered…`, the Vistoli-standard
direction of the cleavage ↔ fibration correspondence; the converse
direction — presenting an abstract fibration-with-chosen-lifts by its
cleavage — is cited, not mechanized).  The section is carried as
strict-section *data* (`bundle` on objects, vertical `transport` on
morphisms, functoriality up to the cleavage's structure 2-cells), from
which the literal Capucci–Myers statement — a functor `𝒷 ⥤ ∫ᶜ F` with
`⋙ forget F = 𝟭 𝒷` on the nose — is derived
(`Tangency.sectionFunctor`, `Tangency.sectionFunctor_forget`).

**Design position (choice-free tangency; open).**  Fibres carry what
one RESOLVED step can do.  Nondeterminism is *not* built into this
structure: it enters through a dynamics' parameter axis and denotes by
quantification over the admitted family at the denotation stratum
(the landed evidence: `MdpDemonic` quantifies policies,
`StochasticPetriDemonic` schedulers — both denotation-side).  The
structure itself is agnostic — any pseudofunctor-with-section
instantiates it, so a powerset tangency EXISTS the moment the
structure does (Capucci–Myers admit `T_s S := 𝒫 S` as a peer instance,
their §2); choice-freeness is a POLICY about which instances feed the
certification interface, enforceable at the catalogue level, not the
type level.  See `SuFunctor.Site.TangencyFam` for the powerset
instance presented as a curried encoding with the selection seam
named; whether the catalogue-level policy narrows the peer-primitive
reading is a deliberately open design fork.

Successors (named, not smuggled): the monoidal tangency structure
(CM §2.1, feeds wiring/composition); parameterized induced actions;
the 2-category of tangencies; consumption of (T4) by the
structured-site definition.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

universe w₂ v₂ u₂ v₁ u₁

variable (B : Type u₁) [Category.{v₁} B]

set_option linter.checkUnivs false in
/-- **A tangency** (Capucci–Myers; Libkind–Myers Def. 7.1): a cloven
Grothendieck fibration of action bundles over the category `B` of
state spaces — carried by its cleavage `F`, with total `∫ᶜ F`,
projection `forget F`, and mathlib's `IsFibered` instance — together
with a strict section assigning to each state space its bundle of
admissible changes.  The section is carried as data (`bundle`,
`transport`, functoriality); the section *functor* and its strict
sectionhood are derived below. -/
structure Tangency where
  /-- The cleavage: the indexed category of action bundles.  Fibres
  `F.obj ⟨op S⟩` are categories of bundles over `S`; reindexing along
  `f : S ⟶ S'` is `F.map f.op.toLoc`. -/
  F : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{v₂, u₂}
  /-- The section on objects: each state space's bundle of admissible
  changes, `(T_s S)_{s : S}`. -/
  bundle : ∀ b : B, F.obj ⟨op b⟩
  /-- The section on morphisms: the vertical transport of admissible
  changes into the pullback bundle — for the tangent-bundle tangency
  this is the (first-order) differential of `f`. -/
  transport : ∀ {a b : B} (f : a ⟶ b),
    bundle a ⟶ (F.map f.op.toLoc).toFunctor.obj (bundle b)
  /-- Functoriality at identities, against the cleavage's unit
  2-cell.  (This is exactly the `id.fiber` of `∫ᶜ F`.) -/
  transport_id : ∀ b : B,
    transport (𝟙 b) = (F.mapId ⟨op b⟩).inv.toNatTrans.app (bundle b)
  /-- Functoriality at composites, against the cleavage's composition
  2-cell.  (This is exactly the `comp.fiber` of `∫ᶜ F`.) -/
  transport_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    transport (f ≫ g)
      = transport f ≫ (F.map f.op.toLoc).toFunctor.map (transport g) ≫
          (F.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app (bundle c)

namespace Tangency

variable {B} (𝒯 : Tangency B)

/-- **A dynamics over the tangency**, on state space `b` with
parameter/input bundle `A`: a vertical morphism into the bundle the
tangency selects — the chapter's `u : (s, a) ↦ u(s, a) ∈ T_s S`, and
the `u`-leg of Capucci–Myers' generalized Moore machine.  (Closed
dynamics — `A` the unit bundle — are defined per-instance, where the
fibre category has one; induced actions on observables are
doctrine-specific and live with the instances.) -/
def Dynamics {b : B} (A : 𝒯.F.obj ⟨op b⟩) : Type _ :=
  A ⟶ 𝒯.bundle b

/-- The section, as a functor into the total category of the
fibration: `S ↦ (S, T S)`, `f ↦ (f, transport f)`. -/
def sectionFunctor : B ⥤ ∫ᶜ 𝒯.F where
  obj b := ⟨b, 𝒯.bundle b⟩
  map f := ⟨f, 𝒯.transport f⟩
  map_id b := by
    apply CoGrothendieck.Hom.ext <;> simp <;> exact 𝒯.transport_id b
  map_comp f g := by
    apply CoGrothendieck.Hom.ext <;> simp <;> exact 𝒯.transport_comp f g

/-- **Strict sectionhood**, on the nose: the section functor followed
by the fibration's projection is the identity of the base — the
literal Capucci–Myers clause "a section `T : 𝒷 → ℰ` of `π`". -/
theorem sectionFunctor_forget :
    𝒯.sectionFunctor ⋙ CoGrothendieck.forget 𝒯.F = 𝟭 B :=
  rfl

/-- The fibration stamp: the projection of the tangency's total
category is a fibered category — mathlib's instance for the
CoGrothendieck construction, consumed whole ("cloven Grothendieck
fibration", kernel-checked). -/
example : (CoGrothendieck.forget 𝒯.F).IsFibered := inferInstance

end Tangency

/-! ## Strict-cleavage plumbing

Every shipped instance presents its cleavage as a strict functor
`G : Bᵒᵖ ⥤ Cat` promoted along `Functor.toPseudofunctor'` (whose
`mapId`/`mapComp` are `eqToIso`s).  The two lemmas below reduce the
structure 2-cells' components to `eqToHom`s once, so each instance's
`transport_id`/`transport_comp` obligations reduce to their honest
mathematical content. -/

section StrictPlumbing

variable {B} (G : Bᵒᵖ ⥤ Cat.{v₂, u₂})

theorem strictMapId_inv_app (b : Bᵒᵖ) (x : G.obj b)
    (h : (G.toPseudofunctor'.map
        (𝟙 (⟨b⟩ : LocallyDiscrete Bᵒᵖ))).toFunctor.obj x = x) :
    (G.toPseudofunctor'.mapId ⟨b⟩).inv.toNatTrans.app x = eqToHom h.symm := by
  simp only [Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
  rfl

theorem strictMapComp_inv_app {a b c : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (x : G.obj a)
    (h : (G.toPseudofunctor'.map (f.toLoc ≫ g.toLoc)).toFunctor.obj x
        = (G.toPseudofunctor'.map g.toLoc).toFunctor.obj
            ((G.toPseudofunctor'.map f.toLoc).toFunctor.obj x)) :
    (G.toPseudofunctor'.mapComp f.toLoc g.toLoc).inv.toNatTrans.app x
      = eqToHom h.symm := by
  simp only [Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
  rfl

end StrictPlumbing

end

end Site

end SuFunctor
