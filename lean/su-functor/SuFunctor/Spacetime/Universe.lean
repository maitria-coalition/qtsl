import SuFunctor.Spacetime.Base
import SuFunctor.SingleSiteSemanticUniverse
import SuFunctor.Universe.DemonicClock
import DoubleCat.Functor.Composition
import DoubleCat.Opfibration

/-! # The semantic universe: the iterated double Grothendieck total

Systems/Specs over interfaces over sites.  The profiled wiring base
(`SuFunctor.Spacetime.Base`) carries the site dimension as object
data, with its tight category discretely fibred over site-profiles —
interfaces over sites.  This file adds the spec storey and takes the
total:

* `profiledEmbed` — the profile-forgetting embedding of the profiled
  base into the fused wiring base.  It is **lax and not pseudo, by
  semantics**: its compositor is invertible (a constrained middle is a
  fused middle with a proof, and proofs are irrelevant), but its unit
  comparison embeds the profiled identity pattern as the
  **profile-pinning** sub-pattern of the fused identity — pinning is
  the unit of the profiled world and a genuine constraint in the fused
  world, so the comparison has no inverse.
* `spacetimeSpecFunctor` — the spec storey over the profiled base, by
  **composition** with the landed DNF decoration functor: the fibres
  of the iterated object are the landed fibres definitionally
  (`spacetimeSpecFunctor_fibre_eq`, a `rfl`), which is the staged
  design's Theorem 1(a) parametricity paying inside the indexed
  object.
* **`SemanticUniverse`** — the double Grothendieck total of
  the composite: the iterated construction, Specs over interfaces
  over site-profiles, with the strict projection a discrete double
  opfibration by one-line consumption of the generic theorem.
* Per-site conservativity: for each clock `c`, the one-site wiring
  base sits inside the profiled base at the constant profile, with
  tights, states, and patterns corresponding by equivalences on the
  nose (`constHomEquiv`, `constStates`, `constPatEquiv`) and
  identity/composite patterns corresponding pointwise
  (`constPatEquiv_id_pointwise`, `constPatEquiv_comp_pointwise`).  In
  the state-family presentation the constant-apex narrowing of the
  staged design's Theorem 1(c) dissolves: apex wire-sets do not exist
  here (apex data lives in the family fibres and transports along the
  boundary equivalence).  The equivalences are packaged as the lax
  double functor `constProfile`, pseudo (`constProfile_isPseudo`):
  the `toFun ∘ symm` roundtrip its unitor coherence crosses is
  discharged by surjectivity-destructuring — every constrained state
  is an image point of `constStates`, on which the roundtrip is
  definitional — so the packaging is cast-free.  Contrast
  `profiledEmbed`, lax and not pseudo: forgetting the profile loses
  the pin, while giving the constant profile loses nothing.
* `siteRead` — reading a spacetime spec presentation at one site:
  restriction along the constant-profile packing, the fibre-level
  face of conservativity.
* Walls, generic: conjoining a pure-safety wall into a DNF
  presentation is exactly one more conjunct at the model-class level
  (`SpecDnf.mem_modelClass_withWall`, riding the landed
  `coupledSat_sup_wall_iff`) — the fibre-side vocabulary by which
  clock morphisms (sampler seams) and profile pins enter the iterated
  total's own fibres, where the landed seam-crossing entailment
  criterion applies verbatim.
-/

namespace SuFunctor.Spacetime

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor SuFunctor.Plain SuFunctor.Universe
open scoped ENNReal

universe u

variable {Clk : Type u} {Rec : Clk → Type u}

/-! ## The profile-forgetting embedding -/

/-- Forget the profile: the underlying fused interface. -/
def embObj (A : SpacetimeBase Clk Rec) : WireSpan (ClockedEl Clk Rec) :=
  ⟨A.wires⟩

/-- The profile-membership predicate on fused states. -/
def IsProfiled (A : SpacetimeBase Clk Rec)
    (x : A.wires → ClockedEl Clk Rec) : Prop :=
  ∀ w, (x w).1 = A.profile w

/-- A profiled pattern, read over fused states: the same family, with
the two profile memberships carried as (proof-irrelevant) data. -/
def embPat {A B : SpacetimeBase Clk Rec} (M : Pat A B) :
    WireSpan.Pat (embObj A) (embObj B) :=
  fun x y => Σ (hx : PLift (IsProfiled A x)) (hy : PLift (IsProfiled B y)),
    M ⟨x, hx.down⟩ ⟨y, hy.down⟩

/-- **The profile-forgetting embedding**, a lax double functor from
the profiled base to the fused wiring base.  Lax and not pseudo: the
compositor is invertible, the unit comparison is the profile-pinning
inclusion. -/
def profiledEmbed (Clk : Type u) (Rec : Clk → Type u) :
    LaxDoubleFunctor (SpacetimeBase Clk Rec)
      (WireSpan (ClockedEl Clk Rec)) where
  toFunctor :=
    { obj := embObj
      map := fun φ => φ.1
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  mapLoose := embPat
  mapCell {_ _ _ _ _ _ φ ψ} γ := fun x y s =>
    ⟨⟨fun w => (s.1.down (φ.1 w)).trans (φ.2 w)⟩,
     ⟨fun w => (s.2.1.down (ψ.1 w)).trans (ψ.2 w)⟩,
     γ ⟨x, s.1.down⟩ ⟨y, s.2.1.down⟩ s.2.2⟩
  mapCell_vId _ := rfl
  mapCell_vComp _ _ := rfl
  laxComp _ _ := fun _ _ s =>
    ⟨s.2.2.1.1,
     ⟨s.1, ⟨s.2.2.1.2⟩, s.2.2.2.1⟩,
     ⟨⟨s.2.2.1.2⟩, s.2.1, s.2.2.2.2⟩⟩
  laxId _ := fun _ _ s => ⟨⟨congrArg Subtype.val s.2.2.down.down⟩⟩
  laxComp_natural _ _ := rfl
  laxId_natural _ := rfl
  laxComp_assoc _ _ _ := rfl
  laxComp_leftUnitor _ := rfl
  laxComp_rightUnitor _ := rfl

/-- The embedding is faithful on tights: forgetting the preservation
proof loses nothing (it is a proposition). -/
theorem profiledEmbed_faithful_tight {A B : SpacetimeBase Clk Rec}
    {φ ψ : A ⟶ B}
    (h : (profiledEmbed Clk Rec).map φ = (profiledEmbed Clk Rec).map ψ) :
    φ = ψ :=
  Subtype.ext h

/-! ## The iterated total -/

/-- **The spec storey over the profiled base**: the landed DNF spec
decoration functor, composed along the profile-forgetting embedding.
The middle and inner storeys of the tower, assembled by composition —
every fibre computation is inherited definitionally. -/
noncomputable def spacetimeSpecFunctor (Clk : Type u) (Rec : Clk → Type u) :
    SpanValued.{u + 1, u, u, u + 1, u} (SpacetimeBase Clk Rec) :=
  (profiledEmbed Clk Rec).comp (dnfSpecFunctor (ClockedEl Clk Rec))

/-- The fibres of the iterated object are the landed DNF fibres, on
the nose — the parametricity of the landed assembly paying inside the
indexed object. -/
theorem spacetimeSpecFunctor_fibre_eq (A : SpacetimeBase Clk Rec) :
    (spacetimeSpecFunctor Clk Rec).toFunctor.obj A
      = SpecDnf (Joint (A.wires → ClockedEl Clk Rec)) := rfl

/-- The tight transport of the iterated object is the landed atom-level
transport, on the nose. -/
theorem spacetimeSpecFunctor_map_eq {A B : SpacetimeBase Clk Rec}
    (φ : A ⟶ B) (D : SpecDnf (Joint (A.wires → ClockedEl Clk Rec))) :
    (spacetimeSpecFunctor Clk Rec).toFunctor.map φ D
      = dnfPull (WireSpan.res (A := embObj A) (B := embObj B) φ.1) D := rfl

/-- **The semantic universe**: the iterated double Grothendieck
total — Specs over interfaces over site-profiles.
Objects are profiled interfaces with a designated coupled-DNF
presentation over their fused states; loose arrows are profiled wiring
patterns with an apex presentation; the outer indexing is the site
dimension, carried by the profiled base whose tight category is
discretely fibred over profiles. -/
abbrev SemanticUniverse (Clk : Type u) (Rec : Clk → Type u) :=
  SpanValued.Grothendieck (spacetimeSpecFunctor Clk Rec)

/-- The iterated total is a pseudo double category, by instance
search. -/
theorem semanticUniverse_pseudoDoubleCategory
    (Clk : Type u) (Rec : Clk → Type u) :
    ∃ _ : PseudoDoubleCategory (SemanticUniverse Clk Rec), True :=
  ⟨inferInstance, trivial⟩

/-- The strict projection of the iterated total to the profiled
base. -/
noncomputable def universeProj (Clk : Type u) (Rec : Clk → Type u) :
    LaxDoubleFunctor (SemanticUniverse Clk Rec)
      (SpacetimeBase Clk Rec) :=
  SpanValued.proj (spacetimeSpecFunctor Clk Rec)

/-- The projection is pseudo. -/
theorem universeProj_isPseudo (Clk : Type u) (Rec : Clk → Type u) :
    (universeProj Clk Rec).IsPseudo :=
  SpanValued.proj_isPseudo (spacetimeSpecFunctor Clk Rec)

/-- **The projection is a discrete double opfibration** — by one-line
consumption of the generic theorem, exactly as at the plain tier: the
lifting calculus never inspects fibre internals, so the site grading
costs it nothing. -/
theorem universeProj_discreteOpfibration
    (Clk : Type u) (Rec : Clk → Type u) :
    IsDiscreteDoubleOpfibration (universeProj Clk Rec) :=
  SpanValued.proj_isDiscreteOpfibration (spacetimeSpecFunctor Clk Rec)

/-! ## Per-site conservativity: the constant-profile equivalences -/

section Conservativity

variable (c : Clk)

private theorem sigma_pack (c : Clk) :
    ∀ (p : ClockedEl Clk Rec) (h : p.1 = c),
      (⟨c, h ▸ p.2⟩ : ClockedEl Clk Rec) = p := by
  rintro ⟨c', r⟩ h
  subst h
  rfl

/-- One-site states are constant-profile states: the boundary
repackaging equivalence.  (The single place a leaf-level transport
appears — inside an `Equiv`, never in category structure.) -/
def constStates (S : WireSpan (Rec c)) :
    WireSpan.states S ≃ states (constObj (Rec := Rec) c S.wires) where
  toFun x := ⟨fun w => ⟨c, x w⟩, fun _ => rfl⟩
  invFun y := fun w => (show (y.1 w).1 = c from y.2 w) ▸ (y.1 w).2
  left_inv _ := rfl
  right_inv y := Subtype.ext (funext fun w => sigma_pack c (y.1 w) (y.2 w))

/-- Tight fullness and faithfulness of the constant-profile embedding,
as an equivalence on the nose: at constant profiles the preservation
condition is vacuous. -/
def constHomEquiv (S T : WireSpan (Rec c)) :
    (S ⟶ T) ≃ (constObj (Rec := Rec) c S.wires ⟶ constObj c T.wires) where
  toFun φ := ⟨φ, fun _ => rfl⟩
  invFun φ := φ.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- **Loose-level conservativity**: one-site patterns are exactly the
constant-profile patterns, along the boundary repackaging.  In the
state-family presentation this equivalence is total — the cospan
presentation's constant-apex narrowing (adjudication M3 of the staged
design) dissolves, because apex data lives in the family fibres and
transports along the boundary equivalence rather than in an apex wire
set that could carry foreign clocks. -/
def constPatEquiv (S T : WireSpan (Rec c)) :
    WireSpan.Pat S T ≃ Pat (constObj (Rec := Rec) c S.wires)
      (constObj c T.wires) where
  toFun M := fun x y =>
    M ((constStates c S).symm x) ((constStates c T).symm y)
  invFun P := fun a b => P ((constStates c S) a) ((constStates c T) b)
  left_inv _ := rfl
  right_inv P := by
    funext x y
    show P ((constStates c S) ((constStates c S).symm x))
        ((constStates c T) ((constStates c T).symm y)) = P x y
    rw [(constStates c S).apply_symm_apply, (constStates c T).apply_symm_apply]

/-- Identity patterns correspond, pointwise: the one-site diagonal
transports to the constant-profile diagonal.  (The source type is
`constPatEquiv c S S (WireSpan.Pat.id S) x y`, written unfolded so its
`ULift` structure is directly visible.) -/
def constPatEquiv_id_pointwise (S : WireSpan (Rec c))
    (x y : states (constObj (Rec := Rec) c S.wires)) :
    WireSpan.Pat.id S ((constStates c S).symm x) ((constStates c S).symm y)
      ≃ Pat.id (constObj (Rec := Rec) c S.wires) x y where
  toFun e := ⟨⟨(constStates c S).symm.injective e.down.down⟩⟩
  invFun e := ⟨⟨congrArg (fun t => (constStates c S).symm t) e.down.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Composite patterns correspond, pointwise: gluing transports along
the boundary repackaging of the shared middle.  (The source type is
`constPatEquiv c S V (WireSpan.Pat.comp M N) x z`, written unfolded;
the equivalence is reindexing of the middle along `constStates`.) -/
def constPatEquiv_comp_pointwise {S T V : WireSpan (Rec c)}
    (M : WireSpan.Pat S T) (N : WireSpan.Pat T V)
    (x : states (constObj (Rec := Rec) c S.wires))
    (z : states (constObj (Rec := Rec) c V.wires)) :
    WireSpan.Pat.comp M N ((constStates c S).symm x) ((constStates c V).symm z)
      ≃ Pat.comp (constPatEquiv c S T M) (constPatEquiv c T V N) x z :=
  Equiv.sigmaCongrLeft
    (β := fun y' => constPatEquiv c S T M x y' × constPatEquiv c T V N y' z)
    (constStates c T)

/-- Reading a spacetime spec presentation at one site: restriction of
the fibre along the constant-profile packing — the fibre-level face of
conservativity (functorial via `dnfPull_dnfPull`). -/
noncomputable def siteRead (c : Clk) {S : Type u}
    (D : SpecDnf (Joint (S → ClockedEl Clk Rec))) :
    SpecDnf (Joint (S → Rec c)) :=
  dnfPull (fun x w => ⟨c, x w⟩) D

/-! ### The constant-profile embedding, packaged

Per-site conservativity as a single object: the equivalence family
assembled into a lax double functor from the one-site wiring base into
the profiled base, with an `IsPseudo` certificate.  The proofs ride one
observation: `constStates.left_inv` is `rfl`, so on **image points** of
`constStates` every `toFun ∘ symm` roundtrip is definitional — and every
constrained state is an image point (`constStates` is an equivalence),
so `obtain ⟨x', rfl⟩ := (constStates c S).surjective x` reduces each
unitor law and the compositor's inverse to `rfl`.  No heq, no casts. -/

/-- **The constant-profile embedding**: the one-site wiring base inside
the profiled base at the constant profile, as a lax double functor —
objects take the constant profile, tights ride `constHomEquiv`, looses
ride `constPatEquiv`, and the compositor repackages the shared middle
along `constStates` (the `sigmaCongrLeft` direction of
`constPatEquiv_comp_pointwise`).  Pseudo, by `constProfile_isPseudo`
below: nothing is forgotten in this direction — contrast
`profiledEmbed`, whose unit comparison is the (non-invertible)
profile pin. -/
def constProfile :
    LaxDoubleFunctor (WireSpan (Rec c)) (SpacetimeBase Clk Rec) where
  toFunctor :=
    { obj := fun S => constObj (Rec := Rec) c S.wires
      map := fun φ => constHomEquiv c _ _ φ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  mapLoose {S T} M := constPatEquiv c S T M
  mapCell {_ _ S' T' _ _ _ _} γ := fun x y s =>
    γ ((constStates c S').symm x) ((constStates c T').symm y) s
  mapCell_vId _ := rfl
  mapCell_vComp _ _ := rfl
  laxComp {_ T _} M N := fun x z s =>
    ⟨constStates c T s.1, s.2.1, s.2.2⟩
  laxId S := fun x y e => ⟨⟨(constStates c S).symm.injective e.down.down⟩⟩
  laxComp_natural _ _ := rfl
  laxId_natural _ := rfl
  laxComp_assoc _ _ _ := rfl
  laxComp_leftUnitor {S _} m := by
    funext x y s
    obtain ⟨x', rfl⟩ := (constStates c S).surjective x
    rfl
  laxComp_rightUnitor {_ T} m := by
    funext x y s
    obtain ⟨y', rfl⟩ := (constStates c T).surjective y
    rfl

/-- The packaged functor's tight action is the landed equivalence. -/
theorem constProfile_map_eq {S T : WireSpan (Rec c)} (φ : S ⟶ T) :
    (constProfile (Rec := Rec) c).map φ = constHomEquiv c S T φ := rfl

/-- The packaged functor's loose action is the landed equivalence. -/
theorem constProfile_mapLoose_eq {S T : WireSpan (Rec c)}
    (M : WireSpan.Pat S T) :
    (constProfile (Rec := Rec) c).mapLoose M = constPatEquiv c S T M := rfl

/-- **The constant-profile embedding is pseudo**: both comparison cells
are invertible — the compositor's inverse unpacks the middle along
`constStates.symm`, the unit comparison's inverse is `congrArg` under
`constStates.symm`.  This is the packaging of per-site conservativity:
against `profiledEmbed` (lax, unit = the profile pin), `constProfile`
is the direction in which nothing is forgotten, as a certificate. -/
theorem constProfile_isPseudo :
    (constProfile (Rec := Rec) c).IsPseudo where
  laxComp_isInvertible {_ T _} M N := by
    refine ⟨fun x z s => ⟨(constStates c T).symm s.1, s.2.1, s.2.2⟩, ?_, rfl⟩
    funext x z s
    obtain ⟨y, mm, nn⟩ := s
    obtain ⟨y', rfl⟩ := (constStates c T).surjective y
    rfl
  laxId_isInvertible S :=
    ⟨fun x y e => ⟨⟨congrArg (fun t => (constStates c S).symm t) e.down.down⟩⟩,
      rfl, rfl⟩

end Conservativity

end SuFunctor.Spacetime

/-! ## Walls, generic: seams as conjuncts in the fibres

Pure-safety walls conjoined into DNF presentations — the fibre-side
vocabulary of the site dimension: a declared clock morphism (sampler
seam) enters the composite's presentation as a wall on the joint
carrier, and satisfaction of the walled presentation is satisfaction
of the original plus domination of the wall — one more conjunct,
exactly as the landed seam-crossing entailment criterion consumes it.
Carrier-generic; the realized-record sampler wall `B_φ` instantiates
these over `Joint` carriers (named successor). -/

namespace SuFunctor.Universe

open scoped ENNReal

universe u

variable {K : Type u}

/-- Conjoin a pure-safety wall into an atom: join the wall into the
floor, marks unchanged.  Option-A shape is preserved on the nose. -/
def SpecAtom.withWall (a : SpecAtom K) (w : K → ℝ≥0∞) : SpecAtom K where
  floor := a.floor ⊔ w
  marks := a.marks
  finite_marks := a.finite_marks
  top_mem := a.top_mem

@[simp] theorem SpecAtom.withWall_floor (a : SpecAtom K) (w : K → ℝ≥0∞) :
    (a.withWall w).floor = a.floor ⊔ w := rfl

@[simp] theorem SpecAtom.withWall_marks (a : SpecAtom K) (w : K → ℝ≥0∞) :
    (a.withWall w).marks = a.marks := rfl

/-- Walling an atom is exactly one more conjunct at the model-class
level — the landed wall lemma, in the authoritative fibres'
vocabulary. -/
theorem SpecAtom.mem_modelClass_withWall {a : SpecAtom K}
    {w σ : K → ℝ≥0∞} :
    σ ∈ (a.withWall w).modelClass ↔ w ≤ σ ∧ σ ∈ a.modelClass :=
  coupledSat_sup_wall_iff

/-- Conjoin a pure-safety wall into every atom of a DNF
presentation. -/
def SpecDnf.withWall (D : SpecDnf K) (w : K → ℝ≥0∞) : SpecDnf K where
  atoms := (SpecAtom.withWall · w) '' D.atoms
  finite_atoms := D.finite_atoms.image _

@[simp] theorem SpecDnf.withWall_atoms (D : SpecDnf K) (w : K → ℝ≥0∞) :
    (D.withWall w).atoms = (SpecAtom.withWall · w) '' D.atoms := rfl

/-- Walling a presentation is exactly one more conjunct: the wall
distributes over the disjuncts. -/
theorem SpecDnf.mem_modelClass_withWall {D : SpecDnf K}
    {w σ : K → ℝ≥0∞} :
    σ ∈ (D.withWall w).modelClass ↔ w ≤ σ ∧ σ ∈ D.modelClass := by
  simp only [SpecDnf.mem_modelClass_iff, SpecDnf.withWall_atoms,
    Set.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨a, ha, hsat⟩
    have h := (coupledSat_sup_wall_iff
      (σ := σ) (u := a.floor) (w := w) (𝒱 := a.marks)).mp hsat
    exact ⟨h.1, a, ha, h.2⟩
  · rintro ⟨hw, a, ha, hsat⟩
    exact ⟨a, ha, (coupledSat_sup_wall_iff
      (σ := σ) (u := a.floor) (w := w) (𝒱 := a.marks)).mpr ⟨hw, hsat⟩⟩

end SuFunctor.Universe
