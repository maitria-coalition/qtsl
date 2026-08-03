import DoubleCat.WireSpan

/-! # The spacetime-site stratum and the profiled wiring base

The site dimension of the semantic universe, at the base level.  A
**spacetime site** is a small collection of windows with points — the
finite/possibilistic stratum of the (duration, tangency)-structured
site signature; a **spacetime clock** is a site with admissible
realizations per window; a **realized record** carries its window and
realization alongside its observation history.  Nothing in the graded
construction below consumes duration or coverage structure: that
blindness is deliberate and load-bearing — it is the parametricity
that lets the landed decoration tier instantiate at clocked state
vocabularies without a re-proof.

The **profiled wiring base** `SpacetimeBase` is the site-indexed face
of the wiring base: objects carry their site assignment (one clock
per wire — the *profile*) as object data, tight arrows are
profile-preserving wire maps, and states are the fused clocked states
constrained to match the profile.  Two design facts carry the file:

* **Profile constraints are propositions riding subtypes.**  States
  are `{x : wires → Σ c, Rec c // ∀ w, (x w).1 = profile w}` — the
  fused presentation with a `Prop` fence, never a dependent family
  `∀ w, Rec (profile w)` — so definitional proof irrelevance and
  structure eta keep every category and double-category law at the
  same `rfl` grade as the unprofiled base: no cast ever touches data.
* **The tight category is discretely fibred over profiles.**  Along
  any raw wire map into a profiled interface there is exactly one
  source profile making it a tight (`profileLift`, uniqueness below) —
  interfaces are indexed over site-profiles, the middle storey of the
  iterated total.  And the grammar refuses cross-site identification:
  a tight that merges two wires forces their sites equal
  (`profile_eq_of_identified`), while cross-site *patterns* remain
  grammatical (`mixedInterface`, the sampler's boundary) — which is
  the design reason the indexing is by profiles and not by single
  sites: a mixed-boundary device has no home over a single-site base.
-/

namespace SuFunctor.Spacetime

open CategoryTheory PseudoDoubleCategoryStruct

universe u

/-! ## Spacetime sites, clocks, realized records -/

/-- A spacetime site, at the finite/possibilistic stratum: windows,
with points per window.  The full signature adds window inclusions, a
coverage, and a duration monoid; none of that is consumed by the
graded construction below — the blindness is the parametricity of the
decoration tier, made visible. -/
structure SpacetimeSite : Type (u + 1) where
  /-- The windows of the site. -/
  Window : Type u
  /-- The points of a window (the observation slots a record fills). -/
  pts : Window → Type u

/-- A spacetime clock: a spacetime site together with an admissible
realization class per window.  (At this stratum a realization class is
a bare type of realizations; the analytic clauses — nonemptiness,
closedness — are the ambient semantics' regularity content, out of
scope here and priced there.) -/
structure SpacetimeClock : Type (u + 1) where
  /-- The underlying spacetime site. -/
  site : SpacetimeSite.{u}
  /-- Admissible realizations of each window. -/
  Real : site.Window → Type u

/-- A realized record over a spacetime clock: a window, an admissible
realization of it, and an observation history along its points.  A
record carries its own window and realization — the clock is a
component of the state, never ambient indexing. -/
structure SpacetimeRec (c : SpacetimeClock.{u}) (X : Type u) : Type u where
  /-- The record's window. -/
  w : c.site.Window
  /-- The realization the record rode. -/
  θ : c.Real w
  /-- The observation history. -/
  x : c.site.pts w → X

/-- The tick site: integer windows `(start, length)`, with `n + 1`
points in a window of length `n`. -/
def tickSite : SpacetimeSite.{u} where
  Window := ULift.{u} (ℕ × ℕ)
  pts p := ULift.{u} (Fin (p.down.2 + 1))

/-- The pinned tick clock: exactly one admissible realization per
window (the zero-jitter grid). -/
def pinnedTickClock : SpacetimeClock.{u} where
  site := tickSite
  Real _ := PUnit

/-- A jittered tick clock at the quantized stratum: per window, a
choice of jitter index per point (a nontrivial finite realization
class, distinct from the pinned clock over the same site). -/
def jitteredTickClock : SpacetimeClock.{u} where
  site := tickSite
  Real p := ULift.{u} (Fin (p.down.2 + 1)) → ULift.{u} (Fin 3)

/-! ## The clocked state vocabulary -/

variable (Clk : Type u) (Rec : Clk → Type u)

/-- The fused clocked state vocabulary: a state is a realized record
tagged with its clock.  Instantiating the landed decoration tier at
this vocabulary is the parametric face of the site dimension. -/
abbrev ClockedEl : Type u := Σ c : Clk, Rec c

/-! ## The profiled wiring base -/

/-- A profiled interface: wires, each carrying its spacetime site
assignment (its clock).  The site dimension as object data — the
middle storey of the iterated total.  (`Rec` is a phantom parameter
here: objects and tights never consume value spaces, but the type must
carry the full vocabulary so that its double-category structure —
whose loose stratum does consume `Rec` — is determined by the type.) -/
structure SpacetimeBase (Clk : Type u) (Rec : Clk → Type u) :
    Type (u + 1) where
  /-- The wires of the interface. -/
  wires : Type u
  /-- The profile: each wire's clock. -/
  profile : wires → Clk

variable {Clk Rec}

/-- Tight arrows are profile-preserving wire maps.  The preservation
condition is a proposition, so composition stays definitional on
data. -/
instance : Category.{u} (SpacetimeBase Clk Rec) where
  Hom A B := {φ : A.wires → B.wires // ∀ w, B.profile (φ w) = A.profile w}
  id A := ⟨fun w => w, fun _ => rfl⟩
  comp f g := ⟨fun w => g.1 (f.1 w), fun w => (g.2 (f.1 w)).trans (f.2 w)⟩

@[simp] theorem id_coe (A : SpacetimeBase Clk Rec) {w : A.wires} :
    (𝟙 A : A ⟶ A).1 w = w := rfl

@[simp] theorem comp_coe {A B C : SpacetimeBase Clk Rec} (f : A ⟶ B)
    (g : B ⟶ C) {w : A.wires} : (f ≫ g).1 w = g.1 (f.1 w) := rfl

/-- The state space of a profiled interface: fused clocked states
constrained to match the profile.  The constraint is a proposition —
proof irrelevance keeps every law below at `rfl` grade. -/
abbrev states (A : SpacetimeBase Clk Rec) : Type u :=
  {x : A.wires → ClockedEl Clk Rec // ∀ w, (x w).1 = A.profile w}

/-- Restriction of states along a tight (contravariant); the profile
constraint transports along the tight's preservation condition — the
one place the Hom condition is consumed, and the reason raw wire maps
cannot restrict profiled states. -/
abbrev res {A B : SpacetimeBase Clk Rec} (φ : A ⟶ B) :
    states B → states A :=
  fun y => ⟨fun w => y.1 (φ.1 w), fun w => (y.2 (φ.1 w)).trans (φ.2 w)⟩

@[simp] theorem res_id {A : SpacetimeBase Clk Rec} : res (𝟙 A) = id := rfl

theorem res_comp {A B C : SpacetimeBase Clk Rec} (φ : A ⟶ B) (ψ : B ⟶ C) :
    res (φ ≫ ψ) = res φ ∘ res ψ := rfl

/-- A wiring pattern between profiled interfaces, presented by its
state family. -/
abbrev Pat (A B : SpacetimeBase Clk Rec) : Type (u + 1) :=
  states A → states B → Type u

namespace Pat

/-- The identity pattern: the diagonal family. -/
@[reducible] def id (A : SpacetimeBase Clk Rec) : Pat A A :=
  fun x y => ULift (PLift (x = y))

/-- Composition of patterns: gluing along the shared boundary. -/
@[reducible] def comp {A B C : SpacetimeBase Clk Rec} (M : Pat A B)
    (N : Pat B C) : Pat A C :=
  fun x z => Σ y : states B, M x y × N y z

/-- The apex state space of a pattern. -/
@[reducible] def Tot {A B : SpacetimeBase Clk Rec} (M : Pat A B) : Type u :=
  Σ (x : states A) (y : states B), M x y

/-- The first joint-to-component projection of a glued apex. -/
@[reducible] def compFst {A B C : SpacetimeBase Clk Rec} (M : Pat A B)
    (N : Pat B C) : Tot (comp M N) → Tot M :=
  fun t => ⟨t.1, t.2.2.1, t.2.2.2.1⟩

/-- The second joint-to-component projection of a glued apex. -/
@[reducible] def compSnd {A B C : SpacetimeBase Clk Rec} (M : Pat A B)
    (N : Pat B C) : Tot (comp M N) → Tot N :=
  fun t => ⟨t.2.2.1, t.2.1, t.2.2.2.2⟩

end Pat

/-- A cell between profiled patterns over tights `(φ, ψ)`: a map of
apex states, backward, exactly as in the unprofiled base. -/
abbrev PatCell {A B A' B' : SpacetimeBase Clk Rec} (M : Pat A B)
    (N : Pat A' B') (φ : A ⟶ A') (ψ : B ⟶ B') : Type u :=
  ∀ x y, N x y → M (res φ x) (res ψ y)

namespace PatCell

/-- The action of a cell on apex state spaces (backward). -/
@[reducible] def tot {A B A' B' : SpacetimeBase Clk Rec} {M : Pat A B}
    {N : Pat A' B'} {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ) :
    Pat.Tot N → Pat.Tot M :=
  fun t => ⟨res φ t.1, res ψ t.2.1, γ t.1 t.2.1 t.2.2⟩

end PatCell

/-- The pseudo double category of profiled interfaces and wiring
patterns — the landed base's structure, transferred verbatim: the
profile constraints ride proof-irrelevant subtypes, so every law
closes by the same scripts. -/
instance instPseudoDoubleCategoryStruct :
    PseudoDoubleCategoryStruct (SpacetimeBase Clk Rec) where
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

@[simp] theorem lId_def (A : SpacetimeBase Clk Rec) : 𝟙ˡ A = Pat.id A := rfl

@[simp] theorem lComp_def {A B C : SpacetimeBase Clk Rec} (M : Loose A B)
    (N : Loose B C) : M ⊙ N = Pat.comp M N := rfl

/-- The axioms, by the unprofiled base's scripts. -/
instance instPseudoDoubleCategory :
    PseudoDoubleCategory (SpacetimeBase Clk Rec) where
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

/-! ## The `Tot`-calculus, transferred -/

section TotCalculus

variable {A B C D A' B' C' : SpacetimeBase Clk Rec}

theorem tot_vId (M : Pat A B) :
    PatCell.tot (PseudoDoubleCategoryStruct.vId
      (C := SpacetimeBase Clk Rec) M) = id := rfl

theorem tot_vComp {M₁ : Pat A B} {M₂ : Pat A' B'} {M₃ : Pat C D}
    {f₁ : A ⟶ A'} {g₁ : B ⟶ B'} {f₂ : A' ⟶ C} {g₂ : B' ⟶ D}
    (α : PatCell M₁ M₂ f₁ g₁) (β : PatCell M₂ M₃ f₂ g₂) :
    PatCell.tot (PseudoDoubleCategoryStruct.vComp
        (C := SpacetimeBase Clk Rec) α β) =
      PatCell.tot α ∘ PatCell.tot β := rfl

theorem compFst_tot_hComp {M₁ : Pat A B} {M₂ : Pat B C} {N₁ : Pat A' B'}
    {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ) :
    Pat.compFst M₁ M₂ ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.hComp
          (C := SpacetimeBase Clk Rec) α β) =
      PatCell.tot α ∘ Pat.compFst N₁ N₂ := rfl

theorem compSnd_tot_hComp {M₁ : Pat A B} {M₂ : Pat B C} {N₁ : Pat A' B'}
    {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ) :
    Pat.compSnd M₁ M₂ ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.hComp
          (C := SpacetimeBase Clk Rec) α β) =
      PatCell.tot β ∘ Pat.compSnd N₁ N₂ := rfl

theorem compFst_compFst_tot_lAssoc (M : Pat A B) (N : Pat B C)
    (P : Pat C D) :
    Pat.compFst M N ∘ Pat.compFst (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc
          (C := SpacetimeBase Clk Rec) M N P) =
      Pat.compFst M (N.comp P) := rfl

theorem compSnd_compFst_tot_lAssoc (M : Pat A B) (N : Pat B C)
    (P : Pat C D) :
    Pat.compSnd M N ∘ Pat.compFst (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc
          (C := SpacetimeBase Clk Rec) M N P) =
      Pat.compFst N P ∘ Pat.compSnd M (N.comp P) := rfl

theorem compSnd_tot_lAssoc (M : Pat A B) (N : Pat B C) (P : Pat C D) :
    Pat.compSnd (M.comp N) P ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc
          (C := SpacetimeBase Clk Rec) M N P) =
      Pat.compSnd N P ∘ Pat.compSnd M (N.comp P) := rfl

theorem compSnd_tot_lLeftUnitor (M : Pat A B) :
    Pat.compSnd (Pat.id A) M ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor
          (C := SpacetimeBase Clk Rec) M) =
      id := rfl

theorem compFst_tot_lRightUnitor (M : Pat A B) :
    Pat.compFst M (Pat.id B) ∘ PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor
          (C := SpacetimeBase Clk Rec) M) =
      id := rfl

end TotCalculus

/-! ## The site-fibration facts: interfaces over site-profiles

The tight category is discretely fibred over profiles — the middle
storey of the iterated total, stated directly: unique cartesian lifts
at the tight level, cross-site identification refused, cross-site
patterns grammatical. -/

section SiteFibration

variable {A B : SpacetimeBase Clk Rec}

/-- **Cross-site identification is unrepresentable** (the staged
design's Remark 1.1, mechanized): a tight arrow that merges two wires
forces their spacetime sites equal.  The one illegal move — "this
discrete wire *is* that continuous wire", no morphism declared — is
refused by the grammar itself; cross-site relating lives in pattern
content, where clock morphisms are wiring data. -/
theorem profile_eq_of_identified (φ : A ⟶ B) {w w' : A.wires}
    (h : φ.1 w = φ.1 w') : A.profile w = A.profile w' :=
  (φ.2 w).symm.trans ((congrArg B.profile h).trans (φ.2 w'))

/-- The profile lift: along any raw wire map into a profiled
interface, the pulled-back profile. -/
def profileLift (S : Type u) (φ : S → B.wires) : SpacetimeBase Clk Rec :=
  ⟨S, fun w => B.profile (φ w)⟩

/-- The lifted profile makes the raw map a tight — existence of the
cartesian lift. -/
def profileLiftHom (S : Type u) (φ : S → B.wires) :
    profileLift (Rec := Rec) S φ ⟶ B :=
  ⟨φ, fun _ => rfl⟩

/-- The lifted profile is the **only** source profile admitting the
raw map as a tight — uniqueness of the cartesian lift.  Together with
`profileLiftHom` this is the discrete-fibration property of
profile-forgetting at the tight level: interfaces are indexed over
site-profiles. -/
theorem profile_unique_of_hom {S : Type u} {κ : S → Clk}
    {φ : S → B.wires} (h : ∀ w, B.profile (φ w) = κ w) :
    κ = fun w => B.profile (φ w) :=
  funext fun w => (h w).symm

/-- The mixed-profile interface: two wires on two (possibly distinct)
spacetime sites — the sampler's boundary.  Its existence is what
per-system single-site indexing cannot type, and the design reason the
outer indexing is by profiles. -/
def mixedInterface (c c' : Clk) : SpacetimeBase Clk Rec :=
  ⟨ULift.{u} Bool, fun b => if b.down then c else c'⟩

/-- The constant-profile interface: every wire on one spacetime
site. -/
def constObj (c : Clk) (S : Type u) : SpacetimeBase Clk Rec :=
  ⟨S, fun _ => c⟩

/-- Cross-site *patterns* are grammatical: between any two
constant-profile interfaces on distinct sites there is a pattern
relating their states (here: the everywhere-inhabited family — the
coupling-free juxtaposition seam; genuinely constraining seams add
penalty content in the decoration tier, where clock morphisms live).
Identification is refused (`profile_eq_of_identified`); relation is
decoration. -/
example (c c' : Clk) (S T : Type u) :
    Pat (constObj (Rec := Rec) c S) (constObj (Rec := Rec) c' T) :=
  fun _ _ => PUnit

end SiteFibration

end SuFunctor.Spacetime
