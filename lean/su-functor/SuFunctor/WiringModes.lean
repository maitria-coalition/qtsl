import SuFunctor.SingleSiteSemanticUniverse

/-! # The wiring modes against the semantic universe: naturality of the
transport trio

The composition-patterns chapter ships three wiring modes — parameter
setting (`set`), variable sharing (`share`), and mode switching
(`switch`) — as row families with transport rules.  This file states,
per mode, the pattern-level naturality against the mechanized semantic
universe, in the form that is *true* of each mode rather than one form
forced onto all three:

* **Variable sharing carries the trio's spatial content and gets the
  square.**  A family of share rows denotes the *identification
  pattern* of the wiring base (`WireRows.pat`): the loose arrow whose
  apex states are the boundary states agreeing on every row.  The
  denotation is a function of the row *set* (`ofList_perm`,
  `ofList_pair_left` — composition data are rows, not operations), it
  is symmetric in its parties (`swapEquiv`: identification, not
  assignment), row-preserving renames induce cells functorially
  (`cellOf`, `cellOf_vId`, `cellOf_vComp`), and the certificate
  transport along those cells is **natural against the compositor**:
  transporting a composite presentation equals composing the
  transported presentations (`share_transport_boxplus`), packaged
  literally as a natural transformation (`shareBoxplus :
  pairDec ⟶ compDec`) between the decoration functors on the category
  of composable share-wiring pairs.

* **Parameter setting subsumes into sharing, and the subsumption is a
  theorem.**  The wiring base is deliberately undirected, so the `set`
  mode's direction premises (producer endpoint an output, consumer
  endpoint an input) have no carrier at this stratum: they are
  formation-refusal data.  `SetRows.pat_eq_share` states the factoring
  — and it holds by `rfl`, which is the finding: a set-mode denotation
  *could not* read direction even if it wanted to, so every share-mode
  naturality statement transfers to set mode on the nose
  (`set_transport_boxplus`).  What is genuinely specific to parameter
  setting is the assume–guarantee **slack arithmetic**: entailment
  with slack composes additively across a set wire (`boxplus_mono`,
  `boxplus_add_const`, `boxplus_le_slack`, and the atom-level face
  `atomBoxplus_floor_le_slack`) — the semantic soundness of
  recomputing slack by addition when certificates transport across
  the composite boundary.

* **Mode switching splits: statics here, dynamics one stratum down.**
  A switch composite's *static* interface is one supervisory location
  wire plus the roster's wires (`switchObj`; the location wire's value
  encodes the active location, and the untyped stratum deliberately
  does not fix the encoding — cf. the design note of the wiring
  base).  Per-location spec transport into the composite is the tight
  transport along `switchIncl`, and it is **natural in component
  renames** (`switchIncl_natural`, `dnfPull_switch_natural`), with
  `switchMap` functorial (`switchMap_id`, `switchMap_comp`) and the
  location wire's independence from the roster exhibited by the
  factoring through `rosterObj` (`switchIncl_factor`).  Deliberately
  *not* stated: any spec-class-level composition law for the switch
  species (guarded / rate / forced) — the supervisory edges compose
  behaviors in time, not interfaces in space, and their semantics is
  generator-stratum content; asserting a compositor square for them
  here would be an invented formal block.
-/

namespace SuFunctor

namespace WiringModes

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

universe u

variable {El : Type u}

/-! ## Rows and their denotation: the identification pattern -/

/-- A family of wiring rows between two interfaces: the composition
data of the `set` and `share` modes, as data — a set of wire pairs,
each identifying one wire of the left interface with one wire of the
right. -/
structure WireRows (A B : WireSpan El) : Type u where
  /-- The rows: pairs of identified wires. -/
  rows : Set (A.wires × B.wires)

namespace WireRows

variable {A B C : WireSpan El}

/-- The denotation of a row family: the **identification pattern**,
whose apex states over a boundary pair are the proofs that the
boundary agrees on every row.  This is the share mode's semantics, and
(by `SetRows.pat_eq_share`) the set mode's as well. -/
def pat (R : WireRows A B) : Pat A B :=
  fun x y => ULift (PLift (∀ p ∈ R.rows, x p.1 = y p.2))

/-- Row families from listed composition data. -/
def ofList (l : List (A.wires × B.wires)) : WireRows A B :=
  ⟨{p | p ∈ l}⟩

/-- **Rows, not operations**: the denotation consumes the row *set*,
so permuting listed composition data changes nothing. -/
theorem ofList_perm {l l' : List (A.wires × B.wires)} (h : l.Perm l') :
    ofList l = ofList l' :=
  congrArg WireRows.mk (Set.ext fun _ => ⟨fun hp => h.mem_iff.mp hp,
    fun hp => h.mem_iff.mpr hp⟩)

/-- Duplicate rows are absorbed: listing an identification twice is the
same composition data. -/
theorem ofList_pair_left (p : A.wires × B.wires)
    (l : List (A.wires × B.wires)) :
    ofList (p :: p :: l) = ofList (p :: l) :=
  congrArg WireRows.mk (Set.ext fun q => by
    simp only [Set.mem_setOf_eq, List.mem_cons, or_self_left])

/-! ### Symmetry: identification, not assignment -/

/-- The party swap of a row family. -/
def swap (R : WireRows A B) : WireRows B A :=
  ⟨Prod.swap ⁻¹' R.rows⟩

/-- The share denotation is symmetric in its parties: apex states of
the swapped rows are apex states of the original, boundary-wise.  (The
machine form of the chapter's "identification, not assignment": no
direction survives into the denotation for a swap to disturb.) -/
def swapEquiv (R : WireRows A B) (x : states A) (y : states B) :
    R.swap.pat y x ≃ R.pat x y where
  toFun s := ⟨⟨fun p hp => (s.down.down (p.2, p.1) hp).symm⟩⟩
  invFun s := ⟨⟨fun q hq => (s.down.down (q.2, q.1) hq).symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The symmetry, at the level the decoration tier consumes: the apex
state spaces of a row family and its swap are equivalent, exchanging
the boundary data. -/
def swapTot (R : WireRows A B) : Pat.Tot R.swap.pat ≃ Pat.Tot R.pat where
  toFun t := ⟨t.2.1, t.1, swapEquiv R t.2.1 t.1 t.2.2⟩
  invFun t := ⟨t.2.1, t.1, (swapEquiv R t.1 t.2.1).symm t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Functoriality: row-preserving renames induce cells -/

/-- A row-preserving rename pair induces a cell of the wiring base
between the identification patterns, with the base's variance (apex
states pull back): an agreement state for the target rows restricts to
an agreement state for the source rows. -/
def cellOf {A' B' : WireSpan El} {φ : A ⟶ A'} {ψ : B ⟶ B'}
    (R : WireRows A B) (R' : WireRows A' B')
    (h : ∀ p ∈ R.rows, (φ p.1, ψ p.2) ∈ R'.rows) :
    PatCell R.pat R'.pat φ ψ :=
  fun _ _ s => ⟨⟨fun p hp => s.down.down _ (h p hp)⟩⟩

/-- The identity rename induces the identity cell. -/
theorem cellOf_vId (R : WireRows A B) :
    cellOf R R (fun _ hp => hp)
      = PseudoDoubleCategoryStruct.vId (C := WireSpan El) R.pat := rfl

/-- Cells of composite renames are tight-wise composites of the cells:
`cellOf` is functorial from row-preserving rename pairs to cells. -/
theorem cellOf_vComp {A' B' A'' B'' : WireSpan El}
    {φ : A ⟶ A'} {ψ : B ⟶ B'} {φ' : A' ⟶ A''} {ψ' : B' ⟶ B''}
    (R : WireRows A B) (R' : WireRows A' B') (R'' : WireRows A'' B'')
    (h : ∀ p ∈ R.rows, (φ p.1, ψ p.2) ∈ R'.rows)
    (h' : ∀ p ∈ R'.rows, (φ' p.1, ψ' p.2) ∈ R''.rows) :
    PseudoDoubleCategoryStruct.vComp (C := WireSpan El)
        (cellOf R R' h) (cellOf R' R'' h')
      = cellOf R R'' (fun p hp => h' _ (h p hp)) := rfl

end WireRows

/-! ## Parameter setting: formation-directed, semantically undirected -/

/-- Formation data of the `set` mode: rows together with the direction
premises of its formation rule, relative to declared direction sets on
the two interfaces (the producer side's outputs, the consumer side's
inputs).  The premises are formation-refusal data: the wiring base is
deliberately undirected, so nothing at the semantic stratum can consume
them. -/
structure SetRows (A B : WireSpan El)
    (outs : Set A.wires) (ins : Set B.wires) : Type u
    extends WireRows A B where
  /-- Every row leaves from a declared output. -/
  from_output : ∀ p ∈ rows, p.1 ∈ outs
  /-- Every row arrives at a declared input. -/
  to_input : ∀ p ∈ rows, p.2 ∈ ins

namespace SetRows

variable {A B : WireSpan El} {outs : Set A.wires} {ins : Set B.wires}

/-- The set-mode denotation: the identification pattern of the
underlying rows. -/
def pat (R : SetRows A B outs ins) : Pat A B :=
  R.toWireRows.pat

/-- **Parameter setting factors through variable sharing** — by `rfl`,
which is the content: the direction premises have no carrier at this
stratum, so the denotation *could not* read them.  Every share-mode
naturality statement transfers to set mode on the nose. -/
theorem pat_eq_share (R : SetRows A B outs ins) :
    R.pat = R.toWireRows.pat := rfl

end SetRows

/-! ## The compositor squares

The general extraction first: the naturality of the semantic
universe's compositor along arbitrary cells, exposed as a named lemma
(it is proved inline in the functor's `laxComp_natural` obligation);
then its instantiation at the share cells — the pattern-level
naturality statement of the wiring modes. -/

section Compositor

variable {A B C A' B' C' : WireSpan El}

/-- Naturality of the image-level compositor along arbitrary cells, at
the penalty-class stratum (the generality reservoir): transporting a
composite class along a loose-wise composite cell is the composite of
the transported classes. -/
theorem pull_tot_hComp_image2_boxplus {M₁ : Pat A B} {M₂ : Pat B C}
    {N₁ : Pat A' B'} {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'}
    {ψ : C ⟶ C'} (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ)
    (𝒰₁ : Cpl M₁) (𝒰₂ : Cpl M₂) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)) ''
        Set.image2 boxplus 𝒰₁ 𝒰₂
      = Set.image2 boxplus (Pen.pull (PatCell.tot α) '' 𝒰₁)
          (Pen.pull (PatCell.tot β) '' 𝒰₂) := by
  rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
  exact Set.image2_congr fun u₁ _ u₂ _ => pull_tot_hComp_boxplus α β u₁ u₂

/-- Naturality of the semantic universe's compositor along arbitrary
cells, at the authoritative DNF stratum: transporting a composite
presentation along a loose-wise composite cell is the composite of the
transported presentations. -/
theorem dnfPull_tot_hComp_dnfBoxplus {M₁ : Pat A B} {M₂ : Pat B C}
    {N₁ : Pat A' B'} {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'}
    {ψ : C ⟶ C'} (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ)
    (D₁ : DnfCpl M₁) (D₂ : DnfCpl M₂) :
    dnfPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β))
        (dnfBoxplus D₁ D₂)
      = dnfBoxplus (dnfPull (PatCell.tot α) D₁)
          (dnfPull (PatCell.tot β) D₂) := by
  apply SpecDnf.ext
  show atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)) ''
        Set.image2 atomBoxplus D₁.atoms D₂.atoms
      = Set.image2 atomBoxplus (atomPull (PatCell.tot α) '' D₁.atoms)
          (atomPull (PatCell.tot β) '' D₂.atoms)
  rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
  exact Set.image2_congr fun a₁ _ a₂ _ =>
    atomPull_tot_hComp_boxplus α β a₁ a₂

/-- **The share transport is natural against the compositor** (the
pattern-level statement of the variable-sharing mode): for
row-preserving renames of a two-wiring composite, transporting the
composite presentation along the induced composite cell equals
composing the transported presentations. -/
theorem share_transport_boxplus {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (R : WireRows A B) (S : WireRows B C)
    (R' : WireRows A' B') (S' : WireRows B' C')
    (hR : ∀ p ∈ R.rows, (φ p.1, γ p.2) ∈ R'.rows)
    (hS : ∀ p ∈ S.rows, (γ p.1, ψ p.2) ∈ S'.rows)
    (D₁ : DnfCpl R.pat) (D₂ : DnfCpl S.pat) :
    dnfPull (PatCell.tot (PseudoDoubleCategoryStruct.hComp
        (C := WireSpan El) (R.cellOf R' hR) (S.cellOf S' hS)))
        (dnfBoxplus D₁ D₂)
      = dnfBoxplus (dnfPull (PatCell.tot (R.cellOf R' hR)) D₁)
          (dnfPull (PatCell.tot (S.cellOf S' hS)) D₂) :=
  dnfPull_tot_hComp_dnfBoxplus _ _ D₁ D₂

/-- The set-mode instance, on the nose: parameter-setting transport is
natural against the compositor because its denotation is the share
denotation (`SetRows.pat_eq_share`). -/
theorem set_transport_boxplus {oA : Set A.wires} {iB : Set B.wires}
    {oB : Set B.wires} {iC : Set C.wires}
    {oA' : Set A'.wires} {iB' : Set B'.wires}
    {oB' : Set B'.wires} {iC' : Set C'.wires}
    {φ : A ⟶ A'} {γ : B ⟶ B'} {ψ : C ⟶ C'}
    (R : SetRows A B oA iB) (S : SetRows B C oB iC)
    (R' : SetRows A' B' oA' iB') (S' : SetRows B' C' oB' iC')
    (hR : ∀ p ∈ R.rows, (φ p.1, γ p.2) ∈ R'.rows)
    (hS : ∀ p ∈ S.rows, (γ p.1, ψ p.2) ∈ S'.rows)
    (D₁ : DnfCpl R.pat) (D₂ : DnfCpl S.pat) :
    dnfPull (PatCell.tot (PseudoDoubleCategoryStruct.hComp
        (C := WireSpan El)
        (R.toWireRows.cellOf R'.toWireRows hR)
        (S.toWireRows.cellOf S'.toWireRows hS)))
        (dnfBoxplus D₁ D₂)
      = dnfBoxplus
          (dnfPull (PatCell.tot (R.toWireRows.cellOf R'.toWireRows hR)) D₁)
          (dnfPull (PatCell.tot (S.toWireRows.cellOf S'.toWireRows hS)) D₂) :=
  share_transport_boxplus _ _ _ _ hR hS D₁ D₂

end Compositor

/-! ## The transport as a natural transformation, literally

The category of composable share-wiring pairs, its two decoration
functors, and the compositor as a natural transformation between
them.  The naturality field *is* `share_transport_boxplus`. -/

/-- A composable pair of share wirings: three interfaces and two row
families in series. -/
structure SharePair (El : Type u) : Type (u + 1) where
  /-- The left interface. -/
  left : WireSpan El
  /-- The middle interface. -/
  mid : WireSpan El
  /-- The right interface. -/
  right : WireSpan El
  /-- The rows wiring left to middle. -/
  fst : WireRows left mid
  /-- The rows wiring middle to right. -/
  snd : WireRows mid right

/-- A morphism of composable pairs: a rename triple preserving both
row families. -/
structure SharePairHom (X Y : SharePair El) : Type u where
  /-- The left rename. -/
  mapL : X.left ⟶ Y.left
  /-- The middle rename. -/
  mapM : X.mid ⟶ Y.mid
  /-- The right rename. -/
  mapR : X.right ⟶ Y.right
  /-- The first row family is preserved. -/
  presFst : ∀ p ∈ X.fst.rows, (mapL p.1, mapM p.2) ∈ Y.fst.rows
  /-- The second row family is preserved. -/
  presSnd : ∀ p ∈ X.snd.rows, (mapM p.1, mapR p.2) ∈ Y.snd.rows

instance : Category (SharePair El) where
  Hom := SharePairHom
  id X := ⟨𝟙 X.left, 𝟙 X.mid, 𝟙 X.right,
    fun _ hp => hp, fun _ hp => hp⟩
  comp f g := ⟨f.mapL ≫ g.mapL, f.mapM ≫ g.mapM, f.mapR ≫ g.mapR,
    fun p hp => g.presFst _ (f.presFst p hp),
    fun p hp => g.presSnd _ (f.presSnd p hp)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The pair-of-decorations functor: a composable pair carries the
decorations of its two wirings, transported componentwise along the
induced cells. -/
def pairDec (El : Type u) : SharePair El ⥤ Type u where
  obj X := DnfCpl X.fst.pat × DnfCpl X.snd.pat
  map {X Y} f := TypeCat.ofHom fun D =>
    (dnfPull (PatCell.tot (X.fst.cellOf Y.fst f.presFst)) D.1,
     dnfPull (PatCell.tot (X.snd.cellOf Y.snd f.presSnd)) D.2)
  map_id X :=
    congrArg TypeCat.ofHom (funext fun D => by
      show (dnfPull (PatCell.tot (X.fst.cellOf X.fst _)) D.1,
            dnfPull (PatCell.tot (X.snd.cellOf X.snd _)) D.2) = D
      rw [WireRows.cellOf_vId, WireRows.cellOf_vId]
      show (dnfPull id D.1, dnfPull id D.2) = D
      rw [dnfPull_id, dnfPull_id])
  map_comp {X Y Z} f g :=
    congrArg TypeCat.ofHom (funext fun D => by
      show (dnfPull (PatCell.tot (X.fst.cellOf Z.fst _)) D.1,
            dnfPull (PatCell.tot (X.snd.cellOf Z.snd _)) D.2)
          = (dnfPull (PatCell.tot (Y.fst.cellOf Z.fst g.presFst))
               (dnfPull (PatCell.tot (X.fst.cellOf Y.fst f.presFst)) D.1),
             dnfPull (PatCell.tot (Y.snd.cellOf Z.snd g.presSnd))
               (dnfPull (PatCell.tot (X.snd.cellOf Y.snd f.presSnd)) D.2))
      rw [dnfPull_dnfPull, dnfPull_dnfPull]
      rfl)

/-- The composite-decoration functor: a composable pair carries the
decorations of its glued wiring, transported along the loose-wise
composite of the induced cells. -/
def compDec (El : Type u) : SharePair El ⥤ Type u where
  obj X := DnfCpl (Pat.comp X.fst.pat X.snd.pat)
  map {X Y} f := TypeCat.ofHom (dnfPull (PatCell.tot
    (PseudoDoubleCategoryStruct.hComp (C := WireSpan El)
      (X.fst.cellOf Y.fst f.presFst) (X.snd.cellOf Y.snd f.presSnd))))
  map_id X :=
    congrArg TypeCat.ofHom (funext fun D => by
      show dnfPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El)
          (X.fst.cellOf X.fst _) (X.snd.cellOf X.snd _))) D = D
      rw [WireRows.cellOf_vId, WireRows.cellOf_vId]
      exact dnfPull_id D)
  map_comp {X Y Z} f g :=
    congrArg TypeCat.ofHom (funext fun D => by
      show dnfPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El)
          (X.fst.cellOf Z.fst _) (X.snd.cellOf Z.snd _))) D
        = dnfPull (PatCell.tot
            (PseudoDoubleCategoryStruct.hComp (C := WireSpan El)
              (Y.fst.cellOf Z.fst g.presFst)
              (Y.snd.cellOf Z.snd g.presSnd)))
            (dnfPull (PatCell.tot
              (PseudoDoubleCategoryStruct.hComp (C := WireSpan El)
                (X.fst.cellOf Y.fst f.presFst)
                (X.snd.cellOf Y.snd f.presSnd))) D)
      rw [dnfPull_dnfPull]
      rfl)

/-- **The compositor is a natural transformation** from the
pair-of-decorations functor to the composite-decoration functor: the
transport of the variable-sharing (and, on the nose, the
parameter-setting) mode, as a natural transformation, literally.  The
naturality field is `share_transport_boxplus`. -/
def shareBoxplus (El : Type u) : pairDec El ⟶ compDec El where
  app X := TypeCat.ofHom fun D => dnfBoxplus D.1 D.2
  naturality {X Y} f := by
    apply TypeCat.Hom.ext
    show TypeCat.Fun.mk _ = TypeCat.Fun.mk _
    refine congrArg TypeCat.Fun.mk (funext fun D => ?_)
    exact (share_transport_boxplus X.fst X.snd Y.fst Y.snd
      f.presFst f.presSnd D.1 D.2).symm

/-! ## The assume–guarantee slack arithmetic

The genuinely set-mode-specific semantics: certificates transport
across a set wire by spec-to-spec entailment *with slack*, and the
slack is recomputed additively.  These lemmas are that arithmetic's
soundness at the semantic stratum: the compositor is monotone, and
constant slack rides it additively. -/

section Slack

variable {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}

/-- The compositor is monotone in both arguments (pointwise order of
penalty functionals): entailment transports across a wiring. -/
theorem boxplus_mono {u₁ v₁ : Pen (Pat.Tot M)} {u₂ v₂ : Pen (Pat.Tot N)}
    (h₁ : u₁ ≤ v₁) (h₂ : u₂ ≤ v₂) :
    boxplus u₁ u₂ ≤ boxplus v₁ v₂ :=
  fun ν => add_le_add (h₁ (ν.push (Pat.compFst M N))) (h₂ (ν.push (Pat.compSnd M N)))

/-- Constant slack rides the compositor additively. -/
theorem boxplus_add_const (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N))
    (ε₁ ε₂ : ℝ≥0∞) :
    boxplus (u₁ + fun _ => ε₁) (u₂ + fun _ => ε₂)
      = boxplus u₁ u₂ + fun _ => ε₁ + ε₂ :=
  funext fun ν => by
    show (u₁ _ + ε₁) + (u₂ _ + ε₂) = (u₁ _ + u₂ _) + (ε₁ + ε₂)
    exact add_add_add_comm _ _ _ _

/-- **The assume–guarantee slack square**: if each component's penalty
entails its target with slack, the composite entails the composite
target with the *sum* of the slacks — recomputing slack additively
across a set wire is sound. -/
theorem boxplus_le_slack {u₁ v₁ : Pen (Pat.Tot M)} {u₂ v₂ : Pen (Pat.Tot N)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : u₁ ≤ v₁ + fun _ => ε₁) (h₂ : u₂ ≤ v₂ + fun _ => ε₂) :
    boxplus u₁ u₂ ≤ boxplus v₁ v₂ + fun _ => ε₁ + ε₂ := by
  have h := boxplus_mono h₁ h₂
  rwa [boxplus_add_const] at h

/-- The slack square at the semantic universe's atom stratum: floors
of composite atoms obey the additive slack arithmetic. -/
theorem atomBoxplus_floor_le_slack
    {a₁ b₁ : SpecAtom (Joint (Pat.Tot M))}
    {a₂ b₂ : SpecAtom (Joint (Pat.Tot N))} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : a₁.floor ≤ b₁.floor + fun _ => ε₁)
    (h₂ : a₂.floor ≤ b₂.floor + fun _ => ε₂) :
    (atomBoxplus a₁ a₂).floor
      ≤ (atomBoxplus b₁ b₂).floor + fun _ => ε₁ + ε₂ :=
  boxplus_le_slack h₁ h₂

end Slack

/-! ## Mode switching: the statics, and only the statics

The switch composite's static interface, its per-location transports,
and their naturality in component renames.  The supervisory species
(guarded / rate / forced) compose behaviors in time, not interfaces in
space; their semantics is generator-stratum content and no
spec-class-level composition law is asserted for them here. -/

section Switch

variable {ι : Type u}

/-- The shared-nothing roster object of a component family: the
disjoint union of the components' wires (its state space is the
product of the component state spaces). -/
def rosterObj (F : ι → WireSpan El) : WireSpan El :=
  ⟨Σ i, (F i).wires⟩

/-- The roster inclusion of one component's wires. -/
def rosterIncl (F : ι → WireSpan El) (i : ι) : F i ⟶ rosterObj F :=
  fun w => ⟨i, w⟩

/-- The mode-switching composite's static interface: one supervisory
**location wire** (`none`) plus the roster's wires (`some`).  The
location wire's value encodes the active location; the untyped stratum
deliberately does not fix the encoding, and nothing below consumes
it — the machine-checked face of the switching content (species,
edges) living at the generator stratum, not here. -/
def switchObj (F : ι → WireSpan El) : WireSpan El :=
  ⟨Option (Σ i, (F i).wires)⟩

/-- The static inclusion of one component into the switch composite. -/
def switchIncl (F : ι → WireSpan El) (i : ι) : F i ⟶ switchObj F :=
  fun w => some ⟨i, w⟩

/-- The roster embeds in the switch composite (everything but the
location wire). -/
def switchRoster (F : ι → WireSpan El) : rosterObj F ⟶ switchObj F :=
  fun w => some w

/-- The switch inclusion factors through the roster: the location wire
is genuinely extra structure, not a re-reading of component wires. -/
theorem switchIncl_factor (F : ι → WireSpan El) (i : ι) :
    switchIncl F i = rosterIncl F i ≫ switchRoster F := rfl

/-- The action of per-component renames on the switch composite,
fixing the location wire. -/
def switchMap {F G : ι → WireSpan El} (ρ : ∀ i, F i ⟶ G i) :
    switchObj F ⟶ switchObj G :=
  Option.map fun p => ⟨p.1, ρ p.1 p.2⟩

/-- `switchMap` preserves identities. -/
theorem switchMap_id (F : ι → WireSpan El) :
    switchMap (fun i => 𝟙 (F i)) = 𝟙 (switchObj F) :=
  funext fun w => by cases w <;> rfl

/-- `switchMap` preserves composition. -/
theorem switchMap_comp {F G H : ι → WireSpan El}
    (ρ : ∀ i, F i ⟶ G i) (τ : ∀ i, G i ⟶ H i) :
    switchMap (fun i => ρ i ≫ τ i) = switchMap ρ ≫ switchMap τ :=
  funext fun w => by cases w <;> rfl

/-- **The switch inclusions are natural in component renames.** -/
theorem switchIncl_natural {F G : ι → WireSpan El}
    (ρ : ∀ i, F i ⟶ G i) (i : ι) :
    switchIncl F i ≫ switchMap ρ = ρ i ≫ switchIncl G i := rfl

/-- Per-location spec transport into the switch composite is natural
in component renames: transporting into the composite and renaming
there equals renaming the component and transporting. -/
theorem dnfPull_switch_natural {F G : ι → WireSpan El}
    (ρ : ∀ i, F i ⟶ G i) (i : ι) (D : DnfSpec (F i)) :
    dnfPull (res (switchMap ρ)) (dnfPull (res (switchIncl F i)) D)
      = dnfPull (res (switchIncl G i)) (dnfPull (res (ρ i)) D) := by
  rw [dnfPull_dnfPull, dnfPull_dnfPull]
  rfl

end Switch

end

end WiringModes

end SuFunctor
