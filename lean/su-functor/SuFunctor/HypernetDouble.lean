import SuFunctor.HypernetInclusion
import DoubleCat.GrothendieckBase

/-! # The double category of open hypernets, and the packaged inclusion

`SuFunctor.HypernetInclusion` proves the four transformation laws of the
possibilistic inclusion θ — exactly, as standalone theorems.  This module
packages them: it constructs the pseudo double category `HNet` of open
hypernets at the content-addressed stratum, exhibits θ as a
`TightTransformation` over the state-family base change, and produces the
inclusion

  `hnetInclusion : HNet ty → SingleSiteSemanticUniverse ElVal`

as a lax double functor by the base-change Grothendieck machinery
(`CategoryTheory.SpanValued.bmap`): a functor over the base change
(`hnetInclusion_proj`) that preserves the canonical opcartesian lifts of
the two elements projections on the nose (`hnetInclusion_pushGLoose`) —
the split-opcleavage preservation of the decorated-cospan picture.

## The stratum, and the shape of the base

Wire identity is content-addressed: names are **rigid designators** — a
wire's identifier is derived from its content, so distinct names denote
distinct wires and no capture-avoiding renaming is ever required.  The
tight direction of the packaged base is therefore *inclusion of wire
rosters*, not renaming: `AlignedCtx` has rosters as objects, inclusions
as tight arrows, the aligned cospans of `SuFunctor.HypernetInclusion` as
loose arrows, and apex inclusions as cells.  Cells are subsingletons, so
every coherence law of the base holds by proof irrelevance — in
particular the loose-wise composition of cells, which for *renaming*
cells over union apexes would require a copairing that representable
name collisions refuse (the packaging boundary discussed in
`SuFunctor.HypernetInclusion`), exists here uniquely: the inclusion of a
union into a union.  Renaming cells at full generality remain covered by
the standalone `theta_rename`; the packaged base is the stratum on which
content-addressed hypernets actually compose.

## Laxity, located honestly

The base change `stateBase` (rosters to conformant-state families) is a
**genuinely lax** double functor, and both components of its laxity are
semantically meaningful:

* Its compositor is the *split* of a union-apex state into an agreeing
  pair — total on all representations, because the wiring base's cells
  act contravariantly on states.  It is invertible exactly on the
  seam-disjoint locus (`hnetInclusion_laxComp_isInvertible`): the union
  of two apexes is their pushout precisely when they overlap only in
  the shared boundary, which is what distinct content addresses
  guarantee for encoded hypernets.  Off the locus the inverse merge
  does not exist, and the functor is honestly lax.
* Its unit comparison reads a conformant roster state as a diagonal
  state pair; the reverse direction would have to conjure conformance
  for an arbitrary state, so the comparison has no inverse.  This is
  conformance-pinning, the same shape as the profile-pinning unit of
  `SuFunctor.Spacetime.profiledEmbed`: typing lives in the pattern
  carrier, and forgetting it is a genuine constraint, not a defect.

θ's own comparison data is exact throughout — every decoration
condition below is discharged by one of the landed equalities
(`theta_unit`, `theta_comp`, `theta_rename`, `vacDnf_dnfPull`), never by
a comparison cell.

## Main definitions and results

* `AlignedCtx`, with its `PseudoDoubleCategory` instance: rosters,
  inclusions, aligned looses, apex-inclusion cells.
* `stateBase : LaxDoubleFunctor AlignedCtx (WireSpan ElVal)` — the
  state-family base change.
* `hnetFunctor : SpanValued AlignedCtx` — the decoration functor: fibres
  are type-consistent, apex-supported application lists; the compositor
  is block concatenation; the unit is the empty diagram.
* `HNet ty := SpanValued.Grothendieck (hnetFunctor ty)` — **the double
  category of open hypernets**: objects are wire rosters; loose arrows
  are aligned cospans decorated with a wiring diagram on the apex;
  loose composition is union of apexes with block concatenation.
  Pseudo double category by the generic construction; its projection to
  `AlignedCtx` is a discrete double opfibration
  (`hnetProj_isDiscreteOpfibration`).
* `hnetTheta` — the possibilistic coupling, packaged as a tight
  transformation over the base change.
* `hnetInclusion := SpanValued.bmap (stateBase ty) (hnetTheta ty)` —
  **the inclusion of open hypernets into the semantic universe**, with
  `hnetInclusion_proj`, `hnetInclusion_pushGLoose`,
  `hnetInclusion_laxComp_isInvertible` (the compositor laxators invert
  on the seam-disjoint locus), and `hnetInclusion_dec_eq_iff` (the
  kernel on decorations is extensional equivalence of admissible
  regions — the inclusion is deliberately non-faithful).

## References

* B. Fong, *Decorated cospans*, Theory Appl. Categ. 30 (2015), 1096–1120.
* E. Patterson, *Structured and decorated cospans from the viewpoint of
  double category theory*, arXiv:2304.00447 (2023).
* G.S.H. Cruttwell, M. Lambert, D. Pronk, M. Szyld, *Double fibrations*,
  Theory Appl. Categ. 38 (2022), 1326–1394.
-/

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PPLC
open SuFunctor.Plain SuFunctor.Universe
open PseudoDoubleCategoryStruct
open scoped NNReal ENNReal

/-! ## The rigid base: rosters, inclusions, aligned looses -/

/-- A content-addressed wire context: a finite roster of wire names.
On a content-addressed namespace, names are rigid designators, so the
structure-preserving maps of contexts are the inclusions. -/
structure AlignedCtx : Type where
  /-- The wire roster. -/
  roster : Finset Wire

namespace AlignedCtx

/-- Tight arrows are roster inclusions.  All category laws are proof
irrelevance. -/
instance : Category AlignedCtx where
  Hom X Y := PLift (X.roster ⊆ Y.roster)
  id X := ⟨Finset.Subset.refl X.roster⟩
  comp φ ψ := ⟨φ.down.trans ψ.down⟩

instance homSubsingleton (X Y : AlignedCtx) : Subsingleton (X ⟶ Y) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The pseudo double category structure: loose arrows are the aligned
cospans of `SuFunctor.HypernetInclusion` (an apex roster containing both
feet), cells are apex inclusions, loose composition is union of apexes.
Every cell is a subsingleton. -/
instance instPseudoDoubleCategoryStruct :
    PseudoDoubleCategoryStruct AlignedCtx where
  Loose X Y := AlignedLoose X.roster Y.roster
  Cell M N _ _ := PLift (M.apex ⊆ N.apex)
  vId _ := ⟨Finset.Subset.refl _⟩
  vComp α β := ⟨α.down.trans β.down⟩
  lId X := AlignedLoose.unit X.roster
  lComp M N := M.seq N
  hId φ := ⟨φ.down⟩
  hComp α β := ⟨Finset.union_subset_union α.down β.down⟩
  lAssoc _ _ _ :=
    ⟨Finset.union_subset
      (Finset.union_subset Finset.subset_union_left
        (Finset.subset_union_left.trans Finset.subset_union_right))
      (Finset.subset_union_right.trans Finset.subset_union_right)⟩
  lAssocInv _ _ _ :=
    ⟨Finset.union_subset
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (Finset.union_subset
        (Finset.subset_union_right.trans Finset.subset_union_left)
        Finset.subset_union_right)⟩
  lLeftUnitor m := ⟨Finset.union_subset m.left_le (Finset.Subset.refl _)⟩
  lLeftUnitorInv _ := ⟨Finset.subset_union_right⟩
  lRightUnitor m := ⟨Finset.union_subset (Finset.Subset.refl _) m.right_le⟩
  lRightUnitorInv _ := ⟨Finset.subset_union_left⟩

instance cellSubsingleton {X Y X' Y' : AlignedCtx}
    (M : Loose X Y) (N : Loose X' Y') (φ : X ⟶ X') (ψ : Y ⟶ Y') :
    Subsingleton (Cell M N φ ψ) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The axioms: every equation is between elements of a subsingleton
cell type. -/
instance instPseudoDoubleCategory : PseudoDoubleCategory AlignedCtx where
  vId_vComp _ := Subsingleton.elim _ _
  vComp_vId _ := Subsingleton.elim _ _
  vComp_assoc _ _ _ := Subsingleton.elim _ _
  hId_id _ := Subsingleton.elim _ _
  hId_comp _ _ := Subsingleton.elim _ _
  hComp_vId _ _ := Subsingleton.elim _ _
  interchange _ _ _ _ := Subsingleton.elim _ _
  lAssoc_natural _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_natural _ := Subsingleton.elim _ _
  lRightUnitor_natural _ := Subsingleton.elim _ _
  lAssoc_lAssocInv _ _ _ := Subsingleton.elim _ _
  lAssocInv_lAssoc _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_lLeftUnitorInv _ := Subsingleton.elim _ _
  lLeftUnitorInv_lLeftUnitor _ := Subsingleton.elim _ _
  lRightUnitor_lRightUnitorInv _ := Subsingleton.elim _ _
  lRightUnitorInv_lRightUnitor _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

end AlignedCtx

variable (ty : Wire → Option TensorType)

/-! ## Extensionality helpers for composite state families -/

instance {p : Prop} : Subsingleton (PLift p) := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

instance {α : Type _} [Subsingleton α] : Subsingleton (ULift α) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => congrArg ULift.up (Subsingleton.elim a b)⟩

/-- Extensionality for elements of a composite pattern. -/
theorem patComp_ext {A B C : WireSpan ElVal} {M : Pat A B} {N : Pat B C}
    {x : states A} {z : states C} {p q : Pat.comp M N x z}
    (hy : p.1 = q.1) (hm : p.2.1 ≍ q.2.1) (hn : p.2.2 ≍ q.2.2) : p = q := by
  obtain ⟨y, pm, pn⟩ := p
  obtain ⟨y', qm, qn⟩ := q
  cases hy
  obtain rfl : pm = qm := eq_of_heq hm
  obtain rfl : pn = qn := eq_of_heq hn
  rfl

/-- Heterogeneous extensionality for aligned state-family elements
across equalities of their boundary states. -/
theorem alignedPat_heq {W V : Finset Wire} {m : AlignedLoose W V}
    {x x' : states (ctxIface W)} {y y' : states (ctxIface V)}
    (hx : x = x') (hy : y = y')
    {s : alignedPat ty m x y} {s' : alignedPat ty m x' y'}
    (h : s.1 = s'.1) : s ≍ s' := by
  subst hx; subst hy
  exact heq_of_eq (Subtype.ext h)

/-! ## The state-family base change -/

/-- The state transport of an apex inclusion: restrict a conformant
state of the larger apex to the smaller one, over the boundary
restrictions.  (The contravariant cell action of the wiring base.) -/
def inclCell {X Y X' Y' : AlignedCtx}
    {m : Loose X Y} {n : Loose X' Y'} {φ : X ⟶ X'} {ψ : Y ⟶ Y'}
    (c : Cell m n φ ψ) (x : states (ctxIface X'.roster))
    (y : states (ctxIface Y'.roster)) (s : alignedPat ty n x y) :
    alignedPat ty m (fun w => x ⟨w.1, φ.down w.2⟩)
      (fun w => y ⟨w.1, ψ.down w.2⟩) :=
  ⟨restrictState c.down s.1,
   s.2.1.restrict ty c.down,
   fun w => s.2.2.1 ⟨w.1, φ.down w.2⟩,
   fun w => s.2.2.2 ⟨w.1, ψ.down w.2⟩⟩

/-- The fibred split of a union-apex state into an agreeing pair: the
compositor of the base change, total on all representations (the
fibrewise form of `splitTot`). -/
def splitCell {X Y Z : AlignedCtx} (m : Loose X Y) (n : Loose Y Z)
    (x : states (ctxIface X.roster)) (z : states (ctxIface Z.roster))
    (s : alignedPat ty (m.seq n) x z) :
    Pat.comp (alignedPat ty m) (alignedPat ty n) x z :=
  ⟨fun w => s.1 ⟨w.1, Finset.subset_union_left (m.right_le w.2)⟩,
   ⟨restrictState Finset.subset_union_left s.1,
     s.2.1.restrict ty Finset.subset_union_left,
     fun w => s.2.2.1 w,
     fun _ => rfl⟩,
   ⟨restrictState Finset.subset_union_right s.1,
     s.2.1.restrict ty Finset.subset_union_right,
     fun _ => rfl,
     fun w => s.2.2.2 w⟩⟩

/-- **The state-family base change**: rosters to their conformant-state
interfaces, aligned looses to their state families, apex inclusions to
state restrictions.  Genuinely lax: the compositor is the (total) split,
invertible exactly on the seam-disjoint locus; the unit comparison is
conformance-pinning (cf. the profile-pinning unit of
`SuFunctor.Spacetime.profiledEmbed`). -/
def stateBase : LaxDoubleFunctor AlignedCtx (WireSpan ElVal) where
  toFunctor :=
    { obj := fun X => ctxIface X.roster
      map := fun φ w => ⟨w.1, φ.down w.2⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  mapLoose m := alignedPat ty m
  mapCell c := fun x y s => inclCell ty c x y s
  mapCell_vId _ := rfl
  mapCell_vComp _ _ := rfl
  laxComp m n := fun x z s => splitCell ty m n x z s
  laxId _ := fun x y s =>
    ⟨⟨funext fun w => (s.2.2.1 w).symm.trans (s.2.2.2 w)⟩⟩
  laxComp_natural _ _ := rfl
  laxId_natural _ := rfl
  laxComp_assoc _ _ _ := rfl
  laxComp_leftUnitor m := by
    funext x y s
    refine patComp_ext (funext fun w => s.2.2.1 w)
      (Subsingleton.helim
        (congrArg (fun t => ULift (PLift (x = t)))
          (funext fun w => s.2.2.1 w)) _ _)
      (alignedPat_heq ty (funext fun w => s.2.2.1 w) rfl rfl)
  laxComp_rightUnitor m := by
    funext x y s
    refine patComp_ext (funext fun w => s.2.2.2 w)
      (alignedPat_heq ty rfl (funext fun w => s.2.2.2 w) rfl)
      (Subsingleton.helim
        (congrArg (fun t => ULift (PLift (t = y)))
          (funext fun w => s.2.2.2 w)) _ _)

/-- The compositor's state transport is the landed total split. -/
theorem tot_stateBase_laxComp {X Y Z : AlignedCtx}
    (m : Loose X Y) (n : Loose Y Z) :
    PatCell.tot ((stateBase ty).laxComp m n) = splitTot ty m n := rfl

/-- The unit comparison's state transport is the landed carrier
comparison. -/
theorem tot_stateBase_laxId (X : AlignedCtx) :
    PatCell.tot ((stateBase ty).laxId X) = idTot ty X.roster := rfl

/-! ## The decoration functor and the double category of open hypernets -/

/-- The decoration set of an aligned loose: raw wiring diagrams on its
apex — finite application lists, type-consistent at the apex table and
wire-supported on the apex.  No linearity and no acyclicity: the raw
stratum, on which the possibilistic face composes for the full
calculus. -/
abbrev HDec {X Y : Finset Wire} (m : AlignedLoose X Y) : Type :=
  {T : List PrimApp //
    (∀ a ∈ T, a.TypeConsistent (tableOn ty m.apex)) ∧
    ∀ a ∈ T, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex}

namespace HDec

variable {X Y Z X' Y' : Finset Wire}

/-- The apex table extends along an apex inclusion. -/
theorem tableOn_le {W W' : Finset Wire} (h : W ⊆ W') :
    ∀ w τ, tableOn ty W w = some τ → tableOn ty W' w = some τ :=
  fun w τ hw => by
    have hmem : w ∈ W := mem_of_tableOn_some ty hw
    rw [tableOn_pos ty (h hmem), ← tableOn_pos ty hmem]
    exact hw

/-- Weakening: the same diagram, read on a larger apex. -/
def weaken {m : AlignedLoose X Y} {n : AlignedLoose X' Y'}
    (h : m.apex ⊆ n.apex) (T : HDec ty m) : HDec ty n :=
  ⟨T.1,
   fun a ha => (T.2.1 a ha).mono (tableOn_le ty h),
   fun a ha w hw => h (T.2.2 a ha w hw)⟩

/-- Block concatenation: the compositor of the decoration functor. -/
def glue {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    (T₁ : HDec ty m) (T₂ : HDec ty n) : HDec ty (m.seq n) :=
  ⟨T₁.1 ++ T₂.1,
   fun a ha => by
     rcases List.mem_append.mp ha with h | h
     · exact (T₁.2.1 a h).mono (tableOn_le ty Finset.subset_union_left)
     · exact (T₂.2.1 a h).mono (tableOn_le ty Finset.subset_union_right),
   fun a ha w hw => by
     rcases List.mem_append.mp ha with h | h
     · exact Finset.subset_union_left (T₁.2.2 a h w hw)
     · exact Finset.subset_union_right (T₂.2.2 a h w hw)⟩

/-- The empty diagram: the unit of the decoration functor. -/
def empty (X : Finset Wire) : HDec ty (AlignedLoose.unit X) :=
  ⟨[], by simp⟩

end HDec

/-- **The decoration functor**: a span-valued lax double functor on the
rigid base, with wiring-diagram fibres — the `SpanValued` instantiation
of the decorated-cospan picture at the content-addressed stratum.
Objects carry no decoration; loose fibres are constant in the endpoint
points (decorations do not depend on states). -/
def hnetFunctor : SpanValued.{0, 0, 0, 0, 0} AlignedCtx where
  toFunctor :=
    { obj := fun _ => PUnit
      map := fun _ => 𝟙 PUnit
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  mapLoose m := fun _ _ => HDec ty m
  mapCell c := fun _ _ T => HDec.weaken ty c.down T
  mapCell_vId _ := rfl
  mapCell_vComp _ _ := rfl
  laxComp m n := fun _ _ s => HDec.glue ty s.2.1 s.2.2
  laxId X := fun _ _ _ => HDec.empty ty X.roster
  laxComp_natural _ _ := rfl
  laxId_natural _ := rfl
  laxComp_assoc m n p := by
    funext x w s
    exact Subtype.ext (List.append_assoc _ _ _)
  laxComp_leftUnitor m := by
    funext x y s
    obtain ⟨y', e, T⟩ := s
    obtain ⟨⟨rfl⟩⟩ := e
    rfl
  laxComp_rightUnitor m := by
    funext x y s
    obtain ⟨y', T, e⟩ := s
    obtain ⟨⟨rfl⟩⟩ := e
    exact Subtype.ext (List.append_nil _)

/-- **The double category of open hypernets**, content-addressed
stratum: the double category of elements of the decoration functor.
Objects are wire rosters; loose arrows are aligned cospans decorated
with a wiring diagram on the apex; loose composition is union of apexes
with block concatenation of diagrams; cells are apex inclusions
transporting the diagram by weakening. -/
abbrev HNet := SpanValued.Grothendieck (hnetFunctor ty)

/-- The double category of open hypernets is a pseudo double category,
by the generic construction. -/
theorem hnet_pseudoDoubleCategory :
    ∃ _ : PseudoDoubleCategory (HNet ty), True :=
  ⟨inferInstance, trivial⟩

/-- The projection of the double category of open hypernets to the
rigid base. -/
def hnetProj : LaxDoubleFunctor (HNet ty) AlignedCtx :=
  SpanValued.proj (hnetFunctor ty)

/-- The projection is pseudo. -/
theorem hnetProj_isPseudo : (hnetProj ty).IsPseudo :=
  SpanValued.proj_isPseudo (hnetFunctor ty)

/-- The projection is a discrete double opfibration: decorated loose
arrows push forward uniquely along base cells — the split opcleavage of
the decorated-cospan picture, by the generic theorem. -/
theorem hnetProj_isDiscreteOpfibration :
    IsDiscreteDoubleOpfibration (hnetProj ty) :=
  SpanValued.proj_isDiscreteOpfibration (hnetFunctor ty)

/-! ## The possibilistic coupling, packaged -/

/-- The identity-map renaming cell of an apex inclusion: the bridge from
inclusion cells to the standalone rename-transport theorems. -/
def inclusionAlignedCell {X Y X' Y' : AlignedCtx}
    {m : Loose X Y} {n : Loose X' Y'} {φ : X ⟶ X'} {ψ : Y ⟶ Y'}
    (c : Cell m n φ ψ) : AlignedCell ty m n where
  map := id
  mem := fun _ hw => c.down hw
  ty_eq := fun _ _ => rfl
  left_mem := fun _ hw => φ.down hw
  right_mem := fun _ hw => ψ.down hw

@[simp] theorem inclusionAlignedCell_map {X Y X' Y' : AlignedCtx}
    {m : Loose X Y} {n : Loose X' Y'} {φ : X ⟶ X'} {ψ : Y ⟶ Y'}
    (c : Cell m n φ ψ) : (inclusionAlignedCell ty c).map = id := rfl

/-- The state transport of an apex-inclusion cell is the landed rename
transport at the identity map. -/
theorem tot_stateBase_mapCell {X Y X' Y' : AlignedCtx}
    {m : Loose X Y} {n : Loose X' Y'} {φ : X ⟶ X'} {ψ : Y ⟶ Y'}
    (c : Cell m n φ ψ) :
    PatCell.tot ((stateBase ty).mapCell c)
      = renameTot ty (inclusionAlignedCell ty c) := rfl

/-- A diagram is fixed by the identity renaming. -/
theorem map_rename_id (T : List PrimApp) :
    T.map (PrimApp.rename id) = T := by
  rw [show PrimApp.rename id = id from funext PrimApp.rename_id, List.map_id]

/-- The loose component's naturality core: the austere coupling of a
weakened diagram is the transport of the austere coupling along the
inclusion's state restriction — `theta_rename` at the identity map. -/
theorem austere_weaken {X Y X' Y' : AlignedCtx} {m : Loose X Y}
    {n : Loose X' Y'} {φ : X ⟶ X'} {ψ : Y ⟶ Y'} (α : Cell m n φ ψ)
    (T : HDec ty m) :
    austereDnf ty n (HDec.weaken ty α.down T).1
      = dnfPull (renameTot ty (inclusionAlignedCell ty α))
          (austereDnf ty m T.1) := by
  rw [theta_rename ty (inclusionAlignedCell ty α) T.1 T.2.1 T.2.2,
    inclusionAlignedCell_map, map_rename_id]
  rfl

/-- The loose component's compositor core: the austere coupling of a
glued diagram is the semantic universe's compositor of the parts',
transported along the split — `theta_comp` in the packaged
vocabulary. -/
theorem austere_glue {X Y Z : AlignedCtx} (m : Loose X Y) (n : Loose Y Z)
    (T₁ : HDec ty m) (T₂ : HDec ty n) :
    austereDnf ty (m.seq n) (HDec.glue ty T₁ T₂).1
      = dnfPull (splitTot ty m n)
          (dnfBoxplus (austereDnf ty m T₁.1) (austereDnf ty n T₂.1)) :=
  (theta_comp ty m n T₁.1 T₂.1 T₁.2.1 T₁.2.2 T₂.2.1 T₂.2.2).symm

/-- The loose component's unit core: the austere coupling of the empty
diagram is the semantic universe's unit, transported along the carrier
comparison — `theta_unit` in the packaged vocabulary. -/
theorem austere_empty (X : AlignedCtx) :
    austereDnf ty (AlignedLoose.unit X.roster) (HDec.empty ty X.roster).1
      = dnfPull (idTot ty X.roster) (dnfUnit (ctxIface X.roster)) :=
  (theta_unit ty X.roster).symm

/-- Naturality of the vacuous component: the vacuous presentation is a
fixed point of every transport (`vacDnf_dnfPull`, in hom form). -/
theorem vac_naturality {X X' : AlignedCtx} (φ : X ⟶ X') :
    (hnetFunctor ty).map φ ≫
        (TypeCat.ofHom fun _ =>
          vacDnf (Plain.Joint (states (ctxIface X'.roster))))
      = (TypeCat.ofHom fun _ =>
          vacDnf (Plain.Joint (states (ctxIface X.roster))))
        ≫ ((stateBase ty).comp (dnfSpecFunctor ElVal)).map φ := by
  ext u
  exact (vacDnf_dnfPull (res ((stateBase ty).map φ))).symm

/-- The composite functor's compositor, stripped of its boundary cast:
its value is the semantic universe's compositor pulled along the
split. -/
theorem comp_laxComp_strip {X Y Z : AlignedCtx} (m : Loose X Y)
    (n : Loose Y Z)
    (a : ((stateBase ty).comp (dnfSpecFunctor ElVal)).obj X)
    (c : ((stateBase ty).comp (dnfSpecFunctor ElVal)).obj Z)
    (s : (((stateBase ty).comp (dnfSpecFunctor ElVal)).mapLoose m ⊙
        ((stateBase ty).comp (dnfSpecFunctor ElVal)).mapLoose n) a c) :
    (((stateBase ty).comp (dnfSpecFunctor ElVal)).laxComp m n) a c s
      ≍ dnfPull (splitTot ty m n) (dnfBoxplus s.2.1 s.2.2) := by
  have h : (((stateBase ty).comp (dnfSpecFunctor ElVal)).laxComp m n)
      ≍ ((dnfSpecFunctor ElVal).laxComp ((stateBase ty).mapLoose m)
            ((stateBase ty).mapLoose n) ≫ᵥ
          (dnfSpecFunctor ElVal).mapCell ((stateBase ty).laxComp m n)) :=
    Cell.cast_heq _ _ _
  exact DepSpan.FamCell.heq_apply (by simp) (by simp) h a c s

/-- The composite functor's unit comparison, stripped of its boundary
cast: its value is the semantic universe's unit pulled along the
carrier comparison. -/
theorem comp_laxId_strip (X : AlignedCtx)
    (a b : ((stateBase ty).comp (dnfSpecFunctor ElVal)).obj X)
    (e : (𝟙ˡ (((stateBase ty).comp (dnfSpecFunctor ElVal)).obj X)) a b) :
    (((stateBase ty).comp (dnfSpecFunctor ElVal)).laxId X) a b e
      ≍ dnfPull (idTot ty X.roster) (dnfUnit (ctxIface X.roster)) := by
  have h : (((stateBase ty).comp (dnfSpecFunctor ElVal)).laxId X)
      ≍ ((dnfSpecFunctor ElVal).laxId ((stateBase ty).obj X) ≫ᵥ
          (dnfSpecFunctor ElVal).mapCell ((stateBase ty).laxId X)) :=
    Cell.cast_heq _ _ _
  exact DepSpan.FamCell.heq_apply (by simp) (by simp) h a b e

/-- **The possibilistic coupling, as a tight transformation** over the
state-family base change: the object component is the vacuous
presentation, the loose component is the austere possibilistic coupling
of the diagram's admissible region.  Every compatibility condition is an
instance of a landed exact equality: naturality on tights is
`vacDnf_dnfPull`, naturality on cells is `theta_rename` at the
identity-map cell, compositor compatibility is `theta_comp`, and unit
compatibility is `theta_unit`. -/
def hnetTheta :
    TightTransformation (hnetFunctor ty)
      ((stateBase ty).comp (dnfSpecFunctor ElVal)) where
  app X := TypeCat.ofHom fun _ =>
    vacDnf (Plain.Joint (states (ctxIface X.roster)))
  naturality {X X'} φ := vac_naturality ty φ
  looseApp m := fun _ _ T => austereDnf ty m T.1
  looseApp_natural {X Y X' Y'} {m n} {φ ψ} α := by
    rw [Cell.eq_cast_iff_heq]
    exact DepSpan.FamCell.heq_of_apply
      (vac_naturality ty φ) (vac_naturality ty ψ)
      fun x y T => heq_of_eq (austere_weaken ty α T)
  looseApp_laxComp {X Y Z} m n := by
    rw [Cell.eq_cast_iff_heq]
    refine DepSpan.FamCell.heq_of_apply rfl rfl fun x z s => ?_
    exact (heq_of_eq (austere_glue ty m n s.2.1 s.2.2)).trans
      (comp_laxComp_strip ty m n _ _
        ⟨vacDnf (Plain.Joint (states (ctxIface Y.roster))),
          austereDnf ty m s.2.1.1, austereDnf ty n s.2.2.1⟩).symm
  looseApp_laxId X := by
    rw [Cell.eq_cast_iff_heq]
    refine DepSpan.FamCell.heq_of_apply rfl rfl fun x y e => ?_
    exact (heq_of_eq (austere_empty ty X)).trans
      (comp_laxId_strip ty X _ _ _).symm

/-! ## The packaged inclusion -/

/-- **The inclusion of open hypernets into the semantic universe**: the
base-change Grothendieck image of the possibilistic coupling.  A loose
arrow — an apex with a wiring diagram over its feet — maps to its
conformant-state pattern decorated with the austere possibilistic
coupling of the diagram's admissible region; loose composition maps to
the semantic universe's compositor by the exact law `theta_comp`. -/
def hnetInclusion : LaxDoubleFunctor (HNet ty) (SingleSiteSemanticUniverse ElVal) :=
  SpanValued.bmap (stateBase ty) (hnetTheta ty)

/-- The inclusion is a functor over the base change: the projections
intertwine. -/
theorem hnetInclusion_proj :
    (hnetInclusion ty).comp (singleSiteUniverseProj ElVal)
      = (hnetProj ty).comp (stateBase ty) :=
  SpanValued.bmap_proj (stateBase ty) (hnetTheta ty)

/-- **The inclusion preserves the split opcleavages on the nose**: the
canonical opcartesian lifts of the two elements projections — pushing a
decorated loose arrow forward along a base cell — correspond under the
inclusion.  This is the storage-license morphism of the decorated-cospan
picture, by the generic theorem. -/
theorem hnetInclusion_pushGLoose {p q : HNet ty}
    (M : SpanValued.GLoose p q) {c d : AlignedCtx} {n : Loose c d}
    {f' : p.1 ⟶ c} {g' : q.1 ⟶ d} (γ : Cell M.base n f' g') :
    SpanValued.bmapLoose (stateBase ty) (hnetTheta ty)
        (SpanValued.pushGLoose M γ) ≍
      SpanValued.pushGLoose
        (SpanValued.bmapLoose (stateBase ty) (hnetTheta ty) M)
        ((stateBase ty).mapCell γ) :=
  SpanValued.bmap_pushGLoose (stateBase ty) (hnetTheta ty) M γ

/-! ## The seam-disjoint locus: where the compositor inverts

The compositor laxator of the inclusion has the (total) split as its
base.  On the seam-disjoint locus — apex overlap contained in the shared
boundary, which is what distinct content addresses mean for encoded
hypernets — the split has the merge as a two-sided inverse, and the
laxator is invertible.  Off the locus, representable name collisions
defeat the merge, and the laxator is honestly non-invertible: the
inclusion is lax, pseudo exactly on the locus. -/

section Locus

variable {X Y Z : AlignedCtx}

/-- The fibred merge of an agreeing pair into a union-apex state, on
the seam-disjoint locus (the fibrewise form of `mergeTot`). -/
def mergeCell (m : Loose X Y) (n : Loose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y.roster)
    (x : states (ctxIface X.roster)) (z : states (ctxIface Z.roster))
    (s : Pat.comp (alignedPat ty m) (alignedPat ty n) x z) :
    alignedPat ty (m.seq n) x z :=
  ⟨fun w =>
     if h : w.1 ∈ m.apex then s.2.1.1 ⟨w.1, h⟩
     else s.2.2.1 ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩,
   by
     intro w
     by_cases h : w.1 ∈ m.apex
     · simpa [h] using s.2.1.2.1 ⟨w.1, h⟩
     · simpa [h] using s.2.2.2.1
         ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩,
   by
     intro w
     have h : w.1 ∈ m.apex := m.left_le w.2
     simpa [h] using s.2.1.2.2.1 w,
   by
     intro w
     have hn : w.1 ∈ n.apex := n.right_le w.2
     by_cases h : w.1 ∈ m.apex
     · have hY : w.1 ∈ Y.roster := hdisj w.1 h hn
       have h1 : s.2.1.1 ⟨w.1, h⟩ = s.1 ⟨w.1, hY⟩ := s.2.1.2.2.2 ⟨w.1, hY⟩
       have h2 : s.2.2.1 ⟨w.1, hn⟩ = s.1 ⟨w.1, hY⟩ := s.2.2.2.2.1 ⟨w.1, hY⟩
       have h3 : s.2.2.1 ⟨w.1, hn⟩ = z w := s.2.2.2.2.2 w
       simpa [h] using h1.trans (h2.symm.trans h3)
     · simpa [h] using s.2.2.2.2.2 w⟩

/-- Merging after splitting recovers the union-apex state. -/
theorem merge_split_cell (m : Loose X Y) (n : Loose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y.roster)
    (x : states (ctxIface X.roster)) (z : states (ctxIface Z.roster))
    (s : alignedPat ty (m.seq n) x z) :
    mergeCell ty m n hdisj x z (splitCell ty m n x z s) = s := by
  refine Subtype.ext (funext fun w => ?_)
  show (if h : w.1 ∈ m.apex
      then restrictState Finset.subset_union_left s.1 ⟨w.1, h⟩
      else restrictState Finset.subset_union_right s.1
        ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩)
    = s.1 w
  by_cases h : w.1 ∈ m.apex
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

/-- Splitting after merging recovers the agreeing pair, on the
seam-disjoint locus. -/
theorem split_merge_cell (m : Loose X Y) (n : Loose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y.roster)
    (x : states (ctxIface X.roster)) (z : states (ctxIface Z.roster))
    (s : Pat.comp (alignedPat ty m) (alignedPat ty n) x z) :
    splitCell ty m n x z (mergeCell ty m n hdisj x z s) = s := by
  have hmid : (splitCell ty m n x z (mergeCell ty m n hdisj x z s)).1
      = s.1 := by
    funext w
    show (if h : w.1 ∈ m.apex
        then s.2.1.1 ⟨w.1, h⟩
        else s.2.2.1 ⟨w.1, _⟩) = s.1 w
    rw [dif_pos (m.right_le w.2)]
    exact s.2.1.2.2.2 w
  refine patComp_ext hmid (alignedPat_heq ty rfl hmid ?_)
    (alignedPat_heq ty hmid rfl ?_)
  · funext w
    show (if h : w.1 ∈ m.apex
        then s.2.1.1 ⟨w.1, h⟩
        else s.2.2.1 ⟨w.1, _⟩) = s.2.1.1 w
    rw [dif_pos w.2]
    rfl
  · funext w
    show (if h : w.1 ∈ m.apex
        then s.2.1.1 ⟨w.1, h⟩
        else s.2.2.1 ⟨w.1, _⟩) = s.2.2.1 w
    by_cases h : w.1 ∈ m.apex
    · rw [dif_pos h]
      have hY : w.1 ∈ Y.roster := hdisj w.1 h w.2
      have h1 : s.2.1.1 ⟨w.1, h⟩ = s.1 ⟨w.1, hY⟩ := s.2.1.2.2.2 ⟨w.1, hY⟩
      have h2 : s.2.2.1 ⟨w.1, w.2⟩ = s.1 ⟨w.1, hY⟩ := s.2.2.2.2.1 ⟨w.1, hY⟩
      exact h1.trans h2.symm
    · rw [dif_neg h]
      rfl

/-- **The compositor laxators of the inclusion invert on the
seam-disjoint locus**: when two composable decorated looses overlap only
in their shared boundary, the compositor comparison cell of
`hnetInclusion` is invertible — its inverse is the merge, and the
decoration condition of the inverse transfers by generic transport.
This is the precise sense in which the content-addressed stratum makes
the inclusion's composition comparison strict: distinct content
addresses guarantee the locus, and on it the split and the merge are a
two-sided inverse pair. -/
theorem hnetInclusion_laxComp_isInvertible {p q r : HNet ty}
    (M : Loose p q) (N : Loose q r)
    (hdisj : ∀ w ∈ M.base.apex, w ∈ N.base.apex → w ∈ q.1.roster) :
    ((hnetInclusion ty).laxComp M N).IsInvertible := by
  have hsplit_merge :
      ((stateBase ty).laxComp M.base N.base) ≫ᵥ
          (fun x z s => mergeCell ty M.base N.base hdisj x z s :
            PatCell (alignedPat ty (M.base.seq N.base))
              (Pat.comp (alignedPat ty M.base) (alignedPat ty N.base))
              (𝟙 _) (𝟙 _))
        ≍ PseudoDoubleCategoryStruct.vId
            ((stateBase ty).mapLoose M.base ⊙ (stateBase ty).mapLoose N.base) :=
    heq_of_eq (funext fun x => funext fun z => funext fun s =>
      split_merge_cell ty M.base N.base hdisj x z s)
  have hmerge_split :
      (fun x z s => mergeCell ty M.base N.base hdisj x z s :
          PatCell (alignedPat ty (M.base.seq N.base))
            (Pat.comp (alignedPat ty M.base) (alignedPat ty N.base))
            (𝟙 _) (𝟙 _)) ≫ᵥ
          ((stateBase ty).laxComp M.base N.base)
        ≍ PseudoDoubleCategoryStruct.vId
            ((stateBase ty).mapLoose (M.base ⊙ N.base)) :=
    heq_of_eq (funext fun x => funext fun z => funext fun s =>
      merge_split_cell ty M.base N.base hdisj x z s)
  refine ⟨⟨fun x z s => mergeCell ty M.base N.base hdisj x z s,
    SpanValued.GCell.dec_inv
      (SpanValued.bmapLaxComp (stateBase ty) (hnetTheta ty) M N).dec
      hsplit_merge⟩, ?_, ?_⟩
  · exact Cell.eq_cast_iff_heq.mpr
      (SpanValued.GCell.heq_ext (by simp) (by simp) hsplit_merge)
  · exact Cell.eq_cast_iff_heq.mpr
      (SpanValued.GCell.heq_ext (by simp) (by simp) hmerge_split)

end Locus

/-- **The kernel of the inclusion on decorations is extensional
equivalence**: two diagrams over the same aligned loose share an image
decoration exactly when they admit the same valuations.  Syntax and its
content addressing live in the double category of open hypernets; the
semantic universe sees the relation. -/
theorem hnetInclusion_dec_eq_iff {X Y : Finset Wire}
    (m : AlignedLoose X Y) (T T' : List PrimApp) :
    austereDnf ty m T = austereDnf ty m T'
      ↔ AdmRegion ty m T = AdmRegion ty m T' :=
  austereDnf_eq_iff ty m T T'

/-! ## Axiom receipts (in-package convention: `#print axioms`) -/

end

end SuFunctor

#print axioms SuFunctor.AlignedCtx.instPseudoDoubleCategory
#print axioms SuFunctor.stateBase
#print axioms SuFunctor.hnetFunctor
#print axioms SuFunctor.hnet_pseudoDoubleCategory
#print axioms SuFunctor.hnetProj_isDiscreteOpfibration
#print axioms SuFunctor.hnetTheta
#print axioms SuFunctor.hnetInclusion
#print axioms SuFunctor.hnetInclusion_proj
#print axioms SuFunctor.hnetInclusion_pushGLoose
#print axioms SuFunctor.hnetInclusion_laxComp_isInvertible
#print axioms SuFunctor.hnetInclusion_dec_eq_iff
