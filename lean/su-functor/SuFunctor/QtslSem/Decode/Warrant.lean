import SuFunctor.QtslSem.Decode.Acceptance
import SuFunctor.QtslSem.SpecJudg
import QtslAux.QtslAliases

/-!
# The warrant route: region-warranted satisfaction through
`SpecJudgLayer`

The widened acceptance fragment — **v2 = v1 + the warrant route**,
beside the landed acceptor, which this module imports and does not
modify.  A satisfaction claim may now close by the `QSatFromRegion`
record shape (the dissolution of the former rule: not a rule node —
the `QSat` record carrying its own closing demands): a ternary `qsat_warrant`
citation — (f, sat, warrant) on the event-4 wire — naming which
safety-face component it warrants, the root tie (`ax/qsat/root_tie`,
refuse-mode at event 4 — the cited component IS the `SInit` image of
the cited row's formula), face membership (`ax/wf/qsat_warrant_member`
— the cited component is among the claimed spec's safety faces), the
init-membership demand (`ax/wf/qsat_init` — a `qtsl_init_member`
relation row indexed by exactly the cited row's region atom and the
claim's subject, (region, sys) on the wire), and
the membership evaluation leaf through the landed `acceptGroundLeaf`
(the `pConstExact` class — the carried validity is built through the
promoted functor at acceptance, exactly the eval-leaf posture).

**The honesty split, stated where it binds.**  Unconditional content:
the route checks (all kernel-decidable — every refusal fixture below is
a `decide`) and the membership leaf's leaf-stratum validity (carried,
`promoteThin`).  Conditional content: the cited region row's own claim
(its concluding proof is opaque at this stratum — proof-node species
are the S5 seam) and the deep reading of the leaf as region membership
(region atoms ride as sort-checked references; the exact-ℚ tie is
`rootEval_sublevel_iff`'s, class-stratum campaign).  The conditional
part is not a bare hypothesis box: an accepted warrant **resolves**,
for any class assignment over any wiring pattern, its region hypothesis
to the claim conclusion through `SpecJudgLayer` — the membership cell
composed with the warrant cell in the thin carrier, the checked root
tie consumed in the retyping — and the pointwise face of that
resolution is literally `sound_QSatFromRegion` (∀-elimination, the
QtslAliases stock) at `X := Pen (Pat.Tot M)`.  Decoded warrant
citations resolving through `SpecJudgLayer` to their soundness lemma.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-! ## The accepted warrant -/

/-- An accepted region-warranted satisfaction claim: the claim's
subject, the cited safety-face component and its `SInit` argument φ,
the resolved `QRegionSat` row, the **root tie as a proof field** (the
E2 posture: an acceptor whose tie check disagrees with its carried tie
cannot be built), and the membership leaf — an `AcceptedLeaf`, so its
validity was carried through the promoted functor at acceptance and
every leaf-stratum theorem applies to it verbatim. -/
structure AcceptedWarrant where
  /-- The `QSat` element this warrant closes. -/
  elem : Nat
  /-- The claim's subject (`QSat/sys`). -/
  sysElem : Nat
  /-- The cited safety-face component (the warrant row's `f`), found
  among the claimed spec's decoded faces — the face-membership check
  (`ax/wf/qsat_warrant_member`) is this find. -/
  fElem : Nat
  /-- The face's `SInit` argument φ — the event-4 reading of the
  retired "spec root". -/
  phiElem : Nat
  /-- The resolved region-satisfaction row the citation names. -/
  region : QRegionSatVal
  /-- The root tie, checked at acceptance (`ax/qsat/root_tie`,
  refuse-mode at event 4: `f = SInit(region.formula)`). -/
  root_tie : region.formula = phiElem
  /-- The membership leaf (`ax/wf/qsat_init`'s witness), accepted
  through the landed `acceptGroundLeaf` — carried validity included. -/
  leaf : AcceptedLeaf

/-- An entry of the widened claim roster: an eval-routed leaf or a
region-warranted claim. -/
abbrev QEntry := Sum AcceptedLeaf AcceptedWarrant

/-! ## The route -/

/-- Accept one region-warranted claim: resolve the citation in the
decoded region rows (fail-closed), find the cited component among the
claimed spec's decoded safety faces (`ax/wf/qsat_warrant_member` — a
face from someone else's spec refuses), demand its `SInit` form and
check the root tie against the cited row's formula (`ax/qsat/root_tie`
at event 4: the memo §3.5 mutant locus, re-sorted), check the
init-membership demand row indexed by exactly (cited region atom,
subject) — the event-4 wire order — then accept the membership leaf
through the landed route.  The checks precede the leaf so that every
refusal path is pure table-and-match work for the kernel. -/
def acceptWarrantSat (tb : QRowTbls) (regs : List QRegionSatVal)
    (sat : QSatVal) (f w p : Nat) : Option AcceptedWarrant :=
  match regs.find? (fun r => r.elem == w) with
  | none => none
  | some reg =>
    match sat.spec.forallComps.find? (fun c => c.elem == f) with
    | none => none
    | some c =>
      match c.former, c.args with
      | "SInit", [.ref (.loc phi)] =>
        if htie : reg.formula = phi then
          if (tb.relRows "qtsl_init_member").contains
              [.ref (.loc reg.region), .ref (.loc sat.sys)] then
            match acceptLeaf tb sat.elem p with
            | none => none
            | some l =>
              some { elem := sat.elem, sysElem := sat.sys,
                     fElem := f, phiElem := phi, region := reg,
                     root_tie := htie, leaf := l }
          else none
        else none
      | _, _ => none

/-- Accept every claim of the widened fragment, in claim order: an
eval-only route through the landed `acceptLeaf`, a warrant-and-eval
route through `acceptWarrantSat`.  A warrant without an evaluation
leaf refuses — the init-membership demand has no witness — and a
routeless claim refuses as at v1: nothing is accepted vacuously. -/
def acceptClaimsW (tb : QRowTbls) (regs : List QRegionSatVal) :
    List QSatVal → Option (List QEntry)
  | [] => some []
  | sat :: rest =>
    match sat.warrant, sat.evalLeaf with
    | none, some p =>
      match acceptLeaf tb sat.elem p with
      | none => none
      | some l =>
        match acceptClaimsW tb regs rest with
        | none => none
        | some es => some (.inl l :: es)
    | some (f, w), some p =>
      match acceptWarrantSat tb regs sat f w p with
      | none => none
      | some aw =>
        match acceptClaimsW tb regs rest with
        | none => none
        | some es => some (.inr aw :: es)
    | _, _ => none

/-- The widened fragment gate: the statistical, spec-equivalence, and
invariance-scope tiers still refuse whole; region-satisfaction rows are
admitted **iff warrant-cited** — a freestanding region row is an
undischarged claim v2 cannot close, exactly as at v1. -/
def acceptFragmentGateW (pres : QtslPresentation) : Bool :=
  pres.satConfs.isEmpty && pres.specEquivs.isEmpty &&
    pres.invScopes.isEmpty &&
    pres.regionSats.all (fun r =>
      pres.sats.any (fun s => (s.warrant.map Prod.snd) == some r.elem))

/-- An accepted claim set of the widened fragment. -/
structure QtslAcceptedW where
  /-- The decoded row presentation. -/
  pres : QtslPresentation
  /-- The accepted entries, one per satisfaction claim, in order. -/
  entries : List QEntry

/-- The eval-routed leaves of an accepted value. -/
def QtslAcceptedW.leaves (a : QtslAcceptedW) : List AcceptedLeaf :=
  a.entries.filterMap fun e =>
    match e with
    | .inl l => some l
    | .inr _ => none

/-- The accepted warrants of an accepted value. -/
def QtslAcceptedW.warrants (a : QtslAcceptedW) : List AcceptedWarrant :=
  a.entries.filterMap fun e =>
    match e with
    | .inl _ => none
    | .inr w => some w

/-- **Accept a QTSL-stratum artifact's ops, widened**: scan
(fail-closed), assemble, gate, then accept every claim by its route. -/
def acceptQtslOpsW (deps : List Bytes) (ops : List GOp) :
    Option QtslAcceptedW :=
  match scanQtslOps deps ops with
  | .error _ => none
  | .ok tb =>
    match assembleQtsl tb with
    | .error _ => none
    | .ok pres =>
      if acceptFragmentGateW pres then
        match acceptClaimsW tb pres.regionSats pres.sats with
        | none => none
        | some es => some ⟨pres, es⟩
      else none

/-- Accept a sealed container's bytes, widened: the reflection route's
own sealed reader, one commit demanded, then op-level acceptance. -/
def acceptQtslSealedW (bs : Bytes) : Option QtslAcceptedW :=
  match readGeologSealed bs with
  | .err _ _ _ => none
  | .ok g =>
    match g.commits with
    | [commit] => acceptQtslOpsW commit.cskel.deps commit.cbody.ops
    | _ => none

/-! ## Soundness (one line because carried) -/

/-- Every eval-routed entry's sequent is semantically valid over every
context — the carried proof is the witness. -/
theorem acceptQtslOpsW_sound_leaf {deps : List Bytes} {ops : List GOp}
    {a : QtslAcceptedW} (_h : acceptQtslOpsW deps ops = some a) :
    ∀ l : AcceptedLeaf, Sum.inl l ∈ a.entries →
      ∀ H : Hypernet, l.seq.semanticallyValid H :=
  fun l _ H => l.valid.down H

/-- Every accepted warrant's **membership leaf** is semantically valid
over every context — the unconditional stratum of the warrant route,
carried through the promoted functor exactly as the eval-leaf class. -/
theorem acceptQtslOpsW_sound_membership {deps : List Bytes}
    {ops : List GOp} {a : QtslAcceptedW}
    (_h : acceptQtslOpsW deps ops = some a) :
    ∀ w : AcceptedWarrant, Sum.inr w ∈ a.entries →
      ∀ H : Hypernet, w.leaf.seq.semanticallyValid H :=
  fun w _ H => w.leaf.valid.down H

/-- Sealed-byte soundness, eval-routed entries. -/
theorem acceptQtslSealedW_sound_leaf {bs : Bytes} {a : QtslAcceptedW}
    (_h : acceptQtslSealedW bs = some a) :
    ∀ l : AcceptedLeaf, Sum.inl l ∈ a.entries →
      ∀ H : Hypernet, l.seq.semanticallyValid H :=
  fun l _ H => l.valid.down H

/-- Sealed-byte soundness, membership leaves. -/
theorem acceptQtslSealedW_sound_membership {bs : Bytes}
    {a : QtslAcceptedW} (_h : acceptQtslSealedW bs = some a) :
    ∀ w : AcceptedWarrant, Sum.inr w ∈ a.entries →
      ∀ H : Hypernet, w.leaf.seq.semanticallyValid H :=
  fun w _ H => w.leaf.valid.down H

/-- **Acceptance in the semantic universe, widened**: every accepted
entry's checked sequent — the eval leaf, or the warrant's membership
leaf — is a judgment in the semantic universe, in the fibre over the
context's wire object. -/
theorem acceptQtslSealedW_su_sound {bs : Bytes} {a : QtslAcceptedW}
    (_h : acceptQtslSealedW bs = some a) :
    ∀ e ∈ a.entries, ∀ H : Hypernet,
      Adequacy.cylWallW H (Sum.elim AcceptedLeaf.seq
          (fun w => w.leaf.seq) e) ∈
        (Adequacy.sequentSpec H (Sum.elim AcceptedLeaf.seq
          (fun w => w.leaf.seq) e)).modelClass := by
  intro e _ H
  cases e with
  | inl l =>
    exact (Adequacy.semanticallyValid_iff_fibre H l.seq).mp
      (l.valid.down H)
  | inr w =>
    exact (Adequacy.semanticallyValid_iff_fibre H w.leaf.seq).mp
      (w.leaf.valid.down H)

/-! ## The `SpecJudgLayer` resolution

What remains of a warranted claim after the checks is exactly one
judgment-layer step: the cited region row's own claim, read at the
class stratum as a penalty-class inclusion.  (Post-event-4, "the
claim's spec root" means the cited `SInit` face's argument φ.)  Given any such reading,
the accepted warrant resolves it to the claim conclusion through the
thin carrier — the membership cell composed with the warrant cell,
`cellOfSubset` both, the checked root tie consumed in the warrant
cell's retyping.  The pointwise face of the resolution is
`sound_QSatFromRegion` verbatim. -/

noncomputable section

open CategoryTheory.WireSpan PseudoDoubleCategoryStruct SuFunctor.Plain

universe u

/-- A class-stratum reading of the row vocabulary over a wiring
pattern: penalty classes for state-formula elements (judgment
classes), region-atom elements (region classes), and subject elements
(initial classes).  The deep decode that would *compute* such a
reading from the rows is the class-stratum campaign's; the resolution
below is generic in it. -/
structure ClassAssignment {El : Type u} {X Y : WireSpan El}
    (M : Pat X Y) : Type u where
  /-- Judgment classes of state-formula elements. -/
  formulaCpl : Nat → Cpl M
  /-- Region classes of region-atom elements. -/
  regionCpl : Nat → Cpl M
  /-- Initial classes of subject elements. -/
  initCpl : Nat → Cpl M

variable {El : Type u} {X Y : WireSpan El} {M : Pat X Y}

/-- The membership cell: the claim's initial class inside the cited
region's class, as a judgment-layer cell over identity boundaries. -/
def AcceptedWarrant.membershipCell (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hinit : A.initCpl w.sysElem ⊆ A.regionCpl w.region.region) :
    Cell (C := SpecJudgLayer El)
      (⟨M, A.initCpl w.sysElem⟩ :
        JudgLayer.JLoose (specJudgOrder El) (.of X) (.of Y))
      ⟨M, A.regionCpl w.region.region⟩
      (𝟙 (JudgLayer.of X)) (𝟙 (JudgLayer.of Y)) :=
  cellOfSubset hinit

/-- The warrant cell: the cited region row's claim — region class
inside the row's formula's judgment class — **retyped at the cited
face's `SInit` argument φ by the carried root tie**.  This is where
the checked tie is consumed: without it, the cell would conclude at
the wrong formula's class. -/
def AcceptedWarrant.warrantCell (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hchild : A.regionCpl w.region.region ⊆
      A.formulaCpl w.region.formula) :
    Cell (C := SpecJudgLayer El)
      (⟨M, A.regionCpl w.region.region⟩ :
        JudgLayer.JLoose (specJudgOrder El) (.of X) (.of Y))
      ⟨M, A.formulaCpl w.phiElem⟩
      (𝟙 (JudgLayer.of X)) (𝟙 (JudgLayer.of Y)) :=
  cellOfSubset (w.root_tie ▸ hchild)

/-- **The resolved cell**: the composite of the membership cell with
the warrant cell in `SpecJudgLayer` — the warrant citation resolved
through the thin carrier to the claim conclusion. -/
def AcceptedWarrant.resolvedCell (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hchild : A.regionCpl w.region.region ⊆
      A.formulaCpl w.region.formula)
    (hinit : A.initCpl w.sysElem ⊆ A.regionCpl w.region.region) :
    Cell (C := SpecJudgLayer El)
      (⟨M, A.initCpl w.sysElem⟩ :
        JudgLayer.JLoose (specJudgOrder El) (.of X) (.of Y))
      ⟨M, A.formulaCpl w.phiElem⟩
      (𝟙 (JudgLayer.of X) ≫ 𝟙 (JudgLayer.of X))
      (𝟙 (JudgLayer.of Y) ≫ 𝟙 (JudgLayer.of Y)) :=
  vComp (w.membershipCell A hinit) (w.warrantCell A hchild)

/-- The resolved inclusion, at identity boundaries (thinness makes
this and the composite presentations of one content — in a thin
carrier, existence is the content). -/
theorem AcceptedWarrant.resolve (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hchild : A.regionCpl w.region.region ⊆
      A.formulaCpl w.region.formula)
    (hinit : A.initCpl w.sysElem ⊆ A.regionCpl w.region.region) :
    A.initCpl w.sysElem ⊆ A.formulaCpl w.phiElem := by
  rw [← w.root_tie]
  exact hinit.trans hchild

/-- The resolved inclusion as a single judgment-layer cell over
identity boundaries. -/
def AcceptedWarrant.resolveCell (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hchild : A.regionCpl w.region.region ⊆
      A.formulaCpl w.region.formula)
    (hinit : A.initCpl w.sysElem ⊆ A.regionCpl w.region.region) :
    Cell (C := SpecJudgLayer El)
      (⟨M, A.initCpl w.sysElem⟩ :
        JudgLayer.JLoose (specJudgOrder El) (.of X) (.of Y))
      ⟨M, A.formulaCpl w.phiElem⟩
      (𝟙 (JudgLayer.of X)) (𝟙 (JudgLayer.of Y)) :=
  cellOfSubset (w.resolve A hchild hinit)

/-- **The resolution's pointwise face is the soundness lemma**: a
penalty in the claim's initial class lands in the cited face's
judgment class by `Qtsl.Aliases.sound_QSatFromRegion` — the catalogue's stock
witness for the dissolved rule, wired here at `X := Pen (Pat.Tot M)`,
with the region class as `R` and membership in the root's class as
`sat` — the warrant citation resolved to its soundness lemma,
literally.  (The `Decode.Binding` table's `QSatFromRegion` row names
exactly this lemma; this theorem is that row's consumption.) -/
theorem AcceptedWarrant.resolve_pointwise (w : AcceptedWarrant)
    (A : ClassAssignment M)
    (hchild : A.regionCpl w.region.region ⊆
      A.formulaCpl w.region.formula)
    (hinit : A.initCpl w.sysElem ⊆ A.regionCpl w.region.region)
    {p : Pen (Pat.Tot M)} (hp : p ∈ A.initCpl w.sysElem) :
    p ∈ A.formulaCpl w.phiElem :=
  Qtsl.Aliases.sound_QSatFromRegion
    (R := A.regionCpl w.region.region)
    (sat := (· ∈ A.formulaCpl w.phiElem))
    (fun x hx => w.root_tie ▸ hchild hx) (hinit hp)

/-- Within an accepted warrant, the raw-formula reading and the
spec-root reading of the judgment class coincide — the tie check made
them so.  (This equation is what the tie-drop and laundering mutants
break at the acceptor: an untied citation would read the warrant at
the wrong class.) -/
theorem AcceptedWarrant.formula_class_agrees (w : AcceptedWarrant)
    (A : ClassAssignment M) :
    A.formulaCpl w.region.formula = A.formulaCpl w.phiElem := by
  rw [w.root_tie]

end

/-! ## Correspondence: the widened roster against the decode -/

/-- An accepted warrant records its claim's element. -/
theorem acceptWarrantSat_elem {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {aw : AcceptedWarrant}
    (h : acceptWarrantSat tb regs sat f w p = some aw) :
    aw.elem = sat.elem := by
  unfold acceptWarrantSat at h
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  injection h with h
  subst h
  rfl

/-- An accepted warrant records its claim's subject. -/
theorem acceptWarrantSat_sys {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {aw : AcceptedWarrant}
    (h : acceptWarrantSat tb regs sat f w p = some aw) :
    aw.sysElem = sat.sys := by
  unfold acceptWarrantSat at h
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  injection h with h
  subst h
  rfl

/-- An accepted warrant records the cited safety-face component. -/
theorem acceptWarrantSat_f {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {aw : AcceptedWarrant}
    (h : acceptWarrantSat tb regs sat f w p = some aw) :
    aw.fElem = f := by
  unfold acceptWarrantSat at h
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  injection h with h
  subst h
  rfl

/-- An accepted warrant's region row was found in the decoded region
roster, keyed by the citation. -/
theorem acceptWarrantSat_region {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {aw : AcceptedWarrant}
    (h : acceptWarrantSat tb regs sat f w p = some aw) :
    regs.find? (fun r => r.elem == w) = some aw.region := by
  unfold acceptWarrantSat at h
  split at h
  any_goals contradiction
  rename_i reg hfind
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  injection h with h
  subst h
  exact hfind

/-- An accepted warrant's membership leaf came through the landed leaf
route on its claim's evaluation citation. -/
theorem acceptWarrantSat_leaf {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {aw : AcceptedWarrant}
    (h : acceptWarrantSat tb regs sat f w p = some aw) :
    acceptLeaf tb sat.elem p = some aw.leaf := by
  unfold acceptWarrantSat at h
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  rename_i l hleaf
  injection h with h
  subst h
  exact hleaf

/-- **The widened roster correspondence**: accepted entries pair the
satisfaction claims one-to-one — an eval-routed claim yields a leaf
whose sequent is its cited leaf's decoded conclusion; a warranted claim
yields a warrant whose region row resolves its citation, whose subject
and spec root are the claim's, and whose membership leaf decodes from
its evaluation citation. -/
theorem acceptClaimsW_spec {tb : QRowTbls} {regs : List QRegionSatVal}
    {sats : List QSatVal} {es : List QEntry}
    (h : acceptClaimsW tb regs sats = some es) :
    List.Forall₂ (fun sat e =>
      match e with
      | .inl l => l.elem = sat.elem ∧ sat.warrant = none ∧
          ∃ p, sat.evalLeaf = some p ∧ leafSequent tb p = .ok l.seq
      | .inr aw => aw.elem = sat.elem ∧ aw.sysElem = sat.sys ∧
          (∃ f w, sat.warrant = some (f, w) ∧ aw.fElem = f ∧
            regs.find? (fun r => r.elem == w) = some aw.region) ∧
          ∃ p, sat.evalLeaf = some p ∧
            leafSequent tb p = .ok aw.leaf.seq)
      sats es := by
  induction sats generalizing es with
  | nil =>
      unfold acceptClaimsW at h
      injection h with h
      subst h
      exact .nil
  | cons sat rest ih =>
      unfold acceptClaimsW at h
      split at h
      any_goals contradiction
      · rename_i p hw he
        split at h
        any_goals contradiction
        rename_i l hal
        split at h
        any_goals contradiction
        rename_i es' hrec
        injection h with h
        subst h
        exact .cons
          ⟨acceptLeaf_elem hal, hw, p, he, acceptLeaf_seq hal⟩
          (ih hrec)
      · rename_i f w p hw he
        split at h
        any_goals contradiction
        rename_i aw haw
        split at h
        any_goals contradiction
        rename_i es' hrec
        injection h with h
        subst h
        exact .cons ⟨acceptWarrantSat_elem haw,
          acceptWarrantSat_sys haw,
          ⟨f, w, hw, acceptWarrantSat_f haw,
            acceptWarrantSat_region haw⟩,
          p, he, acceptLeaf_seq (acceptWarrantSat_leaf haw)⟩
          (ih hrec)

/-! ## Fixtures: the warranted claim, accepted; every named refusal

The staged rows extend the S1 fixture: the same ground leaf, plus a
region atom (17), a region-satisfaction row (18, its own judgment 19),
the tie formula φ (20 : `StatePred`), an `SInit`-formed safety face in
place of the eval fixture's `SProbGE` one, the ternary warrant
citation, the init-membership demand at the event-4 wire order, and
the evaluation route now reading as the membership leaf. -/

/-- The warranted fixture's specification rows: the face is
`SInit(φ)` — the only form the event-4 root tie admits — attached by
`spec_forall` (f, spec). -/
def warrantSpecRows : List GOp :=
  [.funa (.ext 0 653) [.ref (.loc 20)] (.ref (.loc 3)),      -- SInit
   .rela (.ext 0 742) [.ref (.loc 3), .ref (.loc 2)]]        -- spec_forall

/-- The warranted fixture: element layout 0–16 as the S1 fixture, then
17 `QRegionAtom`, 18 `QRegionSat`, 19 `QJudgment` (the region claim's
own judgment), 20 `StatePred` (φ, the tie formula). -/
def fixtureOpsWarrant : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 141),                                     -- 19 : QJudgment
     .elta (.ext 0 61)] ++                                   -- 20 : StatePred (φ)
    fixtureGround ++ warrantSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),     -- QSat/judgment
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),     -- QSat/spec
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],       -- qsat_warrant (f, sat, warrant)
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],      -- qsat_eval (eval, sat)
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),   -- QRegionSat/judgment
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 20)),   -- QRegionSat/formula = φ
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),   -- QRegionSat/region
     .rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)],     -- qtsl_init_member (region, sys)
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- The warranted fixture's scanned tables. -/
def fixtureTblsWarrant : QRowTbls :=
  match scanQtslOps fixtureDeps fixtureOpsWarrant with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- The warranted fixture's decoded specification (the `SInit` face). -/
def warrantSpecVal : QSpecVal :=
  ⟨2, [⟨3, "SInit", [.ref (.loc 20)]⟩], []⟩

/-- The warranted fixture's expected presentation, in full. -/
def fixtureWarrantExpected : QtslPresentation :=
  { judgments := [0, 19]
    sats := [⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩]
    satConfs := []
    specEquivs := []
    regionSats := [⟨18, 19, 20, 17⟩]
    invScopes := []
    proofs := [⟨6, 0⟩] }

/-- The warranted fixture decodes to exactly the expected
presentation. -/
theorem decode_fixtureWarrant_ok :
    decodeQtslPresentationOps fixtureDeps fixtureOpsWarrant =
      .ok fixtureWarrantExpected := by
  decide

/-- The expected accepted warrant: the resolved region row, the tie by
`rfl` (the region row's formula IS the face's `SInit` argument 20),
and the membership leaf — the S1 fixture's leaf value verbatim
(`acceptGroundLeaf` is table-independent on equal decoded
sequents). -/
def fixtureWarrant : AcceptedWarrant where
  elem := 5
  sysElem := 1
  fElem := 3
  phiElem := 20
  region := ⟨18, 19, 20, 17⟩
  root_tie := rfl
  leaf := fixtureLeaf

/-- The expected accepted value of the warranted fixture. -/
def fixtureWarrantAccepted : QtslAcceptedW :=
  ⟨fixtureWarrantExpected, [.inr fixtureWarrant]⟩

/-- The warranted fixture's membership leaf decodes to the S1 leaf
sequent (the same ground rows; the added declarations shift no
element indices). -/
theorem fixtureWarrant_leaf_seq :
    leafSequent fixtureTblsWarrant 7 = .ok leafSeqDemo := by
  rfl

/-- The warranted claim is accepted through the warrant route, with
the expected cargo.  (Kernel-first discipline throughout: the citation
resolution, face find, `SInit` match, and tie are `rfl`-reduced in the
key equation; the demand-row check is a `decide`-carried equation; the
one stuck redex — the membership leaf's Rat gate — is crossed by the
landed `acceptGroundLeaf_fixture`.) -/
theorem acceptWarrantSat_fixture :
    acceptWarrantSat fixtureTblsWarrant [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 =
      some fixtureWarrant := by
  have key : acceptWarrantSat fixtureTblsWarrant [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 =
      (if (fixtureTblsWarrant.relRows "qtsl_init_member").contains
          [.ref (.loc 17), .ref (.loc 1)] then
        match acceptLeaf fixtureTblsWarrant 5 7 with
        | none => none
        | some l =>
          some { elem := 5, sysElem := 1, fElem := 3, phiElem := 20,
                 region := ⟨18, 19, 20, 17⟩, root_tie := rfl,
                 leaf := l }
      else none) := rfl
  have hleaf : acceptLeaf fixtureTblsWarrant 5 7 = some fixtureLeaf := by
    have k2 : acceptLeaf fixtureTblsWarrant 5 7 =
        acceptGroundLeaf 5 leafSeqDemo := by
      unfold acceptLeaf
      rw [fixtureWarrant_leaf_seq]
    rw [k2, acceptGroundLeaf_fixture]
  rw [key,
    if_pos (by decide :
      ((fixtureTblsWarrant.relRows "qtsl_init_member").contains
        [.ref (.loc 17), .ref (.loc 1)]) = true),
    hleaf]
  rfl

/-- The warranted claim roster is accepted whole. -/
theorem acceptClaimsW_fixture :
    acceptClaimsW fixtureTblsWarrant fixtureWarrantExpected.regionSats
      fixtureWarrantExpected.sats = some [.inr fixtureWarrant] := by
  have key : acceptClaimsW fixtureTblsWarrant
      fixtureWarrantExpected.regionSats fixtureWarrantExpected.sats =
      (match acceptWarrantSat fixtureTblsWarrant [⟨18, 19, 20, 17⟩]
          ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 with
       | none => none
       | some aw => some [.inr aw]) := rfl
  rw [key, acceptWarrantSat_fixture]

/-- **The warrant-route acceptance fixture**: the staged warranted
rows are accepted whole — presentation and entry roster exactly as
expected.  The row set that refused at v1 (`refuse_warrant_routed`'s
class), completed with its membership witness, is discharged by v2. -/
theorem acceptW_fixture_warrant :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrant =
      some fixtureWarrantAccepted := by
  have k1 : acceptQtslOpsW fixtureDeps fixtureOpsWarrant =
      (match assembleQtsl fixtureTblsWarrant with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGateW pres then
           match acceptClaimsW fixtureTblsWarrant pres.regionSats
               pres.sats with
           | none => none
           | some es => some ⟨pres, es⟩
         else none) := by
    unfold acceptQtslOpsW
    rw [(by decide : scanQtslOps fixtureDeps fixtureOpsWarrant =
      .ok fixtureTblsWarrant)]
  rw [k1, (by decide : assembleQtsl fixtureTblsWarrant =
    .ok fixtureWarrantExpected)]
  show (if acceptFragmentGateW fixtureWarrantExpected then
          match acceptClaimsW fixtureTblsWarrant
              fixtureWarrantExpected.regionSats
              fixtureWarrantExpected.sats with
          | none => none
          | some es => some (⟨fixtureWarrantExpected, es⟩ : QtslAcceptedW)
        else none) = some fixtureWarrantAccepted
  rw [if_pos (by decide :
      acceptFragmentGateW fixtureWarrantExpected = true),
    acceptClaimsW_fixture]
  rfl

/-- Fixture-level conservativity: the S1 eval-only rows are accepted
by the widened acceptor with the same leaf, as an eval entry. -/
theorem acceptW_fixture_evalOnly :
    acceptQtslOpsW fixtureDeps fixtureOps =
      some ⟨fixtureExpected, [.inl fixtureLeaf]⟩ := by
  have k1 : acceptQtslOpsW fixtureDeps fixtureOps =
      (match assembleQtsl fixtureTbls with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGateW pres then
           match acceptClaimsW fixtureTbls pres.regionSats pres.sats with
           | none => none
           | some es => some ⟨pres, es⟩
         else none) := by
    unfold acceptQtslOpsW
    rw [(by decide : scanQtslOps fixtureDeps fixtureOps =
      .ok fixtureTbls)]
  rw [k1, (by decide : assembleQtsl fixtureTbls = .ok fixtureExpected)]
  show (if acceptFragmentGateW fixtureExpected then
          match acceptClaimsW fixtureTbls fixtureExpected.regionSats
              fixtureExpected.sats with
          | none => none
          | some es => some (⟨fixtureExpected, es⟩ : QtslAcceptedW)
        else none) = some ⟨fixtureExpected, [.inl fixtureLeaf]⟩
  have key : acceptClaimsW fixtureTbls fixtureExpected.regionSats
      fixtureExpected.sats =
      (match acceptLeaf fixtureTbls 5 7 with
       | none => none
       | some l => some [.inl l]) := rfl
  rw [if_pos (by decide : acceptFragmentGateW fixtureExpected = true),
    key, acceptLeaf_fixture]

/-- The membership leaf of the accepted warranted fixture at the
checker face, over any context — extracted from the acceptance value's
carried proof, no hypotheses. -/
theorem acceptedW_fixture_membership_face (H : Hypernet) :
    Plain.upperProb (Plain.admCyl H leafSeqDemo)
      (Plain.postEvt H leafSeqDemo)ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (acceptQtslOpsW_sound_membership acceptW_fixture_warrant
      fixtureWarrant (List.Mem.head _) H)

/-! ### Refusal fixtures (each green; the prereg'd mutants disable the
corresponding check to prove the refusal load-bearing) -/

/-- **A warrant without an evaluation leaf refuses** — the
init-membership demand (`ax/wf/qsat_init`) has no witness.  This is
S4's `fixtureOpsWarrantRouted` VERBATIM, single-guarded at v2: its
region row is warrant-cited, so the widened gate admits it, and the
missing eval route is the one remaining refusal — the S4 finding's
"doubly guarded, no single mutant" fixture resolves here. -/
theorem refuse_warrant_no_eval :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantRouted = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The wrong-tie variant: element 21 staged as a second `StatePred`,
the region row's formula pointed at it — a warrant whose cited face is
NOT the `SInit` image of the cited row's formula. -/
def fixtureOpsWarrantWrongTie : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 141),                                     -- 19 : QJudgment
     .elta (.ext 0 61),                                      -- 20 : StatePred (φ)
     .elta (.ext 0 61)] ++                                   -- 21 : StatePred (≠ φ)
    fixtureGround ++ warrantSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 21)),   -- formula ≠ φ
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     .rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)],
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A warrant citing a child whose formula is not the face's `SInit`
argument refuses** — the memo §3.5 mutant locus, at its event-4
re-sort, as a green refusal. -/
theorem refuse_warrant_wrong_tie :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantWrongTie = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The face-not-`SInit` variant: the warranted rows with the eval
fixture's `SProbGE`-formed face in place of the `SInit` one (φ stays
staged; the region row points at it; nothing else changes) — the
refuse-mode tie (`ax/qsat/root_tie`) admits no other former. -/
def fixtureOpsWarrantNotSInit : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 141),                                     -- 19 : QJudgment
     .elta (.ext 0 61)] ++                                   -- 20 : StatePred (φ)
    fixtureGround ++ fixtureSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 20)),
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     .rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)],
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A warrant citing a non-`SInit` face refuses.** -/
theorem refuse_warrant_face_not_sinit :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantNotSInit = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The foreign-face variant: a second `Spec` (21) with its own
`SInit`-formed face (22, over the SAME φ) — and the warrant cites THAT
face while the claim's spec is still element 2.  Every other check
would pass: the tie holds (same φ), the demand row stands.  Only face
membership separates this from the green fixture. -/
def fixtureOpsWarrantForeignFace : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 141),                                     -- 19 : QJudgment
     .elta (.ext 0 61),                                      -- 20 : StatePred (φ)
     .elta (.ext 0 103),                                     -- 21 : Spec (foreign)
     .elta (.ext 0 64)] ++                                   -- 22 : ForallSpec (foreign face)
    fixtureGround ++ warrantSpecRows ++
    [.funa (.ext 0 653) [.ref (.loc 20)] (.ref (.loc 22)),   -- SInit (foreign face, same φ)
     .rela (.ext 0 742) [.ref (.loc 22), .ref (.loc 21)],    -- spec_forall (foreign)
     .funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 22), .ref (.loc 5), .ref (.loc 18)],      -- warrant cites the foreign face
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 20)),
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     .rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)],
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A warrant citing a face from another spec refuses**
(`ax/wf/qsat_warrant_member`'s content, fail-closed). -/
theorem refuse_warrant_foreign_face :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantForeignFace = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The old-wire-order variant: the green warranted rows with the
init-membership demand staged at the RETIRED event-3 order,
(sys, region).  The event-4 read demands (region, sys) — the latent
producer/acceptor divergence the residue survey named, made
load-bearing here. -/
def fixtureOpsWarrantInitOldOrder : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),
     .elta (.ext 0 155),
     .elta (.ext 0 141),
     .elta (.ext 0 61)] ++
    fixtureGround ++ warrantSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 20)),
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     .rela (.ext 0 922) [.ref (.loc 1), .ref (.loc 17)],     -- (sys, region): retired order
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **An init-membership demand staged at the retired event-3 wire
order refuses.** -/
theorem refuse_warrant_init_member_order :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantInitOldOrder = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The missing-demand variant: the warranted fixture without its
`qtsl_init_member` row. -/
def fixtureOpsWarrantNoInitMember : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),
     .elta (.ext 0 155),
     .elta (.ext 0 141),
     .elta (.ext 0 61)] ++
    fixtureGround ++ warrantSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 19)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 20)),
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A warranted claim without its init-membership demand row
refuses** (`ax/wf/qsat_init` unindexed). -/
theorem refuse_warrant_no_initmember :
    acceptQtslOpsW fixtureDeps fixtureOpsWarrantNoInitMember = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- **A freestanding region row still refuses at v2** — S4's
`fixtureOpsRegionTier` VERBATIM: its claim is eval-routed and fine,
its region row is cited by no warrant, and the widened gate is the
single guard. -/
theorem refuse_uncited_region_W :
    acceptQtslOpsW fixtureDeps fixtureOpsRegionTier = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- **The statistical tier still refuses at v2** (inherited
conjunct). -/
theorem refuse_statistical_W :
    acceptQtslOpsW fixtureDeps fixtureOpsStatistical = none :=
  Option.isNone_iff_eq_none.mp (by decide)

end Decode

end QtslSem

end SuFunctor
