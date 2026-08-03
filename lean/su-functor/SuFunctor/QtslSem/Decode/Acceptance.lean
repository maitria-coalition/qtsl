import SuFunctor.QtslSem.Decode.BLMultiSeam
import SuFunctor.Adequacy.CheckerCarrier

/-!
# The QtslSem acceptance theorem

The E2 architecture (`Reflection/Accept.lean`) at the theory-Qtsl
stratum: an acceptance function whose returned value **carries its own
validity proof, built through the promoted functor during
acceptance** — decode theory-Qtsl rows (S1, fail-closed) → the
many-object presentation (`blPresentationM`, the decoded leaf as an
embedded `pConstExact` generator) → the promoted functor
(`promoteThin`, via `qtslSemBLM.mapCell`) → the semantic-universe
judgment.  The soundness theorems are one line (`l.valid.down`) by
design, not shortcut: every obligation was discharged during
acceptance, and no decode, check, or assembly stage after the gate is
trusted.  The four landed E4 altitudes (`CheckerAcceptance`'s design)
are mirrored per accepted leaf: the checker face, the model-class
membership, the valuation-embedded face, and fibre citizenship in the
semantic universe.

**The v1 acceptance fragment, stated honestly** (preregistered
before the proofs were built): accepted presentations are those whose
every satisfaction claim carries an evaluation route to a ground leaf
whose conclusion is a comparison atom evaluating closed to true — the
wired `pConstExact` class.  Everything else refuses, by the named
check: routeless claims at the route match (never accept-vacuously),
warrant-without-eval claims at the same match, uncited region rows and
the statistical tier (`QSatConf`) at the fragment gate, non-atom ground
conclusions at the shape match, eval-false atoms at the evaluation
gate, non-ground leaves and unpinned vocabulary (battery/HPlate species
included) at the landed S1 decoders.
The accepted conclusion per claim is the LEAF-level SU judgment over
every context (v1 ground leaves are wire-free by construction —
checked, not assumed); the full `⟦QSat⟧` model-class statement over the
spec's deep semantics arrives with the warrant discharge + deep spec
decode (the class stratum, a later stage of this development).

**The v1.1 alias-citation walk** (likewise preregistered): a claim
carrying BOTH routes —
`qsat_warrant` and `qsat_eval` — is the QSatFromRegion citation shape
(the rule has since dissolved into the `QSat` record's own demand set:
a region-satisfaction child rooted at the spec's root plus the
initial-membership evaluation leaf, the degenerate-box-vs-sublevel
constructor pair).  The walk resolves the citation to its unpacked
`pConstExact` core and accepts THAT, with the same carried proof, iff
every citation check passes, each fail-closed: the warrant resolves in
the decoded region-satisfaction roster; its formula is the claim's spec
root (`ax/qsat/root_tie`, checked at the row stratum); its region atom
constructs by `qraSublevel` over a `QCertFam`-sorted family; and the
decoded leaf is the sublevel's own membership reading — comparator
`.le`, right side the sublevel's own threshold literal.  The honest
boundary, stated: the accepted conclusion is still the LEAF-level SU
judgment; the warrant's region-satisfaction premise (`QRegionSat` as a
claim) is recorded and structurally verified, NOT discharged — its
discharge, and the cert-family content tie (leaf left side vs the
family's table polynomial at the init point, outside the S1 decode
fragment), are class-stratum campaign material.  Transport: an accepted leaf's generator
splices into the cite derivation (`acceptedCiteDeriv`, empty-tops
composite, extension-arrow tights), so accepted claims transport along
context extensions inside the calculus — one covering, one `mapCell`
trip.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-! ## The generic assembly lemmas: an arbitrary checked ground leaf
through the many-object promoted functor

The seam's `decodedLeafRule` machinery, generalized from the fixture's
literal to any sequent with a checked comparison-atom conclusion — the
S2 component (`sound_pConstExact`, already wired as the `pConstExact`
arm) reached through the S3 assembly (`promoteThin`), generic in the
decoded data.  These are what the acceptance function invokes to build
the carried proof. -/

/-- The checked ground leaf as a zero-premise multicell of the
many-object presented carrier at context `⟨H⟩`: the `pConstExact`
generator on `s`, its gate exactly the check's two facts. -/
def groundLeafCellM (H : Hypernet) {s : Sequent} {e₁ e₂ : Term}
    {b : BowTie}
    (heval : (Formula.atom b e₁ e₂).evalClosed = some true)
    (hpost : s.post = .atom b e₁ e₂) :
    VirtualDoubleCategoryData.Cell (C := Presented blPresentationM)
      (embDecodedTops H)
      ((s : Sequent) :
        VirtualDoubleCategoryData.Loose (.of (.of H)) (.of (.of H)))
      (𝟙 (Presented.of (BLHCtx.of H)))
      (𝟙 (Presented.of (BLHCtx.of H))) := by
  exact ⟨⟨DerivT.gen (P := blPresentationM)
    (.emb H (.pConstExact s e₁ e₂ b)) ⟨heval, hpost⟩⟩⟩

/-- Its covering in the free promotion of the many-object carrier. -/
def groundLeafCoveringM (H : Hypernet) {s : Sequent} {e₁ e₂ : Term}
    {b : BowTie}
    (heval : (Formula.atom b e₁ e₂).evalClosed = some true)
    (hpost : s.post = .atom b e₁ e₂) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented blPresentationM))
      (a := .of (.of (.of H))) (b := .of (.of (.of H)))
      (c := .of (.of (.of H))) (d := .of (.of (.of H)))
      (embDecodedTops H)
      (LoosePath.single ((s : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of (BLHCtx.of H))
          (Presented.of (BLHCtx.of H))))
      (𝟙 (FreePromotion.of (Presented.of (BLHCtx.of H))))
      (𝟙 (FreePromotion.of (Presented.of (BLHCtx.of H)))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (groundLeafCellM H heval hpost)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The generic checked leaf is valid over every context, through the
promoted functor**: the route the acceptance function runs to build the
carried proof — `qtslSemBLM.mapCell` on the generic covering. -/
theorem groundLeaf_valid_through_M {s : Sequent} {e₁ e₂ : Term}
    {b : BowTie}
    (heval : (Formula.atom b e₁ e₂).evalClosed = some true)
    (hpost : s.post = .atom b e₁ e₂) (H : Hypernet) :
    s.semanticallyValid H := by
  have himp := (qtslSemBLM.mapCell (groundLeafCoveringM H heval hpost)).down
  exact (himp trivial).1

/-- The generic checked leaf through the judgment-layer route: same
covering, the other carrier, same endpoint. -/
theorem groundLeaf_valid_through_MJ {s : Sequent} {e₁ e₂ : Term}
    {b : BowTie}
    (heval : (Formula.atom b e₁ e₂).evalClosed = some true)
    (hpost : s.post = .atom b e₁ e₂) (H : Hypernet) :
    s.semanticallyValid H := by
  obtain ⟨_, himp⟩ :=
    (qtslSemBLMJ.mapCell (groundLeafCoveringM H heval hpost)).down
  exact (himp trivial).1

/-! ## The accepted leaf -/

/-- An accepted evaluation leaf: the decoded sequent, its checked atom
decomposition, the wire-freeness checks, and the **carried validity** —
constructed through `groundLeaf_valid_through_M` at acceptance time
(the E2 `Accepted.valid` posture, one stratum up: v1 ground leaves are
wire-free, so the carried judgment is context-generic). -/
structure AcceptedLeaf where
  /-- The `QSat` element this leaf warrants. -/
  elem : Nat
  /-- The decoded leaf sequent. -/
  seq : Sequent
  /-- The conclusion atom's comparator. -/
  cmp : BowTie
  /-- The conclusion atom's left term. -/
  lhs : Term
  /-- The conclusion atom's right term. -/
  rhs : Term
  /-- The conclusion is the atom (the gate's shape fact). -/
  post_eq : seq.post = .atom cmp lhs rhs
  /-- The atom evaluates closed to true (the gate's checked fact). -/
  eval_true : (Formula.atom cmp lhs rhs).evalClosed = some true
  /-- The premise is wire-free (checked). -/
  preWF : seq.pre.freeWires = []
  /-- The conclusion is wire-free (checked). -/
  postWF : seq.post.freeWires = []
  /-- The carried validity, built through the promoted functor. -/
  valid : PLift (∀ H : Hypernet, seq.semanticallyValid H)

/-- An accepted leaf is well-scoped over every context: both formulas
are wire-free, so the scoping quantifier is vacuous. -/
theorem AcceptedLeaf.scopedAll (l : AcceptedLeaf) (H : Hypernet) :
    l.seq.wellScoped H := by
  intro w hw
  rcases hw with h | h
  · rw [l.preWF] at h
    simp at h
  · rw [l.postWF] at h
    simp at h

/-- The accepted leaf's generator: `pConstExact` on its own
decomposition (definitionally concluding `l.seq`). -/
def acceptedLeafRule (l : AcceptedLeaf) : BLRule :=
  .pConstExact l.seq l.lhs l.rhs l.cmp

/-- Its gate holds at every context, from the carried checks. -/
theorem acceptedLeafRule_gate (l : AcceptedLeaf) (H : Hypernet) :
    (blPresentation H).gate (acceptedLeafRule l) :=
  ⟨l.eval_true, l.post_eq⟩

/-! ## The acceptance route -/

/-- Accept one ground leaf: the conclusion-shape match, the closed
evaluation gate, the wire-freeness checks — and on success the value
carries its validity, built through the promoted functor.  Refusals
are the fragment speaking: a non-atom conclusion or a false (or stuck)
evaluation is outside the wired v1 class. -/
def acceptGroundLeaf (elem : Nat) (s : Sequent) : Option AcceptedLeaf :=
  match hpost : s.post with
  | .atom b e₁ e₂ =>
    if heval : (Formula.atom b e₁ e₂).evalClosed = some true then
      match hpre : s.pre.freeWires with
      | [] =>
        match hpw : s.post.freeWires with
        | [] =>
          some { elem := elem, seq := s, cmp := b, lhs := e₁, rhs := e₂,
                 post_eq := hpost, eval_true := heval,
                 preWF := hpre, postWF := hpw,
                 valid := ⟨fun H =>
                   groundLeaf_valid_through_M heval hpost H⟩ }
        | _ :: _ => none
      | _ :: _ => none
    else none
  | _ => none

/-- Accept a satisfaction claim's evaluation leaf: decode the leaf's
concluded sequent (S1, fail-closed), then check and carry. -/
def acceptLeaf (tb : QRowTbls) (elem p : Nat) : Option AcceptedLeaf :=
  match leafSequent tb p with
  | .error _ => none
  | .ok s => acceptGroundLeaf elem s

/-! ### The alias-citation walk (v1.1) -/

/-- The region-atom constructor roster (all three pinned). -/
def regionAtomCtors : List String := ["qraSublevel", "qraBox", "qraAffine"]

/-- Resolve one alias citation — the QSatFromRegion shape at event 4:
the row's cited component `f` must be found among the claimed spec's
decoded safety faces (`ax/wf/qsat_warrant_member`), be `SInit`-formed
with the cited row's formula as its argument (the refuse-mode root
tie, `ax/qsat/root_tie` — one tie semantics with the v2 warrant
route), and the cited row's region atom must construct by exactly one
`qraSublevel` row over a `QCertFam`-sorted family.  Returns the
sublevel's threshold; every failure — a dangling citation, a foreign
or non-`SInit` face, a mis-tied warrant, a missing, duplicated, or
foreign region constructor, an ill-sorted or unreadable family or
threshold — refuses. -/
def resolveCitation (tb : QRowTbls) (regionSats : List QRegionSatVal)
    (spec : QSpecVal) (f w : Nat) : Option Rat :=
  match regionSats.find? (fun rs => rs.elem == w) with
  | none => none
  | some rs =>
    match spec.forallComps.find? (fun c => c.elem == f) with
    | none => none
    | some c =>
      match c.former, c.args with
      | "SInit", [.ref (.loc phi)] =>
        if rs.formula == phi then
          match tb.ctorRowsOf regionAtomCtors rs.region with
          | [("qraSublevel", [cv, t])] =>
            match elemOfVal cv, qOfVal t with
            | some cf, some thr =>
              if tb.sortAt cf == some "QCertFam" then some thr else none
            | _, _ => none
          | _ => none
        else none
      | _, _ => none

/-- The sublevel-membership reading of a decoded leaf sequent: the
conclusion is `_ ≤ thr` with the citation's own threshold literal on
the right — the degenerate-box-vs-sublevel pair's evaluation leaf,
`rootEvalFormula`'s shape.  Checked BEFORE the evaluation gate, so a
mis-tied citation refuses without ever constructing a carried proof. -/
def sequentMatchesSublevel (s : Sequent) (thr : Rat) : Bool :=
  match s.post with
  | .atom .le _ (.const q) => q == thr
  | _ => false

/-- Accept every satisfaction claim of the decoded presentation.  An
eval-only claim accepts through its checked leaf; a claim with BOTH
routes is an alias citation and accepts through the SAME leaf check
after the citation walk (`resolveCitation` + the sublevel reading); a
claim with NO route, or a warrant without its membership leaf, refuses:
the fragment discharges nothing it did not check, so nothing is ever
accepted vacuously. -/
def acceptLeaves (tb : QRowTbls) (regionSats : List QRegionSatVal) :
    List QSatVal → Option (List AcceptedLeaf)
  | [] => some []
  | sat :: rest =>
    match sat.warrant, sat.evalLeaf with
    | none, some p =>
      match acceptLeaf tb sat.elem p with
      | none => none
      | some l =>
        match acceptLeaves tb regionSats rest with
        | none => none
        | some ls => some (l :: ls)
    | some (f, w), some p =>
      match resolveCitation tb regionSats sat.spec f w with
      | none => none
      | some thr =>
        match leafSequent tb p with
        | .error _ => none
        | .ok s =>
          if sequentMatchesSublevel s thr then
            match acceptGroundLeaf sat.elem s with
            | none => none
            | some l =>
              match acceptLeaves tb regionSats rest with
              | none => none
              | some ls => some (l :: ls)
          else none
    | _, none => none

/-- The fragment gate: no content of the out-of-fragment claim tiers —
statistical (`QSatConf`), spec-equivalence, invariance scope — and
**citation coverage** for the region tier: every region-satisfaction
row must be cited by some claim's warrant (a freestanding
`QRegionSat` row is itself a claim, and v1.1 cannot discharge it — the
cited ones ride their claims as recorded premises, per the module
header's honest boundary). -/
def acceptFragmentGate (pres : QtslPresentation) : Bool :=
  pres.satConfs.isEmpty && pres.specEquivs.isEmpty &&
    pres.invScopes.isEmpty &&
    pres.regionSats.all (fun rs =>
      pres.sats.any (fun sat => (sat.warrant.map Prod.snd) == some rs.elem))

/-- An accepted claim set: the decoded presentation and one accepted
leaf per satisfaction claim. -/
structure QtslAccepted where
  /-- The decoded row presentation. -/
  pres : QtslPresentation
  /-- The accepted leaves, one per satisfaction claim, in order. -/
  leaves : List AcceptedLeaf

/-- **Accept a QTSL-stratum artifact's ops**: scan (fail-closed against
the fragment pins), assemble the row presentation, refuse any
out-of-fragment claim tier, then accept every satisfaction claim's
evaluation leaf. -/
def acceptQtslOps (deps : List Bytes) (ops : List GOp) :
    Option QtslAccepted :=
  match scanQtslOps deps ops with
  | .error _ => none
  | .ok tb =>
    match assembleQtsl tb with
    | .error _ => none
    | .ok pres =>
      if acceptFragmentGate pres then
        match acceptLeaves tb pres.regionSats pres.sats with
        | none => none
        | some ls => some ⟨pres, ls⟩
      else none

/-- **Accept a sealed container's bytes** (the memo's `acceptQtslRows`
headline): the reflection route's own sealed reader, one commit
demanded, then op-level acceptance. -/
def acceptQtslSealed (bs : Bytes) : Option QtslAccepted :=
  match readGeologSealed bs with
  | .err _ _ _ => none
  | .ok g =>
    match g.commits with
    | [commit] => acceptQtslOps commit.cskel.deps commit.cbody.ops
    | _ => none

/-! ## The acceptance theorems (one line because carried) -/

/-- **Soundness of op-level acceptance**: every accepted leaf's sequent
is semantically valid over every hypernet context.  One line — the
carried proof is the witness (the E2 pattern; the acceptance equation
is unused because no stage after the gate is trusted). -/
theorem acceptQtslOps_sound (deps : List Bytes) (ops : List GOp)
    (a : QtslAccepted) (_h : acceptQtslOps deps ops = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet, l.seq.semanticallyValid H :=
  fun l _ H => l.valid.down H

/-- **Soundness of sealed-byte acceptance**: theory-Qtsl rows in, per-
claim semantic validity out. -/
theorem acceptQtslSealed_sound (bs : Bytes) (a : QtslAccepted)
    (_h : acceptQtslSealed bs = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet, l.seq.semanticallyValid H :=
  fun l _ H => l.valid.down H

/-! ### The four E4 altitudes at the Qtsl stratum

Each is one `Iff.mp` of a landed identification applied to the carried
validity — `CheckerAcceptance`'s design, mirrored.  Quantifier delta vs
E4, honest: E4's accepted value pins the certificate's own hypernet;
v1 Qtsl leaves are wire-free, so these hold over every context — the
∀-genericity is the fragment speaking, not extra strength. -/

/-- Acceptance at the checker face: the vanishing upper probability of
the accepted conclusion's complement over the credal compile of the
premise-and-admissibility cylinder. -/
theorem acceptQtslSealed_face_sound (bs : Bytes) (a : QtslAccepted)
    (_h : acceptQtslSealed bs = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet,
      Plain.upperProb (Plain.admCyl H l.seq) (Plain.postEvt H l.seq)ᶜ = 0 :=
  fun l _ H =>
    (Plain.semanticallyValid_iff_face H l.seq).mp (l.valid.down H)

/-- Acceptance at the model class: the cylinder's wall belongs to the
model class of the accepted sequent's presentation. -/
theorem acceptQtslSealed_modelClass_sound (bs : Bytes) (a : QtslAccepted)
    (_h : acceptQtslSealed bs = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet,
      Adequacy.cylWall H l.seq ∈
        (Adequacy.sequentDnf H l.seq).modelClass :=
  fun l _ H =>
    (Adequacy.semanticallyValid_iff_mem_modelClass H l.seq).mp
      (l.valid.down H)

/-- Acceptance at the record space: the checker face read over the
state space of the context's wire object along the valuation
embedding. -/
theorem acceptQtslSealed_face_valWire_sound (bs : Bytes)
    (a : QtslAccepted) (_h : acceptQtslSealed bs = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet,
      Plain.upperProb (Adequacy.valState '' Plain.admCyl H l.seq)
        ((Adequacy.valState '' Plain.postEvt H l.seq))ᶜ = 0 :=
  fun l _ H =>
    (Adequacy.semanticallyValid_iff_face_valWire H l.seq).mp
      (l.valid.down H)

/-- **Acceptance in the semantic universe**: a claim accepted from
theory-Qtsl rows is a judgment in the semantic universe — the
cylinder's wall system belongs to the model class of the accepted
sequent's presentation, in the fibre over the context's wire object.
The end-to-end theorem of the QtslSem route: theory rows in, fibre
citizenship out, over every context. -/
theorem acceptQtslSealed_su_sound (bs : Bytes) (a : QtslAccepted)
    (_h : acceptQtslSealed bs = some a) :
    ∀ l ∈ a.leaves, ∀ H : Hypernet,
      Adequacy.cylWallW H l.seq ∈
        (Adequacy.sequentSpec H l.seq).modelClass :=
  fun l _ H =>
    (Adequacy.semanticallyValid_iff_fibre H l.seq).mp (l.valid.down H)

/-! ## Transport: accepted claims along context extensions

The extend route through acceptance — the accepted leaf's generator
spliced into the cite derivation by simultaneous substitution: an
empty-tops composite with extension-arrow tights, generic in the
accepted leaf (the seam's `decodedCiteDeriv`, with the fixture's decode
equality replaced by the carried checks).  The composition happens
inside the calculus: one covering, one `mapCell` trip. -/

/-- The accepted leaf's cite derivation along an extension arrow:
extend-then-weaken consuming the accepted generator — no premises
remain. -/
def acceptedCiteDeriv (l : AcceptedLeaf) {a b : BLHCtx} (e : a ⟶ b)
    (rider : Formula) :
    DerivT blPresentationM .nil (citeFacet l.seq rider) e e :=
  DerivT.subst (citeDeriv e l.seq rider (l.scopedAll a.ctx))
    (DerivSeqT.cons
      (DerivT.gen (P := blPresentationM) (.emb a.ctx (acceptedLeafRule l))
        (acceptedLeafRule_gate l a.ctx))
      (DerivSeqT.nil (𝟙 a)))

/-- The accepted cite composite as a multicell of the presented virtual
double category, framed by the extension arrow on both tight sides. -/
def acceptedCiteCell (l : AcceptedLeaf) {a b : BLHCtx} (e : a ⟶ b)
    (rider : Formula) :
    VirtualDoubleCategoryData.Cell (C := Presented blPresentationM)
      (decodedCiteTops a)
      ((citeFacet l.seq rider : Sequent) :
        VirtualDoubleCategoryData.Loose (.of b) (.of b))
      (e : Presented.of a ⟶ Presented.of b) e := by
  exact ⟨⟨acceptedCiteDeriv l e rider⟩⟩

/-- Its covering in the free promotion — empty tops, extension-arrow
tights. -/
def acceptedCiteCovering (l : AcceptedLeaf) {x y : BLHCtx} (e : x ⟶ y)
    (rider : Formula) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented blPresentationM))
      (a := .of (.of x)) (b := .of (.of x))
      (c := .of (.of y)) (d := .of (.of y))
      (decodedCiteTops x)
      (LoosePath.single ((citeFacet l.seq rider : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of y)
          (Presented.of y)))
      (e : FreePromotion.of (Presented.of x) ⟶ .of (.of y)) e := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (acceptedCiteCell l e rider)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The accepted facet's validity over the extended context**: no
hypotheses beyond the accepted leaf — its gate was checked at
acceptance, and the derivation composed the generator with the
transport inside the calculus. -/
theorem acceptedCiteFacet_valid_through_M (l : AcceptedLeaf)
    {a b : BLHCtx} (e : a ⟶ b) (rider : Formula) :
    (citeFacet l.seq rider).semanticallyValid b.ctx := by
  have himp := (qtslSemBLM.mapCell (acceptedCiteCovering l e rider)).down
  exact (himp trivial).1

/-- The accepted facet's validity through the judgment-layer route. -/
theorem acceptedCiteFacet_valid_through_MJ (l : AcceptedLeaf)
    {a b : BLHCtx} (e : a ⟶ b) (rider : Formula) :
    (citeFacet l.seq rider).semanticallyValid b.ctx := by
  obtain ⟨_, himp⟩ :=
    (qtslSemBLMJ.mapCell (acceptedCiteCovering l e rider)).down
  exact (himp trivial).1

/-- The accepted leaf cited into a disjoint union from the left, at the
checker face. -/
theorem acceptedCiteLeft_face_through_promotionM (l : AcceptedLeaf)
    {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2) (rider : Formula) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet l.seq rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet l.seq rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet l.seq rider)).mp
    (acceptedCiteFacet_valid_through_M l (extLeft hd) rider)

/-- The accepted leaf cited into a disjoint union from the right, at
the checker face. -/
theorem acceptedCiteRight_face_through_promotionM (l : AcceptedLeaf)
    {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2) (rider : Formula) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet l.seq rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet l.seq rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet l.seq rider)).mp
    (acceptedCiteFacet_valid_through_M l (extRight hd) rider)

/-- The left cite, judgment-layer route. -/
theorem acceptedCiteLeft_face_through_promotionMJ (l : AcceptedLeaf)
    {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2) (rider : Formula) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet l.seq rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet l.seq rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet l.seq rider)).mp
    (acceptedCiteFacet_valid_through_MJ l (extLeft hd) rider)

/-! ## Correspondence: acceptance agrees with the S1 decode

Acceptance re-runs the decoder's own scan and assembly, so an accepted
value's presentation IS the decode's, and its leaf roster pairs the
eval-routed satisfaction claims with their decoded leaf sequents — the
seam enumerator's cargo.  (The generic `satLeafSequents` equation is
named residue: it wants `List.filterMapM` unfolding lemmas; the
`Forall₂` form below carries the same content, and the fixture-level
tie is exact.) -/

/-- An accepted ground leaf records the element it was given. -/
theorem acceptGroundLeaf_elem {n : Nat} {s : Sequent} {l : AcceptedLeaf}
    (h : acceptGroundLeaf n s = some l) : l.elem = n := by
  unfold acceptGroundLeaf at h
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

/-- An accepted ground leaf records the sequent it was given. -/
theorem acceptGroundLeaf_seq {n : Nat} {s : Sequent} {l : AcceptedLeaf}
    (h : acceptGroundLeaf n s = some l) : l.seq = s := by
  unfold acceptGroundLeaf at h
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

/-- An accepted leaf's sequent is its claimed leaf's decoded
conclusion. -/
theorem acceptLeaf_seq {tb : QRowTbls} {n p : Nat} {l : AcceptedLeaf}
    (h : acceptLeaf tb n p = some l) :
    leafSequent tb p = .ok l.seq := by
  unfold acceptLeaf at h
  split at h
  any_goals contradiction
  rename_i s heq
  rw [heq, acceptGroundLeaf_seq h]

/-- An accepted leaf records its claim's element. -/
theorem acceptLeaf_elem {tb : QRowTbls} {n p : Nat} {l : AcceptedLeaf}
    (h : acceptLeaf tb n p = some l) : l.elem = n := by
  unfold acceptLeaf at h
  split at h
  any_goals contradiction
  exact acceptGroundLeaf_elem h

/-- **The roster correspondence**: an accepted leaf list pairs the
satisfaction claims one-to-one — each claim carries an evaluation route
whose leaf decodes to exactly the accepted sequent, and is either
warrant-free or an alias citation whose walk succeeded (the resolved
threshold matched by the accepted sequent's sublevel reading). -/
theorem acceptLeaves_spec {tb : QRowTbls} {rsl : List QRegionSatVal}
    {sats : List QSatVal} {ls : List AcceptedLeaf}
    (h : acceptLeaves tb rsl sats = some ls) :
    List.Forall₂ (fun sat l =>
      l.elem = sat.elem ∧
      (∃ p, sat.evalLeaf = some p ∧ leafSequent tb p = .ok l.seq) ∧
      (sat.warrant = none ∨
        ∃ f w thr, sat.warrant = some (f, w) ∧
          resolveCitation tb rsl sat.spec f w = some thr ∧
          sequentMatchesSublevel l.seq thr = true))
      sats ls := by
  induction sats generalizing ls with
  | nil =>
      unfold acceptLeaves at h
      injection h with h
      subst h
      exact .nil
  | cons sat rest ih =>
      unfold acceptLeaves at h
      split at h
      any_goals contradiction
      · rename_i p hw he
        split at h
        any_goals contradiction
        rename_i l hal
        split at h
        any_goals contradiction
        rename_i ls' hrec
        injection h with h
        subst h
        exact .cons
          ⟨acceptLeaf_elem hal, ⟨p, he, acceptLeaf_seq hal⟩, .inl hw⟩
          (ih hrec)
      · rename_i f w p hw he
        split at h
        any_goals contradiction
        rename_i thr hres
        split at h
        any_goals contradiction
        rename_i s hseq
        split at h
        any_goals contradiction
        rename_i hmatch
        split at h
        any_goals contradiction
        rename_i l hgl
        split at h
        any_goals contradiction
        rename_i ls' hrec
        injection h with h
        subst h
        refine .cons ⟨acceptGroundLeaf_elem hgl, ⟨p, he, ?_⟩,
          .inr ⟨f, w, thr, hw, hres, ?_⟩⟩ (ih hrec)
        · rw [acceptGroundLeaf_seq hgl]
          exact hseq
        · rw [acceptGroundLeaf_seq hgl]
          exact hmatch

/-- **The acceptance–decode correspondence**: an accepted value's
presentation is the S1 decode's, and its leaves pair the satisfaction
claims per `acceptLeaves_spec` — against the same scanned tables. -/
theorem accept_spec {deps : List Bytes} {ops : List GOp}
    {a : QtslAccepted} (h : acceptQtslOps deps ops = some a) :
    ∃ tb, scanQtslOps deps ops = .ok tb ∧
      decodeQtslPresentationOps deps ops = .ok a.pres ∧
      List.Forall₂ (fun sat l =>
        l.elem = sat.elem ∧
        (∃ p, sat.evalLeaf = some p ∧ leafSequent tb p = .ok l.seq) ∧
        (sat.warrant = none ∨
          ∃ f w thr, sat.warrant = some (f, w) ∧
            resolveCitation tb a.pres.regionSats sat.spec f w
              = some thr ∧
            sequentMatchesSublevel l.seq thr = true))
        a.pres.sats a.leaves := by
  unfold acceptQtslOps at h
  split at h
  any_goals contradiction
  rename_i tb hscan
  split at h
  any_goals contradiction
  rename_i pres hasm
  split at h
  any_goals contradiction
  split at h
  any_goals contradiction
  rename_i ls hlv
  injection h with h
  subst h
  refine ⟨tb, hscan, ?_, acceptLeaves_spec hlv⟩
  unfold decodeQtslPresentationOps
  rw [hscan]
  exact hasm

/-! ## The fixture: the S1 staged rows, through acceptance

The same hand-staged op list the decoder's own fixture drives
(`fixtureOps`: one `QSat` with an evaluation route to the leaf
`⊤ ⊢ (2 + 4) = 6`), now driven through the ACCEPTANCE route — and
refusal fixtures for every named out-of-fragment tier, each a green
theorem on a variant op list. -/

/-- The staged leaf's gate fact (`norm_num`, not `decide`: closed `Rat`
arithmetic is not kernel-reducible under the `Decidable` instances —
the campaign's lesson (j)). -/
theorem fixtureEval :
    (Formula.atom .eq (.add (.const 2) (.const 4))
      (.const 6)).evalClosed = some true := by
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The expected accepted leaf of the staged rows. -/
def fixtureLeaf : AcceptedLeaf where
  elem := 5
  seq := leafSeqDemo
  cmp := .eq
  lhs := .add (.const 2) (.const 4)
  rhs := .const 6
  post_eq := rfl
  eval_true := fixtureEval
  preWF := rfl
  postWF := rfl
  valid := ⟨fun H => groundLeaf_valid_through_M fixtureEval rfl H⟩

/-- The expected accepted value of the staged rows. -/
def fixtureAccepted : QtslAccepted :=
  ⟨fixtureExpected, [fixtureLeaf]⟩

/-- The staged leaf is accepted, with the expected cargo.  (Proof
discipline, banked from the r1 stall: every heavy reduction rides the
KERNEL — the `key` equations are small iota/delta defeqs that never
evaluate the tables, `decide` carries the scans, and the one stuck
redex — the Rat-arithmetic gate — is crossed by `dif_pos`/`dif_neg`
with its `norm_num` fact; no elaborator-side `whnf` of the chain.) -/
theorem acceptGroundLeaf_fixture :
    acceptGroundLeaf 5 leafSeqDemo = some fixtureLeaf := by
  have key : acceptGroundLeaf 5 leafSeqDemo =
      if _h : (Formula.atom .eq (.add (.const 2) (.const 4))
          (.const 6)).evalClosed = some true then
        some fixtureLeaf
      else none := rfl
  rw [key, dif_pos fixtureEval]

/-- The staged claim's leaf is accepted through the decode. -/
theorem acceptLeaf_fixture :
    acceptLeaf fixtureTbls 5 7 = some fixtureLeaf := by
  have key : acceptLeaf fixtureTbls 5 7 =
      acceptGroundLeaf 5 leafSeqDemo := by
    unfold acceptLeaf
    rw [fixture_leaf_seq]
  rw [key, acceptGroundLeaf_fixture]

/-- The staged claim roster is accepted whole. -/
theorem acceptLeaves_fixture :
    acceptLeaves fixtureTbls fixtureExpected.regionSats
      fixtureExpected.sats = some [fixtureLeaf] := by
  have key : acceptLeaves fixtureTbls fixtureExpected.regionSats
      fixtureExpected.sats =
      (match acceptLeaf fixtureTbls 5 7 with
       | none => none
       | some l => some [l]) := rfl
  rw [key, acceptLeaf_fixture]

/-- **The acceptance fixture**: the staged rows are accepted whole —
presentation and leaf roster exactly as expected. -/
theorem accept_fixture :
    acceptQtslOps fixtureDeps fixtureOps = some fixtureAccepted := by
  have k1 : acceptQtslOps fixtureDeps fixtureOps =
      (match assembleQtsl fixtureTbls with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGate pres then
           match acceptLeaves fixtureTbls pres.regionSats pres.sats with
           | none => none
           | some ls => some ⟨pres, ls⟩
         else none) := by
    unfold acceptQtslOps
    rw [(by decide :
      scanQtslOps fixtureDeps fixtureOps = .ok fixtureTbls)]
  rw [k1, (by decide :
    assembleQtsl fixtureTbls = .ok fixtureExpected)]
  show (if acceptFragmentGate fixtureExpected then
          match acceptLeaves fixtureTbls fixtureExpected.regionSats
            fixtureExpected.sats with
          | none => none
          | some ls => some (⟨fixtureExpected, ls⟩ : QtslAccepted)
        else none) = some fixtureAccepted
  rw [if_pos (by decide : acceptFragmentGate fixtureExpected = true),
    acceptLeaves_fixture]
  rfl

/-- The accepted presentation is the decoded one (projection form). -/
theorem accept_fixture_pres :
    (acceptQtslOps fixtureDeps fixtureOps).map QtslAccepted.pres =
      some fixtureExpected := by
  rw [accept_fixture]
  rfl

/-- The accepted leaf roster's data (projection form). -/
theorem accept_fixture_leaves :
    (acceptQtslOps fixtureDeps fixtureOps).map
      (fun a => a.leaves.map fun l => (l.elem, l.seq)) =
      some [(5, leafSeqDemo)] := by
  rw [accept_fixture]
  rfl

/-- The fixture-level enumerator tie: acceptance's roster is exactly
the seam enumerator's output on the same tables and presentation. -/
theorem accept_fixture_matches_enumerator :
    satLeafSequents fixtureTbls fixtureExpected =
      .ok (fixtureAccepted.leaves.map fun l => (l.elem, l.seq)) :=
  satLeafSequents_fixture

/-- **Row bytes to the checker face through acceptance, no
hypotheses**: the staged rows' accepted leaf at the checker face over
any context — extracted from the acceptance value, not from the S1
fixture theorems. -/
theorem accepted_fixture_face_through_M (H : Hypernet) :
    Plain.upperProb (Plain.admCyl H leafSeqDemo)
      (Plain.postEvt H leafSeqDemo)ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (acceptQtslOps_sound fixtureDeps fixtureOps fixtureAccepted
      accept_fixture fixtureLeaf (List.Mem.head _) H)

/-- Row bytes to fibre citizenship through acceptance, no hypotheses:
the SU-judgment endpoint on the staged rows. -/
theorem accepted_fixture_su_sound (H : Hypernet) :
    Adequacy.cylWallW H leafSeqDemo ∈
      (Adequacy.sequentSpec H leafSeqDemo).modelClass :=
  (Adequacy.semanticallyValid_iff_fibre H leafSeqDemo).mp
    (acceptQtslOps_sound fixtureDeps fixtureOps fixtureAccepted
      accept_fixture fixtureLeaf (List.Mem.head _) H)

/-! ### Refusal fixtures (each green; the prereg'd mutants disable the
corresponding check to prove the refusal load-bearing) -/

/-- A claim with no route at all: the eval relation dropped. -/
def fixtureOpsRouteless : List GOp :=
  fixtureDecls ++ fixtureGround ++ fixtureSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A routeless claim refuses** — nothing is accepted vacuously.
(`isNone` + `decide` puts the whole evaluation in the kernel; the
refusal path never constructs a carried proof, so the reduction is
pure table-and-match work.) -/
theorem refuse_routeless :
    acceptQtslOps fixtureDeps fixtureOpsRouteless = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The region tier staged FREESTANDING: a `QRegionSat` child
(elements 17–18) beside the intact evaluation route, cited by no
warrant — a claim v1 cannot discharge, present in the container. -/
def fixtureOpsRegionTier : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 61)] ++                                   -- 19 : StatePred
    fixtureGround ++ fixtureSpecRows ++ fixtureClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 0)),    -- QRegionSat/judgment
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 19)),   -- QRegionSat/formula
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17))]   -- QRegionSat/region

/-- **The freestanding region tier refuses at the fragment gate**: a
region-satisfaction row cited by no claim's warrant is a claim nobody
walked, and the fragment discharges nothing it did not check.  (Since
the v1.1 citation walk this is the coverage conjunct's witness — its
prereg'd mutant deletes that conjunct and expects exactly this theorem
red.) -/
theorem refuse_region_tier :
    acceptQtslOps fixtureDeps fixtureOpsRegionTier = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- A warrant-routed claim: a ternary `qsat_warrant` citation to a
staged `QRegionSat` child in place of the evaluation route — at the
event-4 grid with an `SInit`-formed face (18's formula IS the face's
argument), the demand row at the wire order, everything the warrant
walk checks in place EXCEPT the membership leaf.  (Since the v1.1
citation walk, singly guarded, documented: the region row is
warrant-cited so the coverage gate passes; what refuses is the route
match — a warrant without its membership leaf is not the citation
shape.  The walk-refusal loci have their own fixtures in
`AliasAcceptance`.) -/
def fixtureOpsWarrantRouted : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 155),                                     -- 18 : QRegionSat
     .elta (.ext 0 61)] ++                                   -- 19 : StatePred (φ)
    fixtureGround ++
    [.funa (.ext 0 653) [.ref (.loc 19)] (.ref (.loc 3)),    -- SInit (the face)
     .rela (.ext 0 742) [.ref (.loc 3), .ref (.loc 2)],      -- spec_forall
     .funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 18)],       -- qsat_warrant (f, sat, warrant)
     .funa (.ext 0 938) [.ref (.loc 18)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 18)] (.ref (.loc 19)),   -- formula = φ
     .funa (.ext 0 940) [.ref (.loc 18)] (.ref (.loc 17)),
     .rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)],     -- qtsl_init_member (region, sys)
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

/-- **A warrant-routed claim refuses**: the warrant route is the
class-stratum campaign's, not v1's. -/
theorem refuse_warrant_routed :
    acceptQtslOps fixtureDeps fixtureOpsWarrantRouted = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The statistical tier staged: a `QSatConf` row (element 17). -/
def fixtureOpsStatistical : List GOp :=
  fixtureDecls ++
    [.elta (.ext 0 152)] ++                                  -- 17 : QSatConf
    fixtureGround ++ fixtureSpecRows ++ fixtureClaimRows ++
    [.funa (.ext 0 928) [.ref (.loc 17)] (.ref (.loc 0)),    -- QSatConf/judgment
     .funa (.ext 0 929) [.ref (.loc 17)] (.ref (.loc 1)),    -- QSatConf/sys
     .funa (.ext 0 930) [.ref (.loc 17)] (.ref (.loc 2)),    -- QSatConf/spec
     .funa (.ext 0 931) [.ref (.loc 17)] (.lit 0 [1, 9, 10])] -- QSatConf/alpha

/-- **The statistical tier refuses** at the fragment gate. -/
theorem refuse_statistical_tier :
    acceptQtslOps fixtureDeps fixtureOpsStatistical = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- A non-atom ground conclusion staged: the leaf's post is `⊤ ∧ ⊤`
(element 14 rebuilt by `FAnd` — still ground, still true, but outside
the wired `pConstExact` class). -/
def fixtureOpsNonAtom : List GOp :=
  fixtureDecls ++
    [.funa (.ext 0 336) [.lit 0 [1, 2, 1]] (.ref (.loc 9)),
     .funa (.ext 0 336) [.lit 0 [1, 4, 1]] (.ref (.loc 10)),
     .funa (.ext 0 337) [.ref (.loc 9), .ref (.loc 10)] (.ref (.loc 11)),
     .funa (.ext 0 336) [.lit 0 [1, 6, 1]] (.ref (.loc 12)),
     .funa (.ext 0 352) [] (.ref (.loc 13)),                 -- FTrue
     .funa (.ext 0 350) [.ref (.loc 13), .ref (.loc 13)]
       (.ref (.loc 14)),                                     -- FAnd ⊤ ⊤
     .funa (.ext 0 354) [.ref (.loc 8)] (.ref (.loc 13)),
     .funa (.ext 0 355) [.ref (.loc 8)] (.ref (.loc 14)),
     .funa (.ext 0 358) [.ref (.loc 7)] (.ref (.loc 8))] ++
    fixtureSpecRows ++ fixtureClaimRows

/-- **A non-atom conclusion refuses** at the shape match — even a true
one: the v1 class is the wired `pConstExact` generator, exactly. -/
theorem refuse_nonatom_concl :
    acceptQtslOps fixtureDeps fixtureOpsNonAtom = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The eval-false variant: the staged conclusion is `(2 + 4) = 7`. -/
def fixtureOpsEvalFalse : List GOp :=
  fixtureDecls ++
    [.funa (.ext 0 336) [.lit 0 [1, 2, 1]] (.ref (.loc 9)),
     .funa (.ext 0 336) [.lit 0 [1, 4, 1]] (.ref (.loc 10)),
     .funa (.ext 0 337) [.ref (.loc 9), .ref (.loc 10)] (.ref (.loc 11)),
     .funa (.ext 0 336) [.lit 0 [1, 7, 1]] (.ref (.loc 12)),  -- TConst 7
     .funa (.ext 0 352) [] (.ref (.loc 13)),
     .funa (.ext 0 345) [.ref (.loc 11), .ref (.loc 12)] (.ref (.loc 14)),
     .funa (.ext 0 354) [.ref (.loc 8)] (.ref (.loc 13)),
     .funa (.ext 0 355) [.ref (.loc 8)] (.ref (.loc 14)),
     .funa (.ext 0 358) [.ref (.loc 7)] (.ref (.loc 8))] ++
    fixtureSpecRows ++ fixtureClaimRows

/-- The false atom's evaluation fact. -/
theorem fixtureEvalFalse :
    (Formula.atom .eq (.add (.const 2) (.const 4))
      (.const 7)).evalClosed = some false := by
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The eval-false variant's scanned tables. -/
def fixtureTblsEvalFalse : QRowTbls :=
  match scanQtslOps fixtureDeps fixtureOpsEvalFalse with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- The eval-false variant's decoded leaf sequent. -/
def leafSeqEvalFalse : Sequent :=
  ⟨.tt, .atom .eq (.add (.const 2) (.const 4)) (.const 7)⟩

/-- **A false evaluation refuses** at the gate: acceptance discharges
claims, so a claim whose leaf evaluates false cannot be accepted.
(Same kernel-first proof discipline as `accept_fixture`; the
presentation of the variant is `fixtureExpected` verbatim — term rows
never enter the presentation, which is exactly why the gate must
re-evaluate the leaf.) -/
theorem refuse_eval_false :
    acceptQtslOps fixtureDeps fixtureOpsEvalFalse = none := by
  have hgl : acceptGroundLeaf 5 leafSeqEvalFalse = none := by
    have key : acceptGroundLeaf 5 leafSeqEvalFalse =
        if h : (Formula.atom .eq (.add (.const 2) (.const 4))
            (.const 7)).evalClosed = some true then
          some { elem := 5, seq := leafSeqEvalFalse, cmp := .eq,
                 lhs := .add (.const 2) (.const 4), rhs := .const 7,
                 post_eq := rfl, eval_true := h,
                 preWF := rfl, postWF := rfl,
                 valid := ⟨fun H =>
                   groundLeaf_valid_through_M h rfl H⟩ }
        else none := rfl
    rw [key, dif_neg (by simp [fixtureEvalFalse])]
  have hal : acceptLeaf fixtureTblsEvalFalse 5 7 = none := by
    have hleafEF : leafSequent fixtureTblsEvalFalse 7 =
        .ok leafSeqEvalFalse := rfl
    have key : acceptLeaf fixtureTblsEvalFalse 5 7 =
        acceptGroundLeaf 5 leafSeqEvalFalse := by
      unfold acceptLeaf
      rw [hleafEF]
    rw [key, hgl]
  have halv : acceptLeaves fixtureTblsEvalFalse fixtureExpected.regionSats
      fixtureExpected.sats = none := by
    have key : acceptLeaves fixtureTblsEvalFalse fixtureExpected.regionSats
        fixtureExpected.sats =
        (match acceptLeaf fixtureTblsEvalFalse 5 7 with
         | none => none
         | some l => some [l]) := rfl
    rw [key, hal]
  have k1 : acceptQtslOps fixtureDeps fixtureOpsEvalFalse =
      (match assembleQtsl fixtureTblsEvalFalse with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGate pres then
           match acceptLeaves fixtureTblsEvalFalse pres.regionSats
             pres.sats with
           | none => none
           | some ls => some ⟨pres, ls⟩
         else none) := by
    unfold acceptQtslOps
    rw [(by decide :
      scanQtslOps fixtureDeps fixtureOpsEvalFalse = .ok fixtureTblsEvalFalse)]
  rw [k1, (by decide :
    assembleQtsl fixtureTblsEvalFalse = .ok fixtureExpected)]
  show (if acceptFragmentGate fixtureExpected then
          match acceptLeaves fixtureTblsEvalFalse fixtureExpected.regionSats
            fixtureExpected.sats with
          | none => none
          | some ls => some (⟨fixtureExpected, ls⟩ : QtslAccepted)
        else none) = none
  rw [if_pos (by decide : acceptFragmentGate fixtureExpected = true),
    halv]

end Decode

end QtslSem

end SuFunctor
