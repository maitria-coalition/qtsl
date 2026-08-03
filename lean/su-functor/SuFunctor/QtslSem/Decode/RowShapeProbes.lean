import SuFunctor.QtslSem.Decode.Warrant

/-!
# Row-shape probes: the acceptance fragment's shape boundary, pinned

Behavior-DOCUMENTING fixtures.  The acceptance fragment treats a
pinned relation's rows in one of five ways, and these probes pin the
boundary between row-shape corruption that refuses and row-shape
corruption that is silently carried — **as of the demand-shape walk**
(`demandRelSane`, the successor this module's first form was built to
flip loudly for; that form's five demand accept-cells are now the
four refusal cells + the one deliberate carry below):

- **route relations** (`qsat_warrant`, `qsat_eval`) are walked whole
  (`routeRelSane3` / `routeRelSaneSnd`): every row's arity and claim
  citation are checked, so a malformed row refuses even when a green
  row sits beside it;
- **component relations** (`spec_forall`, `spec_exists`) are walked
  for arity and spec-citation (`compRelSane`); the component argument
  is checked only where the citing spec is decoded;
- **demanded relations** (`qtsl_init_member`) are shape-walked whole
  (`demandRelSane`: binary, `QRegionAtom`-sorted first argument,
  `System`-sorted second) and then read existentially (`contains`
  with the exact demanded row).  An ill-SHAPED row — swapped
  arguments, wrong arity, a ground literal — refuses loudly at
  assembly; a WELL-FORMED extra row (duplicates included) is carried:
  it denotes a point of the relation's semantic table, and the
  monotone existential read must never refuse denoting content.  The
  walk polices the denotation boundary; the read stays monotone;
- **field functions** (`QSat/judgment` and kin) are read exactly-one
  per subject under an exact-shape key: a duplicate WELL-FORMED row
  refuses, while a duplicate row with corrupted arity is dropped by
  the key filter and silently carried — corruption makes a field row
  harder to see, not easier (the inversion is unchanged by the demand
  walk, whose scope is exactly the read demand relation);
- rows of pinned relations the fragment does not read are carried
  silently a fortiori.

Soundness posture unchanged (CertRows): acceptance quantifies over
whatever was reconstructed, so the silence of the unread and
field-inversion classes costs diagnosis, never soundness.  What the
demand walk buys is the diagnosis: a producer whose demand-row
emission drifts (wire order, arity) now refuses at the reference
acceptor even while a green row rides beside the drift.  One honest
residual, carried from the design: acceptance is thereby non-monotone
in the RAW WIRE table — a future consumer that unions row tables
across commits must run the walk per-commit at the denotation
boundary, never over unions.

Scope note: these are ops-level probes (`acceptQtslOpsW`), like every
fixture in `Decode.Warrant` — they sit below the sealed reader, so
wire-level canonicity (which already excludes dangling and
non-element local references, refused at byte decode) is out of frame
here; every reference staged below is in range.  Schema references
are at the PRIMARY (event 5.1) counters, matching `fixtureDeps`.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC.Geolog

/-! ## Generic acceptance steps (the fixture proof, factored over the
table so each carrying variant reuses it) -/

/-- The fragment gate holds at the warranted fixture's presentation
(proved once; every accepting variant below decodes to this exact
presentation — that is part of what "silently carried" means). -/
private theorem gate_fixtureWarrantExpected :
    acceptFragmentGateW fixtureWarrantExpected = true := by decide

/-- The leaf acceptance step, generic in the table: any variant whose
leaf-relevant rows still read as the fixture's sequent accepts the
fixture's leaf. -/
theorem acceptLeaf_of {tb : QRowTbls}
    (hseq : leafSequent tb 7 = .ok leafSeqDemo) :
    acceptLeaf tb 5 7 = some fixtureLeaf := by
  unfold acceptLeaf
  rw [hseq]
  exact acceptGroundLeaf_fixture

/-- The warrant acceptance step, generic in the table: citation
resolution, face find, `SInit` match, and tie reduce over the fixture
literals; only the demand-row read and the leaf consult the table. -/
theorem acceptWarrantSat_of {tb : QRowTbls}
    (hmem : (tb.relRows "qtsl_init_member").contains
      [.ref (.loc 17), .ref (.loc 1)] = true)
    (hleaf : acceptLeaf tb 5 7 = some fixtureLeaf) :
    acceptWarrantSat tb [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 =
      some fixtureWarrant := by
  have key : acceptWarrantSat tb [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 =
      (if (tb.relRows "qtsl_init_member").contains
          [.ref (.loc 17), .ref (.loc 1)] then
        match acceptLeaf tb 5 7 with
        | none => none
        | some l =>
          some { elem := 5, sysElem := 1, fElem := 3, phiElem := 20,
                 region := ⟨18, 19, 20, 17⟩, root_tie := rfl,
                 leaf := l }
      else none) := rfl
  rw [key, if_pos hmem, hleaf]
  rfl

/-- The claim-roster step, generic in the table. -/
theorem acceptClaimsW_of {tb : QRowTbls}
    (h : acceptWarrantSat tb [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 =
      some fixtureWarrant) :
    acceptClaimsW tb fixtureWarrantExpected.regionSats
      fixtureWarrantExpected.sats = some [.inr fixtureWarrant] := by
  have key : acceptClaimsW tb fixtureWarrantExpected.regionSats
      fixtureWarrantExpected.sats =
      (match acceptWarrantSat tb [⟨18, 19, 20, 17⟩]
          ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 with
       | none => none
       | some aw => some [.inr aw]) := rfl
  rw [key, h]

/-- Whole-acceptor assembly of the three steps: any variant that
scans, assembles to the fixture presentation, and accepts the fixture
claim is accepted EXACTLY as the green fixture is — the extra content
it carries is invisible in the accepted value. -/
theorem acceptW_of {ops : List GOp} {tb : QRowTbls}
    (hscan : scanQtslOps fixtureDeps ops = .ok tb)
    (hasm : assembleQtsl tb = .ok fixtureWarrantExpected)
    (hclaims : acceptClaimsW tb fixtureWarrantExpected.regionSats
      fixtureWarrantExpected.sats = some [.inr fixtureWarrant]) :
    acceptQtslOpsW fixtureDeps ops = some fixtureWarrantAccepted := by
  unfold acceptQtslOpsW
  rw [hscan]
  show (match assembleQtsl tb with
        | .error _ => none
        | .ok pres =>
          if acceptFragmentGateW pres then
            match acceptClaimsW tb pres.regionSats pres.sats with
            | none => none
            | some es => some ⟨pres, es⟩
          else none) = some fixtureWarrantAccepted
  rw [hasm]
  show (if acceptFragmentGateW fixtureWarrantExpected then
          match acceptClaimsW tb fixtureWarrantExpected.regionSats
              fixtureWarrantExpected.sats with
          | none => none
          | some es => some (⟨fixtureWarrantExpected, es⟩ : QtslAcceptedW)
        else none) = some fixtureWarrantAccepted
  rw [if_pos gate_fixtureWarrantExpected, hclaims]
  rfl

/-! ## The deliberate carry: a WELL-FORMED extra demand row is
invisible (duplicates denote; the walk is not at-most-one) -/

/-- The green warranted fixture plus one EXTRA well-formed
`qtsl_init_member` row — an exact duplicate of the green demand row
(17, 1). -/
def opsExtraDupInit : List GOp :=
  fixtureOpsWarrant ++
    [.rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)]]

def tblsExtraDupInit : QRowTbls :=
  match scanQtslOps fixtureDeps opsExtraDupInit with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- The well-formed duplicate is invisible in the decoded
presentation — it passes the shape walk (it denotes) and the
existential read is blind to multiplicity … -/
theorem decode_extraDupInit :
    decodeQtslPresentationOps fixtureDeps opsExtraDupInit =
      .ok fixtureWarrantExpected := by decide

/-- … and in the accepted value: the duplicated unit is accepted
byte-for-byte as the green fixture is. -/
theorem accepts_extraDupInit :
    acceptQtslOpsW fixtureDeps opsExtraDupInit =
      some fixtureWarrantAccepted :=
  acceptW_of (tb := tblsExtraDupInit) (by decide) (by decide)
    (acceptClaimsW_of (acceptWarrantSat_of (by decide)
      (acceptLeaf_of (by rfl))))

/-! ## The flipped cells: ill-SHAPED demand rows refuse loudly at
assembly (`demandRelSane`), even beside the green row — the four
corruption modes this module's first form measured as silently
carried -/

/-- Extra row at the RETIRED wire order (sys, region) — the drift the
first form carried silently; the walk refuses it by sort (element 1
is `System`, not `QRegionAtom`). -/
def opsExtraSwappedInit : List GOp :=
  fixtureOpsWarrant ++
    [.rela (.ext 0 922) [.ref (.loc 1), .ref (.loc 17)]]

theorem decode_extraSwappedInit :
    decodeQtslPresentationOps fixtureDeps opsExtraSwappedInit =
      .error (.unreadable, "qtsl_init_member_region_not_atom", 1) := by
  decide

theorem refuses_extraSwappedInit :
    acceptQtslOpsW fixtureDeps opsExtraSwappedInit = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Extra unary row: refused by arity. -/
def opsExtraUnaryInit : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 922) [.ref (.loc 17)]]

theorem decode_extraUnaryInit :
    decodeQtslPresentationOps fixtureDeps opsExtraUnaryInit =
      .error (.unreadable, "qtsl_init_member_arity", 0) := by
  decide

theorem refuses_extraUnaryInit :
    acceptQtslOpsW fixtureDeps opsExtraUnaryInit = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Extra 4-ary row: refused by arity. -/
def opsExtraQuadInit : List GOp :=
  fixtureOpsWarrant ++
    [.rela (.ext 0 922)
      [.ref (.loc 17), .ref (.loc 1), .ref (.loc 17), .ref (.loc 1)]]

theorem decode_extraQuadInit :
    decodeQtslPresentationOps fixtureDeps opsExtraQuadInit =
      .error (.unreadable, "qtsl_init_member_arity", 0) := by
  decide

theorem refuses_extraQuadInit :
    acceptQtslOpsW fixtureDeps opsExtraQuadInit = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Extra row with a ground literal in the element-sorted first
position: a literal denotes no element, so the walk refuses at the
first argument's tag. -/
def opsExtraLitInit : List GOp :=
  fixtureOpsWarrant ++
    [.rela (.ext 0 922) [.lit 2 [1], .ref (.loc 1)]]

theorem decode_extraLitInit :
    decodeQtslPresentationOps fixtureDeps opsExtraLitInit =
      .error (.unreadable, "qtsl_init_member_region_not_atom", 0) := by
  decide

theorem refuses_extraLitInit :
    acceptQtslOpsW fixtureDeps opsExtraLitInit = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-! ## Unread pinned relations carry anything (out of the demand
walk's scope, deliberately: fragment tolerance for unread vocabulary) -/

/-- An ill-arity row of `qsat_verdict` (pinned, read by nothing in
the fragment). -/
def opsUnreadGarbage : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 936) [.ref (.loc 5)]]

def tblsUnreadGarbage : QRowTbls :=
  match scanQtslOps fixtureDeps opsUnreadGarbage with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

theorem decode_unreadGarbage :
    decodeQtslPresentationOps fixtureDeps opsUnreadGarbage =
      .ok fixtureWarrantExpected := by decide

theorem accepts_unreadGarbage :
    acceptQtslOpsW fixtureDeps opsUnreadGarbage =
      some fixtureWarrantAccepted :=
  acceptW_of (tb := tblsUnreadGarbage) (by decide) (by decide)
    (acceptClaimsW_of (acceptWarrantSat_of (by decide)
      (acceptLeaf_of (by rfl))))

/-! ## The field-row inversion: well-formed duplicates refuse,
corrupted duplicates are silently carried (unchanged by the demand
walk — the field read's exact-shape key is its own boundary) -/

/-- An exact duplicate of the claim's `QSat/judgment` row: the
exactly-one read sees both and REFUSES (`qsat_dup_judgment`). -/
def opsExactDupField : List GOp :=
  fixtureOpsWarrant ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0))]

theorem refuses_exactDupField :
    acceptQtslOpsW fixtureDeps opsExactDupField = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The same duplicate with a corrupted argument list (arity 2): the
exact-shape key filter drops it, so the CORRUPTED duplicate is
silently carried where the well-formed one refused. -/
def opsCorruptDupField : List GOp :=
  fixtureOpsWarrant ++
    [.funa (.ext 0 917) [.ref (.loc 5), .ref (.loc 5)] (.ref (.loc 0))]

def tblsCorruptDupField : QRowTbls :=
  match scanQtslOps fixtureDeps opsCorruptDupField with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

theorem decode_corruptDupField :
    decodeQtslPresentationOps fixtureDeps opsCorruptDupField =
      .ok fixtureWarrantExpected := by decide

theorem accepts_corruptDupField :
    acceptQtslOpsW fixtureDeps opsCorruptDupField =
      some fixtureWarrantAccepted :=
  acceptW_of (tb := tblsCorruptDupField) (by decide) (by decide)
    (acceptClaimsW_of (acceptWarrantSat_of (by decide)
      (acceptLeaf_of (by rfl))))

/-! ## The component-relation residual: a stray row on an undecoded
spec is carried (its component argument is checked only at decode) -/

/-- A second `Spec` element (21) no claim cites, with a `spec_forall`
row whose component argument (20, a `StatePred`) would refuse at
decode — but the stray spec is never decoded. -/
def opsStrayComponent : List GOp :=
  fixtureOpsWarrant ++
    [.elta (.ext 0 103),
     .rela (.ext 0 742) [.ref (.loc 20), .ref (.loc 21)]]

def tblsStrayComponent : QRowTbls :=
  match scanQtslOps fixtureDeps opsStrayComponent with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

theorem decode_strayComponent :
    decodeQtslPresentationOps fixtureDeps opsStrayComponent =
      .ok fixtureWarrantExpected := by decide

theorem accepts_strayComponent :
    acceptQtslOpsW fixtureDeps opsStrayComponent =
      some fixtureWarrantAccepted :=
  acceptW_of (tb := tblsStrayComponent) (by decide) (by decide)
    (acceptClaimsW_of (acceptWarrantSat_of (by decide)
      (acceptLeaf_of (by rfl))))

/-! ## The contrast column: route relations refuse the same
corruption shapes (the walks the demand walk now sits beside) -/

/-- An extra unary `qsat_warrant` row beside the green ternary one:
`routeRelSane3` refuses by arity. -/
def opsExtraUnaryWarrant : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 920) [.ref (.loc 5)]]

theorem refuses_extraUnaryWarrant :
    acceptQtslOpsW fixtureDeps opsExtraUnaryWarrant = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- An extra argument-swapped `qsat_eval` row: `routeRelSaneSnd`
refuses (its second argument is not a claim). -/
def opsExtraSwappedEval : List GOp :=
  fixtureOpsWarrant ++
    [.rela (.ext 0 921) [.ref (.loc 5), .ref (.loc 7)]]

theorem refuses_extraSwappedEval :
    acceptQtslOpsW fixtureDeps opsExtraSwappedEval = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- An extra unary `spec_forall` row: `compRelSane` refuses by
arity. -/
def opsExtraUnaryForall : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 742) [.ref (.loc 3)]]

theorem refuses_extraUnaryForall :
    acceptQtslOpsW fixtureDeps opsExtraUnaryForall = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-! ## Scan-level contrast: the pin table is a shape gate of its own
(and a stricter one than wire admission, which resolves no names) -/

/-- A row of an unpinned schema reference refuses the WHOLE scan. -/
def opsUnpinnedRel : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 9999) []]

theorem refuses_unpinnedRel :
    acceptQtslOpsW fixtureDeps opsUnpinnedRel = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- A relation row citing a FUNCTION pin refuses at the scan
(`fun_in_rel_position`). -/
def opsFnInRelPosition : List GOp :=
  fixtureOpsWarrant ++ [.rela (.ext 0 917) [.ref (.loc 5)]]

theorem refuses_fnInRelPosition :
    acceptQtslOpsW fixtureDeps opsFnInRelPosition = none :=
  Option.isNone_iff_eq_none.mp (by decide)

end Decode

end QtslSem

end SuFunctor
