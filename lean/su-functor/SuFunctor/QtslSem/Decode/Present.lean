import SuFunctor.QtslSem.Decode.Ground
import Reflection.Container

/-!
# `decodeQtslPresentation` — theory-Qtsl rows into the presentation

The S1 decoder proper (design: the QtslSem memo §3.4, in the CertRows
architecture): a fail-closed assembly of the scanned row tables into
the **row presentation** of the claim stratum — the judgment roster
(the loose-generator stock), the satisfaction claims with their
routes (warrant / evaluation / composite), the sibling judgment
kinds, and the proof roster (rule-instance citations, each concluding
exactly one judgment).  This value is what the class-stratum campaign
interprets: its judgment instances land in the two wired carriers
(`ImplDouble` at the truth stratum, `JudgLayer`/`SpecJudgLayer` at
the class stratum, whose tights are the `WireSpan` wire maps for the
wiring/simulation rules), and the `Decode.Binding` table carries the
row-vocabulary → lemma-name column the components wire against.

Fragment boundary (v1 at revision event 4): the claim spine decodes;
specifications decode as their COMPONENT RECORDS — the event-4
re-sort retired the single `Spec/root` in favor of `spec_forall` /
`spec_exists` component relations whose components are cap-valued
former applications (`SInit`, `SProbGE`, …) — each component
shallowly (former name + raw argument cells); region atoms, systems,
and battery kits ride as sort-checked element references.  The
soundness posture is CertRows', verbatim: downstream acceptance
quantifies over whatever was reconstructed — a decode defect can
lose completeness, never soundness.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC.Geolog

/-- A shallowly-decoded specification component: a cap-valued former
application (`ForallSpec`/`ExistsSpec` element, former name, raw
argument cells — deep former decode is per-row campaign material). -/
structure QSpecComponent where
  elem : Nat
  former : String
  args : List GValue
  deriving Repr, DecidableEq

/-- A shallowly-decoded specification at event 4: its element and its
component record — the safety-face components (`spec_forall`) and the
liveness-mark components (`spec_exists`), in row order. -/
structure QSpecVal where
  elem : Nat
  forallComps : List QSpecComponent
  existsComps : List QSpecComponent
  deriving Repr, DecidableEq

/-- The `SInit`-face arguments of a specification: the state-predicate
elements φ of its `SInit`-formed safety faces, in row order.  (The
event-4 reading of the retired "spec root": ties that keyed on
`Spec/root` now key on membership here.) -/
def QSpecVal.sinitPhis (sp : QSpecVal) : List Nat :=
  sp.forallComps.filterMap (fun c =>
    if c.former == "SInit" then
      match c.args with
      | [a] => elemOfVal a
      | _ => none
    else none)

/-- A decoded satisfaction claim (`QSat`): subject and specification
are exactly-one attributes; the closing content is optional by route —
at most one region-satisfaction warrant and at most one evaluation
leaf. -/
structure QSatVal where
  elem : Nat
  judgment : Nat
  sys : Nat
  spec : QSpecVal
  /-- The at-most-one warrant row's payload: the cited safety-face
  component `f` and the cited region-satisfaction row, as one pair —
  they arrive on one `qsat_warrant` row (f, sat, warrant). -/
  warrant : Option (Nat × Nat)
  evalLeaf : Option Nat
  deriving Repr, DecidableEq

/-- A decoded confidence-qualified claim (`QSatConf`). -/
structure QSatConfVal where
  elem : Nat
  judgment : Nat
  sys : Nat
  spec : QSpecVal
  alpha : Rat
  deriving Repr, DecidableEq

/-- A decoded specification-equivalence claim (`QSpecEquiv`). -/
structure QSpecEquivVal where
  elem : Nat
  judgment : Nat
  a : QSpecVal
  b : QSpecVal
  deriving Repr, DecidableEq

/-- A decoded region-satisfaction claim (`QRegionSat`): formula and
region ride as sort-checked references at this stratum. -/
structure QRegionSatVal where
  elem : Nat
  judgment : Nat
  formula : Nat
  region : Nat
  deriving Repr, DecidableEq

/-- A decoded invariance-scope claim (`QInvScope`). -/
structure QInvScopeVal where
  elem : Nat
  judgment : Nat
  region : Nat
  init : Nat
  deriving Repr, DecidableEq

/-- A decoded proof node: one `QProof` element concluding exactly one
judgment (species payloads are campaign material). -/
structure QProofVal where
  elem : Nat
  concludes : Nat
  deriving Repr, DecidableEq

/-- The decoded row presentation of the claim stratum. -/
structure QtslPresentation where
  judgments : List Nat
  sats : List QSatVal
  satConfs : List QSatConfVal
  specEquivs : List QSpecEquivVal
  regionSats : List QRegionSatVal
  invScopes : List QInvScopeVal
  proofs : List QProofVal
  deriving Repr, DecidableEq

/-- Decode one specification component: cap sort check, then the
component element constructed by exactly one former of the cap
roster. -/
def decodeSpecComponent (tb : QRowTbls) (capSort : String) (e : Nat) :
    QRes QSpecComponent := do
  let _ ← tb.demandSort e capSort "spec_face_not_cap_sorted"
  let (former, args) ← tb.ctor1 capFormers e
    "spec_face_unformed" "spec_face_ambiguous"
  pure ⟨e, former, args⟩

/-- Component elements a component relation attaches to one spec:
rows are (component, spec) — field names sorted bytewise, the wire
convention — so the spec is the SECOND argument. -/
def compElemsOf (tb : QRowTbls) (name : String) (spec : Nat) :
    List Nat :=
  (tb.relRows name).filterMap (fun args =>
    match args with
    | [c, s] =>
      if s == GValue.ref (.loc spec) then elemOfVal c else none
    | _ => none)

/-- Every row of a component relation must be binary and cite a
`Spec`-sorted element in its second argument (fail-closed; the
component argument is checked at the per-spec read). -/
def compRelSane (tb : QRowTbls) (name : String) (tag : String) :
    QRes Unit :=
  (tb.relRows name).foldlM (fun _ args =>
    match args with
    | [_, s] =>
      match elemOfVal s with
      | some e => tb.demandSort e "Spec" tag
      | none => qerr .unreadable tag 0
    | _ => qerr .unreadable (tag ++ "_arity") 0) ()

/-- Shallow spec decode at event 4: sort check, then the component
record — each safety face and liveness mark decoded against the cap
roster. -/
def decodeSpecVal (tb : QRowTbls) (e : Nat) : QRes QSpecVal := do
  let _ ← tb.demandSort e "Spec" "spec_not_spec_sorted"
  let fs ← (compElemsOf tb "spec_forall" e).mapM
    (decodeSpecComponent tb "ForallSpec")
  let es ← (compElemsOf tb "spec_exists" e).mapM
    (decodeSpecComponent tb "ExistsSpec")
  pure ⟨e, fs, es⟩

/-- The at-most-one optional route relation read, claim in the SECOND
position (the event-4 wire order of `qsat_eval` rows: (eval, sat) —
field names sorted bytewise): rows of `name` whose second argument is
the given claim, each demanding a first-argument element of sort
`argSort`. -/
def routeRelSnd (tb : QRowTbls) (name : String) (sat : Nat)
    (argSort : String) (badTag dupTag : String) : QRes (Option Nat) := do
  let rows := (tb.relRows name).filterMap (fun args =>
    match args with
    | [a, b] =>
      if b == GValue.ref (.loc sat) then some a else none
    | _ => none)
  match rows with
  | [] => pure none
  | [v] =>
    match elemOfVal v with
    | some w => do
      let _ ← tb.demandSort w argSort badTag
      pure (some w)
    | none => qerr .unreadable badTag sat
  | _ => qerr .unreadable dupTag sat

/-- The at-most-one warrant read (event-4 grid: `qsat_warrant` rows
are ternary, (f, sat, warrant)): the row's payload is the (f, warrant)
pair, each side sort-demanded. -/
def routeRel3 (tb : QRowTbls) (name : String) (sat : Nat)
    (fSort wSort : String) (badTag dupTag : String) :
    QRes (Option (Nat × Nat)) := do
  let rows := (tb.relRows name).filterMap (fun args =>
    match args with
    | [f, s, w] =>
      if s == GValue.ref (.loc sat) then some (f, w) else none
    | _ => none)
  match rows with
  | [] => pure none
  | [(fv, wv)] =>
    match elemOfVal fv, elemOfVal wv with
    | some f, some w => do
      let _ ← tb.demandSort f fSort (badTag ++ "_f")
      let _ ← tb.demandSort w wSort badTag
      pure (some (f, w))
    | _, _ => qerr .unreadable badTag sat
  | _ => qerr .unreadable dupTag sat

/-- Every row of a claim-second route relation must be binary and
cite an existing claim of the expected sort in its SECOND argument (a
stray, ill-sorted, or wrong-arity citation refuses — never a silent
drop; a row still on the event-3 grid refuses here by arity). -/
def routeRelSaneSnd (tb : QRowTbls) (name : String) (satSort : String)
    (tag : String) : QRes Unit :=
  (tb.relRows name).foldlM (fun _ args =>
    match args with
    | [_, b] =>
      match elemOfVal b with
      | some s => tb.demandSort s satSort tag
      | none => qerr .unreadable tag 0
    | _ => qerr .unreadable (tag ++ "_arity") 0) ()

/-- Every warrant row must be ternary with a claim of the expected
sort in its middle argument (an event-3 binary row refuses by
arity). -/
def routeRelSane3 (tb : QRowTbls) (name : String) (satSort : String)
    (tag : String) : QRes Unit :=
  (tb.relRows name).foldlM (fun _ args =>
    match args with
    | [_, s, _] =>
      match elemOfVal s with
      | some e => tb.demandSort e satSort tag
      | none => qerr .unreadable tag 0
    | _ => qerr .unreadable (tag ++ "_arity") 0) ()

/-- Every row of a DEMANDED relation must be binary with
sort-conformant element arguments — the shape walk beside the route
walks, policing the denotation boundary.  Shape only, deliberately:
the demand READ stays the monotone existential `contains` (adding any
row that denotes a point of the semantic table can never flip
accept→refuse), duplicates are legitimate (no at-most-one), and
relations the fragment does not read stay out of scope.  What refuses
is exactly a row-literal that denotes NO point of the relation's
domain: wrong arity (`name ++ "_arity"`), or a non-element or
ill-sorted argument (the per-argument tags). -/
def demandRelSane (tb : QRowTbls) (name : String)
    (fstSort sndSort : String) (fstTag sndTag : String) : QRes Unit :=
  (tb.relRows name).foldlM (fun _ args =>
    match args with
    | [a, b] =>
      match elemOfVal a, elemOfVal b with
      | some x, some y => do
        let _ ← tb.demandSort x fstSort fstTag
        tb.demandSort y sndSort sndTag
      | none, _ => qerr .unreadable fstTag 0
      | _, none => qerr .unreadable sndTag 0
    | _ => qerr .unreadable (name ++ "_arity") 0) ()

/-- Assemble the scanned tables into the row presentation,
fail-closed. -/
def assembleQtsl (tb : QRowTbls) : QRes QtslPresentation := do
  let judgments := tb.elemsOfSort "QJudgment"
  -- the satisfaction claims
  let _ ← compRelSane tb "spec_forall" "spec_forall_spec_not_spec"
  let _ ← compRelSane tb "spec_exists" "spec_exists_spec_not_spec"
  let _ ← routeRelSane3 tb "qsat_warrant" "QSat" "qsat_warrant_sat_not_qsat"
  let _ ← routeRelSaneSnd tb "qsat_eval" "QSat" "qsat_eval_sat_not_qsat"
  let _ ← demandRelSane tb "qtsl_init_member" "QRegionAtom" "System"
    "qtsl_init_member_region_not_atom" "qtsl_init_member_sys_not_system"
  let sats ← (tb.elemsOfSort "QSat").mapM (fun r => do
    let j ← tb.fld1Elem "QSat/judgment" r
      "qsat_missing_judgment" "qsat_dup_judgment"
    let _ ← tb.demandSort j "QJudgment" "qsat_judgment_not_qjudgment"
    let y ← tb.fld1Elem "QSat/sys" r "qsat_missing_sys" "qsat_dup_sys"
    let _ ← tb.demandSort y "System" "qsat_sys_not_system"
    let spE ← tb.fld1Elem "QSat/spec" r "qsat_missing_spec" "qsat_dup_spec"
    let sp ← decodeSpecVal tb spE
    let w ← routeRel3 tb "qsat_warrant" r "ForallSpec" "QRegionSat"
      "qsat_warrant_not_regionsat" "qsat_warrant_dup"
    let ev ← routeRelSnd tb "qsat_eval" r "Proof"
      "qsat_eval_not_proof" "qsat_eval_dup"
    pure (⟨r, j, y, sp, w, ev⟩ : QSatVal))
  -- the statistical tier
  let satConfs ← (tb.elemsOfSort "QSatConf").mapM (fun r => do
    let j ← tb.fld1Elem "QSatConf/judgment" r
      "qsatconf_missing_judgment" "qsatconf_dup_judgment"
    let _ ← tb.demandSort j "QJudgment" "qsatconf_judgment_not_qjudgment"
    let y ← tb.fld1Elem "QSatConf/sys" r
      "qsatconf_missing_sys" "qsatconf_dup_sys"
    let _ ← tb.demandSort y "System" "qsatconf_sys_not_system"
    let spE ← tb.fld1Elem "QSatConf/spec" r
      "qsatconf_missing_spec" "qsatconf_dup_spec"
    let sp ← decodeSpecVal tb spE
    let av ← tb.fld1 "QSatConf/alpha" r
      "qsatconf_missing_alpha" "qsatconf_dup_alpha"
    match qOfVal av with
    | some q => pure (⟨r, j, y, sp, q⟩ : QSatConfVal)
    | none => qerr .unreadable "qsatconf_alpha_not_q" r)
  -- specification equivalence
  let specEquivs ← (tb.elemsOfSort "QSpecEquiv").mapM (fun r => do
    let j ← tb.fld1Elem "QSpecEquiv/judgment" r
      "qspecequiv_missing_judgment" "qspecequiv_dup_judgment"
    let _ ← tb.demandSort j "QJudgment" "qspecequiv_judgment_not_qjudgment"
    let aE ← tb.fld1Elem "QSpecEquiv/a" r
      "qspecequiv_missing_a" "qspecequiv_dup_a"
    let bE ← tb.fld1Elem "QSpecEquiv/b" r
      "qspecequiv_missing_b" "qspecequiv_dup_b"
    pure (⟨r, j, ← decodeSpecVal tb aE, ← decodeSpecVal tb bE⟩ :
      QSpecEquivVal))
  -- region satisfaction
  let regionSats ← (tb.elemsOfSort "QRegionSat").mapM (fun r => do
    let j ← tb.fld1Elem "QRegionSat/judgment" r
      "qregionsat_missing_judgment" "qregionsat_dup_judgment"
    let _ ← tb.demandSort j "QJudgment" "qregionsat_judgment_not_qjudgment"
    let f ← tb.fld1Elem "QRegionSat/formula" r
      "qregionsat_missing_formula" "qregionsat_dup_formula"
    let _ ← tb.demandSort f "StatePred" "qregionsat_formula_not_statepred"
    let g ← tb.fld1Elem "QRegionSat/region" r
      "qregionsat_missing_region" "qregionsat_dup_region"
    let _ ← tb.demandSort g "QRegionAtom" "qregionsat_region_not_atom"
    pure (⟨r, j, f, g⟩ : QRegionSatVal))
  -- invariance scope
  let invScopes ← (tb.elemsOfSort "QInvScope").mapM (fun r => do
    let j ← tb.fld1Elem "QInvScope/judgment" r
      "qinvscope_missing_judgment" "qinvscope_dup_judgment"
    let _ ← tb.demandSort j "QJudgment" "qinvscope_judgment_not_qjudgment"
    let g ← tb.fld1Elem "QInvScope/region" r
      "qinvscope_missing_region" "qinvscope_dup_region"
    let _ ← tb.demandSort g "QRegionAtom" "qinvscope_region_not_atom"
    let i ← tb.fld1Elem "QInvScope/init" r
      "qinvscope_missing_init" "qinvscope_dup_init"
    let _ ← tb.demandSort i "QRegionAtom" "qinvscope_init_not_atom"
    pure (⟨r, j, g, i⟩ : QInvScopeVal))
  -- the proof roster: every proof concludes exactly one judgment
  let proofs ← (tb.elemsOfSort "QProof").mapM (fun p => do
    let j ← tb.fld1Elem "QProof/concludes" p
      "qproof_orphan" "qproof_dup_concludes"
    let _ ← tb.demandSort j "QJudgment" "qproof_concludes_not_qjudgment"
    pure (⟨p, j⟩ : QProofVal))
  pure ⟨judgments, sats, satConfs, specEquivs, regionSats, invScopes,
    proofs⟩

/-- Decode from dependency chids and body ops (the op-level entry the
fixtures drive). -/
def decodeQtslPresentationOps (deps : List Bytes) (ops : List GOp) :
    QRes QtslPresentation := do
  assembleQtsl (← scanQtslOps deps ops)

/-- Decode a sealed container's bytes: the reflection route's own
sealed reader, one commit demanded, then the row scan and assembly. -/
def decodeQtslPresentation (bs : Bytes) : QRes QtslPresentation :=
  match readGeologSealed bs with
  | .err c t w => .error (c, t, w)
  | .ok g =>
    match g.commits with
    | [commit] =>
      decodeQtslPresentationOps commit.cskel.deps commit.cbody.ops
    | _ => qerr .unsupported "multi_commit_unsupported" g.commits.length

/-! ## Proof-kit list walks (the battery species' premise carrier) -/

/-- Walk a `QProofList` cons-chain into its `Proof`-element list,
fuel-bounded: a dangling tail, a foreign constructor, or a cycle
refuses (never a silent reorder — the decoded list is positional in
the chain, so its order is canonical by construction). -/
def walkQProofList (tb : QRowTbls) : Nat → Nat → QRes (List Nat)
  | 0, e => qerr .unreadable "qpl_walk_fuel" e
  | fuel + 1, e => do
    let _ ← tb.demandSort e "QProofList" "qpl_not_qpl_sorted"
    let (n, args) ← tb.ctor1 ["qplNil", "qplCons"] e
      "qpl_ctor_missing" "qpl_ctor_ambiguous"
    match n, args with
    | "qplNil", [] => pure []
    | "qplCons", [h, t] =>
      match elemOfVal h, elemOfVal t with
      | some hd, some tl => do
        let _ ← tb.demandSort hd "Proof" "qpl_head_not_proof"
        pure (hd :: (← walkQProofList tb fuel tl))
      | _, _ => qerr .unreadable "qpl_cons_args" e
    | _, _ => qerr .unreadable "qpl_ctor_arity" e

/-- The standard fuel for kit walks: the element count bounds every
acyclic chain. -/
def QRowTbls.kitFuel (tb : QRowTbls) : Nat := tb.sorts.length + 1

end Decode

end QtslSem

end SuFunctor
