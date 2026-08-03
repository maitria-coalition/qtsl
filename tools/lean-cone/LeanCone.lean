/-
# lean-cone — statements-only audit surfaces for Lean developments

Given a set of target constants, computes the transitive **signature
cone** (see below), topologically sorts it, and emits a single Lean
file containing the statements of theorems and the content of
definitions, ordered so that every reference points backward. The
emitted file elaborates against the real development: each theorem
restatement is proved by direct reference to the real proof, so
`lake env lean <emitted-file>` re-checks that every displayed statement
is the statement actually proved in the tree.

The purpose is auditing: humans and agents can read what a development
*claims and defines* without being distracted by proof content, which
is proof-irrelevant for that purpose and is checked separately (by the
kernel on the real tree, or by an independent checker).

## What counts as a dependency (the signature cone)

A constant used *inside a proof* is not a dependency for auditing
purposes. Concretely, the closure recurses through:

- **theorems / axioms** (and Prop-valued definitions and instances,
  which are proofs in definition clothing): constants of the
  *statement* (the type) only — never the proof term;
- **definitions / abbreviations / instances** (data-valued): constants
  of the type *and* the body, except that (a) proof terms embedded in
  the body (`*._proof_*` auxiliaries and any Prop-valued constant) are
  treated as opaque — recorded, not recursed — and (b) `match`
  auxiliaries are expanded through, since match arms are the
  definition's actual computation;
- **structures / inductives**: the type and the constructor types.
  Constructors, projections, and recursor-family auxiliaries are
  normalized to their parent declaration, so a cone never lists a
  projection separately from its structure.

Constants whose defining module falls outside the configured boundary
(by default: core, the standard library, and the mathlib ecosystem)
are not expanded or emitted; the emitted file reaches them through its
imports. `--include-mathlib` moves the mathlib ecosystem inside the
cone (core and the standard library always stay outside).

## How the emitted file checks

The file imports the umbrella module(s) of the development, so every
displayed reference resolves to the *real* constant — the audit
declarations live under reserved single-atom names
(`LeanCone.«Real.Name»`, the full original name inside one quoted
atom), which cannot shadow anything the statements mention. The
declarations are therefore order-independent for the checker; the
topological order is for the reader. Per declaration the tool emits,
in order of preference (each candidate block is elaborated in-process
before it is written; the first one that checks is emitted):

- theorems: `theorem LeanCone.«N» : <statement> := N` — the receipt
  that the displayed statement is the proved one; rendered with
  readable pretty-printer settings first, then progressively more
  explicit ones when a readable rendering does not re-elaborate;
- data definitions with proof-free bodies: a full copy
  (`noncomputable def LeanCone.«N» : <type> := <body>`) plus, when it
  holds definitionally, `example : @LeanCone.«N» = @N := rfl` — the
  receipt that the displayed body is the real one;
- data definitions whose bodies embed proofs or compiled recursion:
  the signature receipt `noncomputable def LeanCone.«N» : <type> := N`
  with the body displayed alongside as a comment, proof parts elided
  as `⋯` (that elision is the point, not a limitation);
- structures / inductives: source text as written in the tree (when
  resolvable) plus a signature receipt `example : <signature> := N`;
- private constants: display only — a private name cannot be
  referenced from another file; listed in the findings appendix.

All emitted definition copies are `noncomputable`: audit copies are
about meaning, never execution, so the compiler is deliberately out of
the loop. A findings appendix at the end of the emitted file lists
every judgment call the run made (display-only declarations, failed
receipts, the axiom inventory of the signature cone).
-/
import Lean
open Lean Meta Elab

/-! ## Configuration -/

structure ConeConfig where
  targets : Array Name := #[]
  /-- umbrella modules to import (the environment; also the emitted file's imports). -/
  imports : Array Name := #[]
  /-- extra module-name prefixes treated as boundary. -/
  boundary : Array String := #[]
  includeMathlib : Bool := false
  out : Option String := none
  width : Nat := 100
  useSource : Bool := true

/-- Prefixes that are always boundary: the emitted file cannot sensibly
inline core or the standard library. -/
def coreBoundary : Array String := #["Init", "Lean", "Std", "Lake"]

/-- The mathlib-ecosystem prefixes: boundary by default, inlined under
`--include-mathlib`. -/
def mathlibBoundary : Array String :=
  #["Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph",
    "LeanSearchClient", "Plausible", "Cli", "Duper"]

def usage : String := "\
lean-cone: emit a topologically sorted, statements-only audit surface\n\
usage: lean-cone [options] <Constant.Name> [<Constant.Name> ...]\n\
  -o FILE              write to FILE (default: stdout)\n\
  --import MOD         umbrella module to import (repeatable; required)\n\
  --boundary PREFIX    extra module prefix to treat as boundary (repeatable)\n\
  --include-mathlib    inline the mathlib ecosystem into the cone\n\
  --width N            pretty-printer width (default 100)\n\
  --no-source          never splice source text (delaborated display only)\n"

partial def parseArgs : List String → ConeConfig → Except String ConeConfig
  | [], c =>
    if c.targets.isEmpty then .error s!"no target constants given\n\n{usage}"
    else if c.imports.isEmpty then .error "no --import umbrella module given"
    else .ok c
  | "-o" :: f :: rest, c => parseArgs rest { c with out := some f }
  | "--import" :: m :: rest, c => parseArgs rest { c with imports := c.imports.push m.toName }
  | "--boundary" :: p :: rest, c => parseArgs rest { c with boundary := c.boundary.push p }
  | "--include-mathlib" :: rest, c => parseArgs rest { c with includeMathlib := true }
  | "--width" :: n :: rest, c => parseArgs rest { c with width := n.toNat! }
  | "--no-source" :: rest, c => parseArgs rest { c with useSource := false }
  | arg :: rest, c =>
    if arg.startsWith "-" then .error s!"unknown option {arg}\n\n{usage}"
    else parseArgs rest { c with targets := c.targets.push arg.toName }

def ConeConfig.stopSet (c : ConeConfig) : Array String :=
  coreBoundary ++ (if c.includeMathlib then #[] else mathlibBoundary) ++ c.boundary

/-! ## Name and kind utilities -/

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]!
  | none => `«current»

def isBoundary (cfg : ConeConfig) (env : Environment) (n : Name) : Bool :=
  let m := (moduleOf env n).toString
  cfg.stopSet.any (fun p => m == p || m.startsWith (p ++ "."))

/-- name components marking elaborator/compiler detail: never emitted as
nodes; dependency edges flow through them. -/
def detailComponent (s : String) : Bool :=
  s.startsWith "match_" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  || s == "eq_def" || s == "eq_unfold" || s == "injEq" || s == "sizeOf_spec"
  || s == "sizeOf_eq" || s == "_sunfold" || s == "_unary" || s.startsWith "_"

/-- proof-content auxiliary components (elided from data-definition
bodies' cones — they are proofs). -/
def proofAuxComponent (s : String) : Bool :=
  s.startsWith "proof_" || s.startsWith "_proof_"

def userComponents (n : Name) : List Name :=
  ((privateToUserName? n).getD n).components

def isDetail (n : Name) : Bool :=
  n.hasMacroScopes
  || (userComponents n).any (fun c => match c with
      | .str _ s => detailComponent s
      | .num _ _ => true
      | _ => false)

def isProofAux (n : Name) : Bool :=
  (userComponents n).any (fun c => match c with
      | .str _ s => proofAuxComponent s
      | _ => false)

/-- recursor-family suffixes normalized to the parent inductive. -/
def indAuxComponent (s : String) : Bool :=
  s == "rec" || s == "recOn" || s == "casesOn" || s == "brecOn"
  || s == "binductionOn" || s == "below" || s == "ibelow"
  || s == "noConfusion" || s == "noConfusionType"
  || s == "ctorIdx" || s == "toCtorIdx"

/-- The node a name presents as: constructors → their inductive,
projections → their structure, recursor family → the inductive;
`none` for quotient primitives. -/
partial def normalize (env : Environment) (n : Name) : Option Name := do
  match env.find? n with
  | none => none
  | some ci =>
    match ci with
    | .ctorInfo v => normalize env v.induct
    | .recInfo v => normalize env v.getMajorInduct
    | .quotInfo _ => none
    | _ =>
      match env.getProjectionFnInfo? n with
      | some pi =>
        match env.find? pi.ctorName with
        | some (.ctorInfo cv) => normalize env cv.induct
        | _ => some n
      | none =>
        match n with
        | .str p s =>
          if indAuxComponent s && (env.find? p).isSome then normalize env p
          else some n
        | _ => some n

inductive NodeKind | thm | defn | inductD | structD | axiomD | opaqueD | quotD
  deriving BEq, Repr

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : NodeKind :=
  match ci with
  | .thmInfo _ => .thm
  | .defnInfo _ => .defn
  | .opaqueInfo _ => .opaqueD
  | .axiomInfo _ => .axiomD
  | .inductInfo _ => if isStructure env n then .structD else .inductD
  | .ctorInfo _ | .recInfo _ => .inductD  -- normalized away before use
  | .quotInfo _ => .quotD

/-- result-type head constant (forall-telescope stripped). -/
partial def resultHead : Expr → Option Name
  | .forallE _ _ b _ => resultHead b
  | .mdata _ b => resultHead b
  | .letE _ _ _ b _ => resultHead b
  | e => e.getAppFn.constName?

/-! ## The signature-cone walk -/

structure WalkSt where
  propCache : Std.HashMap Name Bool := {}
  /-- cone nodes (house side, normalized). -/
  cone : Std.HashSet Name := {}
  /-- signature-cone edges (node → normalized house deps), for the toposort. -/
  edges : Std.HashMap Name (Array Name) := {}
  /-- first-layer boundary leaves (for the module-footprint appendix). -/
  extLeaves : Std.HashSet Name := {}
  /-- Prop-valued constants mentioned in definition bodies (displayed
  opaquely, not expanded). -/
  proofMentions : Std.HashSet Name := {}
  /-- axioms met anywhere while walking the signature cone. -/
  axioms : Std.HashSet Name := {}

abbrev WalkM := StateT WalkSt MetaM

/-- is this constant a proof (i.e. is its type a Prop)? -/
def isProofConst (env : Environment) (n : Name) : WalkM Bool := do
  if let some r := (← get).propCache.get? n then return r
  let r ← match env.find? n with
    | some ci => Meta.isProp ci.type
    | none => pure false
  modify fun st => { st with propCache := st.propCache.insert n r }
  pure r

/-- raw used constants of the *signature-relevant* parts of a constant:
the type always; constructor types for inductives; the body too for
data-valued definitions (`bodyToo`). -/
def rawSigDeps (env : Environment) (ci : ConstantInfo) (bodyToo : Bool) :
    Array Name × Array Name :=
  match ci with
  | .inductInfo v =>
    let tdeps := v.type.getUsedConstants
    let cdeps := v.ctors.foldl (init := #[]) (fun acc c =>
      match env.find? c with
      | some cci => acc ++ cci.type.getUsedConstants
      | none => acc)
    (tdeps ++ cdeps, #[])
  | _ =>
    let t := ci.type.getUsedConstants
    let v := if bodyToo then
        match ci.value? (allowOpaque := true) with
        | some e => e.getUsedConstants
        | none => #[]
      else #[]
    (t, v)

/-- expand raw dependencies to normalized node names, flowing through
detail constants. `valuePosition` marks body dependencies of a data
definition: there, proof auxiliaries are elided and Prop-valued
constants are recorded as opaque mentions rather than expanded. -/
partial def expandDeps (env : Environment) (self : Name) (raw : Array Name)
    (valuePosition : Bool) : WalkM (Array Name) := do
  let mut out : Std.HashSet Name := {}
  let mut queue := raw.toList
  let mut seen : Std.HashSet Name := {}
  while !queue.isEmpty do
    match queue with
    | [] => pure ()
    | d :: rest =>
      queue := rest
      if seen.contains d then continue
      seen := seen.insert d
      match normalize env d with
      | none => pure ()
      | some nd =>
        if nd == self then continue
        if let some (.axiomInfo _) := env.find? nd then
          modify fun st => { st with axioms := st.axioms.insert nd }
        if isDetail nd then
          if valuePosition && isProofAux nd then
            -- a proof auxiliary in a body is proof content: elide
            continue
          match env.find? nd with
          | some dci =>
            -- in type position a proof auxiliary's *statement* still
            -- contributes; its proof does not
            let bodyToo := !(isProofAux nd)
            let (dt, dv) := rawSigDeps env dci bodyToo
            queue := dt.toList ++ dv.toList ++ queue
          | none => pure ()
        else if valuePosition && (← isProofConst env nd) then
          modify fun st => { st with proofMentions := st.proofMentions.insert nd }
        else
          out := out.insert nd
  pure (out.toList.toArray.qsort (fun a b => a.toString < b.toString))

/-- one node's normalized signature-cone dependencies. -/
def sigDepsOf (env : Environment) (n : Name) : WalkM (Array Name) := do
  let some ci := env.find? n | return #[]
  let kind := kindOf env n ci
  let isProofLike ← match kind with
    | .thm | .axiomD => pure true
    | .defn | .opaqueD => isProofConst env n  -- Prop-valued def: proof in def clothing
    | _ => pure false
  let bodyToo := !isProofLike && (kind matches .defn)
  let (rt, rv) := rawSigDeps env ci bodyToo
  let td ← expandDeps env n rt (valuePosition := false)
  let vd ← expandDeps env n rv (valuePosition := true)
  pure ((td ++ vd).foldl (init := (#[] : Array Name)) (fun acc d =>
    if acc.contains d then acc else acc.push d))

/-- breadth-first closure from the targets, house side only. -/
def walkCone (cfg : ConeConfig) (env : Environment) (targets : Array Name) :
    WalkM Unit := do
  let mut queue := targets.toList
  while !queue.isEmpty do
    match queue with
    | [] => pure ()
    | n :: rest =>
      queue := rest
      if (← get).cone.contains n then continue
      if isBoundary cfg env n then
        modify fun st => { st with extLeaves := st.extLeaves.insert n }
        continue
      modify fun st => { st with cone := st.cone.insert n }
      let deps ← sigDepsOf env n
      modify fun st => { st with edges := st.edges.insert n deps }
      for d in deps do
        if isBoundary cfg env d then
          modify fun st => { st with extLeaves := st.extLeaves.insert d }
      queue := (deps.filter (fun d => !isBoundary cfg env d)).toList ++ queue

/-! ## Topological sort

Kahn's algorithm, always taking the lexicographically least ready name:
the output is the unique lexicographically-least topological order, so
runs are reproducible and diffable. -/

def toposort (nodes : Array Name) (edges : Std.HashMap Name (Array Name)) :
    Array Name × Bool := Id.run do
  let inCone : Std.HashSet Name := nodes.foldl (·.insert ·) {}
  let mut indeg : Std.HashMap Name Nat := {}
  let mut radj : Std.HashMap Name (Array Name) := {}
  for n in nodes do
    let deps := (edges.getD n #[]).filter (fun d => inCone.contains d && d != n)
    indeg := indeg.insert n deps.size
    for d in deps do
      radj := radj.insert d ((radj.getD d #[]).push n)
  let mut ready : Array Name := nodes.filter (fun n => indeg.getD n 0 == 0)
  let mut out : Array Name := #[]
  while !ready.isEmpty do
    -- take the lexicographically least ready node
    let mut best := ready[0]!
    for r in ready do
      if r.toString < best.toString then best := r
    ready := ready.filter (· != best)
    out := out.push best
    for m in (radj.getD best #[]) do
      let k := (indeg.getD m 1) - 1
      indeg := indeg.insert m k
      if k == 0 then ready := ready.push m
  if out.size < nodes.size then
    -- dependency cycle (mutual declarations whose types reference each
    -- other): append the remainder in name order; flagged to the caller
    let done : Std.HashSet Name := out.foldl (·.insert ·) {}
    let rest := (nodes.filter (fun n => !done.contains n)).qsort
      (fun a b => a.toString < b.toString)
    pure (out ++ rest, true)
  else
    pure (out, false)

/-! ## Rendering (meta phase: everything pretty-printed up front) -/

def ppWithOpts (opts : Options) (width : Nat) (e : Expr) : MetaM String := do
  withOptions (fun _ => opts) do
    pure ((← Meta.ppExpr e).pretty width)

/-- pretty-printer tiers: readable first, then progressively more
explicit renderings for statements the readable printer round-trips
badly (omitted binder types + field notation is the classic pair). -/
def mkTiers (base : Options) : Array (String × Options) :=
  #[("readable", base),
    ("strict",
      base |>.setBool `pp.funBinderTypes true |>.setBool `pp.fieldNotation false),
    ("explicit",
      base |>.setBool `pp.funBinderTypes true |>.setBool `pp.fieldNotation false
        |>.setBool `pp.explicit true)]

/-- a fully rendered node, ready for emission (pure data). -/
structure NodePlan where
  name : Name
  kind : NodeKind
  /-- statement-only (theorem, axiom, or Prop-valued definition). -/
  proofLike : Bool
  levelParams : List Name
  /-- type renderings, tier-tagged, deduplicated. -/
  typeTiers : Array (String × String)
  /-- body renderings for data definitions. -/
  valueTiers : Array (String × String) := #[]
  /-- the readable body embeds proof elisions (`⋯`) or compiled recursion. -/
  bodyOpaque : Bool := false
  doc : Option String := none
  srcText : Option String := none
  mod : Name
  isPrivate : Bool := false
  /-- the constant's result type is a class (instance-shaped): copies
  need `@[reducible]` to keep the elaborator's class-def linter quiet. -/
  classValued : Bool := false
  notes : Array String := #[]
  /-- constructor signatures (inductives), readable tier, display only. -/
  ctorSigs : Array String := #[]

/-- render at every tier. Tiers may repeat a rendering (a simple type
prints identically at readable and strict); duplicates are dropped at
candidate level, never here — dropping them here once cost a def its
strict-tier body pairing. -/
def renderTiers (tiers : Array (String × Options)) (width : Nat) (e : Expr) :
    MetaM (Array (String × String)) := do
  let mut out : Array (String × String) := #[]
  for (tag, opts) in tiers do
    out := out.push (tag, ← ppWithOpts opts width e)
  pure out

/-- does a rendered body contain proof elisions or compiled-recursion
scaffolding that make a faithful live copy pointless? (`brecOn` and
`WellFounded.fix` bodies are the equation compiler's output, not what
anyone wrote or wants to read — those definitions display as source
text instead.) -/
def bodyLooksOpaque (self : Name) (rendered : String) (rawValueDeps : Array Name) : Bool :=
  (rendered.splitOn "⋯").length > 1
  || rawValueDeps.any (fun d =>
      d == `WellFounded.fix || d == `WellFounded.fixF
      || (match d with
          | .str p s =>
            s == "brecOn" || s == "binductionOn" || s == "_unary"
            || (p == self && indAuxComponent s)
          | _ => false))

def sourceRootsFromEnv : IO (Array System.FilePath) := do
  let some p ← IO.getEnv "LEAN_SRC_PATH" | return #[]
  let mut out : Array System.FilePath := #[]
  for part in p.splitOn ":" do
    if part ≠ "" && !out.contains ⟨part⟩ then out := out.push ⟨part⟩
  pure out

def moduleSourceFile (roots : Array System.FilePath) (m : Name) :
    IO (Option System.FilePath) := do
  let rel := (System.mkFilePath (m.components.map toString)).addExtension "lean"
  for r in roots do
    let f := r / rel
    if ← f.pathExists then return some f
  return none

def sourceSlice (f : System.FilePath) (l0 l1 : Nat) : IO (Option String) := do
  let txt ← IO.FS.readFile f
  let lines := txt.splitOn "\n"
  if l0 == 0 || l0 > lines.length then return none
  return some ("\n".intercalate ((lines.drop (l0 - 1)).take (l1 - l0 + 1)))

/-- build the emission plan for one cone node. -/
def planNode (cfg : ConeConfig) (env : Environment) (tiers : Array (String × Options))
    (srcRoots : Array System.FilePath) (mutualGroups : Std.HashMap Name (Array Name))
    (n : Name) : MetaM NodePlan := do
  let some ci := env.find? n
    | return { name := n, kind := .quotD, proofLike := false, levelParams := [],
               typeTiers := #[], mod := `«unknown» }
  let kind := kindOf env n ci
  let proofLike ← match kind with
    | .thm | .axiomD => pure true
    | .defn | .opaqueD => Meta.isProp ci.type
    | _ => pure false
  let typeTiers ← renderTiers tiers cfg.width ci.type
  let mut valueTiers : Array (String × String) := #[]
  let mut bodyOpaque := false
  if kind matches .defn then
    if !proofLike then
      match ci.value? with
      | some v =>
        valueTiers ← renderTiers tiers cfg.width v
        bodyOpaque := bodyLooksOpaque n valueTiers[0]!.2 v.getUsedConstants
      | none => bodyOpaque := true
  let doc ← findDocString? env n
  -- source text (house modules only; used for structures/inductives and
  -- opaque-body display)
  let mut srcText : Option String := none
  if cfg.useSource then
    if let some rgs ← findDeclarationRanges? n then
      if let some f ← moduleSourceFile srcRoots (moduleOf env n) then
        srcText ← sourceSlice f rgs.range.pos.line rgs.range.endPos.line
  -- notes
  let mut notes : Array String := #[]
  let mut classValued := false
  if let some h := resultHead ci.type then
    if isClass env h then
      classValued := true
      notes := notes.push s!"instance of class `{h}`"
  if proofLike && (kind matches .defn) then
    notes := notes.push "Prop-valued definition: a proof in definition clothing — statement only"
  if let some grp := mutualGroups.get? n then
    if grp.size > 1 then
      let others := grp.filter (· != n)
      notes := notes.push
        s!"mutual with {", ".intercalate (others.map (fun o => s!"`{o}`")).toList}"
  let mut ctorSigs : Array String := #[]
  if (kind matches .inductD) || (kind matches .structD) then
    if let .inductInfo v := ci then
      for c in v.ctors do
        if let some cci := env.find? c then
          let ty ← ppWithOpts tiers[0]!.2 cfg.width cci.type
          ctorSigs := ctorSigs.push s!"{c} : {ty}"
  pure { name := n, kind, proofLike, levelParams := ci.levelParams, typeTiers,
         valueTiers, bodyOpaque, doc, srcText, mod := moduleOf env n,
         isPrivate := isPrivateName n, classValued, notes, ctorSigs }

/-! ## The self-check harness -/

/-- Parse + elaborate a candidate block against the rolling command
state. Returns `(ok, errorSummary, nextState)`; the state advances only
on success. -/
def checkBlock (cmdState : Command.State) (text : String) (tag : String) :
    IO (Bool × String × Command.State) := do
  let inputCtx := Parser.mkInputContext text s!"<lean-cone:{tag}>"
  let (_, parserState, msgs) ← Parser.parseHeader inputCtx
  let st0 := { cmdState with messages := msgs }
  let frontState ← IO.processCommands inputCtx parserState st0
  let msgs := frontState.commandState.messages
  let hasErr := msgs.toArray.any (·.severity == .error)
  if hasErr then
    let errTxt ← msgs.toArray.filterMapM fun m => do
      if m.severity == .error then pure (some (← m.data.toString)) else pure none
    pure (false, "; ".intercalate errTxt.toList, cmdState)
  else
    pure (true, "",
      { frontState.commandState with messages := cmdState.messages, infoState := {} })

/-! ## Emission -/

def auditName (n : Name) : String := s!"LeanCone.«{n}»"

def levelSuffix (ls : List Name) : String :=
  if ls.isEmpty then ""
  else ".{" ++ ", ".intercalate (ls.map toString) ++ "}"

/-- keep displayed comment text from terminating its comment block. -/
def escapeComment (s : String) : String :=
  (s.replace "-/" "-∕").replace "/-" "∕-"

def indentLines (pfx : String) (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map (fun l => if l == "" then l else pfx ++ l))

structure EmitSt where
  cmdState : Command.State
  chunks : Array String := #[]
  declaredLevels : Std.HashSet Name := {}
  findings : Array String := #[]
  nReceipts : Nat := 0
  nCopies : Nat := 0
  nDisplayOnly : Nat := 0

abbrev EmitM := StateT EmitSt IO

def pushChunk (s : String) : EmitM Unit :=
  modify fun st => { st with chunks := st.chunks.push s }

def pushFinding (s : String) : EmitM Unit :=
  modify fun st => { st with findings := st.findings.push s }

/-- try candidate blocks in order; commit and return the first that
elaborates (with its tag), else `none` (with per-tier errors for the
caller). -/
def tryCandidates (who : String) (cands : Array (String × String)) :
    EmitM (Option (String × String) × Array String) := do
  let mut errs : Array String := #[]
  let mut tried : Array String := #[]
  for (tag, text) in cands do
    if tried.contains text then continue
    tried := tried.push text
    let st ← get
    let (ok, err, next) ← checkBlock st.cmdState text s!"{who}:{tag}"
    if ok then
      set { st with cmdState := next }
      return (some (tag, text), errs)
    else
      errs := errs.push s!"[{tag}] {(err.take 200).toString}"
  return (none, errs)

/-- ensure universe names are declared (for `example`-receipts, which
cannot bind their own universes). -/
def ensureLevels (ls : List Name) : EmitM Unit := do
  let st ← get
  let fresh := ls.filter (fun u => !st.declaredLevels.contains u)
  if fresh.isEmpty then return
  let line := "universe " ++ " ".intercalate (fresh.map toString)
  let (got, _) ← tryCandidates "universe" #[("universe", line)]
  if got.isSome then
    pushChunk line
    modify fun st =>
      { st with declaredLevels := fresh.foldl (·.insert ·) st.declaredLevels }

/-- the per-node header comment: provenance, original doc string, notes.
A plain block comment, never a doc comment: several chunk shapes are not
followed by a doc-accepting declaration, and a dangling doc comment is a
parse error at file assembly time. -/
def headerComment (p : NodePlan) (kindLabel : String) : String :=
  let docPart := match p.doc with
    | some d => indentLines "" (escapeComment d) ++ "\n"
    | none => ""
  let notesPart := if p.notes.isEmpty then "" else
    "\n".intercalate (p.notes.map (fun l => "note: " ++ l)).toList ++ "\n"
  s!"/- **{kindLabel}** `{p.name}` — module `{p.mod}`.\n{docPart}{notesPart}-/\n"

/-- display-only fallback: the best rendering, boxed in a comment.
The chunk is comment-only (no commands, no doc comments), so it cannot
affect the checkability of the assembled file. -/
def emitDisplayOnly (p : NodePlan) (kindLabel : String) (reason : String) : EmitM Unit := do
  let body := match p.srcText with
    | some src => s!"/- source text (module `{p.mod}`):\n{escapeComment src}\n-/"
    | none =>
      let ty := escapeComment p.typeTiers[0]!.2
      let v := if p.valueTiers.isEmpty then "" else
        " :=\n" ++ indentLines "  " (escapeComment p.valueTiers[0]!.2)
      s!"/- {kindLabel} {p.name}{levelSuffix p.levelParams} :\n{indentLines "  " ty}{v}\n-/"
  pushChunk (headerComment p kindLabel ++
    s!"-- display only ({reason}); no machine receipt\n" ++ body)
  modify fun st => { st with nDisplayOnly := st.nDisplayOnly + 1 }
  pushFinding s!"display-only {kindLabel} `{p.name}`: {reason}"

/-- theorems, axioms, Prop-valued definitions: statement + proof-by-reference.
Candidates are complete chunks — comments included — so the self-check
elaborates exactly the text that lands in the file. -/
def emitProofLike (p : NodePlan) : EmitM Unit := do
  let kindLabel := match p.kind with
    | .axiomD => "axiom" | .thm => "theorem" | _ => "def (Prop-valued)"
  if p.isPrivate then
    emitDisplayOnly p kindLabel "private name: not referenceable from another file"
    return
  -- universe params ride file-level `universe` commands: a per-declaration
  -- `.{u}` binder would collide with them ("already been declared")
  ensureLevels p.levelParams
  let pre := headerComment p kindLabel
  let cands := p.typeTiers.map fun (tag, ty) =>
    (tag, pre ++ s!"theorem {auditName p.name} :\n" ++ indentLines "    " ty ++
      s!" :=\n  {p.name}")
  let (got, errs) ← tryCandidates (toString p.name) cands
  match got with
  | some (_, text) =>
    pushChunk text
    modify fun st => { st with nReceipts := st.nReceipts + 1 }
  | none =>
    for e in errs do pushFinding s!"`{p.name}` candidate failed {e}"
    emitDisplayOnly p kindLabel "no rendering of the statement re-elaborated"

/-- data definitions: full copy when the body is proof-free, signature
receipt with displayed body otherwise. -/
def emitDefn (p : NodePlan) : EmitM Unit := do
  let kindLabel := "def"
  if p.isPrivate then
    emitDisplayOnly p kindLabel "private name: not referenceable from another file"
    return
  -- universe params ride file-level `universe` commands (see emitProofLike)
  ensureLevels p.levelParams
  let pre := headerComment p kindLabel
  -- body display, for the reference-body forms (source text preferred)
  let display := match p.srcText with
    | some src => s!"/- source text (module `{p.mod}`):\n{escapeComment src}\n-/\n"
    | none =>
      if p.valueTiers.isEmpty then ""
      else "/- body (proof parts elided as ⋯):\n" ++
        indentLines "  " (escapeComment p.valueTiers[0]!.2) ++ "\n-/\n"
  -- class-typed copies need @[reducible] (the elaborator lints bare
  -- defs of class type)
  let defKw := (if p.classValued then "@[reducible] " else "") ++ "noncomputable def"
  -- signature receipt (referenced-body form): displays the body as a
  -- comment, checks the signature
  let refCands := p.typeTiers.map fun (tag, ty) =>
    (s!"ref-{tag}", pre ++ display ++
      s!"{defKw} {auditName p.name} :\n" ++ indentLines "    " ty ++
      s!" :=\n  {p.name}")
  if p.bodyOpaque || p.valueTiers.isEmpty then
    -- body embeds proofs or compiled recursion: display body, check signature
    let (got, errs) ← tryCandidates (toString p.name) refCands
    match got with
    | some (_, text) =>
      pushChunk text
      modify fun st => { st with nReceipts := st.nReceipts + 1 }
    | none =>
      for e in errs do pushFinding s!"`{p.name}` candidate failed {e}"
      emitDisplayOnly p kindLabel "no rendering of the signature re-elaborated"
  else
    -- proof-free body: full copy, tier-aligned type/body pairs, then
    -- reference fallback (identical candidates deduplicate downstream).
    -- Explicit-tier copies rank BELOW readable reference mode: a fully
    -- @-elaborated body is a worse audit surface than displayed source
    -- plus a checked signature.
    let copyCands := (p.typeTiers.zip p.valueTiers).map fun ((ttag, ty), (_, v)) =>
      (s!"copy-{ttag}",
        pre ++ s!"{defKw} {auditName p.name} :\n" ++ indentLines "    " ty ++
        " :=\n" ++ indentLines "  " v)
    let isExplicit := fun (c : String × String) => c.1.endsWith "explicit"
    let ladder :=
      copyCands.filter (fun c => !isExplicit c) ++ refCands.filter (fun c => !isExplicit c) ++
      copyCands.filter isExplicit ++ refCands.filter isExplicit
    let (got, errs) ← tryCandidates (toString p.name) ladder
    match got with
    | some (tag, text) =>
      let isCopy := tag.startsWith "copy-"
      pushChunk text
      if isCopy then
        modify fun st => { st with nCopies := st.nCopies + 1 }
        -- faithfulness receipt: the copy is definitionally the original
        ensureLevels p.levelParams
        let ls := levelSuffix p.levelParams
        let rflCand := ("rfl",
          s!"example : @{auditName p.name}{ls} = @{p.name}{ls} := rfl")
        let (gotR, _) ← tryCandidates (s!"{p.name}-rfl") #[rflCand]
        match gotR with
        | some (_, rtext) => pushChunk rtext
        | none =>
          pushFinding (s!"`{p.name}`: copy emitted, but the rfl receipt does not "
            ++ "hold definitionally (copy is elaboration-checked only)")
      else
        modify fun st => { st with nReceipts := st.nReceipts + 1 }
        pushFinding (s!"`{p.name}`: body copy did not re-elaborate; emitted "
          ++ "signature receipt with reference body")
        for e in errs do pushFinding s!"`{p.name}` copy candidate failed {e}"
    | none =>
      for e in errs do pushFinding s!"`{p.name}` candidate failed {e}"
      emitDisplayOnly p kindLabel "no rendering re-elaborated"

/-- structures and inductives: source-text display + signature receipt. -/
def emitInductive (p : NodePlan) : EmitM Unit := do
  let kindLabel := if p.kind matches .structD then "structure" else "inductive"
  let display := match p.srcText with
    | some src => s!"/- source text (module `{p.mod}`):\n{escapeComment src}\n-/\n"
    | none =>
      let ctors := "\n".intercalate (p.ctorSigs.map (fun c => "  | " ++ escapeComment c)).toList
      s!"/- {kindLabel} {p.name}{levelSuffix p.levelParams} : {escapeComment p.typeTiers[0]!.2}\n{ctors}\n-/\n"
  if p.isPrivate then
    emitDisplayOnly p kindLabel "private name: not referenceable from another file"
    return
  ensureLevels p.levelParams
  let pre := headerComment p kindLabel ++ display ++ "-- signature receipt:\n"
  let ls := levelSuffix p.levelParams
  let sigCands := p.typeTiers.map fun (tag, ty) =>
    (tag, pre ++ s!"example : {ty} := @{p.name}{ls}")
  let (got, _errs) ← tryCandidates (toString p.name) sigCands
  match got with
  | some (_, text) =>
    pushChunk text
    modify fun st => { st with nReceipts := st.nReceipts + 1 }
  | none =>
    -- the display is the content; signature receipts on dependent
    -- signatures are best-effort
    pushChunk (headerComment p kindLabel ++ display ++
      "-- (signature receipt did not re-elaborate; display only)")
    modify fun st => { st with nDisplayOnly := st.nDisplayOnly + 1 }
    pushFinding s!"{kindLabel} `{p.name}`: signature receipt did not re-elaborate"

/-- opaque constants and definitions without accessible values. -/
def emitOpaque (p : NodePlan) : EmitM Unit := do
  let kindLabel := "opaque"
  if p.isPrivate then
    emitDisplayOnly p kindLabel "private name: not referenceable from another file"
    return
  ensureLevels p.levelParams
  let pre := headerComment p kindLabel ++ "-- signature receipt:\n"
  let ls := levelSuffix p.levelParams
  let sigCands := p.typeTiers.map fun (tag, ty) =>
    (tag, pre ++ s!"example : {ty} := @{p.name}{ls}")
  let (got, _) ← tryCandidates (toString p.name) sigCands
  match got with
  | some (_, text) =>
    pushChunk text
    modify fun st => { st with nReceipts := st.nReceipts + 1 }
  | none =>
    emitDisplayOnly p kindLabel "signature receipt did not re-elaborate"

def emitNode (p : NodePlan) : EmitM Unit := do
  match p.kind with
  | .thm | .axiomD => emitProofLike p
  | .defn => if p.proofLike then emitProofLike p else emitDefn p
  | .inductD | .structD => emitInductive p
  | .opaqueD => emitOpaque p
  | .quotD => pushFinding s!"`{p.name}`: quotient primitive (skipped)"

/-! ## main -/

unsafe def enableInitsUnsafe : IO Unit := enableInitializersExecution
@[implemented_by enableInitsUnsafe] def enableInits : IO Unit := pure ()

def main (argv : List String) : IO UInt32 := do
  let cfg ← match parseArgs argv {} with
    | .ok c => pure c
    | .error e => IO.eprintln e; return 1
  enableInits
  initSearchPath (← findSysroot)
  IO.eprintln s!"lean-cone: importing {cfg.imports}…"
  let env ← try
      importModules (cfg.imports.map ({ module := · })) {}
        (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"lean-cone: could not load the environment: {e.toString}"
      IO.eprintln "lean-cone: is the package built? (`lake build` in the \
        package directory produces the .olean files this tool reads)"
      return 1
  -- resolve + normalize targets
  let mut targets : Array Name := #[]
  for t in cfg.targets do
    match env.find? t with
    | none =>
      IO.eprintln s!"lean-cone: target `{t}` not found in the environment \
        (imported: {cfg.imports})"
      return 1
    | some _ =>
      match normalize env t with
      | some n => if !targets.contains n then targets := targets.push n
      | none =>
        IO.eprintln s!"lean-cone: target `{t}` is a quotient primitive"
        return 1
  let baseOpts : Options := ({} : Options)
    |>.setBool `pp.fullNames true
  let tiers := mkTiers baseOpts
  let coreCtx : Core.Context :=
    { fileName := "<lean-cone>", fileMap := default, options := baseOpts }
  -- phase 1: walk, sort, render
  let plansAct : CoreM (Array NodePlan × WalkSt × Bool) := MetaM.run' do
    let (_, walk) ← (walkCone cfg env targets).run {}
    let nodes := walk.cone.toList.toArray
    IO.eprintln s!"lean-cone: signature cone has {nodes.size} house constants, \
      {walk.extLeaves.toList.length} boundary leaves"
    let (order, hadCycle) := toposort nodes walk.edges
    -- mutual groups
    let mut mutualGroups : Std.HashMap Name (Array Name) := {}
    for n in order do
      if let some ci := env.find? n then
        let all := ci.all.toArray
        if all.size > 1 then mutualGroups := mutualGroups.insert n all
    let srcRoots ← if cfg.useSource then sourceRootsFromEnv else pure #[]
    let mut plans : Array NodePlan := #[]
    for (i, n) in order.mapIdx (fun i n => (i, n)) do
      IO.eprintln s!"lean-cone: [{i + 1}/{order.size}] rendering {n}"
      plans := plans.push (← planNode cfg env tiers srcRoots mutualGroups n)
    pure (plans, walk, hadCycle)
  let ((plans, walk, hadCycle), _) ← plansAct.toIO coreCtx { env }
  -- phase 2: emit with self-checking
  let checkOpts : Options :=
    (baseOpts.setBool `autoImplicit false).set `maxHeartbeats (1000000 : Nat)
  let st0 : EmitSt := { cmdState := Command.mkState env {} checkOpts }
  let emitAct : EmitM Unit := do
    -- file preamble commands participate in the rolling state too
    let preamble :=
      #["set_option autoImplicit false", "set_option maxHeartbeats 1000000",
        "set_option linter.unusedVariables false"]
    for line in preamble do
      let (got, errs) ← tryCandidates "preamble" #[("preamble", line)]
      if got.isSome then pushChunk line
      else for e in errs do pushFinding s!"preamble `{line}` failed {e}"
    for p in plans do
      IO.eprintln s!"lean-cone: emitting {p.name}"
      emitNode p
  let (_, emitSt) ← emitAct.run st0
  -- assemble
  let nl := "\n"
  let headerLines : List String :=
    [ "/- Audit surface generated by lean-cone."
    , ""
    , "Targets: " ++ " ".intercalate (targets.map toString).toList
    , "Boundary: " ++ " ".intercalate cfg.stopSet.toList
    , ""
    , "This file contains the statements of the target theorems and the"
    , "full content of the definitions they depend on — the transitive"
    , "signature cone, topologically sorted so every reference points"
    , "backward. Proofs are references into the real development; proof"
    , "content is deliberately absent. Checking this file re-checks every"
    , "displayed statement against the real one."
    , "-/" ]
  let header := nl.intercalate headerLines
  let imports := nl.intercalate ((cfg.imports.map (fun m => s!"import {m}")).toList)
  let houseMods := ((plans.map (·.mod)).foldl (init := (#[] : Array Name))
    (fun acc m => if acc.contains m then acc else acc.push m)).qsort
    (fun a b => a.toString < b.toString)
  let extMods := (walk.extLeaves.toList.foldl (init := (#[] : Array Name))
    (fun acc n => let m := moduleOf env n
                  if acc.contains m then acc else acc.push m)).qsort
    (fun a b => a.toString < b.toString)
  let footprint := nl.intercalate (
    [ "/- Module footprint."
    , "House modules in the cone:" ]
    ++ (houseMods.map (fun m => s!"  {m}")).toList
    ++ [ "Boundary modules referenced by the displayed signatures"
    , "(reached through the imports above):" ]
    ++ (extMods.map (fun m => s!"  {m}")).toList
    ++ [ "-/" ])
  let axs := walk.axioms.toList.toArray.qsort (fun a b => a.toString < b.toString)
  let axInv :=
    if axs.isEmpty then
      "/- Axiom inventory of the signature cone: none. -/"
    else nl.intercalate (
      [ "/- Axiom inventory of the signature cone (axioms reachable through"
      , "statements and definition bodies — NOT the proof closure, which is"
      , "checked on the real tree):" ]
      ++ (axs.map (fun a => s!"  {a}")).toList
      ++ [ "-/" ])
  let findings :=
    if emitSt.findings.isEmpty then
      "/- Findings: none. Every declaration carries a machine receipt. -/"
    else nl.intercalate (
      [ "/- Findings (judgment calls and degradations this run made):" ]
      ++ (emitSt.findings.map (fun f =>
            indentLines "  " ("• " ++ escapeComment f))).toList
      ++ [ "-/" ])
  let cycleNote := if hadCycle then
      "/- NOTE: the cone contains a dependency cycle (mutually dependent" ++ nl ++
      "signatures); declarations after the cycle point are in name order. -/" ++ nl
    else ""
  let body := (nl ++ nl).intercalate emitSt.chunks.toList
  let out := header ++ nl ++ nl ++ imports ++ nl ++ nl ++ cycleNote ++
    (nl ++ nl).intercalate [body, footprint, axInv, findings] ++ nl
  match cfg.out with
  | some f => IO.FS.writeFile f out
  | none => IO.println out
  IO.eprintln (s!"lean-cone: done — {plans.size} declarations "
    ++ s!"({emitSt.nReceipts} receipts, {emitSt.nCopies} full copies with receipts, "
    ++ s!"{emitSt.nDisplayOnly} display-only), {emitSt.findings.size} findings")
  return 0
