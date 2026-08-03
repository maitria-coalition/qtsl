import Reflection.Container

/-!
# Geolog reader: renderers

The structural dump the cross-implementation differential harness
byte-compares, ported byte-for-byte from the HOL4 reference reader's
renderer family: `OK` plus a container/prereq/commit/op dump on
accept, or a single `CLASS tag witness` line on refusal. Hex is
lowercase, unprefixed inside `deps=[...]`, `0x`-prefixed elsewhere.
-/

namespace PPLC
namespace Geolog
namespace Read

/-- One lowercase hex digit. -/
def hexDig (n : Nat) : String :=
  if n < 10 then String.singleton (Char.ofNat (48 + n))
  else String.singleton (Char.ofNat (87 + n))

/-- Two lowercase hex digits of a byte. -/
def hex2 (b : Nat) : String := hexDig (b / 16) ++ hexDig (b % 16)

/-- Lowercase hex of a byte string. -/
def hexS (bs : Bytes) : String := String.join (bs.map hex2)

/-- Decimal rendering. -/
def numS (n : Nat) : String := toString n

/-- Element reference. -/
def renderRef (r : ElemRef) : String :=
  match r with
  | .loc n => "L(" ++ numS n ++ ")"
  | .ext d c => "E(" ++ numS d ++ "," ++ numS c ++ ")"

/-- Value cell. -/
def renderVal (v : GValue) : String :=
  match v with
  | .ref r => renderRef r
  | .lit code p => "lit(" ++ numS code ++ ",0x" ++ hexS p ++ ")"
  | .commitId i => "cid(" ++ numS i ++ ")"
  | .extBand code p => "ext(" ++ numS code ++ ",0x" ++ hexS p ++ ")"
  | .absence code p => "abs(" ++ numS code ++ ",0x" ++ hexS p ++ ")"

/-- Comma-separated values. -/
def renderVals (vs : List GValue) : String :=
  match vs with
  | [] => ""
  | v :: rest =>
    match rest with
    | [] => renderVal v
    | _ :: _ => renderVal v ++ "," ++ renderVals rest

/-- One optional 32-byte metadata field. -/
def renderMeta1 (tag : String) (h : Option Bytes) : String :=
  match h with
  | none => ""
  | some b => " " ++ tag ++ "=0x" ++ hexS b

/-- One op. -/
def renderOp (op : GOp) : String :=
  match op with
  | .elta r => "elta sort=" ++ renderRef r
  | .rela r args =>
    "rela rel=" ++ renderRef r ++ " args=[" ++ renderVals args ++ "]"
  | .funa r args v =>
    "funa fun=" ++ renderRef r ++ " args=[" ++ renderVals args ++
    "] value=" ++ renderVal v
  | .eltd r => "eltd target=" ++ renderRef r
  | .cert fmt m cert =>
    "cert fmt=" ++ numS fmt ++
    renderMeta1 "goal" m.goalJudgmentHash ++
    renderMeta1 "rev" m.theoryRev ++
    renderMeta1 "root" m.rootHash ++
    (match m.denBoundLog2Max with
     | none => ""
     | some v => " den=" ++ numS v) ++
    " cert=0x" ++ hexS cert
  | .unknown k p =>
    "unknown kind=" ++ numS k ++ " payload=0x" ++ hexS p

/-- Numbered op lines. -/
def renderOps (ops : List GOp) (i : Nat) : String :=
  match ops with
  | [] => ""
  | op :: rest =>
    "op " ++ numS i ++ ": " ++ renderOp op ++ "\n" ++
    renderOps rest (i + 1)

/-- One zone run. -/
def renderZone (r : ZoneRun) : String :=
  "(" ++ numS r.zcount ++ "," ++ numS r.zindex ++ ")"

/-- Comma-separated zone runs. -/
def renderZones (rs : List ZoneRun) : String :=
  match rs with
  | [] => ""
  | r :: rest =>
    match rest with
    | [] => renderZone r
    | _ :: _ => renderZone r ++ "," ++ renderZones rest

/-- Optional message bytes. -/
def renderMsg (m : Option Bytes) : String :=
  match m with
  | none => "none"
  | some b => "0x" ++ hexS b

/-- Comma-separated dep hashes (unprefixed hex). -/
def renderDeps (ds : List Bytes) : String :=
  match ds with
  | [] => ""
  | d :: rest =>
    match rest with
    | [] => hexS d
    | _ :: _ => hexS d ++ "," ++ renderDeps rest

/-- One commit header plus its ops. -/
def renderCommit (c : GCommit) (i : Nat) : String :=
  "commit " ++ numS i ++ ": sig=0x" ++ hexS (c.sigBytes.take 8) ++
  " author=0x" ++ hexS c.cskel.author ++
  " deps=[" ++ renderDeps c.cskel.deps ++ "]" ++
  " parents=" ++ numS c.cskel.parentCount ++
  " ts=" ++ numS c.cskel.tsClaim ++
  " msg=" ++ renderMsg c.cskel.message ++
  " bodyhash=0x" ++ hexS c.cskel.bodyHash ++
  " ops=" ++ numS c.cbody.ops.length ++
  " zones=[" ++ renderZones c.cbody.zoneRuns ++ "]\n" ++
  renderOps c.cbody.ops 0

/-- Numbered commits. -/
def renderCommits (cs : List GCommit) (i : Nat) : String :=
  match cs with
  | [] => ""
  | c :: rest => renderCommit c i ++ renderCommits rest (i + 1)

/-- One prerequisite line. -/
def renderPrereq (p : Prereq) : String :=
  "prereq flag=" ++ numS p.pflag ++ " chid=0x" ++ hexS p.pchid ++
  (match p.prosterId with
   | none => ""
   | some r => " roster=" ++ numS r) ++ "\n"

/-- The container dump. -/
def renderGeolog (g : Geolog) : String :=
  "container version=1 prereqs=" ++ numS g.prereqs.length ++
  " commits=" ++ numS g.commits.length ++ "\n" ++
  String.join (g.prereqs.map renderPrereq) ++
  renderCommits g.commits 0

/-- Refusal class name. -/
def renderClass (c : RClass) : String :=
  match c with
  | .unreadable => "UNREADABLE"
  | .unsupported => "UNSUPPORTED"

/-- The differential surface: `OK` plus the dump, or one
`CLASS tag witness` line. -/
def renderRes (r : GRes) : String :=
  match r with
  | .ok g => "OK\n" ++ renderGeolog g
  | .err c t w => renderClass c ++ " " ++ t ++ " " ++ numS w ++ "\n"

end Read

/-- Differential-surface renderer (interface export; the definition is
`Read.renderRes`). -/
def renderRes : GRes → String := Read.renderRes

end Geolog
end PPLC
