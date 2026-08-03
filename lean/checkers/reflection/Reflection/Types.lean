/-!
# Geolog reader types (shared interface)

The value model for the geolog container/commit-body reader: the Lean
twins of the reference reader's datatypes, over `List Nat` bytes so
that every consumer downstream — including kernel-side `decide`
evaluation — reduces structurally. Two result classes throughout:

* `RClass.unreadable` — the bytes are not a canonical spelling of any
  well-formed structure (malformed wire, non-minimal encoding,
  ordering violation);
* `RClass.unsupported` — well-formed wire outside the fragment this
  reader accepts (unknown format numbers, reserved flags, op kinds
  outside the sealed-artifact fragment).

Refusals carry a stable tag string plus a witness number, so
cross-implementation differential drivers compare refusal classes
directly.
-/

namespace PPLC
namespace Geolog

/-- Byte string as a list of naturals (each `< 256` by construction of
the readers; nothing here enforces it by type). -/
abbrev Bytes := List Nat

/-- Refusal class: unreadable wire vs well-formed-but-outside-fragment. -/
inductive RClass where
  | unreadable
  | unsupported
  deriving Repr, DecidableEq

/-- Element reference: a local element counter, or a
(dependency index, element counter) pair into a dep commit. -/
inductive ElemRef where
  | loc (n : Nat)
  | ext (dep counter : Nat)
  deriving Repr, DecidableEq

/-- A value cell: reference, primordial literal (code + payload bytes),
commit id, extension-band cell, or absence-band cell. -/
inductive GValue where
  | ref (r : ElemRef)
  | lit (code : Nat) (payload : Bytes)
  | commitId (i : Nat)
  | extBand (code : Nat) (payload : Bytes)
  | absence (code : Nat) (payload : Bytes)
  deriving Repr, DecidableEq

/-- Metadata entries of a residual-channel certificate op. -/
structure CertMeta where
  goalJudgmentHash : Option Bytes := none
  theoryRev        : Option Bytes := none
  rootHash         : Option Bytes := none
  denBoundLog2Max  : Option Nat  := none
  deriving Repr, DecidableEq

/-- A decoded body operation. -/
inductive GOp where
  | elta (r : ElemRef)
  | rela (r : ElemRef) (args : List GValue)
  | funa (r : ElemRef) (args : List GValue) (value : GValue)
  | eltd (r : ElemRef)
  | cert (fmt : Nat) (cmeta : CertMeta) (payload : Bytes)
  | unknown (kind : Nat) (payload : Bytes)
  deriving Repr, DecidableEq

/-- A zone run (count, zone index). -/
structure ZoneRun where
  zcount : Nat
  zindex : Nat
  deriving Repr, DecidableEq

/-- A decoded commit body: canonical op sequence plus zone runs. -/
structure GBody where
  ops      : List GOp
  zoneRuns : List ZoneRun
  deriving Repr, DecidableEq

/-- A decoded skeleton (the hash/sign surface's logical content). -/
structure Skel where
  author      : Bytes
  deps        : List Bytes
  parentCount : Nat
  tsClaim     : Nat
  message     : Option Bytes
  bodyHash    : Bytes
  deriving Repr, DecidableEq

/-- A decoded commit: raw byte spans retained beside the parsed
structures (hash-binding layers re-consume them without re-parsing). -/
structure GCommit where
  sigBytes  : Bytes
  skelBytes : Bytes
  cskel     : Skel
  bodyBytes : Bytes
  cbody     : GBody
  deriving Repr, DecidableEq

/-- A prerequisite-table row. -/
structure Prereq where
  pflag     : Nat
  pchid     : Bytes
  prosterId : Option Nat
  deriving Repr, DecidableEq

/-- A decoded container file. -/
structure Geolog where
  prereqs : List Prereq
  commits : List GCommit
  deriving Repr, DecidableEq

/-- Body decode result. -/
inductive BRes where
  | ok  (b : GBody)
  | err (c : RClass) (tag : String) (witness : Nat)
  deriving Repr

/-- Container decode result. -/
inductive GRes where
  | ok  (g : Geolog)
  | err (c : RClass) (tag : String) (witness : Nat)
  deriving Repr

end Geolog
end PPLC
