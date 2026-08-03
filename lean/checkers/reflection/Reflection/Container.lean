import Reflection.Body

/-!
# Geolog reader: the container

The container walk, ported faithfully from the HOL4 reference reader:
magic `"geologfl"`, u32le version 1, the prerequisite table (u8 flag,
32-byte content hash, flag-1 entries a u16le roster id; content hashes
strictly ascending; flags 0–2 live, flag 3 the reserved lineage
anchor — refused `unsupported`), a u32le commit count ≥ 1, then per
commit a length-framed envelope (64-byte signature, then the canonical
archive skeleton) and a length-framed body. The bytes that hash are
the bytes in the file: length framing only, outside the hashed
strings.

The skeleton is the archive's 92-byte end-anchored root — version,
author, deps vec-ref, parent count, timestamp claim, optional message,
body hash — with out-of-line data (dep entries, then message bytes)
packed first and every position law checked. Skeleton refusals carry
the single tag `"skeleton"`; class agreement (unreadable) with the
production decoder is exact, and the finer-grained census is a cheap
later widening.

`readGeolog` accepts exactly what the production wire decoders accept
(residual kinds carried opaquely, certificate blobs decoded, delete
rows carried); `readGeologSealed` adds the sealed proof-artifact
profile: delete-free and residual-free, refusals named `unsupported`.
Everything checkable without hash computation is checked here; the
returned structure keeps the raw skeleton and body byte strings per
commit precisely so the hash-binding layer can consume them without
re-parsing.

This module also re-exports the frozen interface names at
`PPLC.Geolog` level: `rdBody`, `readGeolog`, `readGeologSealed` (and
`Render.lean` adds `renderRes`).
-/

namespace PPLC
namespace Geolog
namespace Read

/-! ## The skeleton -/

/-- `k` 32-byte dep entries from `base`. -/
def rdSkelDepsA (sk : Bytes) (k base : Nat) (acc : List Bytes) :
    Option (List Bytes) :=
  match k with
  | 0 => some acc.reverse
  | k' + 1 =>
    match bytesAt sk base 32 with
    | none => none
    | some c => rdSkelDepsA sk k' (base + 32) (c :: acc)

/-- Dep entries. -/
def rdSkelDeps (sk : Bytes) (k base : Nat) : Option (List Bytes) :=
  rdSkelDepsA sk k base []

/-- The canonical archive skeleton: 92-byte end-anchored root
(+0 version u8 | +1 author 32 bytes | +33 deps vec-ref | +41
parent_count u16le | +43 ts_claim u64le | +51 optional message, one
tag byte plus an 8-byte vec-ref, the none arm zero-filled | +60
body_hash 32 bytes), out-of-line data first, no slack; parent prefix
and content segment of the deps each strictly ascending with no
cross-segment duplicate. -/
def rdSkeleton (sk : Bytes) : Option Skel :=
  if sk.length < 92 then none
  else
    let root := sk.length - 92
    match sk[root]? with
    | none => none
    | some ver =>
    if ver ≠ 1 then none
    else
    match bytesAt sk (root + 1) 32 with
    | none => none
    | some author =>
    match rdLeAt sk (root + 37) 4 with
    | none => none
    | some depCnt =>
    if 65535 < depCnt then none
    else if !vecRefOK sk (root + 33) 0 depCnt then none
    else
    match rdSkelDeps sk depCnt 0 with
    | none => none
    | some deps =>
    match rdLeAt sk (root + 41) 2 with
    | none => none
    | some pc =>
    if depCnt < pc then none
    else
    match rdLeAt sk (root + 43) 8 with
    | none => none
    | some ts =>
    match sk[root + 51]? with
    | none => none
    | some tag =>
    match (if tag = 0 then
             match bytesAt sk (root + 52) 8 with
             | some z =>
               if z = List.replicate 8 0 then some (none, 0) else none
             | none => none
           else if tag = 1 then
             match rdLeAt sk (root + 56) 4 with
             | none => none
             | some mlen =>
               if 4096 < mlen then none
               else if !vecRefOK sk (root + 52) (32 * depCnt) mlen then none
               else
                 match bytesAt sk (32 * depCnt) mlen with
                 | none => none
                 | some mb =>
                   if utf8Ok mb then some (some mb, mlen) else none
           else none : Option (Option Bytes × Nat)) with
    | none => none
    | some (msg, mlen) =>
    match bytesAt sk (root + 60) 32 with
    | none => none
    | some bh =>
    if sk.length ≠ 32 * depCnt + mlen + 92 then none
    else
      let ps := deps.take pc
      let cs := deps.drop pc
      if strictAsc ps && strictAsc cs && noCrossDup ps cs then
        some { author := author, deps := deps, parentCount := pc,
               tsClaim := ts, message := msg, bodyHash := bh }
      else none

/-! ## The container walk -/

/-- The container magic, `"geologfl"`. -/
def gMagic : Bytes := [103, 101, 111, 108, 111, 103, 102, 108]

/-- Prerequisite-table walk result. -/
inductive PrereqR where
  | ok (ps : List Prereq) (pos : Nat)
  | err (c : RClass) (tag : String) (witness : Nat)

/-- `k` prerequisite entries from `pos`. -/
def rdPrereqsA (bs : Bytes) (k pos : Nat) (acc : List Prereq) : PrereqR :=
  match k with
  | 0 => .ok acc.reverse pos
  | k' + 1 =>
    match bs[pos]? with
    | none => .err .unreadable "prereq_truncated" pos
    | some flag =>
      if flag = 3 then .err .unsupported "prereq_flag_3_reserved" pos
      else if 3 < flag then .err .unreadable "prereq_flag_unknown" flag
      else
        match bytesAt bs (pos + 1) 32 with
        | none => .err .unreadable "prereq_truncated" pos
        | some chid =>
          if flag = 1 then
            match rdLeAt bs (pos + 33) 2 with
            | none => .err .unreadable "prereq_truncated" pos
            | some r =>
              rdPrereqsA bs k' (pos + 35)
                ({ pflag := flag, pchid := chid, prosterId := some r } :: acc)
          else
            rdPrereqsA bs k' (pos + 33)
              ({ pflag := flag, pchid := chid, prosterId := none } :: acc)

/-- Prerequisite table. -/
def rdPrereqs (bs : Bytes) (k pos : Nat) : PrereqR :=
  rdPrereqsA bs k pos []

/-- Commit-sequence walk result. -/
inductive CommitR where
  | ok (cs : List GCommit) (pos : Nat)
  | err (c : RClass) (tag : String) (witness : Nat)

/-- `k` commit records from `pos`: u32le envelope length, envelope
(64-byte signature then skeleton), u32le body length, body. -/
def rdCommitsA (bs : Bytes) (k pos : Nat) (acc : List GCommit) : CommitR :=
  match k with
  | 0 => .ok acc.reverse pos
  | k' + 1 =>
    match rdLeAt bs pos 4 with
    | none => .err .unreadable "commit_env_len_truncated" pos
    | some envLen =>
      if envLen < 64 then
        .err .unreadable "envelope_shorter_than_signature" envLen
      else
        match bytesAt bs (pos + 4) envLen with
        | none => .err .unreadable "envelope_truncated" pos
        | some env =>
          let sg := env.take 64
          let sk := env.drop 64
          match rdSkeleton sk with
          | none => .err .unreadable "skeleton" pos
          | some skv =>
            let bpos := pos + 4 + envLen
            match rdLeAt bs bpos 4 with
            | none => .err .unreadable "commit_body_len_truncated" bpos
            | some bodyLen =>
              match bytesAt bs (bpos + 4) bodyLen with
              | none => .err .unreadable "body_truncated" bpos
              | some bb =>
                match rdBody bb with
                | .err c t w => .err c t w
                | .ok body =>
                  rdCommitsA bs k' (bpos + 4 + bodyLen)
                    ({ sigBytes := sg, skelBytes := sk, cskel := skv,
                       bodyBytes := bb, cbody := body } :: acc)

/-- Commit sequence. -/
def rdCommits (bs : Bytes) (k pos : Nat) : CommitR :=
  rdCommitsA bs k pos []

/-- Prerequisite content hashes strictly ascending. -/
def prereqAsc (ps : List Prereq) : Bool :=
  strictAsc (ps.map (·.pchid))

/-- The whole-container read. -/
def readGeolog (bs : Bytes) : GRes :=
  if bs.take 8 ≠ gMagic then .err .unreadable "magic" 0
  else
  match rdLeAt bs 8 4 with
  | none => .err .unreadable "version_truncated" 8
  | some ver =>
  if ver ≠ 1 then .err .unsupported "container_version" ver
  else
  match rdLeAt bs 12 4 with
  | none => .err .unreadable "prereq_count_truncated" 12
  | some pcount =>
  if bs.length < 16 + 33 * pcount then
    .err .unreadable "prereq_count_over_input" pcount
  else
  match rdPrereqs bs pcount 16 with
  | .err c t w => .err c t w
  | .ok prereqs ppos =>
  if !prereqAsc prereqs then .err .unreadable "prereq_order" 0
  else
  match rdLeAt bs ppos 4 with
  | none => .err .unreadable "commit_count_truncated" ppos
  | some ccount =>
  if ccount = 0 then .err .unreadable "commit_count_zero" 0
  else if bs.length < ppos + 4 + 8 * ccount then
    .err .unreadable "commit_count_over_input" ccount
  else
  match rdCommits bs ccount (ppos + 4) with
  | .err c t w => .err c t w
  | .ok commits cend =>
  if cend ≠ bs.length then
    .err .unreadable "trailing_bytes" (bs.length - cend)
  else
    .ok { prereqs := prereqs, commits := commits }

/-! ## The sealed proof-artifact profile -/

/-- Tag and witness of an op outside the sealed fragment: any delete
row (a proof slice is delete-free), and any residual-channel op at
all. -/
def opUnsuppTag (op : GOp) : Option (String × Nat) :=
  match op with
  | .eltd _ => some ("eltd_in_sealed_artifact", 3)
  | .cert _ _ _ => some ("op_kind_outside_fragment", 6)
  | .unknown k _ => some ("op_kind_outside_fragment", k)
  | _ => none

/-- First op outside the sealed fragment, if any. -/
def firstUnsupp (ops : List GOp) : Option (String × Nat) :=
  match ops with
  | [] => none
  | op :: rest =>
    match opUnsuppTag op with
    | some tw => some tw
    | none => firstUnsupp rest

/-- First outside-the-fragment op across all commits. -/
def sealedCheck (g : Geolog) : Option (String × Nat) :=
  match (g.commits.map fun c =>
          match firstUnsupp c.cbody.ops with
          | some tw => [tw]
          | none => []).flatten with
  | [] => none
  | tw :: _ => some tw

/-- The sealed-artifact read: the container read plus the sealed
profile. -/
def readGeologSealed (bs : Bytes) : GRes :=
  match readGeolog bs with
  | .err c t w => .err c t w
  | .ok g =>
    match sealedCheck g with
    | some (t, w) => .err .unsupported t w
    | none => .ok g

end Read

/-! ## Frozen interface exports -/

/-- Commit-body decode (interface export; the definition is
`Read.rdBody`). -/
def rdBody : Bytes → BRes := Read.rdBody

/-- Container decode (interface export; the definition is
`Read.readGeolog`). -/
def readGeolog : Bytes → GRes := Read.readGeolog

/-- Sealed-profile container decode (interface export; the definition
is `Read.readGeologSealed`). -/
def readGeologSealed : Bytes → GRes := Read.readGeologSealed

end Geolog
end PPLC
