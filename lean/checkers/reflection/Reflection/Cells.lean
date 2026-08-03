import Reflection.Codec

/-!
# Geolog reader: cells

The section-2 cell grammars of the geolog wire contract (rev 15),
ported faithfully from the HOL4 reference reader: the primordial
literal dtype table (codes 0x00–0x0E) with per-code payload
validators, element references (`bstr(2..=7)` external with minimal
uvarint dep index and minimal-LE counter, or `uint` local; the retired
36-byte hash spelling refused), values (reference | `array(2)` of code
and payload, with the contextual commit-id cell at code 0x0F, the
ground-extension band 0x10–0x3F and the absence band 0x40–0x4F carried
opaquely, codes ≥ 0x50 refused), certificate-payload metadata maps,
and the deterministic-CBOR write-side cell encoders the fixed-point
gates re-encode through.
-/

namespace PPLC
namespace Geolog
namespace Read

/-- Default value used only by total-function spellings whose callers
guarantee in-range access (never observable on any accept or refuse
path). -/
instance : Inhabited GValue := ⟨.commitId 0⟩

/-! ## The dtype table -/

/-- Inline blob / string payload cap. -/
def GEOLOG_BLOB_INLINE_MAX : Nat := 4096

/-- Rational-family shared shape: minimal-uvarint numerator length,
numerator bytes, denominator bytes (extent-implied, terminal; both
limbs nonempty). -/
def qShape (p : Bytes) : Option (Bytes × Bytes) :=
  match rdUleb p 0 with
  | none => none
  | some (nlen, pos) =>
    if p.length < pos + nlen then none
    else
      let numB := (p.drop pos).take nlen
      let denB := p.drop (pos + nlen)
      if nlen = 0 ∨ denB = [] then none
      else some (numB, denB)

/-- Rational literal: signed minimal-LE numerator, unsigned minimal-LE
nonzero denominator, reduced form. -/
def litQOk (p : Bytes) : Bool :=
  match qShape p with
  | none => false
  | some (numB, denB) =>
    minLeS numB && minLeU denB && decide (leN denB ≠ 0) &&
    decide (gcdN (sgnMagLe numB) (leN denB) = 1)

/-- Extended-nonnegative rational literal: `n/0` spells infinity and
must be `1/0`; finite values are reduced. -/
def litEnnRatOk (p : Bytes) : Bool :=
  match qShape p with
  | none => false
  | some (numB, denB) =>
    minLeU numB && minLeU denB &&
    (if leN denB = 0 then decide (leN numB = 1)
     else decide (gcdN (leN numB) (leN denB) = 1))

/-- Shape literal: minimal-uvarint count, then that many minimal
uvarints, exact extent. -/
def litShapeOk (p : Bytes) : Bool :=
  match rdUleb p 0 with
  | none => false
  | some (cnt, pos0) =>
    if p.length < pos0 + cnt then false
    else
      match rdHexValsK (fun bs pos => rdUleb bs pos) p pos0 cnt with
      | none => false
      | some (_, pend) => decide (pend = p.length)

/-- Tensor-handle literal: fixed 34-byte multihash shape. -/
def litTensorOk (p : Bytes) : Bool :=
  decide (p.length = 34 ∧ p[0]? = some 30 ∧ p[1]? = some 32)

/-- Blob-reference literal: fixed 35-byte tagged multihash shape. -/
def litBlobRefOk (p : Bytes) : Bool :=
  decide (p.length = 35 ∧ (p[0]? = some 12 ∨ p[0]? = some 4) ∧
          p[1]? = some 30 ∧ p[2]? = some 32)

/-- Peer-id literal: multihash, identity (code 0, length ≤ 42) or
sha2-256 (code 18, length 32), total length ≤ 64, exact extent. -/
def litPeerIdOk (p : Bytes) : Bool :=
  decide (p.length ≤ 64) &&
  (match rdUleb p 0 with
   | none => false
   | some (code, p1) =>
     match rdUleb p p1 with
     | none => false
     | some (len, p2) =>
       decide (p.length = p2 + len) &&
       (if code = 0 then decide (len ≤ 42)
        else if code = 18 then decide (len = 32)
        else false))

/-- The primordial literal validator, by dtype code. -/
def litOk (code : Nat) (p : Bytes) : Bool :=
  if code = 0 then litQOk p
  else if code = 1 then minLeS p && decide (p.length ≤ 8)
  else if code = 2 then minLeU p && decide (p.length ≤ 8)
  else if code = 3 then decide (p = [0] ∨ p = [1])
  else if code = 4 then decide (p.length ≤ GEOLOG_BLOB_INLINE_MAX) && utf8Ok p
  else if code = 5 then litEnnRatOk p
  else if code = 6 then minLeS p
  else if code = 7 then minLeU p
  else if code = 8 then litShapeOk p
  else if code = 9 then minLeU p && decide (p.length ≤ 8)
  else if code = 10 then litTensorOk p
  else if code = 11 then minLeS p && decide (p.length ≤ 8)
  else if code = 12 then decide (p.length ≤ GEOLOG_BLOB_INLINE_MAX)
  else if code = 13 then litBlobRefOk p
  else if code = 14 then litPeerIdOk p
  else false

/-! ## Element references and values -/

/-- Largest legal dependency index. -/
def MAX_DEP_INDEX : Nat := 65534

/-- Element reference cell: `bstr(2..=7)` external (minimal uvarint
dep index ≤ 65534, then a minimal-LE u32 counter, extent-implied) or
`uint` local (≤ u32 max). `bstr(36)` is the retired hash spelling,
refused. -/
def rdElemRef (bs : Bytes) (pos : Nat) : Option (ElemRef × Nat) :=
  match peekMajor bs pos with
  | none => none
  | some m =>
    if m = MAJ_BYTES then
      match rdBstrC bs pos with
      | none => none
      | some (b, p1) =>
        if b.length = 36 then none
        else if b.length < 2 ∨ 7 < b.length then none
        else
          match rdUleb b 0 with
          | none => none
          | some (dep, dpos) =>
            if MAX_DEP_INDEX < dep then none
            else
              let ctr := b.drop dpos
              if minLeU ctr && decide (ctr.length ≤ 8) &&
                 decide (leN ctr ≤ 4294967295)
              then some (.ext dep (leN ctr), p1)
              else none
    else if m = MAJ_UINT then
      match rdUintC bs pos with
      | none => none
      | some (n, p1) =>
        if 4294967295 < n then none else some (.loc n, p1)
    else none

/-- Value cell: element reference, or `array(2)` of code and `bstr`
payload — primordial literal (validated), contextual commit-id cell
(code 15: minimal uvarint deps index, exact extent), extension band
(16–63) and absence band (64–79) carried opaquely, others refused. -/
def rdValue (bs : Bytes) (pos : Nat) : Option (GValue × Nat) :=
  match peekMajor bs pos with
  | none => none
  | some m =>
    if m = MAJ_BYTES ∨ m = MAJ_UINT then
      match rdElemRef bs pos with
      | none => none
      | some (r, p1) => some (.ref r, p1)
    else if m = MAJ_ARRAY then
      match rdArrC bs pos with
      | none => none
      | some (arity, p1) =>
        if arity ≠ 2 then none
        else
          match rdUintC bs p1 with
          | none => none
          | some (code, p2) =>
            match rdBstrC bs p2 with
            | none => none
            | some (payload, p3) =>
              if code = 15 then
                if payload = [] ∨ 3 < payload.length then none
                else
                  match rdUleb payload 0 with
                  | none => none
                  | some (idx, ppos) =>
                    if ppos = payload.length ∧ idx ≤ MAX_DEP_INDEX
                    then some (.commitId idx, p3)
                    else none
              else if code ≤ 14 then
                if litOk code payload then some (.lit code payload, p3)
                else none
              else if 16 ≤ code ∧ code ≤ 63 then
                some (.extBand code payload, p3)
              else if 64 ≤ code ∧ code ≤ 79 then
                some (.absence code payload, p3)
              else none
    else none

/-- `k` consecutive value cells. -/
def rdValuesKA (bs : Bytes) (pos k : Nat) (acc : List GValue) :
    Option (List GValue × Nat) :=
  match k with
  | 0 => some (acc.reverse, pos)
  | k' + 1 =>
    match rdValue bs pos with
    | none => none
    | some (v, p1) => rdValuesKA bs p1 k' (v :: acc)

/-- `k` consecutive value cells. -/
def rdValuesK (bs : Bytes) (pos k : Nat) : Option (List GValue × Nat) :=
  rdValuesKA bs pos k []

/-! ## Row helpers -/

/-- Legacy discrimination: a text-string first cell is the legacy
text-name grammar, which rides body format 0 only — its presence in a
tabled row is refused. -/
def isTextMajor (b : Bytes) : Bool :=
  match peekMajor b 0 with
  | some m => decide (m = MAJ_TEXT)
  | none => false

/-- One element reference, spanning the whole row exactly. -/
def oneRefExact (b : Bytes) : Option ElemRef :=
  match rdElemRef b 0 with
  | none => none
  | some (r, pos) => if pos = b.length then some r else none

/-- An argument row: `array(n)` of value cells, exact extent, with the
count pre-bounded against remaining bytes. -/
def rdArgsRow (b : Bytes) : Option (List GValue) :=
  match rdArrC b 0 with
  | none => none
  | some (n, p1) =>
    if b.length < p1 + n then none
    else
      match rdValuesK b p1 n with
      | none => none
      | some (vs, p2) => if p2 = b.length then some vs else none

/-- One value cell, spanning the whole row exactly. -/
def rdValueRowExact (b : Bytes) : Option GValue :=
  match rdValue b 0 with
  | none => none
  | some (v, pos) => if pos = b.length then some v else none

/-! ## Certificate payloads -/

/-- The empty certificate metadata record. -/
def emptyCertMeta : CertMeta := {}

/-- Certificate metadata map entries: registered keys 0–3, strictly
ascending; keys 0–2 carry `bstr(32)`, key 3 a uint. Primitive
recursion on the entry count. -/
def rdCertMetaEntries (b : Bytes) (pos : Nat) (prev : Option Nat)
    (k : Nat) (m : CertMeta) : Option (CertMeta × Nat) :=
  match k with
  | 0 => some (m, pos)
  | k' + 1 =>
    match rdUintC b pos with
    | none => none
    | some (key, p1) =>
      if (match prev with | some pk => decide (key ≤ pk) | none => false)
      then none
      else if key = 0 then
        match rdBstrC b p1 with
        | some (h, p2) =>
          if h.length = 32 then
            rdCertMetaEntries b p2 (some key) k'
              { m with goalJudgmentHash := some h }
          else none
        | none => none
      else if key = 1 then
        match rdBstrC b p1 with
        | some (h, p2) =>
          if h.length = 32 then
            rdCertMetaEntries b p2 (some key) k'
              { m with theoryRev := some h }
          else none
        | none => none
      else if key = 2 then
        match rdBstrC b p1 with
        | some (h, p2) =>
          if h.length = 32 then
            rdCertMetaEntries b p2 (some key) k'
              { m with rootHash := some h }
          else none
        | none => none
      else if key = 3 then
        match rdUintC b p1 with
        | some (v, p2) =>
          rdCertMetaEntries b p2 (some key) k'
            { m with denBoundLog2Max := some v }
        | none => none
      else none

/-- Certificate-op payload: format uint (≤ 65535), metadata map (≤ 4
entries), certificate `bstr`, exact extent. -/
def rdCertPayload (b : Bytes) : Option (Nat × CertMeta × Bytes) :=
  match rdUintC b 0 with
  | none => none
  | some (fmt, p1) =>
    if 65535 < fmt then none
    else
      match rdMapC b p1 with
      | none => none
      | some (n, p2) =>
        if 4 < n then none
        else
          match rdCertMetaEntries b p2 none n emptyCertMeta with
          | none => none
          | some (mv, p3) =>
            match rdBstrC b p3 with
            | none => none
            | some (cert, p4) =>
              if p4 = b.length then some (fmt, mv, cert) else none

/-! ## Write-side cell encoders (the fixed-point gates' canonical
serializers) -/

/-- Canonical element-reference cell. -/
def encElemRef (r : ElemRef) : Bytes :=
  match r with
  | .loc n => encCborUint n
  | .ext d c => encBstr (encUleb d ++ minLeBytes c)

/-- Canonical natural-literal cell (the mode-1 synthesized cell). -/
def encNatCell (v : Nat) : Bytes :=
  encArrHead 2 ++ encCborUint 2 ++ encBstr (minLeBytes v)

/-- Canonical value cell. -/
def encValue (v : GValue) : Bytes :=
  match v with
  | .ref r => encElemRef r
  | .lit code p => encArrHead 2 ++ encCborUint code ++ encBstr p
  | .commitId i => encArrHead 2 ++ encCborUint 15 ++ encBstr (encUleb i)
  | .extBand code p => encArrHead 2 ++ encCborUint code ++ encBstr p
  | .absence code p => encArrHead 2 ++ encCborUint code ++ encBstr p

/-- Certificate metadata re-encoder (exact inverse of
`rdCertMetaEntries` on its accept set: strictly ascending keys). -/
def encCertMeta (m : CertMeta) : Bytes :=
  let cnt := (match m.goalJudgmentHash with | none => 0 | some _ => 1) +
             (match m.theoryRev with | none => 0 | some _ => 1) +
             (match m.rootHash with | none => 0 | some _ => 1) +
             (match m.denBoundLog2Max with | none => 0 | some _ => 1)
  encCborHead MAJ_MAP cnt ++
  (match m.goalJudgmentHash with
   | none => [] | some h => encCborUint 0 ++ encBstr h) ++
  (match m.theoryRev with
   | none => [] | some h => encCborUint 1 ++ encBstr h) ++
  (match m.rootHash with
   | none => [] | some h => encCborUint 2 ++ encBstr h) ++
  (match m.denBoundLog2Max with
   | none => [] | some v => encCborUint 3 ++ encCborUint v)

/-- Residual-channel row re-encoder (kind u16le, then the payload). -/
def encResidualRow (op : GOp) : Bytes :=
  match op with
  | .cert fmt m cert => encLe2 6 ++ encCborUint fmt ++ encCertMeta m ++ encBstr cert
  | .unknown k p => encLe2 k ++ p
  | _ => []

/-- Zone-run record re-encoder (count u32le, zone index u16le). -/
def encZoneRun (r : ZoneRun) : Bytes := encLe4 r.zcount ++ encLe2 r.zindex

end Read
end Geolog
end PPLC
