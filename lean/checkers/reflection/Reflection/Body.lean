import Reflection.Cells

/-!
# Geolog reader: commit bodies

The commit-body decoder. A body is a u16le format number followed by
an archive frame — eleven byte-vector channels (interleave, symbols,
elta_sort, tmpl, holes_local, holes_nat, lit_payloads, stream_mixed,
eltd_target, seg_other, zone_runs) with an 88-byte root of vec-refs
end-anchored, channel data packed from offset 0, no slack. There is
one body grammar, the **template frame**: cluster templates whose
cells are synthesized from four carriers per position mode and
re-parsed through the shared cell validators, the whole channel set
then re-encoded through the canonical encoder (`encTemplateChans`)
and byte-compared — the frame fixed-point gate, which makes the
accept set exactly the canonical spellings.

Format registry (measured against the production wire):

* **format 1** is the template frame — production geolog-envelope's
  `BODY_FORMAT_HEXANE_TEMPLATES_V1 = 1`, "the only format, and the
  default": the hexane run-length column codec carrying the template
  frame, the only format ever emitted on the production wire;
* **format 2** is the same template frame under the fixture-era
  reference numbering (the landed receipt fixtures were minted with
  this byte), accepted as an alias — see `rdBody`;
* **format 0** is the legacy migration lane, refused `unsupported`
  here; other formats are refused naming the value.

History (measured in both Rust registries): the reference numbering
is the WORKSHOP wire's registry — the workshop engine's
geolog-envelope has 1 = `BODY_FORMAT_HEXANE_COLUMNS_V1`
(a legacy layout, decode-retained there for read-compatibility of
previously staged artifacts) and 2 =
`BODY_FORMAT_TEMPLATE_COLUMNS_V1` (the workshop default encode to
this day). Production geolog-alpha compacted the registry at birth:
1 = templates, nothing else decodes (format 2 is
`UnsupportedBodyFormat` there). So the hexane-columns layout shipped
only on the workshop wire, never the production wire, and nothing
hexane was ever certified through this reader — its walk has been
deleted from this reader; only the run-length column
*codec* (Codec.lean) keeps the hexane name, as does production's
registry constant. The HOL4 reference reader as of this writing still
speaks the workshop-era wire (fmt 1 = hexane, no template grammar);
its port is planned follow-up work.

Refusals are total, fail-closed, and named: `(class, tag, witness)`
with the tag strings mirrored from the HOL4 reference reader where
the grammars overlap (the cross-implementation differential compares
them via renders).
-/

namespace PPLC
namespace Geolog
namespace Read

/-! ## The eleven-channel frame walk -/

/-- The archive frame: 88-byte root of eleven vec-refs at the buffer
end, channel data packed in field order from offset 0, no slack
anywhere. Returns the eleven channel byte strings. -/
def rdFrameChans (fr : Bytes) : Option (List Bytes) :=
  if fr.length < 88 then none
  else
    let root := fr.length - 88
    let rdc := fun i => rdLeAt fr (root + 8 * i + 4) 4
    match rdc 0, rdc 1, rdc 2, rdc 3, rdc 4, rdc 5 with
    | some c0, some c1, some c2, some c3, some c4, some c5 =>
      (match rdc 6, rdc 7, rdc 8, rdc 9, rdc 10 with
       | some c6, some c7, some c8, some c9, some c10 =>
         let cnts := [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
         if fr.length ≠ natSum cnts + 88 then none
         else
           let chk := fun i =>
             vecRefOK fr (root + 8 * i) (natSum (cnts.take i)) (cnts.getD i 0)
           if !(chk 0 && chk 1 && chk 2 && chk 3 && chk 4 && chk 5 &&
                chk 6 && chk 7 && chk 8 && chk 9 && chk 10)
           then none
           else
             let sl := fun i =>
               (fr.drop (natSum (cnts.take i))).take (cnts.getD i 0)
             some [sl 0, sl 1, sl 2, sl 3, sl 4, sl 5,
                   sl 6, sl 7, sl 8, sl 9, sl 10]
       | _, _, _, _, _ => none)
    | _, _, _, _, _, _ => none

/-! ## Zone runs -/

/-- `k` zone records (count u32le, zone index u16le), exact extent. -/
def rdZoneRecsA (b : Bytes) (k pos : Nat) (acc : List ZoneRun) :
    Option (List ZoneRun) :=
  match k with
  | 0 => if pos = b.length then some acc.reverse else none
  | k' + 1 =>
    match rdLeAt b pos 4, rdLeAt b (pos + 4) 2 with
    | some c, some z =>
      rdZoneRecsA b k' (pos + 6) ({ zcount := c, zindex := z } :: acc)
    | _, _ => none

/-- Zone records. -/
def rdZoneRecs (b : Bytes) (k pos : Nat) : Option (List ZoneRun) :=
  rdZoneRecsA b k pos []

/-- Adjacent zone runs carry distinct zone indices. -/
def zAdjOk : List ZoneRun → Bool
  | [] => true
  | r :: rest =>
    match rest with
    | [] => true
    | s :: _ => decide (r.zindex ≠ s.zindex) && zAdjOk rest

/-- The zone-run laws: no empty run, no adjacent duplicates, no
single all-default run, and (when present) exact coverage of the
body's timestamp cells. -/
def zoneLawsOk (runs : List ZoneRun) (tsCells : Nat) : Bool :=
  runs.all (fun r => decide (r.zcount ≠ 0)) &&
  zAdjOk runs &&
  !(match runs with
    | [r] => decide (r.zindex = 65535)
    | _ => false) &&
  (decide (runs = ([] : List ZoneRun)) ||
   decide (natSum (runs.map (·.zcount)) = tsCells))

/-- Timestamp-cell count of a value (dtype code 11). -/
def tsOfVal (v : GValue) : Nat :=
  match v with
  | .lit code _ => if code = 11 then 1 else 0
  | _ => 0

/-- Timestamp-cell count of an op. -/
def tsOfOp (op : GOp) : Nat :=
  match op with
  | .rela _ args => natSum (args.map tsOfVal)
  | .funa _ args v => natSum (args.map tsOfVal) + tsOfVal v
  | _ => 0

/-- Timestamp-cell count of an op sequence. -/
def tsCellCount (ops : List GOp) : Nat := natSum (ops.map tsOfOp)

/-! ## Canonical element order (the breadth-first sort walk) -/

/-- Indices whose sort is the local element `p` (self-loops
excluded). -/
def childrenOf (sorts : List ElemRef) (p : Nat) : List Nat :=
  (List.range sorts.length).filter fun i =>
    match sorts[i]? with
    | some (ElemRef.loc k) => decide (k = p ∧ k ≠ i)
    | _ => false

/-- Breadth-first emission from the root queue; fuel bounds the number
of dequeues. -/
def esBfs (sorts : List ElemRef) (queue emitted : List Nat) (fuel : Nat) :
    List Nat :=
  match fuel with
  | 0 => emitted
  | f + 1 =>
    match queue with
    | [] => emitted
    | p :: rest => esBfs sorts (rest ++ childrenOf sorts p) (emitted ++ [p]) f

/-- A legal element sort: a local reference below the element count
(self-sorted only at index 0) or any external reference. -/
def esLegalSort (sorts : List ElemRef) (i : Nat) : Bool :=
  match sorts[i]? with
  | some (ElemRef.loc k) => decide ((k = i → i = 0) ∧ k < sorts.length)
  | some (ElemRef.ext _ _) => true
  | none => false

/-- The canonical element order: self-rooted elements first, then
external-sorted roots by cell bytes (ties by index), then the
breadth-first descent; defined iff every element is reached. -/
def esEltaOrder (sorts : List ElemRef) (cells : List Bytes) :
    Option (List Nat) :=
  let e := sorts.length
  if !((List.range e).all (esLegalSort sorts)) then none
  else
    let selfRoots := (List.range e).filter fun i =>
      match sorts[i]? with
      | some (ElemRef.loc k) => decide (k = i)
      | _ => false
    let extRoots0 := (List.range e).filter fun i =>
      match sorts[i]? with
      | some (ElemRef.ext _ _) => true
      | _ => false
    let extRoots := sortLe
      (fun i j =>
        lexLt (cells.getD i []) (cells.getD j []) ||
        (decide (cells.getD i [] = cells.getD j []) && decide (i ≤ j)))
      extRoots0
    let order := esBfs sorts (selfRoots ++ extRoots) [] (e + 1)
    if order.length = e then some order else none

/-- The identity permutation check. -/
def isIdentityPerm (order : List Nat) : Bool :=
  decide (order = List.range order.length)

/-! ## Table row decoding (column decodes and the template re-parse path) -/

/-- Symbol-table lookup. -/
def symResolve (symbols : List Bytes) (idx : Nat) : Option Bytes :=
  symbols[idx]?

/-- Element declarations: symbol indices to (sort refs, sort cells). -/
def decEltasA (symbols : List Bytes) (idxs : List Nat)
    (accR : List ElemRef) (accC : List Bytes) :
    Option (List ElemRef × List Bytes) :=
  match idxs with
  | [] => some (accR.reverse, accC.reverse)
  | idx :: rest =>
    match symResolve symbols idx with
    | none => none
    | some cell =>
      if isTextMajor cell then none
      else
        match oneRefExact cell with
        | none => none
        | some r => decEltasA symbols rest (r :: accR) (cell :: accC)

/-- Element declarations. -/
def decEltas (symbols : List Bytes) (idxs : List Nat) :
    Option (List ElemRef × List Bytes) :=
  decEltasA symbols idxs [] []

/-- Element-delete rows: one element reference per row. -/
def decEltdsA (rows : List Bytes) (accO : List GOp) (accK : List Bytes) :
    Option (List GOp × List Bytes) :=
  match rows with
  | [] => some (accO.reverse, accK.reverse)
  | row :: rest =>
    if isTextMajor row then none
    else
      match oneRefExact row with
      | none => none
      | some r => decEltdsA rest (.eltd r :: accO) (row :: accK)

/-- Element-delete rows. -/
def decEltds (rows : List Bytes) : Option (List GOp × List Bytes) :=
  decEltdsA rows [] []

/-- Residual-channel rows: kind u16le then payload. Kinds ≤ 3 belong
to the four ruled tables and are refused here; kind 6 decodes as a
certificate op; all other kinds (the tombstoned 4/5 included) carry
forward opaquely — the sealed profile refuses them later, not at the
wire. -/
def decResidualsA (rows : List Bytes) (acc : List GOp) :
    Option (List GOp) :=
  match rows with
  | [] => some acc.reverse
  | row :: rest =>
    if row.length < 2 then none
    else
      let kind := leN (row.take 2)
      let payload := row.drop 2
      if kind ≤ 3 then none
      else if kind = 6 then
        match rdCertPayload payload with
        | none => none
        | some (fmt, mv, cert) =>
          decResidualsA rest (.cert fmt mv cert :: acc)
      else decResidualsA rest (.unknown kind payload :: acc)

/-- Residual-channel rows. -/
def decResiduals (rows : List Bytes) : Option (List GOp) :=
  decResidualsA rows []

/-- Orphan-freeness: the used-index set is exactly `{0..nsym-1}` —
sort + adjacent dedup gives the strictly ascending enumeration of the
set, and equality with the range is the whole check (indices over
`nsym` were already refused at resolve time). -/
def allUsed (nsym : Nat) (idxs : List Nat) : Bool :=
  decide (dedupAdj (sortLe (fun a b => decide (a ≤ b)) idxs) =
          List.range nsym)

/-! ## Delta columns (format 2) -/

/-- Run-stream value of a delta column: one signed-LEB delta,
sign-magnitude. -/
def rdDeltaVal (bs : Bytes) (pos : Nat) : Option ((Bool × Nat) × Nat) :=
  match rdSleb bs pos with
  | none => none
  | some (neg, mag, p) => some ((neg, mag), p)

/-- Delta value writer. -/
def encDeltaVal (d : Bool × Nat) : Bytes :=
  if d.1 then encSlebNeg d.2 else encSlebPos d.2

def I64MAX : Nat := 9223372036854775807

/-- Realized values are the running prefix sums from base 0; the
value domain is `[0, 2^63)`: a negative or over-i64 running value
refuses. -/
def realizeDeltasA (ds : List (Bool × Nat)) (run : Nat) (acc : List Nat) :
    Option (List Nat) :=
  match ds with
  | [] => some acc.reverse
  | d :: rest =>
    if d.1 then
      if run < d.2 then none
      else realizeDeltasA rest (run - d.2) ((run - d.2) :: acc)
    else
      let v := run + d.2
      if I64MAX < v then none
      else realizeDeltasA rest v (v :: acc)

/-- Prefix-sum realization. -/
def realizeDeltas (ds : List (Bool × Nat)) : Option (List Nat) :=
  realizeDeltasA ds 0 []

/-- Full delta-column read: run-length parse, claim cap, canonical
re-encode gate on the delta sequence, then realization with the
domain law. -/
def readDeltaCol (bs : Bytes) : Option (List Nat) :=
  match readCol rdDeltaVal encDeltaVal bs with
  | none => none
  | some ds => realizeDeltas ds

/-- Delta sequence of a value sequence (encoder side, base 0). -/
def deltasOfA (vs : List Nat) (prev : Nat) (acc : List (Bool × Nat)) :
    List (Bool × Nat) :=
  match vs with
  | [] => acc.reverse
  | v :: rest =>
    deltasOfA rest v
      ((if prev ≤ v then (false, v - prev) else (true, prev - v)) :: acc)

/-- Delta sequence of a value sequence. -/
def deltasOf (vs : List Nat) : List (Bool × Nat) := deltasOfA vs 0 []

/-- Canonical delta-column bytes of a value sequence. -/
def encDeltaColumn (vs : List Nat) : Bytes :=
  hexSave encDeltaVal (deltasOf vs)

/-- Canonical u64-column bytes. -/
def encU64Column (vs : List Nat) : Bytes := hexSave encHexU64 vs

/-- Canonical byte-rows-column bytes. -/
def encBytesColumn (rows : List Bytes) : Bytes := hexSave encHexBytes rows

/-- Framed sub-segment writer: minimal-ULEB length, then the bytes
(the read side is `rdHexBytes`, verbatim). -/
def encSeg (s : Bytes) : Bytes := encUleb s.length ++ s

/-! ## The mode law (format 2) -/

/-- A local element reference. -/
def isLocalRef (v : GValue) : Bool :=
  match v with
  | .ref (.loc _) => true
  | _ => false

/-- A natural literal (dtype code 2). -/
def isNatLit (v : GValue) : Bool :=
  match v with
  | .lit code _ => decide (code = 2)
  | _ => false

/-- Literal/band code of a value, if any. -/
def codeOfVal (v : GValue) : Option Nat :=
  match v with
  | .lit code _ => some code
  | .extBand code _ => some code
  | .absence code _ => some code
  | _ => none

/-- The position-mode law: 0 all-local, 1 all-natural, `16 + code` for
a uniform non-natural code (never 2 or 15), else 2 (mixed). Derived
from the values, never producer choice. -/
def classifyWire (vs : List GValue) : Nat :=
  if vs.all isLocalRef then 0
  else if vs.all isNatLit then 1
  else
    match vs with
    | [] => 2
    | v :: _ =>
      match codeOfVal v with
      | none => 2
      | some c =>
        if decide (c ≠ 2) && decide (c ≠ 15) &&
           vs.all (fun x => decide (codeOfVal x = some c))
        then 16 + c else 2

/-- Carrier projectors (encoder side; total with junk defaults — the
classify guard makes the defaults unreachable on the emit paths). -/
def localOf (v : GValue) : Nat :=
  match v with
  | .ref (.loc n) => n
  | _ => 0

def natOf (v : GValue) : Nat :=
  match v with
  | .lit _ p => leN p
  | _ => 0

def bstrOf (v : GValue) : Bytes :=
  match v with
  | .lit _ p => encBstr p
  | .extBand _ p => encBstr p
  | .absence _ p => encBstr p
  | _ => []

/-! ## The canonical template encoder (format 2, write side as a
function of the decoded content) -/

/-- One pass over ops: elta sorts, rela/funa rows, eltd targets,
residual ops — in op order per family. -/
def splitOpsA (ops : List GOp) (accE : List ElemRef)
    (accR : List (Bool × Bytes × List GValue)) (accD : List ElemRef)
    (accO : List GOp) :
    List ElemRef × List (Bool × Bytes × List GValue) × List ElemRef ×
    List GOp :=
  match ops with
  | [] => (accE.reverse, accR.reverse, accD.reverse, accO.reverse)
  | op :: rest =>
    match op with
    | .elta r => splitOpsA rest (r :: accE) accR accD accO
    | .rela r args =>
      splitOpsA rest accE ((false, encElemRef r, args) :: accR) accD accO
    | .funa r args v =>
      splitOpsA rest accE ((true, encElemRef r, args ++ [v]) :: accR)
        accD accO
    | .eltd r => splitOpsA rest accE accR (r :: accD) accO
    | .cert fmt m c =>
      splitOpsA rest accE accR accD (.cert fmt m c :: accO)
    | .unknown k p =>
      splitOpsA rest accE accR accD (.unknown k p :: accO)

/-- Symbol pairs (cell, reference) of the symbol-bearing ops, in op
order. -/
def symPairsA (ops : List GOp) (acc : List (Bytes × ElemRef)) :
    List (Bytes × ElemRef) :=
  match ops with
  | [] => acc.reverse
  | op :: rest =>
    match op with
    | .elta r => symPairsA rest ((encElemRef r, r) :: acc)
    | .rela r _ => symPairsA rest ((encElemRef r, r) :: acc)
    | .funa r _ _ => symPairsA rest ((encElemRef r, r) :: acc)
    | _ => symPairsA rest acc

/-- The byte-sorted, deduplicated symbol table (the cell determines
the reference — `encElemRef` is injective — so adjacent-pair dedup is
cell dedup). -/
def symTable (ops : List GOp) : List (Bytes × ElemRef) :=
  dedupAdjG (sortLe (fun a b => lexLe a.1 b.1) (symPairsA ops []))

/-- Split the symbol table into the local-value and (dep, counter)
columns. -/
def tblSplitA (pairs : List (Bytes × ElemRef))
    (accL accD accC : List Nat) : List Nat × List Nat × List Nat :=
  match pairs with
  | [] => (accL.reverse, accD.reverse, accC.reverse)
  | p :: rest =>
    match p.2 with
    | .loc n => tblSplitA rest (n :: accL) accD accC
    | .ext d c => tblSplitA rest accL (d :: accD) (c :: accC)

/-- Index of a cell in the symbol-cell list (0 if absent; the callers
only ask for present cells). -/
def symIdxOfA (cells : List Bytes) (cell : Bytes) (i : Nat) : Nat :=
  match cells with
  | [] => 0
  | c :: rest => if c = cell then i else symIdxOfA rest cell (i + 1)

/-- Index of a cell in the symbol-cell list. -/
def symIdxOf (cells : List Bytes) (cell : Bytes) : Nat :=
  symIdxOfA cells cell 0

/-- Maximal runs of (kind, symbol cell, position count) — the
clustering law (derived, never producer choice). -/
def groupClustersA (rows : List (Bool × Bytes × List GValue))
    (curKey : Bool × Bytes × Nat) (curVals : List (List GValue))
    (acc : List ((Bool × Bytes × Nat) × List (List GValue))) :
    List ((Bool × Bytes × Nat) × List (List GValue)) :=
  match rows with
  | [] => ((curKey, curVals.reverse) :: acc).reverse
  | (f, sc, vs) :: rest =>
    if (f, sc, vs.length) = curKey then
      groupClustersA rest curKey (vs :: curVals) acc
    else
      groupClustersA rest (f, sc, vs.length) [vs]
        ((curKey, curVals.reverse) :: acc)

/-- Cluster grouping. -/
def groupClusters (rows : List (Bool × Bytes × List GValue)) :
    List ((Bool × Bytes × Nat) × List (List GValue)) :=
  match rows with
  | [] => []
  | (f, sc, vs) :: rest => groupClustersA rest (f, sc, vs.length) [vs] []

/-- Transpose: `n` is the inner length; the callers guarantee every
row carries exactly `n` entries (the head default is unreachable). -/
def txpose [Inhabited α] (n : Nat) (rows : List (List α)) :
    List (List α) :=
  match n with
  | 0 => []
  | n' + 1 =>
    rows.map (fun r => r.headD default) :: txpose n' (rows.map List.tail)

/-- Per-position fold: modes plus the four carriers, in traversal
order (cluster, position, row). Components: (modes, holes_local,
holes_nat, lit_payloads, stream_mixed). -/
def encPos : List (List GValue) →
    List Nat × List Nat × List Nat × Bytes × Bytes
  | [] => ([], [], [], [], [])
  | vs :: rest =>
    let (ms, hl, hn, lit, mix) := encPos rest
    let m := classifyWire vs
    if m = 0 then (m :: ms, vs.map localOf ++ hl, hn, lit, mix)
    else if m = 1 then (m :: ms, hl, vs.map natOf ++ hn, lit, mix)
    else if m = 2 then (m :: ms, hl, hn, lit, (vs.map encValue).flatten ++ mix)
    else (m :: ms, hl, hn, (vs.map bstrOf).flatten ++ lit, mix)

/-- Per-cluster fold: kind boundary plus the four template columns
plus the carrier streams. Components: (kind boundary, cluster symbol
indices, position counts, row counts, modes, holes_local, holes_nat,
lit_payloads, stream_mixed). -/
def encClusters (symCells : List Bytes) :
    List ((Bool × Bytes × Nat) × List (List GValue)) →
    Nat × List Nat × List Nat × List Nat × List Nat × List Nat ×
    List Nat × Bytes × Bytes
  | [] => (0, [], [], [], [], [], [], [], [])
  | cl :: rest =>
    let (kb, syms, nposs, cnts, ms, hl, hn, lit, mix) :=
      encClusters symCells rest
    let (key, rows) := cl
    let (funa, sc, npos) := key
    let (pms, phl, phn, plit, pmix) := encPos (txpose npos rows)
    ((if funa then kb else kb + 1),
     symIdxOf symCells sc :: syms,
     npos :: nposs,
     rows.length :: cnts,
     pms ++ ms,
     phl ++ hl,
     phn ++ hn,
     plit ++ lit,
     pmix ++ mix)

/-- The eleven canonical channels of a format-2 body, as a function of
the decoded content — the template-columns encoder, channel-wise. -/
def encTemplateChans (ops : List GOp) (runs : List ZoneRun) : List Bytes :=
  let (eltas, rows, eltds, others) := splitOpsA ops [] [] [] []
  let pairs := symTable ops
  let cells := pairs.map (·.1)
  let (locs, deps, ctrs) := tblSplitA pairs [] [] []
  let (kb, syms, nposs, cnts, ms, hl, hn, lit, mix) :=
    encClusters cells (groupClusters rows)
  [ [],
    encSeg (encDeltaColumn locs) ++ encSeg (encU64Column deps) ++
      encSeg (encDeltaColumn ctrs),
    encU64Column (eltas.map fun r => symIdxOf cells (encElemRef r)),
    encUleb kb ++ encSeg (encDeltaColumn syms) ++
      encSeg (encU64Column nposs) ++ encSeg (encU64Column cnts) ++
      encSeg (encU64Column ms),
    encDeltaColumn hl,
    encU64Column hn,
    lit,
    mix,
    encBytesColumn (eltds.map encElemRef),
    encBytesColumn (others.map encResidualRow),
    (runs.map encZoneRun).flatten ]

/-! ## The template expansion loop (format 2, decode side) -/

/-- Same(code) synthesis: `k` cells from lit_payloads — each a
canonical `bstr` (head then payload), the cell being
`array(2) | code | bstr-slice`. -/
def synthSameA (code k : Nat) (lit : Bytes) (lp : Nat)
    (acc : List Bytes) : Option (List Bytes × Nat) :=
  match k with
  | 0 => some (acc.reverse, lp)
  | k' + 1 =>
    match rdBstrC lit lp with
    | none => none
    | some (_, p') =>
      synthSameA code k' lit p'
        ((encArrHead 2 ++ encCborUint code ++ (lit.drop lp).take (p' - lp))
         :: acc)

/-- Mixed synthesis: `k` full canonical value cells from stream_mixed,
carried as the exact consumed slices. -/
def synthMixedA (k : Nat) (mix : Bytes) (mp : Nat) (acc : List Bytes) :
    Option (List Bytes × Nat) :=
  match k with
  | 0 => some (acc.reverse, mp)
  | k' + 1 =>
    match rdValue mix mp with
    | none => none
    | some (_, p') =>
      synthMixedA k' mix p' ((mix.drop mp).take (p' - mp) :: acc)

/-- One cluster's positions: consume one mode per position, then
synthesize `cnt` cell byte strings per position from the mode's
carrier. Returns the per-position cell lists and the four carrier
cursors. -/
def synthPosA (cnt npos : Nat) (modes hl hn : List Nat)
    (lit : Bytes) (lp : Nat) (mix : Bytes) (mp : Nat)
    (acc : List (List Bytes)) :
    Option (List (List Bytes) × List Nat × List Nat × List Nat ×
            Nat × Nat) :=
  match npos with
  | 0 => some (acc.reverse, modes, hl, hn, lp, mp)
  | np' + 1 =>
    match modes with
    | [] => none
    | m :: modes' =>
      if m = 0 then
        if hl.length < cnt then none
        else
          synthPosA cnt np' modes' (hl.drop cnt) hn lit lp mix mp
            ((hl.take cnt).map encCborUint :: acc)
      else if m = 1 then
        if hn.length < cnt then none
        else
          synthPosA cnt np' modes' hl (hn.drop cnt) lit lp mix mp
            ((hn.take cnt).map encNatCell :: acc)
      else if m = 2 then
        match synthMixedA cnt mix mp [] with
        | none => none
        | some (cells, mp') =>
          synthPosA cnt np' modes' hl hn lit lp mix mp' (cells :: acc)
      else if 16 ≤ m ∧ m ≤ 271 then
        if m = 18 ∨ m = 31 then none
        else
          match synthSameA (m - 16) cnt lit lp [] with
          | none => none
          | some (cells, lp') =>
            synthPosA cnt np' modes' hl hn lit lp' mix mp (cells :: acc)
      else none

/-- Row assembly plus re-parse through the format-1 validators: the
synthesized payload rides the same grammar path as a format-1 row. -/
def mkRowsA (funa : Bool) (r : ElemRef) (symCell : Bytes)
    (rows : List (List Bytes)) (accO : List GOp) (accK : List Bytes) :
    Option (List GOp × List Bytes) :=
  match rows with
  | [] => some (accO.reverse, accK.reverse)
  | cells :: rest =>
    if funa then
      if cells = [] then none
      else
        let arow := encArrHead (cells.length - 1) ++
                    ((cells.take (cells.length - 1)).flatten)
        let vrow := cells.getLastD []
        match rdArgsRow arow with
        | none => none
        | some args =>
          match rdValueRowExact vrow with
          | none => none
          | some v =>
            mkRowsA funa r symCell rest
              (.funa r args v :: accO)
              ((symCell ++ arow ++ vrow) :: accK)
    else
      let arow := encArrHead cells.length ++ cells.flatten
      match rdArgsRow arow with
      | none => none
      | some args =>
        mkRowsA funa r symCell rest
          (.rela r args :: accO) ((symCell ++ arow) :: accK)

/-- The cluster walk: named refusals (empty cluster, funa without a
value slot, cluster split, unresolved symbol), then synthesis and row
assembly. Returns the rela and funa blocks with their order keys plus
the four carrier cursors for the trailing checks. -/
def expandClustersA (symbols : List Bytes)
    (syms nposs cnts : List Nat) (cIdx kb : Nat)
    (prevKey : Option (Bool × Nat × Nat))
    (modes hl hn : List Nat) (lit : Bytes) (lp : Nat)
    (mix : Bytes) (mp : Nat)
    (accR : List GOp) (accRK : List Bytes)
    (accF : List GOp) (accFK : List Bytes) :
    Option (List GOp × List Bytes × List GOp × List Bytes ×
            List Nat × List Nat × Nat × Nat) :=
  match syms with
  | [] =>
    if nposs = [] ∧ cnts = [] ∧ modes = []
    then some (accR.reverse, accRK.reverse, accF.reverse, accFK.reverse,
               hl, hn, lp, mp)
    else none
  | sym :: syms' =>
    match nposs, cnts with
    | npos :: nposs', cnt :: cnts' =>
      let funa := decide (kb ≤ cIdx)
      if cnt = 0 then none
      else if funa ∧ npos = 0 then none
      else if prevKey = some (funa, sym, npos) then none
      else
        (match symResolve symbols sym with
         | none => none
         | some symCell =>
           if isTextMajor symCell then none
           else
             match oneRefExact symCell with
             | none => none
             | some r =>
               match synthPosA cnt npos modes hl hn lit lp mix mp [] with
               | none => none
               | some (posCells, modes', hl', hn', lp', mp') =>
                 match mkRowsA funa r symCell (txpose cnt posCells) [] [] with
                 | none => none
                 | some (ops1, keys1) =>
                   if funa then
                     expandClustersA symbols syms' nposs' cnts'
                       (cIdx + 1) kb (some (funa, sym, npos))
                       modes' hl' hn' lit lp' mix mp'
                       accR accRK
                       (ops1.reverse ++ accF) (keys1.reverse ++ accFK)
                   else
                     expandClustersA symbols syms' nposs' cnts'
                       (cIdx + 1) kb (some (funa, sym, npos))
                       modes' hl' hn' lit lp' mix mp'
                       (ops1.reverse ++ accR) (keys1.reverse ++ accRK)
                       accF accFK)
    | _, _ => none

/-- The cluster walk, from the start state. -/
def expandClusters (symbols : List Bytes)
    (syms nposs cnts : List Nat) (kb : Nat)
    (modes hl hn : List Nat) (lit mix : Bytes) :
    Option (List GOp × List Bytes × List GOp × List Bytes ×
            List Nat × List Nat × Nat × Nat) :=
  expandClustersA symbols syms nposs cnts 0 kb none
    modes hl hn lit 0 mix 0 [] [] [] []

/-! ## The format-2 body -/

/-- The format-2 body: parse strictly with named refusals, then the
channel-wise re-encode fixed-point gate (the frame-level
non-canonicality refusal). -/
def rdBody2 (fr : Bytes) : BRes :=
  match rdFrameChans fr with
  | none => .err .unreadable "frame_layout" 0
  | some chans =>
  let ch := fun i => chans.getD i []
  if ch 0 ≠ [] then
    .err .unreadable "interleave_not_empty" (ch 0).length
  else
  -- symbols: three framed integer columns, exact fit
  match rdHexBytes (ch 1) 0 with
  | none => .err .unreadable "symbols_channel" 0
  | some (locSeg, sp1) =>
  match rdHexBytes (ch 1) sp1 with
  | none => .err .unreadable "symbols_channel" 1
  | some (depSeg, sp2) =>
  match rdHexBytes (ch 1) sp2 with
  | none => .err .unreadable "symbols_channel" 2
  | some (ctrSeg, sp3) =>
  if sp3 ≠ (ch 1).length then
    .err .unreadable "symbols_channel_trailing" ((ch 1).length - sp3)
  else
  match readDeltaCol locSeg with
  | none => .err .unreadable "symbols_local_column" 0
  | some locs =>
  match readU64Col depSeg with
  | none => .err .unreadable "symbols_dep_column" 0
  | some deps =>
  match readDeltaCol ctrSeg with
  | none => .err .unreadable "symbols_counter_column" 0
  | some ctrs =>
  if deps.length ≠ ctrs.length then
    .err .unreadable "symbols_table_mismatch" deps.length
  else if locs.any (fun v => 4294967295 < v) then
    .err .unreadable "symbols_local_domain" 0
  else if deps.any (fun v => MAX_DEP_INDEX < v) then
    .err .unreadable "symbols_dep_domain" 0
  else if ctrs.any (fun v => 4294967295 < v) then
    .err .unreadable "symbols_counter_domain" 0
  else if MAX_BODY_OPS < locs.length + deps.length then
    .err .unreadable "symbols_count_overflow" (locs.length + deps.length)
  else
  let symbols := locs.map (fun n => encElemRef (.loc n)) ++
                 (deps.zip ctrs).map (fun p => encElemRef (.ext p.1 p.2))
  if !strictAsc symbols then .err .unreadable "symbols_not_canonical" 0
  else
  match readU64Col (ch 2) with
  | none => .err .unreadable "elta_sort_column" 0
  | some eltaIdx =>
  -- tmpl: kind boundary plus four framed columns, exact fit
  match rdUleb (ch 3) 0 with
  | none => .err .unreadable "tmpl_kind_boundary" 0
  | some (kb, tq0) =>
  match rdHexBytes (ch 3) tq0 with
  | none => .err .unreadable "tmpl_channel" 0
  | some (symSeg, tq1) =>
  match rdHexBytes (ch 3) tq1 with
  | none => .err .unreadable "tmpl_channel" 1
  | some (nposSeg, tq2) =>
  match rdHexBytes (ch 3) tq2 with
  | none => .err .unreadable "tmpl_channel" 2
  | some (cntSeg, tq3) =>
  match rdHexBytes (ch 3) tq3 with
  | none => .err .unreadable "tmpl_channel" 3
  | some (modeSeg, tq4) =>
  if tq4 ≠ (ch 3).length then
    .err .unreadable "tmpl_channel_trailing" ((ch 3).length - tq4)
  else
  match readDeltaCol symSeg with
  | none => .err .unreadable "tmpl_sym_column" 0
  | some tmplSyms =>
  match readU64Col nposSeg with
  | none => .err .unreadable "tmpl_npos_column" 0
  | some tmplNpos =>
  match readU64Col cntSeg with
  | none => .err .unreadable "tmpl_count_column" 0
  | some tmplCnts =>
  match readU64Col modeSeg with
  | none => .err .unreadable "tmpl_mode_column" 0
  | some tmplModes =>
  if tmplNpos.length ≠ tmplSyms.length ∨ tmplCnts.length ≠ tmplSyms.length
  then .err .unreadable "tmpl_table_mismatch" tmplSyms.length
  else if tmplSyms.length < kb then
    .err .unreadable "tmpl_kind_boundary_over" kb
  else if natSum tmplNpos ≠ tmplModes.length then
    .err .unreadable "tmpl_mode_length" tmplModes.length
  else
  match readBytesCol (ch 8) with
  | none => .err .unreadable "eltd_target_column" 0
  | some eltdRows =>
  match readBytesCol (ch 9) with
  | none => .err .unreadable "seg_other_column" 0
  | some otherRows =>
  if MAX_BODY_OPS < eltaIdx.length + eltdRows.length + otherRows.length +
                   natSum tmplCnts then
    .err .unreadable "op_count_overflow"
      (eltaIdx.length + eltdRows.length + otherRows.length +
       natSum tmplCnts)
  else
  match readDeltaCol (ch 4) with
  | none => .err .unreadable "holes_local_column" 0
  | some holesLocal =>
  if holesLocal.any (fun v => 4294967295 < v) then
    .err .unreadable "template_local_domain" 0
  else
  match readU64Col (ch 5) with
  | none => .err .unreadable "holes_nat_column" 0
  | some holesNat =>
  match decEltas symbols eltaIdx with
  | none => .err .unreadable "elta_rows" 0
  | some (eltaSorts, eltaCells) =>
  match expandClusters symbols tmplSyms tmplNpos tmplCnts kb
          tmplModes holesLocal holesNat (ch 6) (ch 7) with
  | none => .err .unreadable "template_rows" 0
  | some (relaOps, relaKeys, funaOps, funaKeys, hl', hn', lp', mp') =>
  if hl' ≠ [] then
    .err .unreadable "carrier_trailing_local" hl'.length
  else if hn' ≠ [] then
    .err .unreadable "carrier_trailing_nat" hn'.length
  else if lp' ≠ (ch 6).length then
    .err .unreadable "carrier_trailing_lit" ((ch 6).length - lp')
  else if mp' ≠ (ch 7).length then
    .err .unreadable "carrier_trailing_mixed" ((ch 7).length - mp')
  else
  match decEltds eltdRows with
  | none => .err .unreadable "eltd_rows" 0
  | some (eltdOps, eltdKeys) =>
  match decResiduals otherRows with
  | none => .err .unreadable "residual_rows" 0
  | some otherOps =>
  if !allUsed symbols.length (eltaIdx ++ tmplSyms) then
    .err .unreadable "symbol_orphan" 0
  else if !sortedLexLe relaKeys then .err .unreadable "rela_order" 0
  else if !sortedLexLe funaKeys then .err .unreadable "funa_order" 0
  else if !sortedLexLe eltdKeys then .err .unreadable "eltd_order" 0
  else
  match esEltaOrder eltaSorts eltaCells with
  | none => .err .unreadable "elta_es_order" 0
  | some order =>
  if !isIdentityPerm order then .err .unreadable "elta_es_order" 0
  else
  let ops := eltaSorts.map GOp.elta ++ relaOps ++ funaOps ++
             eltdOps ++ otherOps
  if MAX_BODY_OPS < ops.length then
    .err .unreadable "op_count_overflow" ops.length
  else if (ch 10).length % 6 ≠ 0 then
    .err .unreadable "zone_runs_extent" (ch 10).length
  else
  match rdZoneRecs (ch 10) ((ch 10).length / 6) 0 with
  | none => .err .unreadable "zone_runs_records" 0
  | some runs =>
  if !zoneLawsOk runs (tsCellCount ops) then
    .err .unreadable "zone_runs_laws" runs.length
  else if chans ≠ encTemplateChans ops runs then
    .err .unreadable "frame_non_canonical" 0
  else
    .ok { ops := ops, zoneRuns := runs }

/-! ## The body dispatcher -/

/-- The commit body: u16le format number, then the frame.  Format 0 is
the legacy migration lane (refused `unsupported`).  **Registry
(measured against the production wire)**: format 1 has been
the TEMPLATE frame on the production wire since its first byte —
geolog-envelope's `BODY_FORMAT_HEXANE_TEMPLATES_V1 = 1`, "the only
format, and the default"; no other body grammar ever shipped there,
and production's decode refuses every other byte.  Format 2 is the
same template grammar under the WORKSHOP wire's registry (the
workshop engine's `BODY_FORMAT_TEMPLATE_COLUMNS_V1 = 2`, its default
encode) — the numbering the landed receipt fixtures were minted
under — kept as an accepted alias.  Note the asymmetry: this reader
therefore accepts fmt-2 bytes production would refuse; the
dual-accept was a deliberate decision, and narrowing it is
a refusal-behavior change on a landed acceptor, not a tidy-up.  The
reference numbering's former format 1 — the workshop's hexane-columns
layout, which never shipped on the production wire — has been
deleted from this reader (module doc: History). -/
def rdBody (bb : Bytes) : BRes :=
  match rdLeAt bb 0 2 with
  | none => .err .unreadable "body_prefix_truncated" bb.length
  | some fmt =>
  if fmt = 0 then .err .unsupported "body_format_0_legacy_lane" 0
  else if fmt = 1 ∨ fmt = 2 then rdBody2 (bb.drop 2)
  else .err .unsupported "body_format_unknown" fmt

end Read
end Geolog
end PPLC
