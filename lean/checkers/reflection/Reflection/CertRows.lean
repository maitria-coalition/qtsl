import Qtsl.Wire
import Reflection.Vocab

/-!
# Certificate reconstruction from object rows

A sealed proof-artifact commit carries one certificate as object rows:
element declarations against the pinned theory sorts, constructor and
field function rows, and relation rows. This module scans those rows
into lookup tables and reconstructs the wire-model certificate value
(`Wire.WCert`) that the established elevation-and-checking pipeline
consumes.

The scan is total and fail-closed: every departure from the expected
row discipline refuses with a class (`unreadable` for content that is
not a well-formed certificate row set, `unsupported` for well-formed
rows outside the accepted first-order fragment), a stable tag, and a
witness number.

No stage of this module carries — or needs — a correctness theorem for
soundness: the reconstructed certificate is elevated and checked by
the audited pipeline downstream, and the acceptance theorem quantifies
over whatever was actually reconstructed, so a decode defect can lose
completeness, never soundness.
-/

namespace PPLC
namespace Geolog

open Wire (WSym WComplex WSimplexR WExtSetR WFormula WJudgment WProof
  WNodeK WSide WCert WHeader)

/-- Little-endian byte-list value. -/
def leN : Bytes → Nat
  | [] => 0
  | b :: bs => b + 256 * leN bs

/-- Minimal ULEB128 read (64-bit bound, canonical: no redundant final
zero group). Returns the value and the next position. -/
def rdUlebLoop (bs : Bytes) (pos shift acc : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    match bs[pos]? with
    | none => none
    | some b =>
      if b < 128 then
        if b == 0 && 0 < shift then none
        else
          let v := acc + b * 2 ^ shift
          if v < 18446744073709551616 then some (v, pos + 1) else none
      else rdUlebLoop bs (pos + 1) (shift + 7) (acc + (b - 128) * 2 ^ shift) fuel

def rdUleb (bs : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  rdUlebLoop bs pos 0 0 10

/-- Rational literal payload shape: minimal-uvarint numerator length,
numerator limbs, terminal denominator limbs (both nonempty). -/
def qShape (p : Bytes) : Option (Bytes × Bytes) :=
  match rdUleb p 0 with
  | none => none
  | some (nlen, pos) =>
    if p.length < pos + nlen then none
    else
      let num := (p.drop pos).take nlen
      let den := p.drop (pos + nlen)
      if nlen == 0 || den.isEmpty then none else some (num, den)

/-- Nat value of a value cell (`Nat` literal, code 2). -/
def natOfVal : GValue → Option Nat
  | .lit code p => if code == 2 then some (leN p) else none
  | _ => none

/-- Rational value of a value cell (`Q` literal, code 0; two's
complement little-endian numerator, unsigned denominator). -/
def qOfVal : GValue → Option Rat
  | .lit code p =>
    if code != 0 then none
    else
      match qShape p with
      | none => none
      | some (nb, db) =>
        let v := leN nb
        let m := 256 ^ nb.length
        let neg := ¬ (2 * v < m)
        let mag := if neg then m - v else v
        let d := leN db
        if d == 0 then none
        else some (if neg then -(mkRat mag d) else mkRat mag d)
  | _ => none

/-- Local-element value of a value cell. -/
def elemOfVal : GValue → Option Nat
  | .ref (.loc n) => some n
  | _ => none

/-- The scanned row tables: element sorts in declaration order,
constructor rows keyed by constructed element, field rows keyed by
(field, subject), rule rows keyed by proof element, and the keyed
record/relation rows in row order. -/
structure RowTbls where
  tsorts : List Vocab
  tctor  : List (Nat × (Vocab × List GValue))
  tfld   : List ((Vocab × Nat) × GValue)
  trp    : List (Nat × (Nat × Nat))
  trec   : List (Vocab × List GValue × Option GValue)

/-- Refusal payload: class, stable tag, witness. -/
abbrev CFail := RClass × String × Nat

abbrev CRes (α : Type) := Except CFail α

private def cerr {α} (c : RClass) (t : String) (w : Nat) : CRes α :=
  .error (c, t, w)

/-- Scan state: reversed sorts, ctor/field/rule tables, reversed
record rows, next op index. -/
private structure ScanSt where
  sorts : List Vocab := []
  ctor  : List (Nat × (Vocab × List GValue)) := []
  fld   : List ((Vocab × Nat) × GValue) := []
  rp    : List (Nat × (Nat × Nat)) := []
  recs  : List (Vocab × List GValue × Option GValue) := []
  i     : Nat := 0

private def scanOp (pins : List ((List Nat × Nat) × Vocab)) (deps : List Bytes)
    (st : ScanSt) : GOp → CRes ScanSt
  | .elta r =>
    match r with
    | .loc _ => cerr .unreadable "local_schema_sort_ref" st.i
    | .ext _ _ =>
      match resolveRef pins deps r with
      | none => cerr .unsupported "schema_sort_unpinned" st.i
      | some v =>
        if v.isSort then pure { st with sorts := v :: st.sorts, i := st.i + 1 }
        else cerr .unreadable "sort_position_not_a_sort" st.i
  | .rela r args =>
    match resolveRef pins deps r with
    | none => cerr .unsupported "schema_rel_unpinned" st.i
    | some v =>
      if v.isRel then
        pure { st with recs := (v, args, none) :: st.recs, i := st.i + 1 }
      else cerr .unsupported "rel_outside_fragment" st.i
  | .funa r args value =>
    match resolveRef pins deps r with
    | none => cerr .unsupported "schema_fun_unpinned" st.i
    | some v =>
      if v.isCtor then
        match elemOfVal value with
        | none => cerr .unreadable "ctor_value_not_local_elem" st.i
        | some e =>
          if (st.ctor.lookup e).isNone then
            pure { st with ctor := (e, (v, args)) :: st.ctor, i := st.i + 1 }
          else cerr .unreadable "ambiguous_constructor" st.i
      else if v.isField then
        match args with
        | [av] =>
          match elemOfVal av with
          | none => cerr .unreadable "field_subject_not_elem" st.i
          | some s =>
            match v with
            | .fRuleProof rt =>
              match elemOfVal value with
              | none => cerr .unreadable "rule_proof_not_elem" st.i
              | some p =>
                if (st.rp.lookup p).isNone then
                  pure { st with rp := (p, (s, rt)) :: st.rp, i := st.i + 1 }
                else cerr .unreadable "proof_claimed_twice" st.i
            | _ =>
              if (st.fld.lookup (v, s)).isNone then
                pure { st with fld := ((v, s), value) :: st.fld, i := st.i + 1 }
              else cerr .unreadable "duplicate_fun_row" st.i
        | _ => cerr .unreadable "field_arity" st.i
      else if v.isRec then
        pure { st with recs := (v, args, some value) :: st.recs, i := st.i + 1 }
      else cerr .unsupported "fun_outside_fragment" st.i
  | .eltd _ => cerr .unsupported "eltd_in_cert_body" st.i
  | .cert _ _ _ => cerr .unsupported "certblob_in_cert_body" st.i
  | .unknown _ _ => cerr .unsupported "op_kind_in_cert_body" st.i

private def scanOpsA (pins : List ((List Nat × Nat) × Vocab))
    (deps : List Bytes) (st : ScanSt) : List GOp → CRes RowTbls
  | [] => pure ⟨st.sorts.reverse, st.ctor, st.fld, st.rp, st.recs.reverse⟩
  | op :: rest => do scanOpsA pins deps (← scanOp pins deps st op) rest

/-- Scan a sealed certificate commit's ops into row tables. -/
def scanOps (pins : List ((List Nat × Nat) × Vocab)) (deps : List Bytes)
    (ops : List GOp) : CRes RowTbls :=
  scanOpsA pins deps {} ops

/-! ## Table lookups -/

def sortAt (tb : RowTbls) (e : Nat) : Option Vocab := tb.tsorts[e]?

def ctorAt (tb : RowTbls) (e : Nat) : Option (Vocab × List GValue) :=
  tb.tctor.lookup e

def fldAt (tb : RowTbls) (v : Vocab) (e : Nat) : Option GValue :=
  tb.tfld.lookup (v, e)

def fldNat (tb : RowTbls) (v : Vocab) (e : Nat) : Option Nat :=
  (fldAt tb v e).bind natOfVal

def fldElem (tb : RowTbls) (v : Vocab) (e : Nat) : Option Nat :=
  (fldAt tb v e).bind elemOfVal

/-- All record/relation rows of one vocabulary entry, in row order. -/
def rowsOfV (tb : RowTbls) (v : Vocab) : List (List GValue × Option GValue) :=
  (tb.trec.filter (fun r => r.1 == v)).map (fun r => (r.2.1, r.2.2))

/-! ## Indexed views

Pure reindexings of the scanned tables for constant-time access
during reconstruction. Element ids of well-formed rows are bounded by
the sort-declaration count; entries outside that range ride overflow
association lists, so every lookup below returns exactly what the
direct list lookup returns (keys are unique by the scan's own
duplicate refusals), and the accepted set is unchanged — the
cross-implementation differential is the check.
-/

structure RowIdx where
  sortsArr : Array Vocab
  ctorArr  : Array (Option (Vocab × List GValue))
  ctorOvf  : List (Nat × (Vocab × List GValue))
  fldArr   : Array (List (Vocab × GValue))
  fldOvf   : List ((Vocab × Nat) × GValue)
  rpArr    : Array (Option (Nat × Nat))
  rpOvf    : List (Nat × (Nat × Nat))
  recSimplexContains : List (List GValue × Option GValue)
  recExtSetContains  : List (List GValue × Option GValue)
  recCellSimpHasV    : List (List GValue × Option GValue)
  recCellExtHasV     : List (List GValue × Option GValue)
  recSimpCCoord      : List (List GValue × Option GValue)
  recCplxSimpAt      : List (List GValue × Option GValue)
  recPromIface       : List (List GValue × Option GValue)
  recSyzComp         : List (List GValue × Option GValue)

def RowIdx.build (tb : RowTbls) : RowIdx := Id.run do
  let n := tb.tsorts.length
  let mut ctorArr : Array (Option (Vocab × List GValue)) :=
    Array.replicate n none
  let mut ctorOvf : List (Nat × (Vocab × List GValue)) := []
  for r in tb.tctor do
    if h : r.1 < ctorArr.size then
      ctorArr := ctorArr.set r.1 (some r.2)
    else
      ctorOvf := r :: ctorOvf
  let mut fldArr : Array (List (Vocab × GValue)) := Array.replicate n []
  let mut fldOvf : List ((Vocab × Nat) × GValue) := []
  for r in tb.tfld do
    let subj := r.1.2
    if h : subj < fldArr.size then
      fldArr := fldArr.set subj ((r.1.1, r.2) :: fldArr[subj])
    else
      fldOvf := r :: fldOvf
  let mut rpArr : Array (Option (Nat × Nat)) := Array.replicate n none
  let mut rpOvf : List (Nat × (Nat × Nat)) := []
  for r in tb.trp do
    if h : r.1 < rpArr.size then
      rpArr := rpArr.set r.1 (some r.2)
    else
      rpOvf := r :: rpOvf
  return { sortsArr := tb.tsorts.toArray,
           ctorArr, ctorOvf, fldArr, fldOvf, rpArr, rpOvf,
           recSimplexContains := rowsOfV tb .rSimplexContains,
           recExtSetContains := rowsOfV tb .rExtSetContains,
           recCellSimpHasV := rowsOfV tb .rCellSimpHasV,
           recCellExtHasV := rowsOfV tb .rCellExtHasV,
           recSimpCCoord := rowsOfV tb .fSimpCCoord,
           recCplxSimpAt := rowsOfV tb .fCplxSimpAt,
           recPromIface := rowsOfV tb .rPromIface,
           recSyzComp := rowsOfV tb .rSyzComp }

def RowIdx.sortAt (ix : RowIdx) (e : Nat) : Option Vocab := ix.sortsArr[e]?

def RowIdx.ctorAt (ix : RowIdx) (e : Nat) : Option (Vocab × List GValue) :=
  match ix.ctorArr[e]? with
  | some o => o
  | none => ix.ctorOvf.lookup e

def RowIdx.fldAt (ix : RowIdx) (v : Vocab) (e : Nat) : Option GValue :=
  match ix.fldArr[e]? with
  | some l => l.lookup v
  | none => ix.fldOvf.lookup (v, e)

def RowIdx.fldNat (ix : RowIdx) (v : Vocab) (e : Nat) : Option Nat :=
  (ix.fldAt v e).bind natOfVal

def RowIdx.fldElem (ix : RowIdx) (v : Vocab) (e : Nat) : Option Nat :=
  (ix.fldAt v e).bind elemOfVal

def RowIdx.rpAt (ix : RowIdx) (p : Nat) : Option (Nat × Nat) :=
  match ix.rpArr[p]? with
  | some o => o
  | none => ix.rpOvf.lookup p

def RowIdx.rowsOf (ix : RowIdx) (v : Vocab) :
    List (List GValue × Option GValue) :=
  match v with
  | .rSimplexContains => ix.recSimplexContains
  | .rExtSetContains => ix.recExtSetContains
  | .rCellSimpHasV => ix.recCellSimpHasV
  | .rCellExtHasV => ix.recCellExtHasV
  | .fSimpCCoord => ix.recSimpCCoord
  | .fCplxSimpAt => ix.recCplxSimpAt
  | .rPromIface => ix.recPromIface
  | .rSyzComp => ix.recSyzComp
  | _ => []

def RowIdx.nSorts (ix : RowIdx) : Nat := ix.sortsArr.size

private def idxOfA [BEq α] (x : α) : List α → Nat → Option Nat
  | [], _ => none
  | h :: t, i => if h == x then some i else idxOfA x t (i + 1)

def idxOf [BEq α] (x : α) (l : List α) : Option Nat := idxOfA x l 0

private def noDup (l : List Nat) : Bool :=
  match l with
  | [] => true
  | h :: t => !(t.contains h) && noDup t

/-- (index value, element) pairs of an index-field family. -/
def idxPairs (tb : RowIdx) (v : Vocab) : List (Nat × Nat) :=
  ((List.range tb.nSorts).map (fun e =>
    match tb.fldNat v e with
    | none => ([] : List (Nat × Nat))
    | some k => [(k, e)])).flatten

/-- A dense index family: exactly `n` rows, indices exactly `0..n-1`;
yields elements in index order. -/
def denseIdx (tb : RowIdx) (v : Vocab) (n : Nat) : Option (List Nat) :=
  let ps := idxPairs tb v
  if ps.length == n && noDup (ps.map (·.1)) && ps.all (fun p => p.1 < n) then
    some ((List.range n).map (fun k => ((ps.lookup k).getD 0)))
  else none

private def recPairsA (anchorFirst : Bool)
    (rows : List (List GValue × Option GValue))
    (anchor : Nat) (acc : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  match rows with
  | [] => some acc
  | (args, value) :: rest =>
    match args with
    | [x, y] =>
      let (kv, av) := if anchorFirst then (y, x) else (x, y)
      match natOfVal kv with
      | none => none
      | some k =>
        match elemOfVal av with
        | none => none
        | some a =>
          if a != anchor then recPairsA anchorFirst rest anchor acc
          else
            match value with
            | none => none
            | some ve =>
              match elemOfVal ve with
              | none => none
              | some e => recPairsA anchorFirst rest anchor ((k, e) :: acc)
    | _ => none

/-- A dense keyed record family under one anchor element. Argument
order per the declaring theory: the complex→simplex family is
(anchor, key); the per-rule component and interface families are
(key, anchor). -/
def denseRecFor (tb : RowIdx) (v : Vocab) (anchor n : Nat) :
    Option (List Nat) :=
  match recPairsA (v == .fCplxSimpAt) (tb.rowsOf v) anchor [] with
  | none => none
  | some ps =>
    if ps.length == n && noDup (ps.map (·.1)) && ps.all (fun p => p.1 < n) then
      some ((List.range n).map (fun k => ((ps.lookup k).getD 0)))
    else none

private def maskVsA (rows : List (List GValue × Option GValue))
    (subj : Nat) (acc : List Nat) : Option (List Nat) :=
  match rows with
  | [] => some acc
  | (args, _) :: rest =>
    match args with
    | [sv, vv] =>
      match elemOfVal sv with
      | none => none
      | some s =>
        if s != subj then maskVsA rest subj acc
        else
          match natOfVal vv with
          | none => none
          | some vtx => maskVsA rest subj (vtx :: acc)
    | _ => none

/-- Vertex membership mask of one subject element. -/
def maskOf (tb : RowIdx) (v : Vocab) (subj nv : Nat) : Option (List Bool) :=
  match maskVsA (tb.rowsOf v) subj [] with
  | none => none
  | some vs =>
    if vs.all (fun x => x < nv) then
      some ((List.range nv).map (fun x => vs.contains x))
    else none

private def cellVsA (rows : List (List GValue × Option GValue))
    (cxe : Nat) (acc : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  match rows with
  | [] => some acc
  | (args, _) :: rest =>
    match args with
    | [cv, av, vv] =>
      match elemOfVal av with
      | none => none
      | some a =>
        if a != cxe then cellVsA rest cxe acc
        else
          match natOfVal cv with
          | none => none
          | some cell =>
            match natOfVal vv with
            | none => none
            | some vtx => cellVsA rest cxe ((cell, vtx) :: acc)
    | _ => none

/-- Per-cell vertex masks of one complex. -/
def cellMasks (tb : RowIdx) (v : Vocab) (cxe ncell nv : Nat) :
    Option (List (List Bool)) :=
  match cellVsA (tb.rowsOf v) cxe [] with
  | none => none
  | some ps =>
    if ps.all (fun p => p.1 < ncell && p.2 < nv) then
      some ((List.range ncell).map (fun c =>
        (List.range nv).map (fun x => ps.contains (c, x))))
    else none

private def coordAlA (rows : List (List GValue × Option GValue))
    (cxe nv amb : Nat) (acc : List ((Nat × Nat) × Rat)) :
    Option (List ((Nat × Nat) × Rat)) :=
  match rows with
  | [] => some acc
  | (args, value) :: rest =>
    match args with
    | [av, jv, vv] =>
      match elemOfVal av with
      | none => none
      | some a =>
        if a != cxe then coordAlA rest cxe nv amb acc
        else
          match natOfVal jv with
          | none => none
          | some j =>
            match natOfVal vv with
            | none => none
            | some vtx =>
              if ¬ (vtx < nv ∧ j < amb) then none
              else if (acc.lookup (vtx, j)).isSome then none
              else
                match value with
                | none => none
                | some qv =>
                  match qOfVal qv with
                  | none => none
                  | some q => coordAlA rest cxe nv amb (((vtx, j), q) :: acc)
    | _ => none

/-- Row-major coordinate table of one complex. -/
def coordsFor (tb : RowIdx) (cxe nv amb : Nat) : Option (List Rat) :=
  match coordAlA (tb.rowsOf .fSimpCCoord) cxe nv amb [] with
  | none => none
  | some al =>
    if al.length == nv * amb then
      some (((List.range nv).map (fun vtx =>
        (List.range amb).map (fun j => ((al.lookup (vtx, j)).getD 0)))).flatten)
    else none

/-! ## Ground-sort values -/

def gConstCode (tb : RowIdx) (e : Nat) : Option (Vocab × Nat) :=
  match tb.ctorAt e with
  | some (.fKindC n, []) => some (.fKindC n, n)
  | some (.fSignC n, []) => some (.fSignC n, n)
  | some (.fExtC n, []) => some (.fExtC n, n)
  | _ => none

def kindOfCode : Nat → Option Kind
  | 0 => some .bool | 1 => some .int | 2 => some .rat
  | 3 => some .f16 | 4 => some .bf16 | 5 => some .f32 | 6 => some .f64
  | _ => none

def signOfCode : Nat → Option Sign
  | 0 => some .nn | 1 => some .signed | _ => none

def extOfCode : Nat → Option Ext
  | 0 => some .fin | 1 => some .ext | _ => none

def bowtieOfCode : Nat → Option BowTie
  | 0 => some .lt | 1 => some .le | 2 => some .eq
  | 3 => some .ge | 4 => some .gt | 5 => some .ne
  | _ => none

def gShapeF (tb : RowIdx) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, e =>
    if tb.sortAt e != some .sShape then none
    else
      match tb.ctorAt e with
      | some (.fShapeEmpty, args) => if args.isEmpty then some [] else none
      | some (.fShapeCons, [h, t]) =>
        match natOfVal h with
        | none => none
        | some hv =>
          match elemOfVal t with
          | none => none
          | some te =>
            match gShapeF tb fuel te with
            | none => none
            | some rest => some (hv :: rest)
      | _ => none

def gDtypeV (tb : RowIdx) (e : Nat) : Option Dtype :=
  if tb.sortAt e != some .sDtype then none
  else
    match tb.ctorAt e with
    | some (.fMkDtype, [ea, ka, sa]) =>
      match elemOfVal ea, elemOfVal ka, elemOfVal sa with
      | some ee, some ke, some se =>
        match gConstCode tb ee, gConstCode tb ke, gConstCode tb se with
        | some (.fExtC en, _), some (.fKindC kn, _), some (.fSignC sn, _) =>
          match kindOfCode kn, signOfCode sn, extOfCode en with
          | some kd, some sg, some et => some ⟨kd, sg, et⟩
          | _, _, _ => none
        | _, _, _ => none
      | _, _, _ => none
    | _ => none

def gTTypeV (tb : RowIdx) (e : Nat) : Option (Dtype × List Nat) :=
  if tb.sortAt e != some .sTensorType then none
  else
    match tb.ctorAt e with
    | some (.fMkTensorType, [dt, sh]) =>
      match elemOfVal dt, elemOfVal sh with
      | some de, some she =>
        match gDtypeV tb de, gShapeF tb (tb.nSorts + 1) she with
        | some d, some s => some (d, s)
        | _, _ => none
      | _, _ => none
    | _ => none

/-! ## Wires and complexes -/

private def gWiresA (tb : RowIdx) : List Nat → Nat → List (Nat × Nat) →
    List WSym → Option (List (Nat × Nat) × List WSym)
  | [], _, accW, accT => some (accW, accT.reverse)
  | e :: rest, i, accW, accT =>
    if tb.sortAt e != some .sWire then none
    else
      match tb.fldElem .fWireType e with
      | none => none
      | some te =>
        match gTTypeV tb te with
        | none => none
        | some (d, sh) =>
          gWiresA tb rest (i + 1) ((e, i) :: accW)
            ({ dtype := d, shape := sh, payload := none } :: accT)

/-- The wire table: element→id map plus symbols in id order. -/
def gWires (tb : RowIdx) (nw : Nat) :
    Option (List (Nat × Nat) × List WSym) :=
  match denseIdx tb .fWireIndex nw with
  | none => none
  | some wes => gWiresA tb wes 0 [] []

private def simpMasks (tb : RowIdx) (cxe nv : Nat) :
    List Nat → Option (List (List Bool))
  | [] => some []
  | e :: rest =>
    if tb.sortAt e != some .sSimplex then none
    else if tb.fldElem .fSimplexComplex e != some cxe then none
    else
      match maskOf tb .rSimplexContains e nv with
      | none => none
      | some m =>
        match simpMasks tb cxe nv rest with
        | none => none
        | some ms => some (m :: ms)

private def oe {α} (tag : String) (o : Option α) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error tag

def gComplex1 (tb : RowIdx) (cxe : Nat) : Except String WComplex :=
  if tb.sortAt cxe != some .sSimpC then .error "cx_sort"
  else do
    let nv ← oe "cx_nvert" (tb.fldNat .fSimpCNVert cxe)
    let amb ← oe "cx_ambdim" (tb.fldNat .fSimpCAmbDim cxe)
    if 4294967295 < nv ∨ 4294967295 < amb then .error "cx_range"
    else do
      let coords ← oe "cx_coords" (coordsFor tb cxe nv amb)
      let nsimp ← oe "cx_nsimp" (tb.fldNat .fSimpCNSimp cxe)
      let sxes ← oe "cx_simpat" (denseRecFor tb .fCplxSimpAt cxe nsimp)
      let simps ← oe "cx_simplexmask" (simpMasks tb cxe nv sxes)
      let ncell ← oe "cx_ncells" (tb.fldNat .fSimpCNCells cxe)
      let sm ← oe "cx_cellsimp" (cellMasks tb .rCellSimpHasV cxe ncell nv)
      let em ← oe "cx_cellext" (cellMasks tb .rCellExtHasV cxe ncell nv)
      pure { nVertices := nv, ambDim := amb,
             coords := coords.toArray,
             simplices := (simps.map List.toArray).toArray,
             cells := ((sm.zip em).map
               (fun p => (p.1.toArray, p.2.toArray))).toArray }

private def gComplexesA (tb : RowIdx) : List Nat → List WComplex →
    Except String (List WComplex)
  | [], acc => .ok acc.reverse
  | e :: rest, acc =>
    match gComplex1 tb e with
    | .error t => .error t
    | .ok cx => gComplexesA tb rest (cx :: acc)

/-- The complex pool: elements in index order plus decoded complexes. -/
def gComplexes (tb : RowIdx) (nc : Nat) :
    Except String (List Nat × List WComplex) :=
  match denseIdx tb .fSimpCIndex nc with
  | none => .error "cx_index"
  | some cxE =>
    match gComplexesA tb cxE [] with
    | .error t => .error t
    | .ok cxs => .ok (cxE, cxs)

/-! ## Terms, formulas, proof trees -/

/-- Reconstruction context: tables, wire element→id map, complex
elements in pool order, decoded complexes. -/
structure RowCtx where
  rtb  : RowIdx
  rwid : List (Nat × Nat)
  rcxE : List Nat
  rcxs : List WComplex

def gSimplexV (rc : RowCtx) (e : Nat) : Option WSimplexR :=
  if rc.rtb.sortAt e != some .sSimplex then none
  else do
    let ce ← rc.rtb.fldElem .fSimplexComplex e
    let ci ← idxOf ce rc.rcxE
    let cx ← rc.rcxs[ci]?
    let m ← maskOf rc.rtb .rSimplexContains e cx.nVertices
    pure { complex := ci, mask := m.toArray }

def gExtSetV (rc : RowCtx) (e : Nat) : Option WExtSetR :=
  if rc.rtb.sortAt e != some .sExtSet then none
  else do
    let se ← rc.rtb.fldElem .fExtSetSimplex e
    let sx ← gSimplexV rc se
    let cx ← rc.rcxs[sx.complex]?
    let m ← maskOf rc.rtb .rExtSetContains e cx.nVertices
    pure { simplex := sx, mask := m.toArray }

def gTermF (rc : RowCtx) : Nat → Nat → Option Term
  | 0, _ => none
  | fuel + 1, e =>
    if rc.rtb.sortAt e != some .sTerm then none
    else
      match rc.rtb.ctorAt e with
      | some (.fTHole, args) =>
        if args.isEmpty then some (.var 4294967295) else none
      | some (.fTVar, [wv]) =>
        match elemOfVal wv with
        | none => none
        | some we =>
          match rc.rwid.lookup we with
          | none => none
          | some id => some (.var id)
      | some (.fTConst, [qv]) =>
        match qOfVal qv with
        | none => none
        | some q => some (.const q)
      | some (.fTAdd, [l, r]) =>
        match elemOfVal l, elemOfVal r with
        | some le, some re =>
          match gTermF rc fuel le, gTermF rc fuel re with
          | some ta, some tb => some (.add ta tb)
          | _, _ => none
        | _, _ => none
      | some (.fTMul, [l, r]) =>
        match elemOfVal l, elemOfVal r with
        | some le, some re =>
          match gTermF rc fuel le, gTermF rc fuel re with
          | some ta, some tb => some (.mul ta tb)
          | _, _ => none
        | _, _ => none
      | some (.fTSub, [l, r]) =>
        match elemOfVal l, elemOfVal r with
        | some le, some re =>
          match gTermF rc fuel le, gTermF rc fuel re with
          | some ta, some tb => some (.sub ta tb)
          | _, _ => none
        | _, _ => none
      | some (.fTNeg, [t]) =>
        match elemOfVal t with
        | none => none
        | some te =>
          match gTermF rc fuel te with
          | none => none
          | some tt => some (.neg tt)
      | some (.fTIdx, [iv, t]) =>
        match natOfVal iv with
        | none => none
        | some ix =>
          if 4294967295 < ix then none
          else
            match elemOfVal t with
            | none => none
            | some te =>
              match gTermF rc fuel te with
              | none => none
              | some tt => some (.idx tt ix)
      | _ => none

private def termFuel (rc : RowCtx) : Nat := rc.rtb.nSorts + 1

def gFwireF (rc : RowCtx) : Nat → Nat → Option WFormula
  | 0, _ => none
  | fuel + 1, e =>
    if rc.rtb.sortAt e != some .sFormula then none
    else
      match rc.rtb.ctorAt e with
      | some (.fFTrue, args) => if args.isEmpty then some .tt else none
      | some (.fFFalse, args) => if args.isEmpty then some .ff else none
      | some (.fFSpH, args) => if args.isEmpty then some .sph else none
      | some (.fFAtom b, [l, r]) =>
        match bowtieOfCode b with
        | none => none
        | some bt =>
          match elemOfVal l, elemOfVal r with
          | some le, some re =>
            match gTermF rc (termFuel rc) le, gTermF rc (termFuel rc) re with
            | some tl, some tr => some (.atom bt tl tr)
            | _, _ => none
          | _, _ => none
      | some (.fFInRegion, [sv, xv, tv]) =>
        match elemOfVal sv, elemOfVal xv, elemOfVal tv with
        | some se, some xe, some te =>
          match gTermF rc (termFuel rc) te with
          | none => none
          | some tt =>
            match gSimplexV rc xe with
            | none => none
            | some sx =>
              match gExtSetV rc se with
              | none => none
              | some es => some (.inRegion tt sx es)
        | _, _, _ => none
      | some (.fFAnd, [l, r]) =>
        match elemOfVal l, elemOfVal r with
        | some le, some re =>
          match gFwireF rc fuel le, gFwireF rc fuel re with
          | some fl, some fr => some (.and fl fr)
          | _, _ => none
        | _, _ => none
      | some (.fFOr, [l, r]) =>
        match elemOfVal l, elemOfVal r with
        | some le, some re =>
          match gFwireF rc fuel le, gFwireF rc fuel re with
          | some fl, some fr => some (.or fl fr)
          | _, _ => none
        | _, _ => none
      | _ => none

/-- Judgment of a proof node; the succedent must be sph-free. -/
def gJudg (rc : RowCtx) (e : Nat) : Option WJudgment :=
  if rc.rtb.sortAt e != some .sJudgment then none
  else do
    let pe ← rc.rtb.fldElem .fJudgPre e
    let qe ← rc.rtb.fldElem .fJudgPost e
    let prew ← gFwireF rc (termFuel rc) pe
    let postw ← gFwireF rc (termFuel rc) qe
    if postw.hasSph then none else pure ⟨prew, postw⟩

def gPathF (rc : RowCtx) : Nat → Nat → Option (List WSide)
  | 0, _ => none
  | fuel + 1, e =>
    if rc.rtb.sortAt e != some .sCtxPath then none
    else
      match rc.rtb.ctorAt e with
      | some (.fPathHere, args) => if args.isEmpty then some [] else none
      | some (.fPathL, [iv]) =>
        match elemOfVal iv with
        | none => none
        | some ie =>
          match gPathF rc fuel ie with
          | none => none
          | some ss => some (.left :: ss)
      | some (.fPathR, [iv]) =>
        match elemOfVal iv with
        | none => none
        | some ie =>
          match gPathF rc fuel ie with
          | none => none
          | some ss => some (.right :: ss)
      | _ => none

/-- Interface wire list of a promise node (dense keyed family). -/
def gIface (rc : RowCtx) (re n : Nat) : Option (List Nat) :=
  match denseRecFor rc.rtb .rPromIface re n with
  | none => none
  | some wes =>
    let ids := wes.map (fun e => rc.rwid.lookup e)
    if ids.all (·.isSome) then some (ids.map (·.getD 0)) else none

private def sideOfNat : Nat → Option WSide
  | 0 => some .left
  | 1 => some .right
  | _ => none

/-- Reconstruct one proof node. The fuel argument bounds proof-tree
depth (the element count suffices: every child reference names a
distinct proof element); recursion is structural in the fuel so the
whole reconstruction reduces inside the kernel. -/
def gProofF (rc : RowCtx) : Nat → Nat → Option WProof
  | 0, _ => none
  | fuel + 1, p =>
    if rc.rtb.sortAt p != some .sProof then none
    else do
      let cj ← gJudg rc (← rc.rtb.fldElem .fProofConcludes p)
      let (re, r) ← rc.rtb.rpAt p
      if !v0fragTag r then none
      else
        let fe := fun k => rc.rtb.fldElem (.fRF r k) re
        let fn := fun k => rc.rtb.fldNat (.fRF r k) re
        let gT := fun e => gTermF rc (termFuel rc) e
        let gF := fun e => gFwireF rc (termFuel rc) e
        let kid := gProofF rc fuel
        if r == 0 then pure (.mk cj .ax)
        else if r == 1 then do
          let pr ← fe 0
          let xw ← gF (← fe 1)
          pure (.mk cj (.weaken (← kid pr) xw))
        else if r == 2 then do
          let lp ← fe 0
          let rp ← fe 1
          let cw ← gF (← fe 2)
          pure (.mk cj (.cut cw (← kid lp) (← kid rp)))
        else if r == 3 then do
          let lp ← fe 0
          let rp ← fe 1
          pure (.mk cj (.andI (← kid lp) (← kid rp)))
        else if r == 4 || r == 5 then do
          let pr ← fe 0
          let wh ← fn 1
          if 1 < wh then none
          else do
            let ow ← gF (← fe 2)
            let side ← sideOfNat wh
            let pp ← kid pr
            pure (.mk cj (if r == 4 then .andE side pp ow else .orI side pp ow))
        else if r == 6 then do
          let lp ← fe 0
          let rp ← fe 1
          let stps ← gPathF rc (termFuel rc) (← fe 2)
          if 4294967295 < stps.length then none
          else pure (.mk cj (.orE (← kid lp) (← kid rp) stps))
        else if r == 7 then do
          let ep ← fe 0
          let bp ← fe 1
          let wid ← rc.rwid.lookup (← fe 2)
          let tT ← gT (← fe 3)
          let tU ← gT (← fe 4)
          let bw ← gF (← fe 5)
          pure (.mk cj (.eqElim (← kid ep) (← kid bp) wid tT tU bw))
        else if r == 8 || r == 9 then do
          let pr ← fe 0
          let tt ← gT (← fe 1)
          let sx ← gSimplexV rc (← fe 2)
          let es ← gExtSetV rc (← fe 3)
          let pp ← kid pr
          pure (.mk cj
            (if r == 8 then .convIntro pp tt sx es else .convElim pp tt sx es))
        else if r == 10 then do
          let pr ← fe 0
          let dir ← fn 1
          if 1 < dir then none
          else do
            let tl ← gT (← fe 2)
            let tr ← gT (← fe 3)
            let bb ← fn 4
            if 4 < bb then none
            else do
              let bt ← bowtieOfCode bb
              let side ← sideOfNat dir
              pure (.mk cj (.arithAtom side (← kid pr) tl tr bt))
        else if r == 11 then do
          let pr ← fe 0
          let tx ← gT (← fe 1)
          let sx ← gSimplexV rc (← fe 2)
          let es ← gExtSetV rc (← fe 3)
          let deg ← fn 4
          if 4294967295 < deg then none
          else do
            let poly ← gT (← fe 5)
            let pd ← gF (← fe 6)
            pure (.mk cj (.bernCone (← kid pr) tx sx es deg poly pd))
        else if r == 12 then do
          let tl ← gT (← fe 0)
          let tr ← gT (← fe 1)
          pure (.mk cj (.norm tl tr))
        else if r == 14 then do
          let cc ← gT (← fe 0)
          let co ← gT (← fe 1)
          let dbl ← fn 2
          pure (.mk cj (.farkas cc co dbl))
        else if r == 23 then do
          let tt ← gT (← fe 0)
          pure (.mk cj (.eqRefl tt))
        else if r == 24 then do
          let pr ← fe 0
          let tT ← gT (← fe 1)
          let tU ← gT (← fe 2)
          pure (.mk cj (.eqSym (← kid pr) tT tU))
        else if r == 25 then do
          let sp ← fe 0
          let cp ← fe 1
          let cw ← gF (← fe 2)
          let stps ← gPathF rc (termFuel rc) (← fe 3)
          let ni ← fn 4
          if 4294967295 < ni ∨ 4294967295 < stps.length then none
          else do
            let ifc ← gIface rc re ni
            pure (.mk cj (.promise (← kid sp) (← kid cp) cw stps ifc))
        else if r == 26 then do
          let ncomp ← fn 0
          let comps ← denseRecFor rc.rtb .rSyzComp re ncomp
          let cc ← gT (← fe 1)
          let co ← gT (← fe 2)
          let dbl ← fn 3
          let kids ← comps.mapM (gProofF rc fuel)
          match rc.rtb.fldAt (.fRF 26 4) re with
          | none => pure (.mk cj (.syzygy kids cc co dbl none))
          | some thv => do
            let q ← qOfVal thv
            pure (.mk cj (.syzygy kids cc co dbl (some q)))
        else none

/-! ## The certificate element and the top-level reconstruction -/

/-- Elements declared at sort `Cert`. -/
def certElems (tb : RowIdx) : List Nat :=
  (List.range tb.nSorts).filter (fun e => tb.sortAt e == some .sCert)

/-- Root dispatch of the certificate element: exactly one of
`Cert/root` (a proof-calculus tree) and `Cert/rootEnc` (an enclosure
judgment) must be present — the reference reader's P-ROOT discipline.
(`Cert/rootFam` remains outside the accepted fragment and refuses at
the scan.) -/
inductive CertRootE where
  | proof (e : Nat)
  | enc (e : Nat)
  deriving Repr

/-- The unique certificate element with its header fields. -/
def gCert (tb : RowIdx) :
    Option (Nat × Nat × Nat × Nat × CertRootE × Option Rat) :=
  match certElems tb with
  | [ce] => do
    let rootE ←
      match tb.fldElem .fCertRoot ce, tb.fldElem .fCertRootEnc ce with
      | some rp, none => some (CertRootE.proof rp)
      | none, some re => some (CertRootE.enc re)
      | _, _ => none
    let nw ← tb.fldNat .fCertNWires ce
    let na ← tb.fldNat .fCertNApps ce
    let nc ← tb.fldNat .fCertNComplexes ce
    match tb.fldAt .fCertTheta ce with
    | none => some (ce, nw, na, nc, rootE, none)
    | some tv => do
      let q ← qOfVal tv
      some (ce, nw, na, nc, rootE, some q)
  | _ => none

/-- The root judgment shape: antecedent must be `and(Φ, sph)`. -/
def rootShapeW (t : WProof) : Bool :=
  match t with
  | .mk cj _ =>
    match cj.pre with
    | .and _ .sph => true
    | _ => false

/-- Synthesized header for a rows-reconstructed certificate: the
downstream pipeline consumes the structured fields only, never
offsets or counts, so every synthesized field is zero except the
population counts carried for display. -/
def synthHeader (nw nc : Nat) : WHeader :=
  { symtabOff := 0, symtabLen := 0, payloadOff := 0, payloadLen := 0,
    diagramOff := 0, diagramLen := 0, proofOff := 0, proofLen := 0,
    nWires := nw, nApps := 0, nProofNodes := 0, nComplexes := nc,
    rootNodeOff := 0, thetaRef := 0 }

/-- An enclosure-judgment certificate at wire grain: the four
`EncJudgment` fields, decoded fail-closed. The judgment claims that
the tagged primitive function is enclosed by its degree-`n` canonical
Maclaurin prefix within `cap` on `[-r, r]`; the prefix is determined
by `(func, n)` and never stored. -/
structure WEnc where
  func : Nat
  n : Nat
  r : Rat
  cap : Rat
  deriving Repr, DecidableEq

/-- A reconstructed certificate of either root kind. -/
inductive CertAny where
  | proof (w : WCert)
  | enc (e : WEnc)

/-- Degree budget for enclosure judgments (mirrors the fast-path
checker's `ENC_MAX_DEGREE`): refusal beyond, never divergence. -/
def encMaxDegree : Nat := 4096

/-- Decode the enclosure root: the root element must be a
`PEnclosure` node whose `concludes` is an `EncJudgment`; the four
judgment fields must be present, sole (the scan's duplicate refusal),
and literal-shaped. The function tag must sit in the three-tag wire
roster (0 = exp, 1 = sin, 2 = cos) and the degree under the budget. -/
def gEnc (tb : RowIdx) (rootE : Nat) : CRes WEnc :=
  if tb.sortAt rootE != some .sPEnclosure then
    cerr .unreadable "enc_root_sort" rootE
  else
    match tb.fldElem .fPEncConcludes rootE with
    | none => cerr .unreadable "enc_concludes" rootE
    | some ej =>
      if tb.sortAt ej != some .sEncJudgment then
        cerr .unreadable "enc_judgment_sort" ej
      else
        match tb.fldNat .fEncFunc ej, tb.fldNat .fEncN ej,
            (tb.fldAt .fEncR ej).bind qOfVal,
            (tb.fldAt .fEncCap ej).bind qOfVal with
        | some func, some n, some r, some cap =>
          if 2 < func then cerr .unsupported "enc_func_roster" func
          else if encMaxDegree < n then
            cerr .unsupported "enc_degree_budget" n
          else .ok { func, n, r, cap }
        | _, _, _, _ => cerr .unreadable "enc_judgment_fields" ej

/-- Reconstruct the certificate from a decoded container:
the tip commit's ops are scanned as rows against the pinned
vocabulary, and the certificate structure is rebuilt value-for-value.
The accepted fragment is the first-order pinned-vocabulary rule set
(proof roots) plus primitive-application enclosure judgments
(`rootEnc`); other primitive applications remain out of fragment. -/
def certOfRowsAny (pins : List ((List Nat × Nat) × Vocab)) (g : Geolog) :
    CRes CertAny :=
  match g.commits with
  | [] => cerr .unreadable "no_commits" 0
  | c0 :: rest =>
    let tip := (c0 :: rest).getLastD c0
    let deps := tip.cskel.deps
    match scanOps pins deps tip.cbody.ops with
    | .error e => .error e
    | .ok tb0 =>
      let tb := RowIdx.build tb0
      match gCert tb with
      | none => cerr .unreadable "cert_element" 0
      | some (_, nw, na, nc, rootD, thQ) =>
        if na != 0 then cerr .unsupported "apps_out_of_v0_fragment" na
        else if 4294967294 < nw then cerr .unreadable "n_wires_range" nw
        else
          match rootD with
          | .enc rootE =>
            -- The enclosure fragment is hypernet-free: a nonempty
            -- wire or complex population refuses (fail-closed; the
            -- committed enclosure fixtures carry 0/0/0).
            if nw != 0 then cerr .unsupported "enc_wires_out_of_fragment" nw
            else if nc != 0 then
              cerr .unsupported "enc_complexes_out_of_fragment" nc
            else
              match gEnc tb rootE with
              | .error e => .error e
              | .ok w => .ok (.enc w)
          | .proof rootE =>
            match gWires tb nw with
            | none => cerr .unreadable "wires" 0
            | some (rwid, ws) =>
              match gComplexes tb nc with
              | .error t => cerr .unreadable ("complexes:" ++ t) 0
              | .ok (cxE, cxs) =>
                let rc : RowCtx :=
                  { rtb := tb, rwid := rwid, rcxE := cxE, rcxs := cxs }
                match gProofF rc (tb.nSorts + 1) rootE with
                | none => cerr .unreadable "proof_tree" 0
                | some wp =>
                  if !rootShapeW wp then cerr .unreadable "root_shape" 0
                  else
                    .ok (.proof
                      { header := synthHeader nw nc,
                        syms := ws.toArray,
                        complexes := cxs.toArray,
                        apps := [],
                        root := wp,
                        theta := thQ })

/-- The proof-calculus face of `certOfRowsAny`: byte-identical
behavior on proof-root certificates; an enclosure root through this
entry point is a scope refusal (the legacy callers reconstruct
`WCert` values only). -/
def certOfRows (pins : List ((List Nat × Nat) × Vocab)) (g : Geolog) :
    CRes WCert :=
  match certOfRowsAny pins g with
  | .error e => .error e
  | .ok (.proof w) => .ok w
  | .ok (.enc _) => cerr .unsupported "enc_root_via_proof_entry" 0

end Geolog
end PPLC
