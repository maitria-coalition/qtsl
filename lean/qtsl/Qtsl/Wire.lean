import Qtsl.Core.Catalogue
import Qtsl.Core.Decide

/-!
# The binary certificate parser

Turns certificate bytes into the checker-consumable structure, in two
layers: `parseWCert : ByteArray → Except Err WCert` — bytes to the
first-order wire model, total, with malformed bytes landing in a named
`Err`, never a panic; and elevation from the wire model to the
certificate structure. Certificate validity flows only through this
parser; its declarative refinement obligation is stated in
`Qtsl.WireSpec`.
-/

namespace PPLC
namespace Wire

inductive Err where
  | badMagic
  | badVersion (got : Nat)
  | badFlags (got : Nat)
  | badReserved (what : String)
  | sectionOutOfBounds (what : String)
  | countMismatch (what : String)
  | badDtype (what : String)
  | badTag (what : String) (tag : Nat)
  | badRat (what : String)
  | truncated (what : String)
  | badWireId (what : String) (wire : Nat)
  | badRef (what : String)
  | forwardRef (what : String)
  | badBitset (what : String)
  | badAlignment (what : String)
  | nanPayload (what : String)

  | infPayload (what : String) (negative : Bool)
  | notTopological (app : Nat)
  | notLinear (wire : Nat)
  | sphInPost
  | sphInIllegalPosition (what : String)
  | badBowTie (what : String)
  | badVariant (what : String)
  | badCellRef (what : String)
  | payloadMismatch (what : String)
  | badRoundMode (what : String)

  | complexIllFormed (which : String) (idx : Nat)
  | simplexEmpty (what : String)
  | extSetIllFormed (which : String) (what : String)
  | holeNotFresh
  | rootShape (what : String)
  | hypernetIllFormed (which : String)
  | typeInconsistent (app : Nat)
  | valueOutOfSet (what : String)
  | floatConstUnsupported (what : String)
  | badContractPattern (what : String)

  | obligation (rule which : String)
  | malformedNode (rule which : String)
  deriving Repr, DecidableEq

instance : ToString Err := ⟨fun e => toString (repr e)⟩

abbrev R (α : Type) := Except Err α

structure Cur where
  b    : ByteArray
  pos  : Nat
  stop : Nat

namespace Cur

def at' (b : ByteArray) (pos stop : Nat) : Cur := ⟨b, pos, stop⟩

def take (c : Cur) (n : Nat) (what : String) : R (List UInt8 × Cur) := do
  if c.pos + n > c.stop || c.pos + n > c.b.size then
    throw (.truncated what)
  let bytes := (List.range n).map (fun i => c.b[c.pos + i]!)
  pure (bytes, { c with pos := c.pos + n })

def u8 (c : Cur) (what : String) : R (Nat × Cur) := do
  let (bs, c) ← c.take 1 what
  pure ((bs.headD 0).toNat, c)

def uLE (c : Cur) (n : Nat) (what : String) : R (Nat × Cur) := do
  let (bs, c) ← c.take n what
  pure (bs.foldr (fun b acc => acc * 256 + b.toNat) 0, c)

def u16 (c : Cur) (what : String) : R (Nat × Cur) := c.uLE 2 what
def u32 (c : Cur) (what : String) : R (Nat × Cur) := c.uLE 4 what
def u64 (c : Cur) (what : String) : R (Nat × Cur) := c.uLE 8 what

end Cur

def bytesToNatLE (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def bytesToIntLE (bs : List UInt8) : Int :=
  let n := bytesToNatLE bs
  match bs.getLast? with
  | none => 0
  | some top =>
    if top.toNat ≥ 0x80 then (n : Int) - ((256 : Int) ^ bs.length) else (n : Int)

def unsignedMinimal (bs : List UInt8) : Bool :=
  match bs.getLast? with
  | none => false
  | some top => bs.length == 1 || top != 0

def signedMinimal (bs : List UInt8) : Bool :=
  match bs with
  | [] => false
  | [_] => true
  | _ =>
    let top := bs.getLast! ; let below := bs[bs.length - 2]!
    !(top == 0x00 && below.toNat < 0x80) && !(top == 0xFF && below.toNat ≥ 0x80)

def readRat (c : Cur) (what : String) : R (Rat × Cur) := do
  let (nlen, c) ← c.u32 what
  let (dlen, c) ← c.u32 what
  let (nb, c) ← c.take nlen what
  let (db, c) ← c.take dlen what
  if !signedMinimal nb || !unsignedMinimal db then throw (.badRat what)
  let num := bytesToIntLE nb
  let den := bytesToNatLE db
  if den == 0 then throw (.badRat what)

  if Nat.gcd num.natAbs den != 1 then throw (.badRat what)
  let q := mkRat num den

  if q.num != num || q.den != den then throw (.badRat what)
  pure (q, c)

def readMask (c : Cur) (n : Nat) (what : String) : R (Array Bool × Cur) := do
  let (bs, c) ← c.take ((n + 7) / 8) what
  let arr := bs.toArray
  let bit (i : Nat) : Bool := ((arr[i / 8]!.toNat >>> (i % 8)) &&& 1) == 1

  for i in [n : arr.size * 8] do
    if bit i then throw (.badBitset what)
  pure ((Array.range n).map bit, c)

def kindOf (k : Nat) (what : String) : R Kind :=
  match k with
  | 0 => pure .bool | 1 => pure .int | 2 => pure .rat
  | 3 => pure .f16  | 4 => pure .bf16 | 5 => pure .f32 | 6 => pure .f64
  | _ => throw (.badDtype what)

def signOf (s : Nat) (what : String) : R Sign :=
  match s with
  | 0 => pure .nn | 1 => pure .signed | _ => throw (.badDtype what)

def extOf (e : Nat) (what : String) : R Ext :=
  match e with
  | 0 => pure .fin | 1 => pure .ext | _ => throw (.badDtype what)

def readDtype (c : Cur) (what : String) : R (Dtype × Cur) := do
  let (k, c) ← c.u8 what
  let (s, c) ← c.u8 what
  let (e, c) ← c.u8 what
  let (pad, c) ← c.u8 what
  if pad != 0 then throw (.badReserved what)
  pure (⟨← kindOf k what, ← signOf s what, ← extOf e what⟩, c)

def bowtieOf (v : Nat) (what : String) : R BowTie :=
  match v with
  | 0 => pure .lt | 1 => pure .le | 2 => pure .eq
  | 3 => pure .ge | 4 => pure .gt | 5 => pure .ne
  | _ => throw (.badBowTie what)

def roundOf (v : Nat) (what : String) : R RoundMode :=
  match v with
  | 0 => pure .rne | 1 => pure .rtz | 2 => pure .rup
  | 3 => pure .rdn | 4 => pure .exact
  | _ => throw (.badRoundMode what)

structure WHeader where
  symtabOff   : Nat
  symtabLen   : Nat
  payloadOff  : Nat
  payloadLen  : Nat
  diagramOff  : Nat
  diagramLen  : Nat
  proofOff    : Nat
  proofLen    : Nat
  nWires      : Nat
  nApps       : Nat
  nProofNodes : Nat
  nComplexes  : Nat
  rootNodeOff : Nat
  thetaRef    : Nat
  deriving Repr

inductive WPayload where
  | bools (bs : List Bool)
  | ints  (vs : List Int)
  | rats  (qs : List Rat)
  | fbits (kind : Kind) (bits : List Nat)
  deriving Repr

structure WSym where
  dtype   : Dtype
  shape   : List Nat
  payload : Option WPayload
  deriving Repr

structure WComplex where
  nVertices : Nat
  ambDim    : Nat

  coords    : Array Rat
  simplices : Array (Array Bool)
  cells     : Array (Array Bool × Array Bool)
  deriving Repr

inductive WAppK where
  | const     (out : Nat)
  | contract  (δ : Dtype) (inputs : List Nat) (output : Nat)
              (extents : List Nat) (inputBindings : List (List Nat))
              (outputBinding : List Nat)
  | cast      (δfrom δto : Dtype) (shape : List Nat) (input output : Nat)
  | cell      (complex : Nat) (input : Nat) (outputs : List Nat)
  | reshape   (newShape : List Nat) (input output : Nat)
  | broadcast (toShape : List Nat) (input output : Nat)
  | copy      (input : Nat) (outputs : List Nat)
  | delete    (input : Nat)
  | swap      (in1 in2 out1 out2 : Nat)
  | stack     (inputs : List Nat) (output : Nat)
  deriving Repr

structure WApp where
  round : RoundMode
  kind  : WAppK
  deriving Repr

structure WSimplexR where
  complex : Nat
  mask    : Array Bool
  deriving Repr, DecidableEq

structure WExtSetR where
  simplex : WSimplexR
  mask    : Array Bool
  deriving Repr, DecidableEq

inductive WFormula where
  | atom (b : BowTie) (l r : Term)
  | inRegion (t : Term) (s : WSimplexR) (S : WExtSetR)
  | and (l r : WFormula)
  | or  (l r : WFormula)
  | tt
  | ff
  | sph
  deriving Repr

def WFormula.hasSph : WFormula → Bool
  | .sph => true
  | .and l r | .or l r => l.hasSph || r.hasSph
  | _ => false

structure WJudgment where
  pre  : WFormula
  post : WFormula
  deriving Repr

inductive WSide where
  | left | right
  deriving Repr, DecidableEq

mutual

inductive WProof where
  | mk (concludes : WJudgment) (node : WNodeK)

inductive WNodeK where
  | ax
  | weaken (premise : WProof) (extra : WFormula)
  | cut (cutFormula : WFormula) (left right : WProof)
  | andI (left right : WProof)
  | andE (which : WSide) (premise : WProof) (other : WFormula)
  | orI  (which : WSide) (premise : WProof) (other : WFormula)
  | orE (left right : WProof) (path : List WSide)
  | eqElim (eqProof bodyProof : WProof) (wire : Nat)
           (termT termU : Term) (bodyForm : WFormula)
  | convIntro (premise : WProof) (term : Term) (s : WSimplexR) (S : WExtSetR)
  | convElim  (premise : WProof) (term : Term) (s : WSimplexR) (S : WExtSetR)
  | arithAtom (dir : WSide) (premise : WProof) (termL termR : Term) (b : BowTie)
  | bernCone (regionProof : WProof) (termX : Term) (s : WSimplexR)
             (S : WExtSetR) (degree : Nat) (polynomial : Term)
             (predicate : WFormula)
  | norm (termL termR : Term)
  | farkas (combinationCoeffs : Term) (conclusion : Term) (denBoundLog2 : Nat)
  | subdivide (regionProof : WProof) (termX : Term) (s : WSimplexR)
              (S : WExtSetR) (branches : List (WSimplexR × WExtSetR × WProof))
              (coverCertificate : Term) (denBoundLog2 : Nat)
  | lirpa (lower upper : WProof) (preact post : Nat)
          (a b α β γ δq : Rat) (denBoundLog2 : Nat)
  | reluPos (premise : WProof) (preact post : Nat)
  | reluNeg (premise : WProof) (preact post : Nat)
  | reluNN (preact post : Nat)
  | reluAbove (preact post : Nat)
  | cellInInterior (premise : WProof) (appIdx whichI : Nat)
  | cellOut (premise : WProof) (appIdx whichJ witnessVertex : Nat)
  | eqRefl (term : Term)
  | eqSym (premise : WProof) (termT termU : Term)
  | promise (supplier consumer : WProof) (contract : WFormula)
            (path : List WSide) (iface : List Nat)
  | syzygy (components : List WProof) (combination conclusion : Term)
           (denBoundLog2 : Nat) (theta : Option Rat)
end

structure WCert where
  header    : WHeader
  syms      : Array WSym
  complexes : Array WComplex
  apps      : List WApp
  root      : WProof
  theta     : Option Rat

def MAGIC : List UInt8 := [0x42, 0x45, 0x52, 0x4E, 0x4C, 0x47, 0x43, 0x01]
def HEADER_LEN : Nat := 128
def HOLE : Nat := 0xFFFFFFFF
def U64_MAX : Nat := 0xFFFFFFFFFFFFFFFF

def parseHeader (b : ByteArray) : R WHeader := do
  if b.size < HEADER_LEN then throw (.truncated "header")
  let c := Cur.at' b 0 HEADER_LEN
  let (magic, c) ← c.take 8 "magic"
  if magic ≠ MAGIC then throw .badMagic
  let (version, c) ← c.u32 "version"
  if version != 1 then throw (.badVersion version)
  let (flags, c) ← c.u32 "flags"
  if flags != 0 then throw (.badFlags flags)
  let (so, c) ← c.u64 "symtab_off"
  let (sl, c) ← c.u64 "symtab_len"
  let (po, c) ← c.u64 "payload_off"
  let (pl, c) ← c.u64 "payload_len"
  let (dgo, c) ← c.u64 "diagram_off"
  let (dgl, c) ← c.u64 "diagram_len"
  let (pfo, c) ← c.u64 "proof_off"
  let (pfl, c) ← c.u64 "proof_len"
  let (nw, c) ← c.u32 "n_wires"
  let (na, c) ← c.u32 "n_apps"
  let (nn, c) ← c.u32 "n_proof_nodes"
  let (nc, c) ← c.u32 "n_complexes"
  let (ro, c) ← c.u64 "root_node_off"
  let (th, c) ← c.u32 "theta_ref"
  let (rsv, _) ← c.take 20 "reserved"
  if rsv.any (· != 0) then throw (.badReserved "header")

  if !(HEADER_LEN ≤ so && so + sl ≤ po && po + pl ≤ dgo &&
       dgo + dgl ≤ pfo && pfo + pfl ≤ b.size) then
    throw (.sectionOutOfBounds "sections (order/overlap/EOF)")
  if nw ≥ HOLE then throw (.badWireId "n_wires" nw)
  if po % 64 != 0 then throw (.badAlignment "payload area")
  pure ⟨so, sl, po, pl, dgo, dgl, pfo, pfl, nw, na, nn, nc, ro, th⟩

def parseSymEntry (b : ByteArray) (h : WHeader) (i : Nat) :
    R (Dtype × List Nat × Option (Nat × Nat)) := do
  let recsLen := 32 * h.nWires
  if recsLen > h.symtabLen then throw (.sectionOutOfBounds "symtab records")
  let base := h.symtabOff
  let c := Cur.at' b (base + 32 * i) (base + h.symtabLen)
  let (dt, c) ← readDtype c "symtab dtype"
  let (rank, c) ← c.u32 "symtab rank"
  let (shapeOff, c) ← c.u64 "symtab shape_off"
  let (payloadOff, c) ← c.u64 "symtab payload_off"
  let (payloadLen, _) ← c.u64 "symtab payload_len"

  if shapeOff < recsLen || shapeOff + 8 * rank > h.symtabLen then
    throw (.sectionOutOfBounds "symtab shape aux")
  let mut sc := Cur.at' b (base + shapeOff) (base + h.symtabLen)
  let mut shape : List Nat := []
  for _ in [0 : rank] do
    let (e, sc') ← sc.u64 "shape extent"
    shape := shape ++ [e]
    sc := sc'
  let loc ← do
    if payloadOff == U64_MAX then
      if payloadLen != 0 then
        throw (.payloadMismatch "len nonzero without payload")
      pure none
    else
      if payloadOff % 64 != 0 then throw (.badAlignment "payload")
      pure (some (payloadOff, payloadLen))
  pure (dt, shape, loc)

def parsePayload (b : ByteArray) (dt : Dtype) (shape : List Nat)
    (off len : Nat) : R WPayload := do
  let n := Shape.totalSize shape
  if off + len > b.size then throw (.sectionOutOfBounds "payload")
  let c := Cur.at' b off (off + len)
  match dt.kind with
  | .bool => do
    if len != (n + 7) / 8 then throw (.payloadMismatch "bool len")
    let (mask, _) ← readMask c n "bool payload padding"
    pure (.bools mask.toList)
  | .int => do
    if len != 8 * n then throw (.payloadMismatch "int len")
    let mut vs : List Int := []
    let mut cc := c
    for _ in [0 : n] do
      let (bs, cc') ← cc.take 8 "int element"

      let v : Int := match dt.sign with
        | .nn => (bytesToNatLE bs : Int)
        | .signed => bytesToIntLE bs
      vs := vs ++ [v]
      cc := cc'
    pure (.ints vs)
  | .rat => do

    let mut offs : List Nat := []
    let mut cc := c
    for _ in [0 : n] do
      let (o, cc') ← cc.u32 "rat offset table"
      offs := offs ++ [o]
      cc := cc'
    let mut qs : List Rat := []
    for o in offs do
      let ec := Cur.at' b (off + o) (off + len)
      let (q, _) ← readRat ec "rat payload"
      qs := qs ++ [q]
    pure (.rats qs)
  | k => do

    let (w, expMask, manMask, signMask) :=
      match k with
      | .f16  => (2, 0x7C00, 0x03FF, 0x8000)
      | .bf16 => (2, 0x7F80, 0x007F, 0x8000)
      | .f32  => (4, 0x7F800000, 0x007FFFFF, 0x80000000)
      | _     => (8, 0x7FF0000000000000, 0x000FFFFFFFFFFFFF,
                  0x8000000000000000)
    if len != w * n then throw (.payloadMismatch "float len")
    let mut bits : List Nat := []
    let mut cc := c
    for _ in [0 : n] do
      let (v, cc') ← cc.uLE w "float element"
      if v &&& expMask == expMask then
        if v &&& manMask != 0 then
          throw (.nanPayload "float payload")
        throw (.infPayload "float payload" (v &&& signMask != 0))
      bits := bits ++ [v]
      cc := cc'
    pure (.fbits k bits)

def parseSymtab (b : ByteArray) (h : WHeader) : R (Array WSym) := do
  let mut out : Array WSym := #[]
  for i in [0 : h.nWires] do
    let (dt, shape, loc) ← parseSymEntry b h i
    let payload ← match loc with
      | none => pure none
      | some (off, len) => do
        if off < h.payloadOff || off + len > h.payloadOff + h.payloadLen then
          throw (.sectionOutOfBounds "wire payload")
        pure (some (← parsePayload b dt shape off len))
    out := out.push ⟨dt, shape, payload⟩
  pure out

def parseComplex (c : Cur) : R (WComplex × Cur) := do
  let (nv, c) ← c.u32 "n_vertices"
  let (ad, c) ← c.u32 "amb_dim"
  let mut coords : Array Rat := #[]
  let mut cc := c
  for _ in [0 : nv * ad] do
    let (q, cc') ← readRat cc "coord"
    coords := coords.push q
    cc := cc'
  let (ns, cc') ← cc.u32 "n_simplices"
  cc := cc'
  let mut simplices : Array (Array Bool) := #[]
  for _ in [0 : ns] do
    let (m, cc') ← readMask cc nv "simplex"
    simplices := simplices.push m
    cc := cc'
  let (ncl, cc') ← cc.u32 "n_cells"
  cc := cc'
  let mut cells : Array (Array Bool × Array Bool) := #[]
  for _ in [0 : ncl] do
    let (sm, cc') ← readMask cc nv "cell simplex"
    let (em, cc'') ← readMask cc' nv "cell ext"
    cells := cells.push (sm, em)
    cc := cc''
  pure (⟨nv, ad, coords, simplices, cells⟩, cc)

def parseApp (c : Cur) (nWires : Nat) (complexes : Array WComplex) :
    R (WApp × Cur) := do
  let wireOk (w : Nat) (what : String) : R Nat :=
    if w ≥ nWires then throw (.badWireId what w) else pure w
  let (tag, c) ← c.u8 "app tag"
  let (rm, c) ← c.u8 "app round"
  let round ← roundOf rm "round mode"
  let (rsv, c) ← c.u16 "app reserved"
  if rsv != 0 then throw (.badReserved "app")

  let requireExact : R Unit :=
    if round != .exact then throw (.badRoundMode "round must be exact (4)")
    else pure ()
  match tag with
  | 0 => do
    requireExact
    let (out, c) ← c.u32 "const out"
    pure (⟨round, .const (← wireOk out "const out")⟩, c)
  | 1 => do
    let (dt, c) ← readDtype c "contract dtype"
    let (nIn, c) ← c.u32 "contract n_inputs"
    let mut inputs : List Nat := []
    let mut cc := c
    for _ in [0 : nIn] do
      let (w, cc') ← cc.u32 "contract input"
      inputs := inputs ++ [← wireOk w "contract input"]
      cc := cc'
    let (out, cc') ← cc.u32 "contract output"
    let output ← wireOk out "contract output"
    let (nIdx, cc'') ← cc'.u32 "contract n_indices"
    cc := cc''
    let mut extents : List Nat := []
    for _ in [0 : nIdx] do
      let (e, cc') ← cc.u64 "contract extent"
      extents := extents ++ [e]
      cc := cc'
    let idxOk (x : Nat) : R Nat :=
      if x ≥ nIdx then throw (.badRef "contract binding") else pure x
    let mut inputBindings : List (List Nat) := []
    for _ in [0 : nIn] do
      let (rank, cc') ← cc.u32 "contract in rank"
      cc := cc'
      let mut ib : List Nat := []
      for _ in [0 : rank] do
        let (x, cc') ← cc.u32 "contract in binding"
        ib := ib ++ [← idxOk x]
        cc := cc'
      inputBindings := inputBindings ++ [ib]
    let (outRank, cc') ← cc.u32 "contract out rank"
    cc := cc'
    let mut ob : List Nat := []
    for _ in [0 : outRank] do
      let (x, cc') ← cc.u32 "contract out binding"
      ob := ob ++ [← idxOk x]
      cc := cc'
    pure (⟨round, .contract dt inputs output extents inputBindings ob⟩, cc)
  | 2 => do
    let (dfrom, c) ← readDtype c "cast from"
    let (dto, c) ← readDtype c "cast to"
    let (rank, c) ← c.u32 "cast rank"
    let mut shape : List Nat := []
    let mut cc := c
    for _ in [0 : rank] do
      let (e, cc') ← cc.u64 "cast shape"
      shape := shape ++ [e]
      cc := cc'
    let (i, cc') ← cc.u32 "cast in"
    let (o, cc'') ← cc'.u32 "cast out"
    pure (⟨round, .cast dfrom dto shape (← wireOk i "cast in")
      (← wireOk o "cast out")⟩, cc'')
  | 3 => do
    requireExact
    let (cx, c) ← c.u32 "cell complex"
    let cxCells ← match complexes[cx]? with
      | none => throw (.badCellRef "cell complex idx")
      | some w => pure w.cells.size
    let (i, c) ← c.u32 "cell in"
    let input ← wireOk i "cell in"
    let (nOut, c) ← c.u32 "cell n_outputs"
    if nOut != cxCells then
      throw (.countMismatch "cell outputs vs complex cells")
    let mut outs : List Nat := []
    let mut cc := c
    for _ in [0 : nOut] do
      let (w, cc') ← cc.u32 "cell out"
      outs := outs ++ [← wireOk w "cell out"]
      cc := cc'
    pure (⟨round, .cell cx input outs⟩, cc)
  | 4 | 5 => do
    requireExact
    let (rank, c) ← c.u32 "shape rank"
    let mut shape : List Nat := []
    let mut cc := c
    for _ in [0 : rank] do
      let (e, cc') ← cc.u64 "shape extent"
      shape := shape ++ [e]
      cc := cc'
    let (i, cc') ← cc.u32 "in"
    let input ← wireOk i "reshape/broadcast in"
    let (o, cc'') ← cc'.u32 "out"
    let output ← wireOk o "reshape/broadcast out"
    if tag == 4 then pure (⟨round, .reshape shape input output⟩, cc'')
    else pure (⟨round, .broadcast shape input output⟩, cc'')
  | 6 => do
    requireExact
    let (k, c) ← c.u32 "copy k"
    let (i, c) ← c.u32 "copy in"
    let input ← wireOk i "copy in"
    let mut outs : List Nat := []
    let mut cc := c
    for _ in [0 : k] do
      let (w, cc') ← cc.u32 "copy out"
      outs := outs ++ [← wireOk w "copy out"]
      cc := cc'
    pure (⟨round, .copy input outs⟩, cc)
  | 7 => do
    requireExact
    let (i, c) ← c.u32 "delete in"
    pure (⟨round, .delete (← wireOk i "delete in")⟩, c)
  | 8 => do
    requireExact
    let (i1, c) ← c.u32 "swap in1"
    let (i2, c) ← c.u32 "swap in2"
    let (o1, c) ← c.u32 "swap out1"
    let (o2, c) ← c.u32 "swap out2"
    pure (⟨round, .swap (← wireOk i1 "swap in1") (← wireOk i2 "swap in2")
      (← wireOk o1 "swap out1") (← wireOk o2 "swap out2")⟩, c)
  | 9 => do

    requireExact
    let (k, c) ← c.u32 "stack k"
    let mut ins : List Nat := []
    let mut cc := c
    for _ in [0 : k] do
      let (w, cc') ← cc.u32 "stack input"
      ins := ins ++ [← wireOk w "stack input"]
      cc := cc'
    let (o, cc') ← cc.u32 "stack output"
    pure (⟨round, .stack ins (← wireOk o "stack output")⟩, cc')
  | t => throw (.badTag "app" t)

def parseDiagram (b : ByteArray) (h : WHeader) :
    R (Array WComplex × List WApp) := do
  let c := Cur.at' b h.diagramOff (h.diagramOff + h.diagramLen)
  let (nc, c) ← c.u32 "n_complexes"
  if nc != h.nComplexes then throw (.countMismatch "n_complexes")
  let mut complexes : Array WComplex := #[]
  let mut cc := c
  for _ in [0 : nc] do
    let (cx, cc') ← parseComplex cc
    complexes := complexes.push cx
    cc := cc'
  let (na, cc') ← cc.u32 "n_apps"
  if na != h.nApps then throw (.countMismatch "n_apps")
  cc := cc'
  let mut apps : List WApp := []
  for _ in [0 : na] do
    let (app, cc') ← parseApp cc h.nWires complexes
    apps := apps ++ [app]
    cc := cc'
  pure (complexes, apps)

def parseTerm (pool : ByteArray) (off : Nat) : R Term := do
  if off ≥ pool.size then throw (.badRef "term")
  let c := Cur.at' pool off pool.size
  let (tag, c) ← c.u8 "term tag"
  match tag with
  | 0x01 => do
    let (w, _) ← c.u32 "term var"
    pure (.var w)
  | 0x02 => do
    let (q, _) ← readRat c "term const"
    pure (.const q)
  | 0x03 | 0x04 | 0x05 => do
    let (l, c) ← c.u32 "term l"
    let (r, _) ← c.u32 "term r"
    if hl : l < off then
      if hr : r < off then do
        let lt ← parseTerm pool l
        let rt ← parseTerm pool r
        match tag with
        | 0x03 => pure (.add lt rt)
        | 0x04 => pure (.mul lt rt)
        | _    => pure (.sub lt rt)
      else throw (.forwardRef "term r")
    else throw (.forwardRef "term l")
  | 0x06 => do
    let (t, _) ← c.u32 "term neg"
    if ht : t < off then
      pure (.neg (← parseTerm pool t))
    else throw (.forwardRef "term neg")
  | 0x07 => do
    let (t, c) ← c.u32 "term idx"
    let (i, _) ← c.u32 "term idx i"
    if ht : t < off then
      pure (.idx (← parseTerm pool t) i)
    else throw (.forwardRef "term idx")
  | t => throw (.badTag "term" t)
termination_by off

def parseSimplexR (pool : ByteArray) (cxs : Array WComplex) (off : Nat) :
    R WSimplexR := do
  if off ≥ pool.size then throw (.badRef "simplex")
  let c := Cur.at' pool off pool.size
  let (tag, c) ← c.u8 "simplex tag"
  if tag != 0x10 then throw (.badTag "simplex" tag)
  let (cx, c) ← c.u32 "simplex complex"
  if hcx : cx < cxs.size then
    let (mask, _) ← readMask c cxs[cx].nVertices "simplex mask"
    pure ⟨cx, mask⟩
  else throw (.badCellRef "simplex complex idx")

def parseExtSetR (pool : ByteArray) (cxs : Array WComplex) (off : Nat) :
    R WExtSetR := do
  if off ≥ pool.size then throw (.badRef "extset")
  let c := Cur.at' pool off pool.size
  let (tag, c) ← c.u8 "extset tag"
  if tag != 0x11 then throw (.badTag "extset" tag)
  let (so, c) ← c.u32 "extset simplex"
  if _h : so < off then
    let s ← parseSimplexR pool cxs so
    if hcx : s.complex < cxs.size then
      let (mask, _) ← readMask c cxs[s.complex].nVertices "extset mask"
      pure ⟨s, mask⟩
    else throw (.badCellRef "extset complex idx")
  else throw (.forwardRef "extset simplex")

def parseFormula (pool : ByteArray) (cxs : Array WComplex) (off : Nat) :
    R WFormula := do
  if off ≥ pool.size then throw (.badRef "formula")
  let c := Cur.at' pool off pool.size
  let (tag, c) ← c.u8 "formula tag"
  match tag with
  | 0x20 => do
    let (bv, c) ← c.u8 "formula bowtie"
    let b ← bowtieOf bv "formula atom"
    let (l, c) ← c.u32 "atom l"
    let (r, _) ← c.u32 "atom r"
    if hl : l < off then
      if hr : r < off then
        pure (.atom b (← parseTerm pool l) (← parseTerm pool r))
      else throw (.forwardRef "atom r")
    else throw (.forwardRef "atom l")
  | 0x21 => do
    let (t, c) ← c.u32 "inregion t"
    let (s, c) ← c.u32 "inregion simplex"
    let (e, _) ← c.u32 "inregion extset"
    if ht : t < off then
      if hs : s < off then
        if he : e < off then
          pure (.inRegion (← parseTerm pool t) (← parseSimplexR pool cxs s)
            (← parseExtSetR pool cxs e))
        else throw (.forwardRef "inregion extset")
      else throw (.forwardRef "inregion simplex")
    else throw (.forwardRef "inregion t")
  | 0x22 | 0x23 => do
    let (l, c) ← c.u32 "bool l"
    let (r, _) ← c.u32 "bool r"
    if hl : l < off then
      if hr : r < off then do
        let lf ← parseFormula pool cxs l
        let rf ← parseFormula pool cxs r
        if tag == 0x22 then pure (.and lf rf) else pure (.or lf rf)
      else throw (.forwardRef "bool r")
    else throw (.forwardRef "bool l")
  | 0x24 => pure .tt
  | 0x25 => pure .ff
  | 0x26 => pure .sph
  | t => throw (.badTag "formula" t)
termination_by off

def parseJudgment (pool : ByteArray) (cxs : Array WComplex) (off : Nat) :
    R WJudgment := do
  if off ≥ pool.size then throw (.badRef "judgment")
  let c := Cur.at' pool off pool.size
  let (tag, c) ← c.u8 "judgment tag"
  if tag != 0x30 then throw (.badTag "judgment" tag)
  let (pre, c) ← c.u32 "judgment pre"
  let (post, _) ← c.u32 "judgment post"
  if hpre : pre < off then
    if hpost : post < off then do
      let preF ← parseFormula pool cxs pre
      let postF ← parseFormula pool cxs post
      if postF.hasSph then throw .sphInPost
      pure ⟨preF, postF⟩
    else throw (.forwardRef "judgment post")
  else throw (.forwardRef "judgment pre")

def parseThetaAt (pool : ByteArray) (off : Nat) (what : String) :
    R Rat := do
  match ← parseTerm pool off with
  | .const q => pure q
  | _ => throw (.badRef what)

def readPath (c : Cur) (what : String) : R (List WSide × Cur) := do
  let (n, c) ← c.u32 what
  let mut steps : List WSide := []
  let mut cc := c
  for _ in [0 : n] do
    let (s, cc') ← cc.u8 what
    match s with
    | 0 => steps := steps ++ [.left]
    | 1 => steps := steps ++ [.right]
    | b => throw (.badTag what b)
    cc := cc'
  pure (steps, cc)

structure NodeCtx where

  section' : ByteArray

  nodesBase : Nat

  pool : ByteArray
  complexes : Array WComplex
  nApps : Nat

mutual

def parseNode (ctx : NodeCtx) (off : Nat) : R WProof := do
  if off < ctx.nodesBase || off ≥ ctx.section'.size then
    throw (.badRef "node offset")
  let c := Cur.at' ctx.section' off ctx.section'.size
  let (tag, c) ← c.u8 "node tag"
  let (variant, c) ← c.u8 "node variant"
  let (rsv, c) ← c.u16 "node reserved"
  if rsv != 0 then throw (.badReserved "node")
  let (cj, c) ← c.u32 "node concludes"
  let concludes ← parseJudgment ctx.pool ctx.complexes cj

  let side (what : String) : R WSide :=
    match variant with
    | 0 => pure .left
    | 1 => pure .right
    | _ => throw (.badVariant what)
  let variantZero (what : String) : R Unit :=
    if variant != 0 then throw (.badVariant what) else pure ()
  let node : WNodeK ← do
    match tag with
    | 0 => do variantZero "ax"; pure .ax
    | 1 => do
      variantZero "weaken"
      let (pr, c) ← c.u64 "weaken premise"
      let (ex, _) ← c.u32 "weaken extra"
      let extra ← parseFormula ctx.pool ctx.complexes ex
      if hp : pr < off then
        pure (.weaken (← parseNode ctx pr) extra)
      else throw (.forwardRef "weaken premise")
    | 2 => do
      variantZero "cut"
      let (cf, c) ← c.u32 "cut formula"
      let cutF ← parseFormula ctx.pool ctx.complexes cf
      let (l, c) ← c.u64 "cut left"
      let (r, _) ← c.u64 "cut right"
      if hl : l < off then
        if hr : r < off then
          pure (.cut cutF (← parseNode ctx l) (← parseNode ctx r))
        else throw (.forwardRef "cut right")
      else throw (.forwardRef "cut left")
    | 3 => do
      variantZero "andI"
      let (l, c) ← c.u64 "andI left"
      let (r, _) ← c.u64 "andI right"
      if hl : l < off then
        if hr : r < off then
          pure (.andI (← parseNode ctx l) (← parseNode ctx r))
        else throw (.forwardRef "andI right")
      else throw (.forwardRef "andI left")
    | 6 => do
      variantZero "orE"
      let (l, c) ← c.u64 "orE left"
      let (r, c) ← c.u64 "orE right"
      let (path, _) ← readPath c "orE path step"
      if hl : l < off then
        if hr : r < off then
          pure (.orE (← parseNode ctx l) (← parseNode ctx r) path)
        else throw (.forwardRef "orE right")
      else throw (.forwardRef "orE left")
    | 4 | 5 => do
      let which ← side "andE/orI"
      let (pr, c) ← c.u64 "premise"
      let (ot, _) ← c.u32 "other"
      let other ← parseFormula ctx.pool ctx.complexes ot
      if hp : pr < off then do
        let premise ← parseNode ctx pr
        if tag == 4 then pure (.andE which premise other)
        else pure (.orI which premise other)
      else throw (.forwardRef "premise")
    | 7 => do
      variantZero "eqElim"
      let (eqp, c) ← c.u64 "eq proof"
      let (bodyp, c) ← c.u64 "body proof"
      let (w, c) ← c.u32 "eqElim wire"
      let (tt', c) ← c.u32 "termT"
      let (tu, c) ← c.u32 "termU"
      let (bf, _) ← c.u32 "bodyForm"
      let termT ← parseTerm ctx.pool tt'
      let termU ← parseTerm ctx.pool tu
      let bodyForm ← parseFormula ctx.pool ctx.complexes bf
      if he : eqp < off then
        if hb : bodyp < off then
          pure (.eqElim (← parseNode ctx eqp) (← parseNode ctx bodyp)
            w termT termU bodyForm)
        else throw (.forwardRef "body proof")
      else throw (.forwardRef "eq proof")
    | 8 | 9 => do
      variantZero "conv"
      let (pr, c) ← c.u64 "conv premise"
      let (tm, c) ← c.u32 "conv term"
      let (sp, c) ← c.u32 "conv simplex"
      let (es, _) ← c.u32 "conv extset"
      let term ← parseTerm ctx.pool tm
      let s ← parseSimplexR ctx.pool ctx.complexes sp
      let e ← parseExtSetR ctx.pool ctx.complexes es
      if hp : pr < off then do
        let premise ← parseNode ctx pr
        if tag == 8 then pure (.convIntro premise term s e)
        else pure (.convElim premise term s e)
      else throw (.forwardRef "conv premise")
    | 10 => do
      let dir ← side "arithAtom"
      let (pr, c) ← c.u64 "arith premise"
      let (tl, c) ← c.u32 "termL"
      let (tr, c) ← c.u32 "termR"
      let (bv, c) ← c.u8 "arith bowtie"

      if bv > 4 then throw (.badBowTie "arithAtom (B5: 0..=4)")
      let b ← bowtieOf bv "arithAtom"
      let (pad, _) ← c.take 3 "arith pad"
      if pad.any (· != 0) then throw (.badReserved "arith pad")
      let termL ← parseTerm ctx.pool tl
      let termR ← parseTerm ctx.pool tr
      if hp : pr < off then
        pure (.arithAtom dir (← parseNode ctx pr) termL termR b)
      else throw (.forwardRef "arith premise")
    | 11 => do

      variantZero "bernCone"
      let (rp, c) ← c.u64 "region proof"
      let (tx, c) ← c.u32 "termX"
      let (sp, c) ← c.u32 "bc simplex"
      let (es, c) ← c.u32 "bc extset"
      let (deg, c) ← c.u32 "degree"
      let (poly, c) ← c.u32 "polynomial"
      let (pred, _) ← c.u32 "predicate"
      let termX ← parseTerm ctx.pool tx
      let s ← parseSimplexR ctx.pool ctx.complexes sp
      let e ← parseExtSetR ctx.pool ctx.complexes es
      let polynomial ← parseTerm ctx.pool poly
      let predicate ← parseFormula ctx.pool ctx.complexes pred
      if hp : rp < off then do
        let regionProof ← parseNode ctx rp
        pure (.bernCone regionProof termX s e deg polynomial predicate)
      else throw (.forwardRef "region proof")
    | 12 => do
      variantZero "norm"
      let (tl, c) ← c.u32 "norm l"
      let (tr, _) ← c.u32 "norm r"
      pure (.norm (← parseTerm ctx.pool tl) (← parseTerm ctx.pool tr))
    | 14 => do
      variantZero "farkas"
      let (cc', c) ← c.u32 "farkas coeffs"
      let (k, c) ← c.u32 "farkas conclusion"
      let (den, _) ← c.u64 "farkas denBoundLog2"
      pure (.farkas (← parseTerm ctx.pool cc') (← parseTerm ctx.pool k) den)
    | 15 => do
      variantZero "subdivide"
      let (rp, c) ← c.u64 "subdiv region"
      let (tx, c) ← c.u32 "subdiv termX"
      let (sp, c) ← c.u32 "subdiv simplex"
      let (es, c) ← c.u32 "subdiv extset"
      let (nb, c) ← c.u32 "nBranches"
      let termX ← parseTerm ctx.pool tx
      let s ← parseSimplexR ctx.pool ctx.complexes sp
      let e ← parseExtSetR ctx.pool ctx.complexes es

      let mut raw : List (Nat × Nat × Nat) := []
      let mut cc := c
      for _ in [0 : nb] do
        let (bs, cc1) ← cc.u32 "branch simplex"
        let (be, cc2) ← cc1.u32 "branch extset"
        let (bp, cc3) ← cc2.u64 "branch proof"
        raw := raw ++ [(bs, be, bp)]
        cc := cc3
      let (cov, cc') ← cc.u32 "cover cert"
      let (den, _) ← cc'.u64 "subdiv denBoundLog2"
      let cover ← parseTerm ctx.pool cov
      let branches ← parseBranches ctx off raw
      if hp : rp < off then
        pure (.subdivide (← parseNode ctx rp) termX s e branches cover den)
      else throw (.forwardRef "subdiv region")
    | 16 => do
      variantZero "lirpa"
      let (lo, c) ← c.u64 "lirpa lower"
      let (hi, c) ← c.u64 "lirpa upper"
      let (pre, c) ← c.u32 "lirpa preact"
      let (post, c) ← c.u32 "lirpa post"
      let (a, c) ← readRat c "lirpa a"
      let (bq, c) ← readRat c "lirpa b"
      let (al, c) ← readRat c "lirpa alpha"
      let (be, c) ← readRat c "lirpa beta"
      let (ga, c) ← readRat c "lirpa gamma"
      let (de, c) ← readRat c "lirpa delta"
      let (den, _) ← c.u64 "lirpa denBoundLog2"
      if hl : lo < off then
        if hh : hi < off then
          pure (.lirpa (← parseNode ctx lo) (← parseNode ctx hi)
            pre post a bq al be ga de den)
        else throw (.forwardRef "lirpa upper")
      else throw (.forwardRef "lirpa lower")
    | 17 | 18 => do
      variantZero "reluPos/Neg"
      let (pr, c) ← c.u64 "relu premise"
      let (pre, c) ← c.u32 "relu preact"
      let (post, _) ← c.u32 "relu post"
      if hp : pr < off then do
        let premise ← parseNode ctx pr
        if tag == 17 then pure (.reluPos premise pre post)
        else pure (.reluNeg premise pre post)
      else throw (.forwardRef "relu premise")
    | 19 | 20 => do
      variantZero "reluNN/Above"
      let (pre, c) ← c.u32 "relu preact"
      let (post, _) ← c.u32 "relu post"
      if tag == 19 then pure (.reluNN pre post)
      else pure (.reluAbove pre post)
    | 21 => do
      variantZero "cellInInterior"
      let (pr, c) ← c.u64 "cellIn premise"
      let (ai, c) ← c.u32 "cellIn app"
      if ai ≥ ctx.nApps then throw (.badCellRef "cellIn app idx")
      let (wi, _) ← c.u32 "whichI"
      if hp : pr < off then
        pure (.cellInInterior (← parseNode ctx pr) ai wi)
      else throw (.forwardRef "cellIn premise")
    | 22 => do
      variantZero "cellOut"
      let (pr, c) ← c.u64 "cellOut premise"
      let (ai, c) ← c.u32 "cellOut app"
      if ai ≥ ctx.nApps then throw (.badCellRef "cellOut app idx")
      let (wj, c) ← c.u32 "whichJ"
      let (wv, _) ← c.u32 "witnessVertex"
      if hp : pr < off then
        pure (.cellOut (← parseNode ctx pr) ai wj wv)
      else throw (.forwardRef "cellOut premise")
    | 23 => do
      variantZero "eqRefl"
      let (tm, _) ← c.u32 "eqRefl term"
      pure (.eqRefl (← parseTerm ctx.pool tm))
    | 24 => do
      variantZero "eqSym"
      let (pr, c) ← c.u64 "eqSym premise"
      let (tt', c) ← c.u32 "eqSym termT"
      let (tu, _) ← c.u32 "eqSym termU"
      let termT ← parseTerm ctx.pool tt'
      let termU ← parseTerm ctx.pool tu
      if hp : pr < off then
        pure (.eqSym (← parseNode ctx pr) termT termU)
      else throw (.forwardRef "eqSym premise")
    | 25 => do
      variantZero "promise"
      let (sup, c) ← c.u64 "promise supplier"
      let (con, c) ← c.u64 "promise consumer"
      let (cf, c) ← c.u32 "promise contract"
      let contract ← parseFormula ctx.pool ctx.complexes cf
      let (path, c) ← readPath c "promise path step"
      let (ni, c) ← c.u32 "promise iface len"
      let mut iface : List Nat := []
      let mut cc := c
      for _ in [0 : ni] do
        let (w, cc') ← cc.u32 "promise iface wire"
        iface := iface ++ [w]
        cc := cc'
      if hs : sup < off then
        if hc : con < off then
          pure (.promise (← parseNode ctx sup) (← parseNode ctx con)
            contract path iface)
        else throw (.forwardRef "promise consumer")
      else throw (.forwardRef "promise supplier")
    | 26 => do
      variantZero "syzygy"
      let (nc, c) ← c.u32 "syzygy n_components"
      let mut compOffs : List Nat := []
      let mut cc := c
      for _ in [0 : nc] do
        let (co, cc') ← cc.u64 "syzygy component"
        compOffs := compOffs ++ [co]
        cc := cc'
      let (comb, cc1) ← cc.u32 "syzygy combination"
      let (conc, cc2) ← cc1.u32 "syzygy conclusion"
      let (den, cc3) ← cc2.u64 "syzygy denBoundLog2"
      let (th, _) ← cc3.u32 "syzygy theta"
      let combination ← parseTerm ctx.pool comb
      let conclusion ← parseTerm ctx.pool conc
      let theta ← if th == HOLE then pure none
        else some <$>
          (parseThetaAt ctx.pool th "syzygy theta must be a term-const record")
      let components ← parseNodeList ctx off compOffs
      pure (.syzygy components combination conclusion den theta)
    | t => throw (.badTag "node" t)
  pure (.mk concludes node)
termination_by (off, 1, 0)

def parseNodeList (ctx : NodeCtx) (me : Nat) (offs : List Nat) :
    R (List WProof) := do
  match offs with
  | [] => pure []
  | o :: rest =>
    if ho : o < me then do
      let p ← parseNode ctx o
      let ps ← parseNodeList ctx me rest
      pure (p :: ps)
    else throw (.forwardRef "syzygy component")
termination_by (me, 0, offs.length)

def parseBranches (ctx : NodeCtx) (me : Nat)
    (raw : List (Nat × Nat × Nat)) :
    R (List (WSimplexR × WExtSetR × WProof)) := do
  match raw with
  | [] => pure []
  | (bs, be, bp) :: rest =>
    if hb : bp < me then do
      let s ← parseSimplexR ctx.pool ctx.complexes bs
      let e ← parseExtSetR ctx.pool ctx.complexes be
      let p ← parseNode ctx bp
      let ps ← parseBranches ctx me rest
      pure ((s, e, p) :: ps)
    else throw (.forwardRef "branch proof")
termination_by (me, 0, raw.length)

end

def parseWCert (b : ByteArray) : R WCert := do
  let h ← parseHeader b
  let syms ← parseSymtab b h
  let (complexes, apps) ← parseDiagram b h

  let c := Cur.at' b h.proofOff (h.proofOff + h.proofLen)
  let (poolLen, _) ← c.u64 "pool_len"
  if 8 + poolLen > h.proofLen then throw (.sectionOutOfBounds "pool")
  let pool := b.extract (h.proofOff + 8) (h.proofOff + 8 + poolLen)
  let section' := b.extract h.proofOff (h.proofOff + h.proofLen)
  let ctx : NodeCtx := ⟨section', 8 + poolLen, pool, complexes, h.nApps⟩
  let root ← parseNode ctx h.rootNodeOff
  let theta ← if h.thetaRef == HOLE then pure none
    else some <$>
      (parseThetaAt pool h.thetaRef "theta_ref must be a term-const record")
  pure ⟨h, syms, complexes, apps, root, theta⟩

mutual
inductive PTree where
  | mk (concludes : Sequent) (node : PNodeK)

inductive PNodeK where
  | ax
  | weaken (premise : PTree) (extra : Formula)
  | cut (cutFormula : Formula) (left right : PTree)
  | andI (left right : PTree)
  | andE (which : WSide) (premise : PTree) (other : Formula)
  | orI  (which : WSide) (premise : PTree) (other : Formula)
  | orE (left right : PTree) (path : ConjPath)
  | eqElim (eqProof bodyProof : PTree) (wire : Wire)
           (termT termU : Term) (bodyForm : Formula)
  | convIntro (premise : PTree) (term : Term) (simplex : Simplex) (S : ExtensionSet)
  | convElim  (premise : PTree) (term : Term) (simplex : Simplex) (S : ExtensionSet)
  | arithAtom (dir : WSide) (premise : PTree) (termL termR : Term) (b : BowTie)
  | bernCone (regionProof : PTree) (termX : Term) (simplex : Simplex)
             (S : ExtensionSet) (degree : Nat) (polynomial : Term)
             (predicate : Formula)
  | norm (termL termR : Term)
  | farkas (combinationCoeffs conclusion : Term) (denBoundLog2 : Nat)
  | subdivide (regionProof : PTree) (termX : Term) (simplex : Simplex)
              (S : ExtensionSet)
              (branches : List (Simplex × ExtensionSet × PTree))
              (coverCertificate : Term) (denBoundLog2 : Nat)
  | lirpa (lower upper : PTree) (preact post : Wire)
          (a b α β γ δq : Rat) (denBoundLog2 : Nat)
  | reluPos (premise : PTree) (preact post : Wire)
  | reluNeg (premise : PTree) (preact post : Wire)
  | reluNN (preact post : Wire)
  | reluAbove (preact post : Wire)
  | cellInInterior (premise : PTree) (appIdx whichI : Nat)
  | cellOut (premise : PTree) (appIdx whichJ witnessVertex : Nat)
  | eqRefl (term : Term)
  | eqSym (premise : PTree) (termT termU : Term)
  | promise (supplier consumer : PTree) (contract : Formula)
            (path : ConjPath) (iface : List Wire)
  | syzygy (components : List PTree) (combination conclusion : Term)
           (denBoundLog2 : Nat) (theta : Option Rat)
end

def PTree.concludes : PTree → Sequent
  | .mk c _ => c

structure ParsedCert where
  hypernet : Hypernet
  goalPre  : Formula
  goalPost : Formula
  proof    : PTree
  theta    : Option Rat

def elabComplex (idx : Nat) (w : WComplex) : R SimpC := do
  let nv := w.nVertices
  let coord : Fin nv → Fin w.ambDim → Rat :=
    fun v j => w.coords[v.val * w.ambDim + j.val]?.getD 0
  let simplices : List (Fin nv → Bool) :=
    w.simplices.toList.map (fun m v => m[v.val]?.getD false)
  let cells : List ((Fin nv → Bool) × (Fin nv → Bool)) :=
    w.cells.toList.map (fun (sm, em) =>
      (fun v => sm[v.val]?.getD false, fun v => em[v.val]?.getD false))
  if hne : ∀ s ∈ simplices, ∃ v, s v = true then
    if hcl : ∀ s ∈ simplices, ∀ v₀, s v₀ = true →
        (∃ v₁, s v₁ = true ∧ v₁ ≠ v₀) →
        ∃ s' ∈ simplices, ∀ v, s' v = (s v && decide (v ≠ v₀)) then
      if hcf : ∀ s₁ ∈ simplices, ∀ s₂ ∈ simplices,
          (∃ v, s₁ v = true ∧ s₂ v = true) →
          ∃ s' ∈ simplices, ∀ v, s' v = (s₁ v && s₂ v) then
        if hdv : ∀ v₁ v₂ : Fin nv, v₁ ≠ v₂ →
            ∃ j, coord v₁ j ≠ coord v₂ j then
          if hcw : ∀ c ∈ cells, c.1 ∈ simplices ∧
              (∀ v, c.2 v = true → c.1 v = true) ∧
              (∃ v, c.1 v = true ∧ c.2 v = false) then
            pure ⟨nv, w.ambDim, coord, simplices, cells,
                  hne, hcl, hcf, hdv, hcw⟩
          else throw (.complexIllFormed "cellsWF" idx)
        else throw (.complexIllFormed "distinctVerts" idx)
      else throw (.complexIllFormed "conformity" idx)
    else throw (.complexIllFormed "closure" idx)
  else throw (.complexIllFormed "nonempty" idx)

def elabComplexes (ws : Array WComplex) : R (Array SimpC) := do
  let mut out : Array SimpC := #[]
  let mut i := 0
  for w in ws do
    out := out.push (← elabComplex i w)
    i := i + 1
  pure out

def elabSimplex (cxs : Array SimpC) (w : WSimplexR) (what : String) :
    R Simplex := do
  if hcx : w.complex < cxs.size then
    let cx := cxs[w.complex]
    let contains : Fin cx.nVertices → Bool := fun v => w.mask[v.val]?.getD false
    if hne : ∃ v, contains v = true then
      pure ⟨cx, contains, hne⟩
    else throw (.simplexEmpty what)
  else throw (.badCellRef what)

def elabExtSet (cxs : Array SimpC) (w : WExtSetR) (what : String) :
    R ExtensionSet := do
  let s ← elabSimplex cxs w.simplex what
  let contains : Fin s.complex.nVertices → Bool := fun v => w.mask[v.val]?.getD false
  if hsc : ∀ v, contains v = true → s.contains v = true then
    if hpr : ∃ v, s.contains v = true ∧ contains v = false then
      pure ⟨s, contains, hsc, hpr⟩
    else throw (.extSetIllFormed "proper" what)
  else throw (.extSetIllFormed "scope" what)

def elabFormula (cxs : Array SimpC) (sp : Formula) : WFormula → R Formula
  | .atom b l r => pure (.atom b l r)
  | .inRegion t s S => do
    pure (.inRegion t (← elabSimplex cxs s "inRegion simplex")
      (← elabExtSet cxs S "inRegion extset"))
  | .and l r => do pure (.and (← elabFormula cxs sp l) (← elabFormula cxs sp r))
  | .or l r => do pure (.or (← elabFormula cxs sp l) (← elabFormula cxs sp r))
  | .tt => pure .tt
  | .ff => pure .ff
  | .sph => pure sp

def elabJudgment (cxs : Array SimpC) (sp : Formula) (j : WJudgment) :
    R Sequent := do
  pure ⟨← elabFormula cxs sp j.pre, ← elabFormula cxs sp j.post⟩

def mkCarrier (δ : Dtype) (q : Rat) : R δ.carrier := do
  match hk : δ.kind with
  | .bool =>
    if h : (q = 0 ∨ q = 1) ∧ (δ.sign = .nn → 0 ≤ q) then
      pure ⟨.fin q, by
        simp only [Dtype.ValueSet, hk, Kind.MemK]; exact h⟩
    else throw (.valueOutOfSet "bool payload")
  | .int =>
    if h : q.den = 1 ∧ (δ.sign = .nn → 0 ≤ q) then
      pure ⟨.fin q, by
        simp only [Dtype.ValueSet, hk, Kind.MemK]; exact h⟩
    else throw (.valueOutOfSet "int payload")
  | .rat =>
    if h : δ.sign = .nn → 0 ≤ q then
      pure ⟨.fin q, by
        simp only [Dtype.ValueSet, hk, Kind.MemK]; exact ⟨trivial, h⟩⟩
    else throw (.valueOutOfSet "rat payload")
  | .f16 | .bf16 | .f32 | .f64 =>
    throw (.floatConstUnsupported "float tensor payload carrier")

def elabTensorValue (ty : TensorType) (p : WPayload) : R (TensorValue ty) := do
  let qs : List Rat ← match p with
    | .bools bs => pure (bs.map (fun b => if b then (1 : Rat) else 0))
    | .ints vs => pure (vs.map (fun v => mkRat v 1))
    | .rats qs => pure qs
    | .fbits _ _ => throw (.floatConstUnsupported "float tensor payload")
  let vals ← qs.mapM (mkCarrier ty.dtype)
  if h : vals.length = ty.shape.totalSize then
    pure ⟨vals, h⟩
  else throw (.payloadMismatch "payload element count vs shape")

def elabApp (cxs : Array SimpC) (syms : Array WSym) (w : WApp) :
    R PrimApp := do
  match w.kind with
  | .const out => do
    match syms[out]? with
    | none => throw (.badWireId "const out" out)
    | some sym =>
      match sym.payload with
      | none => throw (.payloadMismatch "const wire has no payload")
      | some p => do
        let ty : TensorType := ⟨sym.shape, sym.dtype⟩
        pure (.const ty (← elabTensorValue ty p) out)
  | .contract δ inputs output extents inputBindings outputBinding => do
    let inputRanks : List Nat := inputBindings.map (·.length)
    let nIdx := extents.length
    let indexExtent : Fin nIdx → Nat := fun i => extents.get i

    let rawIn : Nat → Nat → Nat := fun i a => (inputBindings.getD i []).getD a 0
    let rawOut : Nat → Nat := fun a => outputBinding.getD a 0
    if hin : ∀ (i : Fin inputRanks.length) (a : Fin (inputRanks.get i)),
        rawIn i.val a.val < nIdx then
      if hout : ∀ a : Fin outputBinding.length, rawOut a.val < nIdx then
        let pat : ContractPattern inputRanks outputBinding.length :=
          { nIndices := nIdx
            indexExtent := indexExtent
            inputBinding := fun i a => ⟨rawIn i.val a.val, hin i a⟩
            outputBinding := fun a => ⟨rawOut a.val, hout a⟩ }
        pure (.contract δ w.round inputs output inputRanks
          outputBinding.length pat)
      else throw (.badContractPattern "output binding")
    else throw (.badContractPattern "input binding")
  | .cast δfrom δto shape input output =>
    pure (.cast δfrom δto w.round shape input output)
  | .cell cx input outputs => do
    if hcx : cx < cxs.size then
      pure (.cell cxs[cx] input outputs)
    else throw (.badCellRef "cell complex idx")
  | .reshape newShape input output => pure (.reshape newShape input output)
  | .broadcast toShape input output => pure (.broadcast toShape input output)
  | .copy input outputs => pure (.copy outputs.length input outputs)
  | .delete input => pure (.delete input)
  | .swap i1 i2 o1 o2 => pure (.swap i1 i2 o1 o2)
  | .stack inputs output => do

    match syms[output]? with
    | none => throw (.badWireId "stack output" output)
    | some sym =>
      match sym.shape with
      | [] => throw (.typeInconsistent 0)
      | _ :: tail => pure (.stack inputs.length tail inputs output)

def elabHypernet (cxs : Array SimpC) (syms : Array WSym)
    (apps : List WApp) : R Hypernet := do
  let prims ← apps.mapM (elabApp cxs syms)
  let wt : Wire → Option TensorType :=
    fun w => (syms[w]?).map (fun s => ⟨s.shape, s.dtype⟩)
  if hlin : Linearity prims then
    if hacy : Acyclic prims then
      if htc : TypeConsistentAll wt prims then
        pure ⟨wt, prims, hlin, hacy, htc⟩
      else throw (.hypernetIllFormed "typeConsistent")
    else throw (.hypernetIllFormed "acyclic (SSA topological order)")
  else throw (.hypernetIllFormed "linearity")

def elabPath : List WSide → ConjPath
  | [] => .here
  | .left :: rest => .left (elabPath rest)
  | .right :: rest => .right (elabPath rest)

mutual

def elabProof (cxs : Array SimpC) (sp : Formula) : WProof → R PTree
  | .mk concludes node => do
    let seq ← elabJudgment cxs sp concludes
    let k : PNodeK ← elabNodeK cxs sp node
    pure (.mk seq k)

def elabNodeK (cxs : Array SimpC) (sp : Formula) : WNodeK → R PNodeK
  | .ax => pure .ax
  | .weaken premise extra => do
    pure (.weaken (← elabProof cxs sp premise) (← elabFormula cxs sp extra))
  | .cut cutFormula left right => do
    pure (.cut (← elabFormula cxs sp cutFormula)
      (← elabProof cxs sp left) (← elabProof cxs sp right))
  | .andI left right => do
    pure (.andI (← elabProof cxs sp left) (← elabProof cxs sp right))
  | .andE which premise other => do
    pure (.andE which (← elabProof cxs sp premise) (← elabFormula cxs sp other))
  | .orI which premise other => do
    pure (.orI which (← elabProof cxs sp premise) (← elabFormula cxs sp other))
  | .orE left right path => do
    pure (.orE (← elabProof cxs sp left) (← elabProof cxs sp right)
      (elabPath path))
  | .eqElim eqProof bodyProof wire termT termU bodyForm => do
    pure (.eqElim (← elabProof cxs sp eqProof) (← elabProof cxs sp bodyProof)
      wire termT termU (← elabFormula cxs sp bodyForm))
  | .convIntro premise term s S => do
    pure (.convIntro (← elabProof cxs sp premise) term
      (← elabSimplex cxs s "convIntro simplex")
      (← elabExtSet cxs S "convIntro extset"))
  | .convElim premise term s S => do
    pure (.convElim (← elabProof cxs sp premise) term
      (← elabSimplex cxs s "convElim simplex")
      (← elabExtSet cxs S "convElim extset"))
  | .arithAtom dir premise termL termR b => do
    pure (.arithAtom dir (← elabProof cxs sp premise) termL termR b)
  | .bernCone regionProof termX s S degree polynomial predicate => do
    pure (.bernCone (← elabProof cxs sp regionProof) termX
      (← elabSimplex cxs s "bernCone simplex")
      (← elabExtSet cxs S "bernCone extset")
      degree polynomial (← elabFormula cxs sp predicate))
  | .norm termL termR => pure (.norm termL termR)
  | .farkas combinationCoeffs conclusion denBoundLog2 =>
    pure (.farkas combinationCoeffs conclusion denBoundLog2)
  | .subdivide regionProof termX s S branches cover denBoundLog2 => do
    let rp ← elabProof cxs sp regionProof
    let bs ← elabBranches cxs sp branches
    pure (.subdivide rp termX
      (← elabSimplex cxs s "subdivide simplex")
      (← elabExtSet cxs S "subdivide extset")
      bs cover denBoundLog2)
  | .lirpa lower upper preact post a b al be ga de den => do
    pure (.lirpa (← elabProof cxs sp lower) (← elabProof cxs sp upper)
      preact post a b al be ga de den)
  | .reluPos premise preact post => do
    pure (.reluPos (← elabProof cxs sp premise) preact post)
  | .reluNeg premise preact post => do
    pure (.reluNeg (← elabProof cxs sp premise) preact post)
  | .reluNN preact post => pure (.reluNN preact post)
  | .reluAbove preact post => pure (.reluAbove preact post)
  | .cellInInterior premise appIdx whichI => do
    pure (.cellInInterior (← elabProof cxs sp premise) appIdx whichI)
  | .cellOut premise appIdx whichJ witnessVertex => do
    pure (.cellOut (← elabProof cxs sp premise) appIdx whichJ witnessVertex)
  | .eqRefl term => pure (.eqRefl term)
  | .eqSym premise termT termU => do
    pure (.eqSym (← elabProof cxs sp premise) termT termU)
  | .promise supplier consumer contract path iface => do
    pure (.promise (← elabProof cxs sp supplier) (← elabProof cxs sp consumer)
      (← elabFormula cxs sp contract) (elabPath path) iface)
  | .syzygy components combination conclusion denBoundLog2 theta => do
    let comps ← elabProofList cxs sp components
    pure (.syzygy comps combination conclusion denBoundLog2 theta)

def elabProofList (cxs : Array SimpC) (sp : Formula) :
    List WProof → R (List PTree)
  | [] => pure []
  | p :: rest => do
    pure ((← elabProof cxs sp p) :: (← elabProofList cxs sp rest))

def elabBranches (cxs : Array SimpC) (sp : Formula) :
    List (WSimplexR × WExtSetR × WProof) →
    R (List (Simplex × ExtensionSet × PTree))
  | [] => pure []
  | (s, e, p) :: rest => do
    let s' ← elabSimplex cxs s "branch simplex"
    let e' ← elabExtSet cxs e "branch extset"
    let p' ← elabProof cxs sp p
    pure ((s', e', p') :: (← elabBranches cxs sp rest))

end

def elabWCert (w : WCert) : R ParsedCert := do
  let cxs ← elabComplexes w.complexes
  let H ← elabHypernet cxs w.syms w.apps

  if !(H.wireType predicateHole).isNone then throw .holeNotFresh
  let sp := H.spConjunction

  match w.root with
  | .mk concludes _ =>
    match concludes.pre with
    | .and phi .sph => do
      if phi.hasSph || concludes.post.hasSph then
        throw (.sphInIllegalPosition "root")
      let goalPre ← elabFormula cxs sp phi
      let goalPost ← elabFormula cxs sp concludes.post
      let proof ← elabProof cxs sp w.root
      pure ⟨H, goalPre, goalPost, proof, w.theta⟩
    | _ => throw (.rootShape "pre must be and(Φ, sph)")

def parseCertificate (b : ByteArray) : R ParsedCert := do
  elabWCert (← parseWCert b)

end Wire
end PPLC
