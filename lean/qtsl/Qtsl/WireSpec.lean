import Qtsl.Wire

/-!
# The wire-format encoding relation

`Encodes b c` is the declarative reading of the binary format
specification: a relation between certificate bytes and the parser's
wire model, transcribed clause-by-clause from the specification tables
— deliberately not from the parser's control flow, so transcription
errors in the two artefacts are decorrelated and the refinement
theorem can catch either. The refinement theorem `parseWCert_sound` —
every successful parse satisfies the encoding relation — closes the
module.
-/

namespace PPLC
namespace Wire
namespace Spec

def sliceIs (b : ByteArray) (p : Nat) (bs : List UInt8) : Prop :=
  p + bs.length ≤ b.size ∧ (b.extract p (p + bs.length)).toList = bs

def uleAt (b : ByteArray) (p n v : Nat) : Prop :=
  ∃ bs, sliceIs b p bs ∧ bs.length = n ∧ bytesToNatLE bs = v

abbrev u8At  (b : ByteArray) (p v : Nat) : Prop := uleAt b p 1 v
abbrev u16At (b : ByteArray) (p v : Nat) : Prop := uleAt b p 2 v
abbrev u32At (b : ByteArray) (p v : Nat) : Prop := uleAt b p 4 v
abbrev u64At (b : ByteArray) (p v : Nat) : Prop := uleAt b p 8 v

def ratAt (b : ByteArray) (p : Nat) (q : Rat) (p' : Nat) : Prop :=
  ∃ nb db : List UInt8,
    u32At b p nb.length ∧
    u32At b (p + 4) db.length ∧
    sliceIs b (p + 8) nb ∧
    sliceIs b (p + 8 + nb.length) db ∧
    signedMinimal nb = true ∧
    unsignedMinimal db = true ∧
    q.num = bytesToIntLE nb ∧
    (q.den : Nat) = bytesToNatLE db ∧
    Nat.gcd q.num.natAbs q.den = 1 ∧
    p' = p + 8 + nb.length + db.length

inductive ratsAt (b : ByteArray) : Nat → List Rat → Nat → Prop where
  | nil (p : Nat) : ratsAt b p [] p
  | cons (p : Nat) (q : Rat) (p₁ : Nat) (qs : List Rat) (p₂ : Nat) :
      ratAt b p q p₁ → ratsAt b p₁ qs p₂ → ratsAt b p (q :: qs) p₂

def maskAt (b : ByteArray) (p n : Nat) (mask : Array Bool) (p' : Nat) : Prop :=
  ∃ bs : List UInt8,
    sliceIs b p bs ∧ bs.length = (n + 7) / 8 ∧
    mask.size = n ∧
    (∀ i, i < n →
      mask.getD i false = ((((bs.getD (i / 8) 0).toNat >>> (i % 8)) &&& 1) == 1)) ∧
    (∀ i, n ≤ i → i < 8 * bs.length →
      (((bs.getD (i / 8) 0).toNat >>> (i % 8)) &&& 1) = 0) ∧
    p' = p + (n + 7) / 8

def kindCode : Kind → Nat
  | .bool => 0 | .int => 1 | .rat => 2
  | .f16 => 3 | .bf16 => 4 | .f32 => 5 | .f64 => 6

def signCode : Sign → Nat
  | .nn => 0 | .signed => 1

def extCode : Ext → Nat
  | .fin => 0 | .ext => 1

def dtypeAt (b : ByteArray) (p : Nat) (δ : Dtype) : Prop :=
  u8At b p (kindCode δ.kind) ∧ u8At b (p+1) (signCode δ.sign) ∧
  u8At b (p+2) (extCode δ.ext) ∧ u8At b (p+3) 0

def bowtieCode : BowTie → Nat
  | .lt => 0 | .le => 1 | .eq => 2 | .ge => 3 | .gt => 4 | .ne => 5

def roundCode : RoundMode → Nat
  | .rne => 0 | .rtz => 1 | .rup => 2 | .rdn => 3 | .exact => 4

def sideCode : WSide → Nat
  | .left => 0 | .right => 1

def u32sAt (b : ByteArray) (p : Nat) (vs : List Nat) (p' : Nat) : Prop :=
  (∀ i, i < vs.length → u32At b (p + 4 * i) (vs.getD i 0)) ∧
  p' = p + 4 * vs.length

def u64sAt (b : ByteArray) (p : Nat) (vs : List Nat) (p' : Nat) : Prop :=
  (∀ i, i < vs.length → u64At b (p + 8 * i) (vs.getD i 0)) ∧
  p' = p + 8 * vs.length

def pathAt (b : ByteArray) (p : Nat) (steps : List WSide) (p' : Nat) : Prop :=
  u32At b p steps.length ∧
  (∀ i, i < steps.length →
    u8At b (p + 4 + i) (sideCode (steps.getD i .left))) ∧
  p' = p + 4 + steps.length

structure HeaderAt (b : ByteArray) (h : WHeader) : Prop where
  size        : 128 ≤ b.size
  magic       : sliceIs b 0 MAGIC
  version     : u32At b 8 1
  flags       : u32At b 12 0
  symtabOff   : u64At b 16 h.symtabOff
  symtabLen   : u64At b 24 h.symtabLen
  payloadOff  : u64At b 32 h.payloadOff
  payloadLen  : u64At b 40 h.payloadLen
  diagramOff  : u64At b 48 h.diagramOff
  diagramLen  : u64At b 56 h.diagramLen
  proofOff    : u64At b 64 h.proofOff
  proofLen    : u64At b 72 h.proofLen
  nWires      : u32At b 80 h.nWires
  nApps       : u32At b 84 h.nApps
  nProofNodes : u32At b 88 h.nProofNodes
  nComplexes  : u32At b 92 h.nComplexes
  rootNodeOff : u64At b 96 h.rootNodeOff
  thetaRef    : u32At b 104 h.thetaRef
  reserved    : ∀ i, i < 20 → u8At b (108 + i) 0

  sections    : 128 ≤ h.symtabOff ∧
                h.symtabOff + h.symtabLen ≤ h.payloadOff ∧
                h.payloadOff + h.payloadLen ≤ h.diagramOff ∧
                h.diagramOff + h.diagramLen ≤ h.proofOff ∧
                h.proofOff + h.proofLen ≤ b.size
  holeGuard   : h.nWires < HOLE
  payloadAligned : h.payloadOff % 64 = 0

def payloadAt (b : ByteArray) (dt : Dtype) (shape : List Nat)
    (off len : Nat) : WPayload → Prop
  | .bools bs =>
    dt.kind = .bool ∧ bs.length = Shape.totalSize shape ∧
    len = (bs.length + 7) / 8 ∧
    maskAt b off bs.length ⟨bs⟩ (off + len)
  | .ints vs =>
    dt.kind = .int ∧ vs.length = Shape.totalSize shape ∧
    len = 8 * vs.length ∧
    (∀ i, i < vs.length →
      ∃ raw, u64At b (off + 8 * i) raw ∧
        vs.getD i 0 = (match dt.sign with
          | .nn => (raw : Int)
          | .signed => if raw < 2 ^ 63 then (raw : Int)
                       else (raw : Int) - 2 ^ 64))
  | .rats qs =>
    dt.kind = .rat ∧ qs.length = Shape.totalSize shape ∧
    ∀ i, i < qs.length →
      ∃ o e, u32At b (off + 4 * i) o ∧
        ratAt b (off + o) (qs.getD i 0) e ∧ e ≤ off + len
  | .fbits k bits =>
    dt.kind = k ∧ bits.length = Shape.totalSize shape ∧
    ∃ w expMask manMask,
      (match k with
       | .f16  => (w, expMask, manMask) = (2, 0x7C00, 0x03FF)
       | .bf16 => (w, expMask, manMask) = (2, 0x7F80, 0x007F)
       | .f32  => (w, expMask, manMask) = (4, 0x7F800000, 0x007FFFFF)
       | .f64  => (w, expMask, manMask) = (8, 0x7FF0000000000000, 0x000FFFFFFFFFFFFF)
       | _ => False) ∧
      len = w * bits.length ∧
      ∀ i, i < bits.length →
        uleAt b (off + w * i) w (bits.getD i 0) ∧
        ¬((bits.getD i 0) &&& expMask = expMask ∧ (bits.getD i 0) &&& manMask ≠ 0)

def symAt (b : ByteArray) (h : WHeader) (i : Nat) (s : WSym) : Prop :=
  let base := h.symtabOff + 32 * i
  dtypeAt b base s.dtype ∧
  u32At b (base + 4) s.shape.length ∧
  (∃ shapeOff,
    u64At b (base + 8) shapeOff ∧
    32 * h.nWires ≤ shapeOff ∧
    shapeOff + 8 * s.shape.length ≤ h.symtabLen ∧
    u64sAt b (h.symtabOff + shapeOff) s.shape
      (h.symtabOff + shapeOff + 8 * s.shape.length)) ∧
  (match s.payload with
   | none =>
     u64At b (base + 16) U64_MAX ∧ u64At b (base + 24) 0
   | some p =>
     ∃ off len,
       u64At b (base + 16) off ∧ u64At b (base + 24) len ∧
       off % 64 = 0 ∧
       h.payloadOff ≤ off ∧ off + len ≤ h.payloadOff + h.payloadLen ∧
       payloadAt b s.dtype s.shape off len p)

def symtabAt (b : ByteArray) (h : WHeader) (syms : Array WSym) : Prop :=
  syms.size = h.nWires ∧
  32 * h.nWires ≤ h.symtabLen ∧
  ∀ i, i < h.nWires → symAt b h i (syms.getD i ⟨Dtype.Q, [], none⟩)

inductive masksAt (b : ByteArray) (n : Nat) :
    Nat → List (Array Bool) → Nat → Prop where
  | nil (p : Nat) : masksAt b n p [] p
  | cons (p : Nat) (m : Array Bool) (p₁ : Nat) (ms : List (Array Bool))
      (p₂ : Nat) :
      maskAt b p n m p₁ → masksAt b n p₁ ms p₂ →
      masksAt b n p (m :: ms) p₂

inductive maskPairsAt (b : ByteArray) (n : Nat) :
    Nat → List (Array Bool × Array Bool) → Nat → Prop where
  | nil (p : Nat) : maskPairsAt b n p [] p
  | cons (p : Nat) (sm em : Array Bool) (p₁ p₂ : Nat)
      (ms : List (Array Bool × Array Bool)) (p₃ : Nat) :
      maskAt b p n sm p₁ → maskAt b p₁ n em p₂ →
      maskPairsAt b n p₂ ms p₃ →
      maskPairsAt b n p ((sm, em) :: ms) p₃

def complexAt (b : ByteArray) (p : Nat) (w : WComplex) (p' : Nat) : Prop :=
  ∃ p₁ p₂ p₃,
    u32At b p w.nVertices ∧
    u32At b (p + 4) w.ambDim ∧
    w.coords.size = w.nVertices * w.ambDim ∧
    ratsAt b (p + 8) w.coords.toList p₁ ∧
    u32At b p₁ w.simplices.size ∧
    masksAt b w.nVertices (p₁ + 4) w.simplices.toList p₂ ∧
    u32At b p₂ w.cells.size ∧
    maskPairsAt b w.nVertices (p₂ + 4) w.cells.toList p₃ ∧
    p' = p₃

inductive complexesAt (b : ByteArray) :
    Nat → List WComplex → Nat → Prop where
  | nil (p : Nat) : complexesAt b p [] p
  | cons (p : Nat) (w : WComplex) (p₁ : Nat) (ws : List WComplex)
      (p₂ : Nat) :
      complexAt b p w p₁ → complexesAt b p₁ ws p₂ →
      complexesAt b p (w :: ws) p₂

def appAt (b : ByteArray) (nWires : Nat) (cxs : List WComplex)
    (p : Nat) (a : WApp) (p' : Nat) : Prop :=
  u8At b (p+1) (roundCode a.round) ∧
  u16At b (p+2) 0 ∧
  (match a.kind with
   | .const out =>
     u8At b p 0 ∧ a.round = .exact ∧
     out < nWires ∧ u32At b (p+4) out ∧ p' = p + 8
   | .contract δ inputs output extents inputBindings outputBinding =>
     u8At b p 1 ∧
     dtypeAt b (p+4) δ ∧
     u32At b (p+8) inputs.length ∧
     (∀ w ∈ inputs, w < nWires) ∧
     (∃ p₁ p₂ p₃,
       u32sAt b (p+12) inputs p₁ ∧
       u32At b p₁ output ∧ output < nWires ∧
       u32At b (p₁+4) extents.length ∧
       u64sAt b (p₁+8) extents p₂ ∧
       inputBindings.length = inputs.length ∧
       bindingsAt b extents.length p₂ inputBindings p₃ ∧
       u32At b p₃ outputBinding.length ∧
       (∀ x ∈ outputBinding, x < extents.length) ∧
       u32sAt b (p₃+4) outputBinding p' )
   | .cast δfrom δto shape input output =>
     u8At b p 2 ∧
     dtypeAt b (p+4) δfrom ∧ dtypeAt b (p+8) δto ∧
     u32At b (p+12) shape.length ∧
     (∃ p₁, u64sAt b (p+16) shape p₁ ∧
       u32At b p₁ input ∧ input < nWires ∧
       u32At b (p₁+4) output ∧ output < nWires ∧
       p' = p₁ + 8)
   | .cell complex input outputs =>
     u8At b p 3 ∧ a.round = .exact ∧
     u32At b (p+4) complex ∧ complex < cxs.length ∧
     u32At b (p+8) input ∧ input < nWires ∧
     u32At b (p+12) outputs.length ∧
     outputs.length = (cxs.getD complex ⟨0,0,#[],#[],#[]⟩).cells.size ∧
     (∀ w ∈ outputs, w < nWires) ∧
     u32sAt b (p+16) outputs p'
   | .reshape newShape input output =>
     u8At b p 4 ∧ a.round = .exact ∧
     u32At b (p+4) newShape.length ∧
     (∃ p₁, u64sAt b (p+8) newShape p₁ ∧
       u32At b p₁ input ∧ input < nWires ∧
       u32At b (p₁+4) output ∧ output < nWires ∧ p' = p₁ + 8)
   | .broadcast toShape input output =>
     u8At b p 5 ∧ a.round = .exact ∧
     u32At b (p+4) toShape.length ∧
     (∃ p₁, u64sAt b (p+8) toShape p₁ ∧
       u32At b p₁ input ∧ input < nWires ∧
       u32At b (p₁+4) output ∧ output < nWires ∧ p' = p₁ + 8)
   | .copy input outputs =>
     u8At b p 6 ∧ a.round = .exact ∧
     u32At b (p+4) outputs.length ∧
     u32At b (p+8) input ∧ input < nWires ∧
     (∀ w ∈ outputs, w < nWires) ∧
     u32sAt b (p+12) outputs p'
   | .delete input =>
     u8At b p 7 ∧ a.round = .exact ∧
     u32At b (p+4) input ∧ input < nWires ∧ p' = p + 8
   | .swap i1 i2 o1 o2 =>
     u8At b p 8 ∧ a.round = .exact ∧
     u32At b (p+4) i1 ∧ u32At b (p+8) i2 ∧
     u32At b (p+12) o1 ∧ u32At b (p+16) o2 ∧
     i1 < nWires ∧ i2 < nWires ∧ o1 < nWires ∧ o2 < nWires ∧
     p' = p + 20
   | .stack inputs output =>
     u8At b p 9 ∧ a.round = .exact ∧
     u32At b (p+4) inputs.length ∧
     (∀ w ∈ inputs, w < nWires) ∧
     (∃ p₁, u32sAt b (p+8) inputs p₁ ∧
       u32At b p₁ output ∧ output < nWires ∧ p' = p₁ + 4))
where

  bindingsAt (b : ByteArray) (nIndices : Nat) :
      Nat → List (List Nat) → Nat → Prop
    | p, [], p' => p' = p
    | p, row :: rest, p' =>
      u32At b p row.length ∧ (∀ x ∈ row, x < nIndices) ∧
      ∃ p₁, u32sAt b (p+4) row p₁ ∧ bindingsAt b nIndices p₁ rest p'

inductive appsAt (b : ByteArray) (nWires : Nat) (cxs : List WComplex) :
    Nat → List WApp → Nat → Prop where
  | nil (p : Nat) : appsAt b nWires cxs p [] p
  | cons (p : Nat) (a : WApp) (p₁ : Nat) (as' : List WApp) (p₂ : Nat) :
      appAt b nWires cxs p a p₁ → appsAt b nWires cxs p₁ as' p₂ →
      appsAt b nWires cxs p (a :: as') p₂

def diagramAt (b : ByteArray) (h : WHeader) (cxs : List WComplex)
    (apps : List WApp) : Prop :=
  ∃ p₁ p₂,
    u32At b h.diagramOff cxs.length ∧ cxs.length = h.nComplexes ∧
    complexesAt b (h.diagramOff + 4) cxs p₁ ∧
    u32At b p₁ apps.length ∧ apps.length = h.nApps ∧
    appsAt b (h.nWires) cxs (p₁ + 4) apps p₂ ∧
    p₂ ≤ h.diagramOff + h.diagramLen

def cxWidth (cxs : List WComplex) (i : Nat) : Nat :=
  (cxs.getD i ⟨0, 0, #[], #[], #[]⟩).nVertices

inductive termAt (pool : ByteArray) : Nat → Term → Prop where
  | var (off w : Nat) :
      u8At pool off 0x01 → u32At pool (off+1) w →
      termAt pool off (.var w)
  | const (off : Nat) (q : Rat) (e : Nat) :
      u8At pool off 0x02 → ratAt pool (off+1) q e →
      termAt pool off (.const q)
  | add (off l r : Nat) (tl tr : Term) :
      u8At pool off 0x03 → u32At pool (off+1) l → u32At pool (off+5) r →
      l < off → r < off → termAt pool l tl → termAt pool r tr →
      termAt pool off (.add tl tr)
  | mul (off l r : Nat) (tl tr : Term) :
      u8At pool off 0x04 → u32At pool (off+1) l → u32At pool (off+5) r →
      l < off → r < off → termAt pool l tl → termAt pool r tr →
      termAt pool off (.mul tl tr)
  | sub (off l r : Nat) (tl tr : Term) :
      u8At pool off 0x05 → u32At pool (off+1) l → u32At pool (off+5) r →
      l < off → r < off → termAt pool l tl → termAt pool r tr →
      termAt pool off (.sub tl tr)
  | neg (off t : Nat) (tt' : Term) :
      u8At pool off 0x06 → u32At pool (off+1) t →
      t < off → termAt pool t tt' →
      termAt pool off (.neg tt')
  | idx (off t i : Nat) (tt' : Term) :
      u8At pool off 0x07 → u32At pool (off+1) t → u32At pool (off+5) i →
      t < off → termAt pool t tt' →
      termAt pool off (.idx tt' i)

def simplexAt (pool : ByteArray) (cxs : List WComplex) (off : Nat)
    (s : WSimplexR) : Prop :=
  u8At pool off 0x10 ∧ u32At pool (off+1) s.complex ∧
  s.complex < cxs.length ∧
  ∃ e, maskAt pool (off+5) (cxWidth cxs s.complex) s.mask e

def extSetAt (pool : ByteArray) (cxs : List WComplex) (off : Nat)
    (S : WExtSetR) : Prop :=
  u8At pool off 0x11 ∧
  ∃ so, u32At pool (off+1) so ∧ so < off ∧
    simplexAt pool cxs so S.simplex ∧
    ∃ e, maskAt pool (off+5) (cxWidth cxs S.simplex.complex) S.mask e

inductive formulaAt (pool : ByteArray) (cxs : List WComplex) :
    Nat → WFormula → Prop where
  | atom (off : Nat) (bt : BowTie) (l r : Nat) (tl tr : Term) :
      u8At pool off 0x20 → u8At pool (off+1) (bowtieCode bt) →
      u32At pool (off+2) l → u32At pool (off+6) r →
      l < off → r < off → termAt pool l tl → termAt pool r tr →
      formulaAt pool cxs off (.atom bt tl tr)
  | inRegion (off t s e : Nat) (tt' : Term) (sr : WSimplexR) (er : WExtSetR) :
      u8At pool off 0x21 →
      u32At pool (off+1) t → u32At pool (off+5) s → u32At pool (off+9) e →
      t < off → s < off → e < off →
      termAt pool t tt' → simplexAt pool cxs s sr → extSetAt pool cxs e er →
      formulaAt pool cxs off (.inRegion tt' sr er)
  | and (off l r : Nat) (fl fr : WFormula) :
      u8At pool off 0x22 → u32At pool (off+1) l → u32At pool (off+5) r →
      l < off → r < off →
      formulaAt pool cxs l fl → formulaAt pool cxs r fr →
      formulaAt pool cxs off (.and fl fr)
  | or (off l r : Nat) (fl fr : WFormula) :
      u8At pool off 0x23 → u32At pool (off+1) l → u32At pool (off+5) r →
      l < off → r < off →
      formulaAt pool cxs l fl → formulaAt pool cxs r fr →
      formulaAt pool cxs off (.or fl fr)
  | tt (off : Nat) : u8At pool off 0x24 → formulaAt pool cxs off .tt
  | ff (off : Nat) : u8At pool off 0x25 → formulaAt pool cxs off .ff
  | sph (off : Nat) : u8At pool off 0x26 → formulaAt pool cxs off .sph

def judgmentAt (pool : ByteArray) (cxs : List WComplex) (off : Nat)
    (j : WJudgment) : Prop :=
  u8At pool off 0x30 ∧
  ∃ pre post, u32At pool (off+1) pre ∧ u32At pool (off+5) post ∧
    pre < off ∧ post < off ∧
    formulaAt pool cxs pre j.pre ∧ formulaAt pool cxs post j.post ∧
    j.post.hasSph = false

mutual

inductive nodeAt (sec pool : ByteArray) (base : Nat) (cxs : List WComplex)
    (nApps : Nat) : Nat → WProof → Prop where
  | ax (off cj : Nat) (j : WJudgment) :
      base ≤ off →
      u8At sec off 0 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      nodeAt sec pool base cxs nApps off (.mk j .ax)
  | weaken (off cj pr ex : Nat) (j : WJudgment) (p : WProof) (extra : WFormula) :
      base ≤ off →
      u8At sec off 1 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) ex →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      formulaAt pool cxs ex extra →
      nodeAt sec pool base cxs nApps off (.mk j (.weaken p extra))
  | cut (off cj cf l r : Nat) (j : WJudgment) (cutF : WFormula) (pl pr' : WProof) :
      base ≤ off →
      u8At sec off 2 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) cf → formulaAt pool cxs cf cutF →
      u64At sec (off+12) l → u64At sec (off+20) r →
      l < off → r < off →
      nodeAt sec pool base cxs nApps l pl →
      nodeAt sec pool base cxs nApps r pr' →
      nodeAt sec pool base cxs nApps off (.mk j (.cut cutF pl pr'))
  | andI (off cj l r : Nat) (j : WJudgment) (pl pr' : WProof) :
      base ≤ off →
      u8At sec off 3 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) l → u64At sec (off+16) r →
      l < off → r < off →
      nodeAt sec pool base cxs nApps l pl →
      nodeAt sec pool base cxs nApps r pr' →
      nodeAt sec pool base cxs nApps off (.mk j (.andI pl pr'))
  | andE (off cj pr ot : Nat) (j : WJudgment) (which : WSide) (p : WProof)
      (other : WFormula) :
      base ≤ off →
      u8At sec off 4 → u8At sec (off+1) (sideCode which) →
      u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) ot →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      formulaAt pool cxs ot other →
      nodeAt sec pool base cxs nApps off (.mk j (.andE which p other))
  | orI (off cj pr ot : Nat) (j : WJudgment) (which : WSide) (p : WProof)
      (other : WFormula) :
      base ≤ off →
      u8At sec off 5 → u8At sec (off+1) (sideCode which) →
      u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) ot →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      formulaAt pool cxs ot other →
      nodeAt sec pool base cxs nApps off (.mk j (.orI which p other))
  | orE (off cj l r : Nat) (j : WJudgment) (pl pr' : WProof)
      (path : List WSide) (pe : Nat) :
      base ≤ off →
      u8At sec off 6 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) l → u64At sec (off+16) r →
      pathAt sec (off+24) path pe →
      l < off → r < off →
      nodeAt sec pool base cxs nApps l pl →
      nodeAt sec pool base cxs nApps r pr' →
      nodeAt sec pool base cxs nApps off (.mk j (.orE pl pr' path))
  | eqElim (off cj ep bp w tt' tu bf : Nat) (j : WJudgment)
      (pe pb : WProof) (termT termU : Term) (bodyForm : WFormula) :
      base ≤ off →
      u8At sec off 7 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) ep → u64At sec (off+16) bp →
      u32At sec (off+24) w → u32At sec (off+28) tt' →
      u32At sec (off+32) tu → u32At sec (off+36) bf →
      ep < off → bp < off →
      nodeAt sec pool base cxs nApps ep pe →
      nodeAt sec pool base cxs nApps bp pb →
      termAt pool tt' termT → termAt pool tu termU →
      formulaAt pool cxs bf bodyForm →
      nodeAt sec pool base cxs nApps off
        (.mk j (.eqElim pe pb w termT termU bodyForm))
  | convIntro (off cj pr tm sp es : Nat) (j : WJudgment) (p : WProof)
      (term : Term) (s : WSimplexR) (S : WExtSetR) :
      base ≤ off →
      u8At sec off 8 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) tm →
      u32At sec (off+20) sp → u32At sec (off+24) es →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      termAt pool tm term → simplexAt pool cxs sp s → extSetAt pool cxs es S →
      nodeAt sec pool base cxs nApps off (.mk j (.convIntro p term s S))
  | convElim (off cj pr tm sp es : Nat) (j : WJudgment) (p : WProof)
      (term : Term) (s : WSimplexR) (S : WExtSetR) :
      base ≤ off →
      u8At sec off 9 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) tm →
      u32At sec (off+20) sp → u32At sec (off+24) es →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      termAt pool tm term → simplexAt pool cxs sp s → extSetAt pool cxs es S →
      nodeAt sec pool base cxs nApps off (.mk j (.convElim p term s S))
  | arithAtom (off cj pr tl tr : Nat) (j : WJudgment) (dir : WSide)
      (p : WProof) (termL termR : Term) (bt : BowTie) :
      base ≤ off →
      u8At sec off 10 → u8At sec (off+1) (sideCode dir) →
      u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) tl → u32At sec (off+20) tr →
      u8At sec (off+24) (bowtieCode bt) →
      bowtieCode bt ≤ 4 →
      u8At sec (off+25) 0 → u8At sec (off+26) 0 → u8At sec (off+27) 0 →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      termAt pool tl termL → termAt pool tr termR →
      nodeAt sec pool base cxs nApps off (.mk j (.arithAtom dir p termL termR bt))
  | bernCone (off cj rp tx sp es deg poly pred : Nat) (j : WJudgment)
      (p : WProof) (termX polynomial : Term) (s : WSimplexR) (S : WExtSetR)
      (predicate : WFormula) :
      base ≤ off →
      u8At sec off 11 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) rp → u32At sec (off+16) tx →
      u32At sec (off+20) sp → u32At sec (off+24) es →
      u32At sec (off+28) deg → u32At sec (off+32) poly →
      u32At sec (off+36) pred →
      rp < off → nodeAt sec pool base cxs nApps rp p →
      termAt pool tx termX → simplexAt pool cxs sp s → extSetAt pool cxs es S →
      termAt pool poly polynomial → formulaAt pool cxs pred predicate →
      nodeAt sec pool base cxs nApps off
        (.mk j (.bernCone p termX s S deg polynomial predicate))
  | norm (off cj tl tr : Nat) (j : WJudgment) (termL termR : Term) :
      base ≤ off →
      u8At sec off 12 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) tl → u32At sec (off+12) tr →
      termAt pool tl termL → termAt pool tr termR →
      nodeAt sec pool base cxs nApps off (.mk j (.norm termL termR))
  | farkas (off cj cc k den : Nat) (j : WJudgment)
      (combinationCoeffs conclusion : Term) :
      base ≤ off →
      u8At sec off 14 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) cc → u32At sec (off+12) k → u64At sec (off+16) den →
      termAt pool cc combinationCoeffs → termAt pool k conclusion →
      nodeAt sec pool base cxs nApps off
        (.mk j (.farkas combinationCoeffs conclusion den))
  | subdivide (off cj rp tx sp es cov den pe : Nat) (j : WJudgment)
      (p : WProof) (termX cover : Term) (s : WSimplexR) (S : WExtSetR)
      (branches : List (WSimplexR × WExtSetR × WProof)) :
      base ≤ off →
      u8At sec off 15 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) rp → u32At sec (off+16) tx →
      u32At sec (off+20) sp → u32At sec (off+24) es →
      u32At sec (off+28) branches.length →
      branchesAt sec pool base cxs nApps off (off+32) branches pe →
      u32At sec pe cov → u64At sec (pe+4) den →
      rp < off → nodeAt sec pool base cxs nApps rp p →
      termAt pool tx termX → simplexAt pool cxs sp s → extSetAt pool cxs es S →
      termAt pool cov cover →
      nodeAt sec pool base cxs nApps off
        (.mk j (.subdivide p termX s S branches cover den))
  | lirpa (off cj lo hi pre post den p₁ p₂ p₃ p₄ p₅ p₆ : Nat) (j : WJudgment)
      (pLo pHi : WProof) (a bq al be ga de : Rat) :
      base ≤ off →
      u8At sec off 16 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) lo → u64At sec (off+16) hi →
      u32At sec (off+24) pre → u32At sec (off+28) post →
      ratAt sec (off+32) a p₁ → ratAt sec p₁ bq p₂ →
      ratAt sec p₂ al p₃ → ratAt sec p₃ be p₄ →
      ratAt sec p₄ ga p₅ → ratAt sec p₅ de p₆ →
      u64At sec p₆ den →
      lo < off → hi < off →
      nodeAt sec pool base cxs nApps lo pLo →
      nodeAt sec pool base cxs nApps hi pHi →
      nodeAt sec pool base cxs nApps off
        (.mk j (.lirpa pLo pHi pre post a bq al be ga de den))
  | reluPos (off cj pr pre post : Nat) (j : WJudgment) (p : WProof) :
      base ≤ off →
      u8At sec off 17 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) pre → u32At sec (off+20) post →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      nodeAt sec pool base cxs nApps off (.mk j (.reluPos p pre post))
  | reluNeg (off cj pr pre post : Nat) (j : WJudgment) (p : WProof) :
      base ≤ off →
      u8At sec off 18 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) pre → u32At sec (off+20) post →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      nodeAt sec pool base cxs nApps off (.mk j (.reluNeg p pre post))
  | reluNN (off cj pre post : Nat) (j : WJudgment) :
      base ≤ off →
      u8At sec off 19 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) pre → u32At sec (off+12) post →
      nodeAt sec pool base cxs nApps off (.mk j (.reluNN pre post))
  | reluAbove (off cj pre post : Nat) (j : WJudgment) :
      base ≤ off →
      u8At sec off 20 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) pre → u32At sec (off+12) post →
      nodeAt sec pool base cxs nApps off (.mk j (.reluAbove pre post))
  | cellInInterior (off cj pr ai wi : Nat) (j : WJudgment) (p : WProof) :
      base ≤ off →
      u8At sec off 21 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) ai → u32At sec (off+20) wi →
      ai < nApps →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      nodeAt sec pool base cxs nApps off (.mk j (.cellInInterior p ai wi))
  | cellOut (off cj pr ai wj wv : Nat) (j : WJudgment) (p : WProof) :
      base ≤ off →
      u8At sec off 22 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) ai →
      u32At sec (off+20) wj → u32At sec (off+24) wv →
      ai < nApps →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      nodeAt sec pool base cxs nApps off (.mk j (.cellOut p ai wj wv))
  | eqRefl (off cj tm : Nat) (j : WJudgment) (term : Term) :
      base ≤ off →
      u8At sec off 23 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) tm → termAt pool tm term →
      nodeAt sec pool base cxs nApps off (.mk j (.eqRefl term))
  | eqSym (off cj pr tt' tu : Nat) (j : WJudgment) (p : WProof)
      (termT termU : Term) :
      base ≤ off →
      u8At sec off 24 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) pr → u32At sec (off+16) tt' → u32At sec (off+20) tu →
      pr < off → nodeAt sec pool base cxs nApps pr p →
      termAt pool tt' termT → termAt pool tu termU →
      nodeAt sec pool base cxs nApps off (.mk j (.eqSym p termT termU))
  | promise (off cj sup con cf pe : Nat) (j : WJudgment)
      (pSup pCon : WProof) (contract : WFormula) (path : List WSide)
      (iface : List Nat) :
      base ≤ off →
      u8At sec off 25 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u64At sec (off+8) sup → u64At sec (off+16) con →
      u32At sec (off+24) cf → formulaAt pool cxs cf contract →
      pathAt sec (off+28) path pe →
      u32At sec pe iface.length →
      u32sAt sec (pe+4) iface (pe + 4 + 4 * iface.length) →
      sup < off → con < off →
      nodeAt sec pool base cxs nApps sup pSup →
      nodeAt sec pool base cxs nApps con pCon →
      nodeAt sec pool base cxs nApps off
        (.mk j (.promise pSup pCon contract path iface))
  | syzygy (off cj comb conc den th : Nat) (j : WJudgment)
      (compOffs : List Nat) (components : List WProof)
      (combination conclusion : Term) (theta : Option Rat) :
      base ≤ off →
      u8At sec off 26 → u8At sec (off+1) 0 → u16At sec (off+2) 0 →
      u32At sec (off+4) cj → judgmentAt pool cxs cj j →
      u32At sec (off+8) compOffs.length →
      u64sAt sec (off+12) compOffs (off + 12 + 8 * compOffs.length) →
      u32At sec (off + 12 + 8 * compOffs.length) comb →
      u32At sec (off + 16 + 8 * compOffs.length) conc →
      u64At sec (off + 20 + 8 * compOffs.length) den →
      u32At sec (off + 28 + 8 * compOffs.length) th →
      (∀ o ∈ compOffs, o < off) →
      componentsAt sec pool base cxs nApps compOffs components →
      termAt pool comb combination → termAt pool conc conclusion →
      (match theta with
       | none => th = HOLE
       | some q => th ≠ HOLE ∧ ∃ e, u8At pool th 0x02 ∧ ratAt pool (th+1) q e) →
      nodeAt sec pool base cxs nApps off
        (.mk j (.syzygy components combination conclusion den theta))

inductive branchesAt (sec pool : ByteArray) (base : Nat)
    (cxs : List WComplex) (nApps : Nat) :
    Nat → Nat → List (WSimplexR × WExtSetR × WProof) → Nat → Prop where
  | nil (me p : Nat) : branchesAt sec pool base cxs nApps me p [] p
  | cons (me p bs be bp : Nat)
      (s : WSimplexR) (S : WExtSetR) (child : WProof)
      (rest : List (WSimplexR × WExtSetR × WProof)) (p' : Nat) :
      u32At sec p bs → u32At sec (p+4) be → u64At sec (p+8) bp →
      bp < me →
      simplexAt pool cxs bs s → extSetAt pool cxs be S →
      nodeAt sec pool base cxs nApps bp child →
      branchesAt sec pool base cxs nApps me (p+16) rest p' →
      branchesAt sec pool base cxs nApps me p ((s, S, child) :: rest) p'

inductive componentsAt (sec pool : ByteArray) (base : Nat)
    (cxs : List WComplex) (nApps : Nat) :
    List Nat → List WProof → Prop where
  | nil : componentsAt sec pool base cxs nApps [] []
  | cons (o : Nat) (p : WProof) (os : List Nat) (ps : List WProof) :
      nodeAt sec pool base cxs nApps o p →
      componentsAt sec pool base cxs nApps os ps →
      componentsAt sec pool base cxs nApps (o :: os) (p :: ps)

end

/-- The declarative encoding relation between certificate bytes and the
parsed wire model. -/
def Encodes (b : ByteArray) (c : WCert) : Prop :=
  HeaderAt b c.header ∧
  symtabAt b c.header c.syms ∧
  diagramAt b c.header c.complexes.toList c.apps ∧
  ∃ poolLen : Nat,
    u64At b c.header.proofOff poolLen ∧
    8 + poolLen ≤ c.header.proofLen ∧

    (let sec := b.extract c.header.proofOff
        (c.header.proofOff + c.header.proofLen)
     let pool := b.extract (c.header.proofOff + 8)
        (c.header.proofOff + 8 + poolLen)
     nodeAt sec pool (8 + poolLen) c.complexes.toList c.header.nApps
       c.header.rootNodeOff c.root ∧
     (match c.theta with
      | none => c.header.thetaRef = HOLE
      | some q => c.header.thetaRef ≠ HOLE ∧
          ∃ e, u8At pool c.header.thetaRef 0x02 ∧
            ratAt pool (c.header.thetaRef + 1) q e))

section Soundness

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem strongNat {P : Nat → Prop} (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have aux : ∀ N n, n < N → P n := by
    intro N
    induction N with
    | zero => intro n h; omega
    | succ N ih => intro n h; exact step n (fun m hm => ih m (by omega))
  exact fun n => aux (n + 1) n (Nat.lt_succ_self n)

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  show Except.bind x f = .ok b ↔ _
  cases x <;> simp [Except.bind]

theorem pure_eq_ok {ε α : Type} {a b : α} :
    (pure a : Except ε α) = .ok b ↔ a = b := by
  show Except.ok a = .ok b ↔ _
  simp

theorem throw_ne_ok {ε α : Type} {e : ε} {b : α} :
    (throw e : Except ε α) = .ok b ↔ False := by
  show Except.error e = .ok b ↔ _
  simp

theorem map_eq_ok {ε α β : Type} {g : α → β} {x : Except ε α} {b : β} :
    g <$> x = .ok b ↔ ∃ a, x = .ok a ∧ g a = b := by
  show Except.map g x = .ok b ↔ _
  cases x <;> simp [Except.map]

theorem ok_eq_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    .ok b = x >>= f ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  rw [eq_comm]; exact bind_eq_ok

theorem ok_eq_pure {ε α : Type} {a b : α} :
    .ok b = (pure a : Except ε α) ↔ a = b := by
  rw [eq_comm]; exact pure_eq_ok

theorem ok_eq_throw {ε α : Type} {e : ε} {b : α} :
    .ok b = (throw e : Except ε α) ↔ False := by
  rw [eq_comm]; exact throw_ne_ok

theorem ok_eq_map {ε α β : Type} {g : α → β} {x : Except ε α} {b : β} :
    .ok b = g <$> x ↔ ∃ a, x = .ok a ∧ g a = b := by
  rw [eq_comm]; exact map_eq_ok

theorem ite_eq_ok {ε α : Type} {p : Prop} [Decidable p] {t e : Except ε α} {v : α} :
    (if p then t else e) = .ok v ↔ (p ∧ t = .ok v) ∨ (¬p ∧ e = .ok v) := by
  by_cases h : p <;> simp [h]

theorem dite_eq_ok {ε α : Type} {p : Prop} [Decidable p]
    {t : p → Except ε α} {e : ¬p → Except ε α} {v : α} :
    (dite p t e) = .ok v ↔ (∃ h, t h = .ok v) ∨ (∃ h, e h = .ok v) := by
  by_cases h : p <;> simp [h]

theorem forIn_list_inv {α β : Type} {body : α → β → R (ForInStep β)}
    (I : β → List α → Prop)
    (step : ∀ x rest b, I b (x :: rest) →
       ∀ r, body x b = .ok r → ∃ b', r = .yield b' ∧ I b' rest) :
    ∀ {xs : List α} {init res : β}, I init xs → forIn xs init body = .ok res → I res [] := by
  intro xs
  induction xs with
  | nil =>
    intro init res h0 hrun
    rw [List.forIn_nil, pure_eq_ok] at hrun
    exact hrun ▸ h0
  | cons x xs ih =>
    intro init res h0 hrun
    rw [List.forIn_cons, bind_eq_ok] at hrun
    obtain ⟨s, hs, hrest⟩ := hrun
    obtain ⟨b', rfl, hI⟩ := step x xs init h0 s hs
    exact ih hI hrest

theorem forIn_range_eq (n : Nat) {β : Type} (init : β) (body : Nat → β → R (ForInStep β)) :
    forIn [0:n] init body = forIn (List.range' 0 n 1) init body := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

theorem forIn_range2_eq (s m : Nat) {β : Type} (init : β) (body : Nat → β → R (ForInStep β)) :
    forIn [s:m] init body = forIn (List.range' s (m - s) 1) init body := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

theorem getD_append_lt {α : Type} (l : List α) (a d : α) (i : Nat) (h : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem get!_bridge (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  obtain ⟨bs⟩ := a
  by_cases h : i < bs.size
  · show bs[i]! = (ByteArray.mk bs)[i]!
    rw [getElem!_pos bs i h, getElem!_pos (ByteArray.mk bs) i h]
    rfl
  · show bs[i]! = (ByteArray.mk bs)[i]!
    rw [getElem!_neg bs i h, getElem!_neg (ByteArray.mk bs) i h]

theorem toList_loop_eq (a : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), a.size - i = k →
    ByteArray.toList.loop a i r
      = r.reverse ++ ((List.range' i k 1).map fun j => a[j]!) := by
  intro k
  induction k with
  | zero =>
    intro i r h
    unfold ByteArray.toList.loop
    have hn : ¬ i < a.size := by omega
    simp [hn, List.range']
  | succ k ih =>
    intro i r h
    unfold ByteArray.toList.loop
    have hi : i < a.size := by omega
    rw [if_pos hi, ih (i + 1) (a.get! i :: r) (by omega), List.range'_succ]
    simp [get!_bridge]

theorem toList_eq (a : ByteArray) :
    a.toList = (List.range' 0 a.size 1).map (fun j => a[j]!) := by
  unfold ByteArray.toList
  rw [toList_loop_eq a a.size 0 [] (by omega)]
  simp

theorem extract_toList {b : ByteArray} {p n : Nat} (h : p + n ≤ b.size) :
    (b.extract p (p + n)).toList = (List.range' 0 n 1).map (fun i => b[p + i]!) := by
  have hs : (b.extract p (p + n)).size = n := by
    rw [ByteArray.size_extract]; omega
  rw [toList_eq, hs]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range'_1] at hi
  have h1 : i < (b.extract p (p + n)).size := by omega
  have h2 : p + i < b.size := by omega
  rw [getElem!_pos _ i h1, getElem!_pos b (p + i) h2, ByteArray.getElem_extract]

theorem sliceIs_getD {b : ByteArray} {p : Nat} {bs : List UInt8}
    (hs : sliceIs b p bs) {i : Nat} (hi : i < bs.length) :
    bs.getD i 0 = b[p + i]! := by
  obtain ⟨hb, he⟩ := hs
  have h1 : bs = (List.range' 0 bs.length 1).map (fun j => b[p + j]!) := by
    rw [← extract_toList (p := p) (n := bs.length) (by omega), he]
  calc bs.getD i 0
      = ((List.range' 0 bs.length 1).map (fun j => b[p + j]!)).getD i 0 := by rw [← h1]
    _ = b[p + i]! := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem (by simp [hi])]
        simp [List.getElem_range']

theorem sliceIs_index {b : ByteArray} {p : Nat} {bs : List UInt8}
    (hs : sliceIs b p bs) {i : Nat} (hi : i < bs.length) :
    u8At b (p + i) ((bs.getD i 0).toNat) := by
  have hb := hs.1
  refine ⟨[bs.getD i 0], ⟨by simp; omega, ?_⟩, rfl, by simp [bytesToNatLE]⟩
  show (b.extract (p + i) ((p + i) + 1)).toList = [bs.getD i 0]
  rw [extract_toList (by omega), sliceIs_getD hs hi]
  simp [List.range']

theorem take_ok {b : ByteArray} {p s : Nat} {n : Nat} {w : String} {bs : List UInt8} {c' : Cur}
    (h : Cur.take ⟨b, p, s⟩ n w = .ok (bs, c')) :
    sliceIs b p bs ∧ bs.length = n ∧
    c' = ⟨b, p + n, s⟩ ∧ p + n ≤ s ∧ p + n ≤ b.size := by
  unfold Cur.take at h
  simp only [letFun] at h
  split at h
  · simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at h
  · rename_i hguard
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    obtain ⟨hstop, hsize⟩ := hguard
    simp only [pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨hbs, hc'⟩ := h
    have hlen : bs.length = n := by rw [← hbs]; simp
    refine ⟨⟨by omega, ?_⟩, hlen, hc'.symm, by omega, by omega⟩
    rw [hlen, extract_toList (by omega), ← hbs, List.range_eq_range']

theorem uLE_ok {b : ByteArray} {p s : Nat} {n : Nat} {w : String} {v : Nat} {c' : Cur}
    (h : Cur.uLE ⟨b, p, s⟩ n w = .ok (v, c')) :
    uleAt b p n v ∧
    c' = ⟨b, p + n, s⟩ ∧ p + n ≤ s ∧ p + n ≤ b.size := by
  unfold Cur.uLE at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨bs, c₁⟩, htake, h⟩ := h
  simp only [pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨hv, hc⟩ := h
  obtain ⟨hslice, hlen, hc₁, hstop, hsize⟩ := take_ok htake
  subst hc
  exact ⟨⟨bs, hslice, hlen, hv⟩, hc₁, hstop, hsize⟩

theorem u8_ok {b : ByteArray} {p s : Nat} {w : String} {v : Nat} {c' : Cur}
    (h : Cur.u8 ⟨b, p, s⟩ w = .ok (v, c')) :
    u8At b p v ∧
    c' = ⟨b, p + 1, s⟩ ∧ p + 1 ≤ s ∧ p + 1 ≤ b.size := by
  unfold Cur.u8 at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨bs, c₁⟩, htake, h⟩ := h
  simp only [pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨hv, hc⟩ := h
  obtain ⟨hslice, hlen, hc₁, hstop, hsize⟩ := take_ok htake
  subst hc
  obtain ⟨x, rfl⟩ : ∃ x, bs = [x] := by
    match bs, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  refine ⟨⟨[x], hslice, hlen, ?_⟩, hc₁, hstop, hsize⟩
  simp [bytesToNatLE] at hv ⊢
  omega

theorem u16_ok {b : ByteArray} {p s : Nat} {w : String} {v : Nat} {c' : Cur}
    (h : Cur.u16 ⟨b, p, s⟩ w = .ok (v, c')) :
    u16At b p v ∧
    c' = ⟨b, p + 2, s⟩ ∧ p + 2 ≤ s ∧ p + 2 ≤ b.size :=
  uLE_ok h

theorem u32_ok {b : ByteArray} {p s : Nat} {w : String} {v : Nat} {c' : Cur}
    (h : Cur.u32 ⟨b, p, s⟩ w = .ok (v, c')) :
    u32At b p v ∧
    c' = ⟨b, p + 4, s⟩ ∧ p + 4 ≤ s ∧ p + 4 ≤ b.size :=
  uLE_ok h

theorem u64_ok {b : ByteArray} {p s : Nat} {w : String} {v : Nat} {c' : Cur}
    (h : Cur.u64 ⟨b, p, s⟩ w = .ok (v, c')) :
    u64At b p v ∧
    c' = ⟨b, p + 8, s⟩ ∧ p + 8 ≤ s ∧ p + 8 ≤ b.size :=
  uLE_ok h

theorem kindOf_ok {k : Nat} {w : String} {κ : Kind} (h : kindOf k w = .ok κ) :
    kindCode κ = k := by
  unfold kindOf at h
  split at h <;> simp [pure_eq_ok, throw_ne_ok] at h <;> subst h <;> rfl

theorem signOf_ok {s : Nat} {w : String} {σ : Sign} (h : signOf s w = .ok σ) :
    signCode σ = s := by
  unfold signOf at h
  split at h <;> simp [pure_eq_ok, throw_ne_ok] at h <;> subst h <;> rfl

theorem extOf_ok {e : Nat} {w : String} {ε : Ext} (h : extOf e w = .ok ε) :
    extCode ε = e := by
  unfold extOf at h
  split at h <;> simp [pure_eq_ok, throw_ne_ok] at h <;> subst h <;> rfl

theorem bowtieOf_ok {v : Nat} {w : String} {bt : BowTie} (h : bowtieOf v w = .ok bt) :
    bowtieCode bt = v := by
  unfold bowtieOf at h
  split at h <;> simp [pure_eq_ok, throw_ne_ok] at h <;> subst h <;> rfl

theorem roundOf_ok {v : Nat} {w : String} {r : RoundMode} (h : roundOf v w = .ok r) :
    roundCode r = v := by
  unfold roundOf at h
  split at h <;> simp [pure_eq_ok, throw_ne_ok] at h <;> subst h <;> rfl

theorem readDtype_ok {b : ByteArray} {p s : Nat} {w : String} {δ : Dtype} {c' : Cur}
    (h : readDtype ⟨b, p, s⟩ w = .ok (δ, c')) :
    dtypeAt b p δ ∧
    c' = ⟨b, p + 4, s⟩ ∧ p + 4 ≤ s ∧ p + 4 ≤ b.size := by
  unfold readDtype at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨k, c₁, hk, sv, c₂, hs, e, c₃, he, pad, c₄, hpad, hpad0, κ, hκ, σ, hσ, ε, hε, hδ, hc'⟩ := h
  obtain ⟨hkAt, rfl, _, _⟩ := u8_ok hk
  obtain ⟨hsAt, rfl, _, _⟩ := u8_ok hs
  obtain ⟨heAt, rfl, _, _⟩ := u8_ok he
  obtain ⟨hpAt, rfl, hst, hsz⟩ := u8_ok hpad
  subst hδ; subst hpad0
  refine ⟨⟨?_, ?_, ?_, hpAt⟩, hc'.symm, by omega, by omega⟩
  · show u8At b p (kindCode κ); rw [kindOf_ok hκ]; exact hkAt
  · show u8At b (p + 1) (signCode σ); rw [signOf_ok hσ]; exact hsAt
  · show u8At b (p + 2) (extCode ε); rw [extOf_ok hε]; exact heAt

theorem readRat_ok {b : ByteArray} {p s : Nat} {w : String} {q : Rat} {c' : Cur}
    (h : readRat ⟨b, p, s⟩ w = .ok (q, c')) :
    ∃ e, ratAt b p q e ∧ c' = ⟨b, e, s⟩ ∧
      p + 8 ≤ e ∧ e ≤ s ∧ e ≤ b.size := by
  unfold readRat at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨nlen, c₁, hnlen, dlen, c₂, hdlen, nb, c₃, hnb, db, c₄, hdb,
          ⟨hminS, hminU⟩, hden0, hgcd, ⟨hnum, hden⟩, hq, hc'⟩ := h
  obtain ⟨hnlenAt, rfl, _, _⟩ := u32_ok hnlen
  obtain ⟨hdlenAt, rfl, _, _⟩ := u32_ok hdlen
  obtain ⟨hnbS, hnbL, rfl, _, _⟩ := take_ok hnb
  obtain ⟨hdbS, hdbL, rfl, hstop, hsize⟩ := take_ok hdb
  subst hq
  refine ⟨p + 8 + nb.length + db.length,
    ⟨nb, db, ?_, ?_, hnbS, ?_, hminS, hminU, hnum, hden, ?_, rfl⟩, ?_, by omega, by omega, by omega⟩
  · rw [hnbL]; exact hnlenAt
  · rw [hdbL]; exact hdlenAt
  · rw [hnbL]; exact hdbS
  · rw [hnum, hden]; exact hgcd
  · rw [← hc']
    simp [Cur.mk.injEq]
    omega

theorem forall_getD_append {α : Type} {P : Nat → α → Prop} {l : List α} {x d : α}
    (hl : ∀ j, j < l.length → P j (l.getD j d)) (hx : P l.length x) :
    ∀ j, j < (l ++ [x]).length → P j ((l ++ [x]).getD j d) := by
  intro j hj
  simp at hj
  rcases Nat.lt_or_ge j l.length with hlt | hge
  · rw [getD_append_lt _ _ _ _ hlt]; exact hl j hlt
  · have hj' : j = l.length := by omega
    subst hj'
    rw [getD_append_len]
    exact hx

theorem forall_mem_append {α : Type} {P : α → Prop} {l : List α} {x : α}
    (hl : ∀ y ∈ l, P y) (hx : P x) : ∀ y ∈ l ++ [x], P y := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hl y h
  · rw [List.mem_singleton.mp h]; exact hx

theorem forIn_check_all {α : Type} {P : α → Prop} {body : α → PUnit → R (ForInStep PUnit)}
    (hbody : ∀ x u r, body x u = .ok r → P x ∧ r = .yield PUnit.unit) :
    ∀ {xs : List α} {res : PUnit}, forIn xs PUnit.unit body = .ok res → ∀ x ∈ xs, P x := by
  intro xs
  induction xs with
  | nil => intro res h x hx; simp at hx
  | cons y ys ih =>
    intro res h x hx
    rw [List.forIn_cons, bind_eq_ok] at h
    obtain ⟨s, hs, hrest⟩ := h
    obtain ⟨hP, rfl⟩ := hbody _ _ _ hs
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hP
    · exact ih hrest x hx'

theorem bytesToNatLE_cons (y : UInt8) (l : List UInt8) :
    bytesToNatLE (y :: l) = bytesToNatLE l * 256 + y.toNat := rfl

theorem bytesToNatLE_append (l : List UInt8) (x : UInt8) :
    bytesToNatLE (l ++ [x]) = bytesToNatLE l + x.toNat * 256 ^ l.length := by
  induction l with
  | nil => simp [bytesToNatLE]
  | cons y t ih =>
    rw [List.cons_append, bytesToNatLE_cons, bytesToNatLE_cons, ih,
        Nat.add_mul, List.length_cons, Nat.pow_succ, ← Nat.mul_assoc]
    omega

theorem bytesToNatLE_lt (l : List UInt8) : bytesToNatLE l < 256 ^ l.length := by
  induction l with
  | nil => simp [bytesToNatLE]
  | cons y t ih =>
    have hy : y.toNat < 256 := y.toNat_lt_size
    rw [bytesToNatLE_cons, List.length_cons, Nat.pow_succ]
    omega

theorem bytesToIntLE_eq8 {l : List UInt8} (h : l.length = 8) :
    bytesToIntLE l = if bytesToNatLE l < 2 ^ 63 then (bytesToNatLE l : Int)
      else (bytesToNatLE l : Int) - 2 ^ 64 := by
  obtain ⟨f, top, rfl⟩ : ∃ f top, l = f ++ [top] := by
    match l, h with
    | x :: t, _ =>
      exact ⟨(x :: t).dropLast, (x :: t).getLast (by simp),
        (List.dropLast_concat_getLast (by simp)).symm⟩
  have hlen : f.length = 7 := by simp at h; omega
  have hB := bytesToNatLE_append f top
  have hBl := bytesToNatLE_lt f
  rw [hlen] at hB hBl
  have hstep : bytesToIntLE (f ++ [top])
      = if top.toNat ≥ 0x80 then ((bytesToNatLE (f ++ [top]) : Int)) - (256 : Int) ^ (f ++ [top]).length
        else (bytesToNatLE (f ++ [top]) : Int) := by
    unfold bytesToIntLE
    rw [List.getLast?_concat]
  rw [hstep, h]
  have c1 : (256 : Nat) ^ 7 = 72057594037927936 := by decide
  have c2 : (256 : Int) ^ (8 : Nat) = 18446744073709551616 := by decide
  have c3 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have c4 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  rw [c1] at hB
  rw [c2, c3, c4]
  split <;> split <;> omega

theorem toArray_getBang (bs : List UInt8) (j : Nat) : bs.toArray[j]! = bs.getD j 0 := by
  by_cases hj : j < bs.length
  · rw [getElem!_pos bs.toArray j (by simpa using hj), List.getElem_toArray,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp
  · rw [getElem!_neg bs.toArray j (by simpa using hj),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem getD_map_range {β : Type} (f : Nat → β) (n i : Nat) (hi : i < n) (d : β) :
    ((Array.range n).map f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp [Array.getElem_map, Array.getElem_range]

theorem readMask_ok {b : ByteArray} {p s : Nat} {n : Nat} {w : String} {m : Array Bool} {c' : Cur}
    (h : readMask ⟨b, p, s⟩ n w = .ok (m, c')) :
    maskAt b p n m (p + (n + 7) / 8) ∧
    c' = ⟨b, p + (n + 7) / 8, s⟩ ∧ p + (n + 7) / 8 ≤ s ∧ p + (n + 7) / 8 ≤ b.size := by
  unfold readMask at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨bs, c₁⟩, htake, h⟩ := h
  obtain ⟨hslice, hlen, rfl, hstop, hsize⟩ := take_ok htake
  simp only [bind_eq_ok] at h
  obtain ⟨u, hloop, h⟩ := h
  simp only [pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨hm, hc'⟩ := h
  rw [forIn_range2_eq] at hloop
  have hpad := forIn_check_all
    (P := fun i => ¬((((bs.toArray[i / 8]!).toNat >>> (i % 8)) &&& 1 == 1) = true))
    (fun x u r hb => by
      split at hb
      · simp [bind_eq_ok, map_eq_ok, throw_ne_ok] at hb
      · rename_i hcond
        simp only [pure_eq_ok] at hb
        exact ⟨hcond, hb.symm⟩) hloop
  have harr : ∀ j, bs.toArray[j]! = bs.getD j 0 := toArray_getBang bs
  refine ⟨⟨bs, hslice, hlen, ?_, ?_, ?_, rfl⟩, hc'.symm, hstop, hsize⟩
  · rw [← hm]; simp
  · intro i hi
    rw [← hm, getD_map_range _ _ _ hi, harr]
  · intro i hni hi8
    have hmem : i ∈ List.range' n (bs.toArray.size * 8 - n) 1 := by
      rw [List.mem_range'_1]
      simp only [List.size_toArray]
      constructor
      · exact hni
      · omega
    have := hpad i hmem
    rw [harr] at this
    simp only [beq_iff_eq] at this
    have hle : ((bs.getD (i / 8) 0).toNat >>> (i % 8)) &&& 1 ≤ 1 := Nat.and_le_right
    omega

theorem readPath_ok {b : ByteArray} {p s : Nat} {w : String} {steps : List WSide} {c' : Cur}
    (h : readPath ⟨b, p, s⟩ w = .ok (steps, c')) :
    pathAt b p steps (p + 4 + steps.length) ∧
    c' = ⟨b, p + 4 + steps.length, s⟩ ∧ p + 4 + steps.length ≤ s ∧ p + 4 + steps.length ≤ b.size := by
  unfold readPath at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨n, c₁⟩, hn, h⟩ := h
  obtain ⟨hnAt, rfl, hst4, hsz4⟩ := u32_ok hn
  simp only [bind_eq_ok] at h
  obtain ⟨⟨stepsA, cend⟩, hloop, h⟩ := h
  simp only [pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨hsteps, hcend⟩ := h
  rw [forIn_range_eq] at hloop
  have hinv := forIn_list_inv (I := fun (st : List WSide × Cur) rest =>
      st.2 = (⟨b, p + 4 + st.1.length, s⟩ : Cur) ∧
      st.1.length + rest.length = n ∧
      (∀ i, i < st.1.length → u8At b (p + 4 + i) (sideCode (st.1.getD i .left))) ∧
      p + 4 + st.1.length ≤ s ∧ p + 4 + st.1.length ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨acc, cc⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨hcc, hcnt, hAt, hstp, hszp⟩ := hI
      subst hcc
      simp only [bind_eq_ok] at hbody
      obtain ⟨⟨sv, c₂⟩, hu8v, hmatch⟩ := hbody
      obtain ⟨hsvAt, rfl, hst', hsz'⟩ := u8_ok hu8v
      dsimp only [] at hmatch
      split at hmatch
      · simp only [pure_eq_ok] at hmatch
        refine ⟨_, hmatch.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun j v => u8At b (p + 4 + j) (sideCode v)) hAt hsvAt,
          by simp <;> omega, by simp <;> omega⟩
      · simp only [pure_eq_ok] at hmatch
        refine ⟨_, hmatch.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun j v => u8At b (p + 4 + j) (sideCode v)) hAt hsvAt,
          by simp <;> omega, by simp <;> omega⟩
      · simp [bind_eq_ok, map_eq_ok, throw_ne_ok] at hmatch)
    (by
      refine ⟨rfl, by simp, by simp, by simpa using hst4, by simpa using hsz4⟩)
    hloop
  obtain ⟨hcendEq, hcnt0, hAt, hbs, hbsz⟩ := hinv
  have hlen : stepsA.length = n := by simpa using hcnt0
  have hnAt' : u32At b p stepsA.length := by rw [hlen]; exact hnAt
  rw [← hsteps, ← hcend]
  exact ⟨⟨hnAt', hAt, rfl⟩, hcendEq, hbs, hbsz⟩

theorem parseTerm_sound (pool : ByteArray) :
    ∀ off t, parseTerm pool off = .ok t → termAt pool off t := by
  refine strongNat (P := fun off => ∀ t, parseTerm pool off = .ok t → termAt pool off t) ?_
  intro off ih t h
  unfold parseTerm at h
  simp [bind_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok, map_eq_ok] at h
  obtain ⟨hoff, tag, c₁, hu8, h⟩ := h
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok hu8
  split at h
  ·
    simp [map_eq_ok, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨w', ⟨c₂, hw⟩, ht⟩ := h
    obtain ⟨hwAt, rfl, _, _⟩ := u32_ok hw
    subst ht
    exact termAt.var off w' htagAt hwAt
  ·
    simp [map_eq_ok, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨q', ⟨c₂, hq⟩, ht⟩ := h
    obtain ⟨e, hrat, rfl, _, _, _⟩ := readRat_ok hq
    subst ht
    exact termAt.const off q' e htagAt hrat
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨l, c₂, hl, r, ⟨c₃, hr⟩, hlo, hro, lt, hlt, rt, hrt, ht⟩ := h
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst ht
    exact termAt.add off l r lt rt htagAt hlAt hrAt hlo hro (ih l hlo lt hlt) (ih r hro rt hrt)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨l, c₂, hl, r, ⟨c₃, hr⟩, hlo, hro, lt, hlt, rt, hrt, ht⟩ := h
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst ht
    exact termAt.mul off l r lt rt htagAt hlAt hrAt hlo hro (ih l hlo lt hlt) (ih r hro rt hrt)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨l, c₂, hl, r, ⟨c₃, hr⟩, hlo, hro, lt, hlt, rt, hrt, ht⟩ := h
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst ht
    exact termAt.sub off l r lt rt htagAt hlAt hrAt hlo hro (ih l hlo lt hlt) (ih r hro rt hrt)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨tOff, ⟨c₂, hu⟩, hlt, tt', htt, ht⟩ := h
    obtain ⟨htAt, rfl, _, _⟩ := u32_ok hu
    subst ht
    exact termAt.neg off tOff tt' htagAt htAt hlt (ih tOff hlt tt' htt)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨tOff, c₂, hu, i, ⟨c₃, hi⟩, hlt, tt', htt, ht⟩ := h
    obtain ⟨htAt, rfl, _, _⟩ := u32_ok hu
    obtain ⟨hiAt, rfl, _, _⟩ := u32_ok hi
    subst ht
    exact termAt.idx off tOff i tt' htagAt htAt hiAt hlt (ih tOff hlt tt' htt)
  ·
    simp [throw_ne_ok] at h

theorem cxWidth_toList (cxs : Array WComplex) {i : Nat} (hi : i < cxs.size) :
    cxWidth cxs.toList i = cxs[i].nVertices := by
  unfold cxWidth
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem hi]
  simp

theorem parseSimplexR_sound (pool : ByteArray) (cxs : Array WComplex) (off : Nat) {sr : WSimplexR}
    (h : parseSimplexR pool cxs off = .ok sr) : simplexAt pool cxs.toList off sr := by
  unfold parseSimplexR at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
  obtain ⟨hoff, tag, c₁, hu8, htag, cx, c₂, hcx32, hcxlt, mask, ⟨c₃, hmask⟩, hsr⟩ := h
  subst htag
  subst hsr
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok hu8
  obtain ⟨hcxAt, rfl, _, _⟩ := u32_ok hcx32
  obtain ⟨hmaskAt, rfl, _, _⟩ := readMask_ok hmask
  refine ⟨htagAt, hcxAt, by simpa using hcxlt, ?_⟩
  have hw : cxWidth cxs.toList (WSimplexR.mk cx mask).complex = cxs[cx].nVertices :=
    cxWidth_toList cxs hcxlt
  rw [hw]
  exact ⟨_, hmaskAt⟩

theorem parseExtSetR_sound (pool : ByteArray) (cxs : Array WComplex) (off : Nat) {er : WExtSetR}
    (h : parseExtSetR pool cxs off = .ok er) : extSetAt pool cxs.toList off er := by
  unfold parseExtSetR at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
  obtain ⟨hoff, tag, c₁, hu8, htag, so, c₂, hso32, hsolt, sr, hsr, hcxlt, mask, ⟨c₃, hmask⟩, her⟩ := h
  subst htag
  subst her
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok hu8
  obtain ⟨hsoAt, rfl, _, _⟩ := u32_ok hso32
  obtain ⟨hmaskAt, rfl, _, _⟩ := readMask_ok hmask
  refine ⟨htagAt, so, hsoAt, hsolt, parseSimplexR_sound pool cxs so hsr, ?_⟩
  have hw : cxWidth cxs.toList (WExtSetR.mk sr mask).simplex.complex = cxs[sr.complex].nVertices :=
    cxWidth_toList cxs hcxlt
  rw [hw]
  exact ⟨_, hmaskAt⟩

theorem parseFormula_sound (pool : ByteArray) (cxs : Array WComplex) :
    ∀ off f, parseFormula pool cxs off = .ok f → formulaAt pool cxs.toList off f := by
  refine strongNat (P := fun off => ∀ f, parseFormula pool cxs off = .ok f →
    formulaAt pool cxs.toList off f) ?_
  intro off ih f h
  unfold parseFormula at h
  simp [bind_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok, map_eq_ok] at h
  obtain ⟨hoff, tag, c₁, hu8, h⟩ := h
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok hu8
  split at h
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨bv, c₂, hbv, bt, hbt, l, c₃, hl, r, ⟨c₄, hr⟩, hlo, hro, tl, htl, tr, htr, hf⟩ := h
    obtain ⟨hbvAt, rfl, _, _⟩ := u8_ok hbv
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst hf
    have hbvAt' : u8At pool (off + 1) (bowtieCode bt) := by rw [bowtieOf_ok hbt]; exact hbvAt
    exact formulaAt.atom off bt l r tl tr htagAt hbvAt' hlAt hrAt hlo hro
      (parseTerm_sound pool l tl htl) (parseTerm_sound pool r tr htr)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨t, c₂, ht32, so, c₃, hs32, eo, ⟨c₄, he32⟩, hto, hso, heo, tt', htt, sr, hsr, er, her, hf⟩ := h
    obtain ⟨htAt, rfl, _, _⟩ := u32_ok ht32
    obtain ⟨hsAt, rfl, _, _⟩ := u32_ok hs32
    obtain ⟨heAt, rfl, _, _⟩ := u32_ok he32
    subst hf
    exact formulaAt.inRegion off t so eo tt' sr er htagAt htAt hsAt heAt hto hso heo
      (parseTerm_sound pool t tt' htt) (parseSimplexR_sound pool cxs so hsr)
      (parseExtSetR_sound pool cxs eo her)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨l, c₂, hl, r, ⟨c₃, hr⟩, hlo, hro, fl, hfl, fr, hfr, hf⟩ := h
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst hf
    exact formulaAt.and off l r fl fr htagAt hlAt hrAt hlo hro
      (ih l hlo fl hfl) (ih r hro fr hfr)
  ·
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
    obtain ⟨l, c₂, hl, r, ⟨c₃, hr⟩, hlo, hro, fl, hfl, fr, hfr, hf⟩ := h
    obtain ⟨hlAt, rfl, _, _⟩ := u32_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u32_ok hr
    subst hf
    exact formulaAt.or off l r fl fr htagAt hlAt hrAt hlo hro
      (ih l hlo fl hfl) (ih r hro fr hfr)
  ·
    simp [pure_eq_ok] at h
    subst h
    exact formulaAt.tt off htagAt
  ·
    simp [pure_eq_ok] at h
    subst h
    exact formulaAt.ff off htagAt
  ·
    simp [pure_eq_ok] at h
    subst h
    exact formulaAt.sph off htagAt
  ·
    simp [throw_ne_ok] at h

theorem parseJudgment_sound (pool : ByteArray) (cxs : Array WComplex) (off : Nat) {j : WJudgment}
    (h : parseJudgment pool cxs off = .ok j) : judgmentAt pool cxs.toList off j := by
  unfold parseJudgment at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok] at h
  obtain ⟨hoff, tag, c₁, hu8, htag, pre, c₂, hpre32, post, ⟨c₃, hpost32⟩, hpo, hqo, preF, hpreF, postF, hpostF, hsph, hj⟩ := h
  subst htag
  subst hj
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok hu8
  obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre32
  obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost32
  exact ⟨htagAt, pre, post, hpreAt, hpostAt, hpo, hqo,
    parseFormula_sound pool cxs pre preF hpreF,
    parseFormula_sound pool cxs post postF hpostF, by simpa using hsph⟩

theorem parseThetaAt_sound {pool : ByteArray} {off : Nat} {w : String} {q : Rat}
    (h : parseThetaAt pool off w = .ok q) :
    ∃ e, u8At pool off 0x02 ∧ ratAt pool (off + 1) q e := by
  unfold parseThetaAt at h
  simp [bind_eq_ok, throw_ne_ok, pure_eq_ok] at h
  obtain ⟨t, hpt, hm⟩ := h
  split at hm <;> simp [pure_eq_ok, throw_ne_ok] at hm
  rename_i q' heq
  subst hm
  have := parseTerm_sound pool off _ hpt
  cases this with
  | const off q e h8 hrat => exact ⟨e, h8, hrat⟩

theorem parseHeader_ok {b : ByteArray} {hd : WHeader}
    (h : parseHeader b = .ok hd) : HeaderAt b hd := by
  unfold parseHeader at h
  simp [bind_eq_ok, map_eq_ok, ite_eq_ok, dite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at'] at h
  obtain ⟨hsz, magic, c₁, hmagic, hmagicEq, ver, c₂, hver, hverEq, fl, c₃, hfl, hflEq,
    so, c₄, hso, sl, c₅, hsl, po, c₆, hpo, pl, c₇, hpl,
    dgo, c₈, hdgo, dgl, c₉, hdgl, pfo, c₁₀, hpfo, pfl, c₁₁, hpfl,
    nw, c₁₂, hnw, na, c₁₃, hna, nn, c₁₄, hnn, nc, c₁₅, hnc,
    ro, c₁₆, hro, th, c₁₇, hth, rsv, ⟨c₁₈, hrsv⟩, hzero, hsec, hhole, halign, hhd⟩ := h
  subst hhd
  subst hmagicEq
  obtain ⟨hmagicS, hmagicL, rfl, _, _⟩ := take_ok hmagic
  obtain ⟨hverAt, rfl, _, _⟩ := u32_ok hver
  obtain ⟨hflAt, rfl, _, _⟩ := u32_ok hfl
  obtain ⟨hsoAt, rfl, _, _⟩ := u64_ok hso
  obtain ⟨hslAt, rfl, _, _⟩ := u64_ok hsl
  obtain ⟨hpoAt, rfl, _, _⟩ := u64_ok hpo
  obtain ⟨hplAt, rfl, _, _⟩ := u64_ok hpl
  obtain ⟨hdgoAt, rfl, _, _⟩ := u64_ok hdgo
  obtain ⟨hdglAt, rfl, _, _⟩ := u64_ok hdgl
  obtain ⟨hpfoAt, rfl, _, _⟩ := u64_ok hpfo
  obtain ⟨hpflAt, rfl, _, _⟩ := u64_ok hpfl
  obtain ⟨hnwAt, rfl, _, _⟩ := u32_ok hnw
  obtain ⟨hnaAt, rfl, _, _⟩ := u32_ok hna
  obtain ⟨hnnAt, rfl, _, _⟩ := u32_ok hnn
  obtain ⟨hncAt, rfl, _, _⟩ := u32_ok hnc
  obtain ⟨hroAt, rfl, _, _⟩ := u64_ok hro
  obtain ⟨hthAt, rfl, _, _⟩ := u32_ok hth
  obtain ⟨hrsvS, hrsvL, rfl, _, _⟩ := take_ok hrsv
  subst hverEq
  subst hflEq
  have hz : ∀ i, i < rsv.length → rsv.getD i 0 = 0 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using hzero _ (List.getElem_mem hi)
  refine ⟨by omega, hmagicS, hverAt, hflAt, hsoAt, hslAt, hpoAt, hplAt,
    hdgoAt, hdglAt, hpfoAt, hpflAt, hnwAt, hnaAt, hnnAt, hncAt, hroAt, hthAt,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < rsv.length := by omega
    have := sliceIs_index hrsvS hi'
    rw [hz i hi'] at this
    simpa using this
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hsec
    exact ⟨h1, h2, h3, h4, h5⟩
  · exact hhole
  · exact halign

theorem range'_cons_inv {s k : Nat} {x : Nat} {r : List Nat}
    (h : List.range' s k 1 = x :: r) : x = s ∧ r = List.range' (s + 1) (k - 1) 1 := by
  match k, h with
  | k + 1, h =>
    rw [List.range'_succ] at h
    injection h with h1 h2
    exact ⟨h1.symm, by simpa using h2.symm⟩

theorem drop_cons_inv {α : Type} {l : List α} {k : Nat} {x : α} {r : List α} (d : α)
    (h : l.drop k = x :: r) : l.getD k d = x ∧ l.drop (k + 1) = r := by
  constructor
  · have h0 : (l.drop k)[0]? = some x := by rw [h]; rfl
    rw [List.getElem?_drop] at h0
    rw [List.getD_eq_getElem?_getD]
    rw [show l[k]? = some x from by simpa using h0]
    rfl
  · have h1 := congrArg (List.drop 1) h
    rw [List.drop_drop] at h1
    simpa using h1

theorem forall_getD_push {α : Type} {P : Nat → α → Prop} {a : Array α} {x d : α}
    (ha : ∀ j, j < a.size → P j (a.getD j d)) (hx : P a.size x) :
    ∀ j, j < (a.push x).size → P j ((a.push x).getD j d) := by
  intro j hj
  rw [Array.size_push] at hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  rcases Nat.lt_or_ge j a.size with hlt | hge
  · rw [if_neg (by omega)]
    have := ha j hlt
    rw [Array.getD_eq_getD_getElem?] at this
    exact this
  · have hj' : j = a.size := by omega
    subst hj'
    rw [if_pos rfl]
    simpa using hx

theorem parsePayload_ok {b : ByteArray} {dt : Dtype} {shape : List Nat} {off len : Nat}
    {pl : WPayload} (h : parsePayload b dt shape off len = .ok pl) :
    payloadAt b dt shape off len pl := by
  unfold parsePayload at h
  simp only [letFun] at h
  split at h
  · simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at h
  split at h
  ·
    rename_i hkind
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
      -List.forIn_yield_eq_foldlM] at h
    obtain ⟨hlen, mask, ⟨c₁, hmask⟩, hpl⟩ := h
    obtain ⟨hmaskAt, rfl, _, _⟩ := readMask_ok hmask
    subst hpl
    have hmsize : mask.size = Shape.totalSize shape := by
      obtain ⟨_, _, _, hms, _, _, _⟩ := hmaskAt
      exact hms
    show dt.kind = .bool ∧ _ ∧ _ ∧ _
    refine ⟨hkind, by simp [hmsize], by simp [hmsize, hlen], ?_⟩
    have hmk : (⟨mask.toList⟩ : Array Bool) = mask := by simp
    rw [hmk, Array.length_toList, hmsize, hlen]
    exact hmaskAt
  ·
    rename_i hkind
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
      -List.forIn_yield_eq_foldlM] at h
    obtain ⟨hlen, vs, ⟨cend, hloop⟩, hpl⟩ := h
    subst hpl
    have hinv := forIn_list_inv (I := fun (st : List Int × Cur) rest =>
        st.2 = (⟨b, off + 8 * st.1.length, off + len⟩ : Cur) ∧
        st.1.length + rest.length = Shape.totalSize shape ∧
        (∀ j, j < st.1.length → ∃ raw, u64At b (off + 8 * j) raw ∧
          st.1.getD j 0 = (match dt.sign with
            | .nn => (raw : Int)
            | .signed => if raw < 2 ^ 63 then (raw : Int) else (raw : Int) - 2 ^ 64)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
        obtain ⟨⟨bs8, c₂⟩, htk, hy⟩ := hbody
        obtain ⟨hsl, hln8, rfl, _, _⟩ := take_ok htk
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega, ?_⟩
        refine forall_getD_append (P := fun j v => ∃ raw, u64At b (off + 8 * j) raw ∧
          v = (match dt.sign with
            | .nn => (raw : Int)
            | .signed => if raw < 2 ^ 63 then (raw : Int) else (raw : Int) - 2 ^ 64)) hAt ?_
        refine ⟨bytesToNatLE bs8, ⟨bs8, hsl, hln8, rfl⟩, ?_⟩
        cases dt.sign with
        | nn => rfl
        | signed => exact bytesToIntLE_eq8 hln8)
      (by exact ⟨rfl, by simp, by simp⟩)
      hloop
    obtain ⟨hcend, hcnt, hAt⟩ := hinv
    have hvslen : vs.length = Shape.totalSize shape := by simpa using hcnt
    exact ⟨hkind, hvslen, by omega, fun i hi => hAt i hi⟩
  ·
    rename_i hkind
    simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
      -List.forIn_yield_eq_foldlM] at h
    obtain ⟨offs, ⟨coff, hloop1⟩, qs, hloop2, hpl⟩ := h
    subst hpl
    have hinv1 := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨b, off + 4 * st.1.length, off + len⟩ : Cur) ∧
        st.1.length + rest.length = Shape.totalSize shape ∧
        (∀ j, j < st.1.length → u32At b (off + 4 * j) (st.1.getD j 0)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
        obtain ⟨⟨o, c₂⟩, ho, hy⟩ := hbody
        obtain ⟨hoAt, rfl, _, _⟩ := u32_ok ho
        exact ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun j v => u32At b (off + 4 * j) v) hAt hoAt⟩)
      (by exact ⟨rfl, by simp, by simp⟩)
      hloop1
    obtain ⟨hcoff, hcnt1, hoffsAt⟩ := hinv1
    have hoffslen : offs.length = Shape.totalSize shape := by simpa using hcnt1
    have hinv2 := forIn_list_inv (I := fun (qs : List Rat) rest =>
        qs.length + rest.length = offs.length ∧
        offs.drop qs.length = rest ∧
        (∀ i, i < qs.length → ∃ e, ratAt b (off + offs.getD i 0) (qs.getD i 0) e ∧
          e ≤ off + len))
      (by
        intro x rest qs hI r hbody
        obtain ⟨hcnt, hdrop, hAt⟩ := hI
        obtain ⟨hx, hdrop'⟩ := drop_cons_inv 0 hdrop
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
        obtain ⟨⟨q, c₂⟩, hq, hy⟩ := hbody
        obtain ⟨e, hrat, rfl, _, hes, _⟩ := readRat_ok hq
        refine ⟨_, hy.symm, by simp at hcnt ⊢ <;> omega, by simpa using hdrop', ?_⟩
        refine forall_getD_append (P := fun j v => ∃ e, ratAt b (off + offs.getD j 0) v e ∧
          e ≤ off + len) hAt ?_
        rw [hx]
        exact ⟨e, hrat, hes⟩)
      (by exact ⟨by simp, by simp, by simp⟩)
      hloop2
    obtain ⟨hcnt2, _, hqsAt⟩ := hinv2
    have hqslen : qs.length = Shape.totalSize shape := by
      simp at hcnt2
      omega
    refine ⟨hkind, hqslen, ?_⟩
    intro i hi
    obtain ⟨e, hrat, he⟩ := hqsAt i hi
    exact ⟨offs.getD i 0, e, hoffsAt i (by omega), hrat, he⟩
  ·
    rename_i kk hnb hni hnr
    rcases hk : dt.kind with _ | _ | _ | _ | _ | _ | _
    · exact absurd hk hnb
    · exact absurd hk hni
    · exact absurd hk hnr
    ·
      rw [hk] at h
      simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
        -List.forIn_yield_eq_foldlM] at h
      obtain ⟨hlen, bits, ⟨cend, hloop⟩, hpl⟩ := h
      subst hpl
      have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, off + 2 * st.1.length, off + len⟩ : Cur) ∧
          st.1.length + rest.length = Shape.totalSize shape ∧
          (∀ j, j < st.1.length → uleAt b (off + 2 * j) 2 (st.1.getD j 0) ∧
            ¬(st.1.getD j 0 &&& 31744 = 31744)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [bind_eq_ok] at hbody
          obtain ⟨⟨v, c₂⟩, hv, hy⟩ := hbody
          obtain ⟨hvAt, rfl, _, _⟩ := uLE_ok hv
          dsimp only [] at hy
          split at hy
          · split at hy <;> simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at hy
          · rename_i hexp
            simp only [pure_eq_ok] at hy
            refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega, ?_⟩
            refine forall_getD_append (P := fun j v => uleAt b (off + 2 * j) 2 v ∧
              ¬(v &&& 31744 = 31744)) hAt ?_
            exact ⟨hvAt, by simpa using hexp⟩)
        (by exact ⟨rfl, by simp, by simp⟩)
        hloop
      obtain ⟨hcend, hcnt, hAt⟩ := hinv
      have hblen : bits.length = Shape.totalSize shape := by simpa using hcnt
      refine ⟨hk, hblen, 2, 31744, 1023, rfl, by rw [hblen]; exact hlen, ?_⟩
      intro i hi
      obtain ⟨hu, hne⟩ := hAt i hi
      exact ⟨hu, fun hc => hne hc.1⟩
    ·
      rw [hk] at h
      simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
        -List.forIn_yield_eq_foldlM] at h
      obtain ⟨hlen, bits, ⟨cend, hloop⟩, hpl⟩ := h
      subst hpl
      have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, off + 2 * st.1.length, off + len⟩ : Cur) ∧
          st.1.length + rest.length = Shape.totalSize shape ∧
          (∀ j, j < st.1.length → uleAt b (off + 2 * j) 2 (st.1.getD j 0) ∧
            ¬(st.1.getD j 0 &&& 32640 = 32640)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [bind_eq_ok] at hbody
          obtain ⟨⟨v, c₂⟩, hv, hy⟩ := hbody
          obtain ⟨hvAt, rfl, _, _⟩ := uLE_ok hv
          dsimp only [] at hy
          split at hy
          · split at hy <;> simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at hy
          · rename_i hexp
            simp only [pure_eq_ok] at hy
            refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega, ?_⟩
            refine forall_getD_append (P := fun j v => uleAt b (off + 2 * j) 2 v ∧
              ¬(v &&& 32640 = 32640)) hAt ?_
            exact ⟨hvAt, by simpa using hexp⟩)
        (by exact ⟨rfl, by simp, by simp⟩)
        hloop
      obtain ⟨hcend, hcnt, hAt⟩ := hinv
      have hblen : bits.length = Shape.totalSize shape := by simpa using hcnt
      refine ⟨hk, hblen, 2, 32640, 127, rfl, by rw [hblen]; exact hlen, ?_⟩
      intro i hi
      obtain ⟨hu, hne⟩ := hAt i hi
      exact ⟨hu, fun hc => hne hc.1⟩
    ·
      rw [hk] at h
      simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
        -List.forIn_yield_eq_foldlM] at h
      obtain ⟨hlen, bits, ⟨cend, hloop⟩, hpl⟩ := h
      subst hpl
      have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, off + 4 * st.1.length, off + len⟩ : Cur) ∧
          st.1.length + rest.length = Shape.totalSize shape ∧
          (∀ j, j < st.1.length → uleAt b (off + 4 * j) 4 (st.1.getD j 0) ∧
            ¬(st.1.getD j 0 &&& 2139095040 = 2139095040)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [bind_eq_ok] at hbody
          obtain ⟨⟨v, c₂⟩, hv, hy⟩ := hbody
          obtain ⟨hvAt, rfl, _, _⟩ := uLE_ok hv
          dsimp only [] at hy
          split at hy
          · split at hy <;> simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at hy
          · rename_i hexp
            simp only [pure_eq_ok] at hy
            refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega, ?_⟩
            refine forall_getD_append (P := fun j v => uleAt b (off + 4 * j) 4 v ∧
              ¬(v &&& 2139095040 = 2139095040)) hAt ?_
            exact ⟨hvAt, by simpa using hexp⟩)
        (by exact ⟨rfl, by simp, by simp⟩)
        hloop
      obtain ⟨hcend, hcnt, hAt⟩ := hinv
      have hblen : bits.length = Shape.totalSize shape := by simpa using hcnt
      refine ⟨hk, hblen, 4, 2139095040, 8388607, rfl, by rw [hblen]; exact hlen, ?_⟩
      intro i hi
      obtain ⟨hu, hne⟩ := hAt i hi
      exact ⟨hu, fun hc => hne hc.1⟩
    ·
      rw [hk] at h
      simp [bind_eq_ok, map_eq_ok, ite_eq_ok, throw_ne_ok, pure_eq_ok, Cur.at',
        -List.forIn_yield_eq_foldlM] at h
      obtain ⟨hlen, bits, ⟨cend, hloop⟩, hpl⟩ := h
      subst hpl
      have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, off + 8 * st.1.length, off + len⟩ : Cur) ∧
          st.1.length + rest.length = Shape.totalSize shape ∧
          (∀ j, j < st.1.length → uleAt b (off + 8 * j) 8 (st.1.getD j 0) ∧
            ¬(st.1.getD j 0 &&& 9218868437227405312 = 9218868437227405312)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [bind_eq_ok] at hbody
          obtain ⟨⟨v, c₂⟩, hv, hy⟩ := hbody
          obtain ⟨hvAt, rfl, _, _⟩ := uLE_ok hv
          dsimp only [] at hy
          split at hy
          · split at hy <;> simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at hy
          · rename_i hexp
            simp only [pure_eq_ok] at hy
            refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega, ?_⟩
            refine forall_getD_append (P := fun j v => uleAt b (off + 8 * j) 8 v ∧
              ¬(v &&& 9218868437227405312 = 9218868437227405312)) hAt ?_
            exact ⟨hvAt, by simpa using hexp⟩)
        (by exact ⟨rfl, by simp, by simp⟩)
        hloop
      obtain ⟨hcend, hcnt, hAt⟩ := hinv
      have hblen : bits.length = Shape.totalSize shape := by simpa using hcnt
      refine ⟨hk, hblen, 8, 9218868437227405312, 4503599627370495, rfl, by rw [hblen]; exact hlen, ?_⟩
      intro i hi
      obtain ⟨hu, hne⟩ := hAt i hi
      exact ⟨hu, fun hc => hne hc.1⟩

theorem parseSymEntry_ok {b : ByteArray} {hd : WHeader} {i : Nat}
    {dt : Dtype} {shape : List Nat} {loc : Option (Nat × Nat)}
    (h : parseSymEntry b hd i = .ok (dt, shape, loc)) :
    32 * hd.nWires ≤ hd.symtabLen ∧
    dtypeAt b (hd.symtabOff + 32 * i) dt ∧
    u32At b (hd.symtabOff + 32 * i + 4) shape.length ∧
    (∃ so, u64At b (hd.symtabOff + 32 * i + 8) so ∧ 32 * hd.nWires ≤ so ∧
      so + 8 * shape.length ≤ hd.symtabLen ∧
      u64sAt b (hd.symtabOff + so) shape (hd.symtabOff + so + 8 * shape.length)) ∧
    (match loc with
     | none => u64At b (hd.symtabOff + 32 * i + 16) U64_MAX ∧
         u64At b (hd.symtabOff + 32 * i + 24) 0
     | some (off, len) => u64At b (hd.symtabOff + 32 * i + 16) off ∧
         u64At b (hd.symtabOff + 32 * i + 24) len ∧ off % 64 = 0) := by
  unfold parseSymEntry at h
  simp only [letFun] at h
  split at h
  · simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at h
  rename_i hrecs
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq, Cur.at'] at h
  obtain ⟨dt', c₁, hdt, rank, c₂, hrank, shapeOff, c₃, hshOff, pOff, c₄, hpOff,
    pLen, c₅, hpLen, h⟩ := h
  obtain ⟨hdtAt, rfl, _, _⟩ := readDtype_ok hdt
  obtain ⟨hrankAt, rfl, _, _⟩ := u32_ok hrank
  obtain ⟨hshOffAt, rfl, _, _⟩ := u64_ok hshOff
  obtain ⟨hpOffAt, rfl, _, _⟩ := u64_ok hpOff
  obtain ⟨hpLenAt, rfl, _, _⟩ := u64_ok hpLen
  split at h
  · simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at h
  rename_i hshg
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hshg
  obtain ⟨hsh1, hsh2⟩ := hshg
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ok_eq_map, ok_eq_bind, ok_eq_pure,
    Prod.exists, Prod.mk.injEq] at h
  obtain ⟨scEnd, shape', hloop, h⟩ := h
  rw [forIn_range_eq] at hloop
  have hinv := forIn_list_inv (I := fun (st : Cur × List Nat) rest =>
      st.1 = (⟨b, hd.symtabOff + shapeOff + 8 * st.2.length, hd.symtabOff + hd.symtabLen⟩ : Cur) ∧
      st.2.length + rest.length = rank ∧
      (∀ j, j < st.2.length → u64At b (hd.symtabOff + shapeOff + 8 * j) (st.2.getD j 0)))
    (by
      intro x rest st hI r hbody
      obtain ⟨sc, acc⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨hsc, hcnt, hAt⟩ := hI
      subst hsc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
      obtain ⟨⟨e, c₆⟩, he, hy⟩ := hbody
      obtain ⟨heAt, rfl, _, _⟩ := u64_ok he
      refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
        forall_getD_append (P := fun j v => u64At b (hd.symtabOff + shapeOff + 8 * j) v) hAt heAt⟩)
    (by exact ⟨rfl, by simp, by simp⟩)
    hloop
  obtain ⟨hscEnd, hcnt, hshAt⟩ := hinv
  have hlen : shape'.length = rank := by simpa using hcnt
  by_cases hmax : (pOff == U64_MAX) = true
  · simp [hmax, map_eq_ok, bind_eq_ok, pure_eq_ok, throw_ne_ok, ite_eq_ok, Prod.mk.injEq] at h
    obtain ⟨hz, hdt2, hsh3, hloc2⟩ := h
    subst hdt2
    subst hsh3
    subst hloc2
    subst hz
    simp only [beq_iff_eq] at hmax
    subst hmax
    exact ⟨by omega, hdtAt, by rw [hlen]; exact hrankAt,
      ⟨shapeOff, hshOffAt, by omega, by omega, hshAt, rfl⟩, hpOffAt, hpLenAt⟩
  · simp only [Bool.not_eq_true] at hmax
    simp [hmax, map_eq_ok, bind_eq_ok, pure_eq_ok, throw_ne_ok, ite_eq_ok, Prod.mk.injEq] at h
    obtain ⟨hal, hdt2, hsh3, hloc2⟩ := h
    subst hdt2
    subst hsh3
    subst hloc2
    exact ⟨by omega, hdtAt, by rw [hlen]; exact hrankAt,
      ⟨shapeOff, hshOffAt, by omega, by omega, hshAt, rfl⟩, hpOffAt, hpLenAt, hal⟩

theorem parseSymtab_ok {b : ByteArray} {hd : WHeader} {syms : Array WSym}
    (h : parseSymtab b hd = .ok syms) : symtabAt b hd syms := by
  unfold parseSymtab at h
  simp only [bind_eq_ok] at h
  obtain ⟨out, hloop, hpure⟩ := h
  simp only [pure_eq_ok] at hpure
  rw [forIn_range_eq] at hloop
  have hinv := forIn_list_inv (I := fun (a : Array WSym) rest =>
      a.size + rest.length = hd.nWires ∧
      List.range' a.size (hd.nWires - a.size) 1 = rest ∧
      (∀ j, j < a.size → symAt b hd j (a.getD j ⟨Dtype.Q, [], none⟩)))
    (by
      intro x rest a hI r hbody
      obtain ⟨hcnt, hrest, hAll⟩ := hI
      obtain ⟨hx, hrest'⟩ := range'_cons_inv hrest
      subst hx
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists] at hbody
      obtain ⟨dt, shape, loc, hentry, hbody⟩ := hbody
      have hE := parseSymEntry_ok hentry
      split at hbody
      ·
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
        obtain ⟨payload, hpay, hy⟩ := hbody
        subst hpay
        refine ⟨_, hy.symm, by simp at hcnt ⊢ <;> omega, by simp [hrest', Nat.sub_sub], ?_⟩
        refine forall_getD_push (P := fun j s => symAt b hd j s) hAll ?_
        obtain ⟨_, hdtAt, hrankAt, hsh, hlocm⟩ := hE
        exact ⟨hdtAt, hrankAt, hsh, hlocm⟩
      ·
        rename_i po pln
        split at hbody
        · simp [map_eq_ok, bind_eq_ok, throw_ne_ok] at hbody
        rename_i hguard
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
        obtain ⟨hg1, hg2⟩ := hguard
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
        obtain ⟨pv, hpv, payload, hpay, hy⟩ := hbody
        subst hpay
        refine ⟨_, hy.symm, by simp at hcnt ⊢ <;> omega, by simp [hrest', Nat.sub_sub], ?_⟩
        refine forall_getD_push (P := fun j s => symAt b hd j s) hAll ?_
        obtain ⟨_, hdtAt, hrankAt, hsh, hlocm⟩ := hE
        obtain ⟨hu16, hu24, hal⟩ := hlocm
        exact ⟨hdtAt, hrankAt, hsh, po, pln, hu16, hu24, hal, by omega, by omega,
          parsePayload_ok hpv⟩)
    (by exact ⟨by simp, by simp, by simp⟩)
    hloop
  rw [← hpure]
  obtain ⟨hcnt, _, hAll⟩ := hinv
  have hsize : out.size = hd.nWires := by simpa using hcnt
  have hbound : 32 * hd.nWires ≤ hd.symtabLen := by
    rcases Nat.eq_zero_or_pos hd.nWires with h0 | hpos
    · omega
    · obtain ⟨_, _, ⟨so, _, hso1, hso2, _⟩, _⟩ := hAll 0 (by omega)
      omega
  exact ⟨hsize, hbound, fun i hi => hAll i (by omega)⟩

theorem ratsAt_snoc {b : ByteArray} {p : Nat} {qs : List Rat} {e : Nat} {q : Rat} {e' : Nat}
    (h : ratsAt b p qs e) (h2 : ratAt b e q e') : ratsAt b p (qs ++ [q]) e' := by
  induction h with
  | nil p => exact ratsAt.cons _ _ _ _ _ h2 (ratsAt.nil _)
  | cons p q1 p1 qs1 p2 h1 hrest ih => exact ratsAt.cons _ _ _ _ _ h1 (ih h2)

theorem masksAt_snoc {b : ByteArray} {n p : Nat} {ms : List (Array Bool)} {e : Nat}
    {m : Array Bool} {e' : Nat}
    (h : masksAt b n p ms e) (h2 : maskAt b e n m e') : masksAt b n p (ms ++ [m]) e' := by
  induction h with
  | nil p => exact masksAt.cons _ _ _ _ _ h2 (masksAt.nil _)
  | cons p m1 p1 ms1 p2 h1 hrest ih => exact masksAt.cons _ _ _ _ _ h1 (ih h2)

theorem maskPairsAt_snoc {b : ByteArray} {n p : Nat} {ms : List (Array Bool × Array Bool)}
    {e : Nat} {sm em : Array Bool} {e₁ e₂ : Nat}
    (h : maskPairsAt b n p ms e) (h1 : maskAt b e n sm e₁) (h2 : maskAt b e₁ n em e₂) :
    maskPairsAt b n p (ms ++ [(sm, em)]) e₂ := by
  induction h with
  | nil p => exact maskPairsAt.cons _ _ _ _ _ _ _ h1 h2 (maskPairsAt.nil _)
  | cons p sm1 em1 p1 p2 ms1 p3 ha hb hrest ih =>
    exact maskPairsAt.cons _ _ _ _ _ _ _ ha hb (ih h1)

theorem complexesAt_snoc {b : ByteArray} {p : Nat} {ws : List WComplex} {e : Nat}
    {w : WComplex} {e' : Nat}
    (h : complexesAt b p ws e) (h2 : complexAt b e w e') : complexesAt b p (ws ++ [w]) e' := by
  induction h with
  | nil p => exact complexesAt.cons _ _ _ _ _ h2 (complexesAt.nil _)
  | cons p w1 p1 ws1 p2 h1 hrest ih => exact complexesAt.cons _ _ _ _ _ h1 (ih h2)

theorem appsAt_snoc {b : ByteArray} {nW : Nat} {cxs : List WComplex} {p : Nat}
    {as' : List WApp} {e : Nat} {a : WApp} {e' : Nat}
    (h : appsAt b nW cxs p as' e) (h2 : appAt b nW cxs e a e') :
    appsAt b nW cxs p (as' ++ [a]) e' := by
  induction h with
  | nil p => exact appsAt.cons _ _ _ _ _ h2 (appsAt.nil _)
  | cons p a1 p1 as1 p2 h1 hrest ih => exact appsAt.cons _ _ _ _ _ h1 (ih h2)

theorem parseComplex_ok {b : ByteArray} {p s : Nat} {w : WComplex} {c' : Cur}
    (h : parseComplex ⟨b, p, s⟩ = .ok (w, c')) :
    ∃ e, complexAt b p w e ∧ c' = ⟨b, e, s⟩ ∧ e ≤ s ∧ e ≤ b.size := by
  unfold parseComplex at h
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ok_eq_map, ok_eq_bind, ok_eq_pure,
    Prod.exists, Prod.mk.injEq] at h
  obtain ⟨nv, c₁, hnv, ad, c₂, had, coordsA, cc₁, hloop1, ns, c₃, hns,
    cc₂, simsA, hloop2, ncl, c₄, hncl, cc₃, cellsA, hloop3, hw, hc'⟩ := h
  obtain ⟨hnvAt, rfl, _, _⟩ := u32_ok hnv
  obtain ⟨hadAt, rfl, hst2, hsz2⟩ := u32_ok had
  rw [forIn_range_eq] at hloop1
  have hinv1 := forIn_list_inv (I := fun (st : Array Rat × Cur) rest =>
      ∃ e, st.2 = (⟨b, e, s⟩ : Cur) ∧ ratsAt b (p + 8) st.1.toList e ∧
        st.1.size + rest.length = nv * ad ∧ e ≤ s ∧ e ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨coords, cc⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨e, hcc, hrats, hcnt, hes, heb⟩ := hI
      subst hcc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
      obtain ⟨⟨q, c₅⟩, hq, hy⟩ := hbody
      obtain ⟨e2, hrat, rfl, _, hes2, hesz2⟩ := readRat_ok hq
      refine ⟨_, hy.symm, e2, rfl, ?_, by simp at hcnt ⊢ <;> omega, hes2, hesz2⟩
      rw [Array.toList_push]
      exact ratsAt_snoc hrats hrat)
    (⟨p + 8, rfl, ratsAt.nil _, by simp, hst2, hsz2⟩)
    hloop1
  obtain ⟨e1, hcc₁, hrats, hcnt1, hes1, hesz1⟩ := hinv1
  dsimp only [] at hcc₁ hrats hcnt1
  subst hcc₁
  obtain ⟨hnsAt, rfl, hst3, hsz3⟩ := u32_ok hns
  rw [forIn_range_eq] at hloop2
  have hinv2 := forIn_list_inv (I := fun (st : Cur × Array (Array Bool)) rest =>
      ∃ e, st.1 = (⟨b, e, s⟩ : Cur) ∧ masksAt b nv (e1 + 4) st.2.toList e ∧
        st.2.size + rest.length = ns ∧ e ≤ s ∧ e ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨cc, sims⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨e, hcc, hmasks, hcnt, hes, heb⟩ := hI
      subst hcc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok] at hbody
      obtain ⟨⟨m, c₅⟩, hm, hy⟩ := hbody
      obtain ⟨hmask, rfl, hs', hb'⟩ := readMask_ok hm
      refine ⟨_, hy.symm, e + (nv + 7) / 8, rfl, ?_, by simp at hcnt ⊢ <;> omega, hs', hb'⟩
      rw [Array.toList_push]
      exact masksAt_snoc hmasks hmask)
    (⟨e1 + 4, rfl, masksAt.nil _, by simp, hst3, hsz3⟩)
    hloop2
  obtain ⟨e2, hcc₂, hmasks, hcnt2, hes2, hesz2⟩ := hinv2
  dsimp only [] at hcc₂ hmasks hcnt2
  subst hcc₂
  obtain ⟨hnclAt, rfl, hst4, hsz4⟩ := u32_ok hncl
  rw [forIn_range_eq] at hloop3
  have hinv3 := forIn_list_inv (I := fun (st : Cur × Array (Array Bool × Array Bool)) rest =>
      ∃ e, st.1 = (⟨b, e, s⟩ : Cur) ∧ maskPairsAt b nv (e2 + 4) st.2.toList e ∧
        st.2.size + rest.length = ncl ∧ e ≤ s ∧ e ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨cc, cells⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨e, hcc, hpairs, hcnt, hes, heb⟩ := hI
      subst hcc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists] at hbody
      obtain ⟨sm, c₅, hsm, em, c₆, hem, hy⟩ := hbody
      obtain ⟨hmask1, rfl, _, _⟩ := readMask_ok hsm
      obtain ⟨hmask2, rfl, hs', hb'⟩ := readMask_ok hem
      refine ⟨_, hy.symm, e + (nv + 7) / 8 + (nv + 7) / 8, rfl, ?_,
        by simp at hcnt ⊢ <;> omega, hs', hb'⟩
      rw [Array.toList_push]
      exact maskPairsAt_snoc hpairs hmask1 hmask2)
    (⟨e2 + 4, rfl, maskPairsAt.nil _, by simp, hst4, hsz4⟩)
    hloop3
  obtain ⟨e3, hcc₃, hpairs, hcnt3, hes3, hesz3⟩ := hinv3
  dsimp only [] at hcc₃ hpairs hcnt3
  subst hcc₃
  subst hw
  subst hc'
  have hsims : simsA.size = ns := by simpa using hcnt2
  have hcells : cellsA.size = ncl := by simpa using hcnt3
  refine ⟨e3, ⟨e1, e2, e3, hnvAt, hadAt, by simpa using hcnt1, hrats,
    by rw [hsims]; exact hnsAt, hmasks, by rw [hcells]; exact hnclAt, hpairs, rfl⟩,
    rfl, hes3, hesz3⟩

theorem bindingsAt_snoc {b : ByteArray} {nIdx : Nat} {row : List Nat} {e e' : Nat}
    (hrl : u32At b e row.length) (hrb : ∀ x ∈ row, x < nIdx)
    (hrs : u32sAt b (e + 4) row e') :
    ∀ {p : Nat} {rows : List (List Nat)},
      appAt.bindingsAt b nIdx p rows e →
      appAt.bindingsAt b nIdx p (rows ++ [row]) e' := by
  intro p rows
  induction rows generalizing p with
  | nil =>
    intro h
    have hep : e = p := h
    rw [← hep]
    exact ⟨hrl, hrb, e', hrs, rfl⟩
  | cons r rs ih =>
    intro h
    obtain ⟨hu, hb, p₁, hus, hrest⟩ := h
    exact ⟨hu, hb, p₁, hus, ih hrest⟩

theorem parseApp_ok {b : ByteArray} {p s : Nat} {nW : Nat} {cxs : Array WComplex}
    {a : WApp} {c' : Cur}
    (h : parseApp ⟨b, p, s⟩ nW cxs = .ok (a, c')) :
    ∃ e, appAt b nW cxs.toList p a e ∧ c' = ⟨b, e, s⟩ ∧ e ≤ s ∧ e ≤ b.size := by
  unfold parseApp at h
  try simp only [letFun] at h
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at h
  obtain ⟨tag, c₁, htag8, rm, c₂, hrm8, round, hround, rsv, c₃, hrsv16, h⟩ := h
  by_cases hrg : (rsv != 0) = true
  · rw [if_pos hrg] at h
    simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h
  rw [if_neg hrg] at h
  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hrg
  subst hrg
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok htag8
  obtain ⟨hrmAt, rfl, _, _⟩ := u8_ok hrm8
  obtain ⟨hrsvAt, rfl, hst3, hsz3⟩ := u16_ok hrsv16
  have hrmAt' : u8At b (p + 1) (roundCode round) := by rw [roundOf_ok hround]; exact hrmAt
  split at h
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, out, cout, hout, dl, ⟨hoge, hodl⟩, ha, hc'⟩ := h
    subst hodl
    subst ha
    subst hc'
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    obtain ⟨houtAt, rfl, hst4, hsz4⟩ := u32_ok hout
    exact ⟨p + 8, ⟨hrmAt', hrsvAt, htagAt, hex, by omega, houtAt, rfl⟩, rfl, by omega, by omega⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨dt, cdt, hdt, nIn, cni, hni, inputs, cl1, hloop1, out, cout, hout,
      output, ⟨houtge, houteq⟩, nIdx, cnx, hnx, cl2, extents, hloop2, cl3, rows, hloop3,
      oRk, cor, hor, cl4, ob, hloop4, ha, hc'⟩ := h
    subst houteq
    subst ha
    subst hc'
    obtain ⟨hdtAt, rfl, _, _⟩ := readDtype_ok hdt
    obtain ⟨hniAt, rfl, _, _⟩ := u32_ok hni
    rw [forIn_range_eq] at hloop1
    have hinv1 := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨b, p + 12 + 4 * st.1.length, s⟩ : Cur) ∧
        st.1.length + rest.length = nIn ∧
        (∀ i, i < st.1.length → u32At b (p + 12 + 4 * i) (st.1.getD i 0)) ∧
        (∀ w ∈ st.1, w < nW))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt, hmem⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
          false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨w, cw, hw, dl, ⟨hwge, hdl⟩, hy⟩ := hbody
        subst hdl
        obtain ⟨hwAt, rfl, _, _⟩ := u32_ok hw
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v => u32At b (p + 12 + 4 * i) v) hAt hwAt,
          forall_mem_append hmem (by omega)⟩)
      (⟨rfl, by simp, by simp, by simp⟩)
      hloop1
    obtain ⟨hcl1, hcnt1, hInAt, hInMem⟩ := hinv1
    dsimp only [] at hcl1 hcnt1 hInAt hInMem
    subst hcl1
    have hlen1 : inputs.length = nIn := by simpa using hcnt1
    obtain ⟨houtAt, rfl, _, _⟩ := u32_ok hout
    obtain ⟨hnxAt, rfl, _, _⟩ := u32_ok hnx
    rw [forIn_range_eq] at hloop2
    have hinv2 := forIn_list_inv (I := fun (st : Cur × List Nat) rest =>
        st.1 = (⟨b, p + 12 + 4 * inputs.length + 4 + 4 + 8 * st.2.length, s⟩ : Cur) ∧
        st.2.length + rest.length = nIdx ∧
        (∀ i, i < st.2.length →
          u64At b (p + 12 + 4 * inputs.length + 4 + 4 + 8 * i) (st.2.getD i 0)))
      (by
        intro x rest st hI r hbody
        obtain ⟨cc, acc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨ev, ce, hev, hy⟩ := hbody
        obtain ⟨hevAt, rfl, _, _⟩ := u64_ok hev
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v =>
            u64At b (p + 12 + 4 * inputs.length + 4 + 4 + 8 * i) v) hAt hevAt⟩)
      (⟨rfl, by simp, by simp⟩)
      hloop2
    obtain ⟨hcl2, hcnt2, hExtAt⟩ := hinv2
    dsimp only [] at hcl2 hcnt2 hExtAt
    subst hcl2
    have hlen2 : extents.length = nIdx := by simpa using hcnt2
    rw [forIn_range_eq] at hloop3
    have hinv3 := forIn_list_inv (I := fun (st : Cur × List (List Nat)) rest =>
        ∃ e, st.1 = (⟨b, e, s⟩ : Cur) ∧
          appAt.bindingsAt b nIdx
            (p + 12 + 4 * inputs.length + 4 + 4 + 8 * extents.length) st.2 e ∧
          st.2.length + rest.length = nIn)
      (by
        intro x rest st hI r hbody
        obtain ⟨cc, acc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨e, hcc, hbnd, hcnt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨rk, crk, hrk, cli, row, hloopi, hy⟩ := hbody
        obtain ⟨hrkAt, rfl, _, _⟩ := u32_ok hrk
        rw [forIn_range_eq] at hloopi
        have hinvi := forIn_list_inv (I := fun (sti : Cur × List Nat) resti =>
            sti.1 = (⟨b, e + 4 + 4 * sti.2.length, s⟩ : Cur) ∧
            sti.2.length + resti.length = rk ∧
            (∀ i, i < sti.2.length → u32At b (e + 4 + 4 * i) (sti.2.getD i 0)) ∧
            (∀ x ∈ sti.2, x < nIdx))
          (by
            intro xi resti sti hIi ri hbodyi
            obtain ⟨cci, acci⟩ := sti
            dsimp only [] at hIi hbodyi
            obtain ⟨hcci, hcnti, hAti, hmemi⟩ := hIi
            subst hcci
            simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
              false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbodyi
            obtain ⟨xv, cxv, hxv, dli, ⟨hxge, hxdl⟩, hyi⟩ := hbodyi
            subst hxdl
            obtain ⟨hxvAt, rfl, _, _⟩ := u32_ok hxv
            refine ⟨_, hyi.symm, by simp <;> omega, by simp at hcnti ⊢ <;> omega,
              forall_getD_append (P := fun i v => u32At b (e + 4 + 4 * i) v) hAti hxvAt,
              forall_mem_append hmemi (by omega)⟩)
          (⟨rfl, by simp, by simp, by simp⟩)
          hloopi
        obtain ⟨hcli, hcnti, hRowAt, hRowMem⟩ := hinvi
        dsimp only [] at hcli hcnti hRowAt hRowMem
        subst hcli
        have hrlen : row.length = rk := by simpa using hcnti
        refine ⟨_, hy.symm, e + 4 + 4 * row.length, by simp, ?_, by simp at hcnt ⊢ <;> omega⟩
        exact bindingsAt_snoc (by rw [hrlen]; exact hrkAt) hRowMem ⟨hRowAt, rfl⟩ hbnd)
      (by exact ⟨p + 12 + 4 * inputs.length + 4 + 4 + 8 * extents.length, rfl, rfl, by simp⟩)
      hloop3
    obtain ⟨e₃, hcl3, hbnds, hcnt3⟩ := hinv3
    dsimp only [] at hcl3 hbnds hcnt3
    subst hcl3
    have hlen3 : rows.length = nIn := by simpa using hcnt3
    obtain ⟨horAt, rfl, hors, horb⟩ := u32_ok hor
    rw [forIn_range_eq] at hloop4
    have hinv4 := forIn_list_inv (I := fun (st : Cur × List Nat) rest =>
        st.1 = (⟨b, e₃ + 4 + 4 * st.2.length, s⟩ : Cur) ∧
        st.2.length + rest.length = oRk ∧
        (∀ i, i < st.2.length → u32At b (e₃ + 4 + 4 * i) (st.2.getD i 0)) ∧
        (∀ x ∈ st.2, x < nIdx) ∧
        e₃ + 4 + 4 * st.2.length ≤ s ∧ e₃ + 4 + 4 * st.2.length ≤ b.size)
      (by
        intro x rest st hI r hbody
        obtain ⟨cc, acc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt, hmem, hes, heb⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
          false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨xv, cxv, hxv, dli, ⟨hxge, hxdl⟩, hy⟩ := hbody
        subst hxdl
        obtain ⟨hxvAt, rfl, hxs, hxb⟩ := u32_ok hxv
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v => u32At b (e₃ + 4 + 4 * i) v) hAt hxvAt,
          forall_mem_append hmem (by omega), by simp <;> omega, by simp <;> omega⟩)
      (⟨rfl, by simp, by simp, by simp, by simpa using hors, by simpa using horb⟩)
      hloop4
    obtain ⟨hcl4, hcnt4, hObAt, hObMem, hobs, hobb⟩ := hinv4
    dsimp only [] at hcl4 hcnt4 hObAt hObMem hobs hobb
    subst hcl4
    have hlen4 : ob.length = oRk := by simpa using hcnt4
    refine ⟨e₃ + 4 + 4 * ob.length, ⟨hrmAt', hrsvAt, htagAt, hdtAt,
      by rw [hlen1]; exact hniAt, hInMem,
      p + 12 + 4 * inputs.length, p + 12 + 4 * inputs.length + 4 + 4 + 8 * extents.length, e₃,
      ⟨hInAt, rfl⟩, houtAt, by omega,
      by rw [hlen2]; exact hnxAt, ⟨hExtAt, by omega⟩,
      by omega,
      by rwa [← hlen2] at hbnds,
      by rw [hlen4]; exact horAt,
      fun x hx => by rw [hlen2]; exact hObMem x hx,
      ⟨hObAt, by omega⟩⟩, rfl, hobs, hobb⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨dfrom, cdf, hdf, dto, cdto, hdto, rk, crk, hrk, shape, cls, hloopS,
      inp, cin, hin, outp, cop, hop, dli, ⟨hige, hidl⟩, dlo, ⟨hoge, hodl⟩, ha, hc'⟩ := h
    subst hidl
    subst hodl
    subst ha
    subst hc'
    obtain ⟨hdfAt, rfl, _, _⟩ := readDtype_ok hdf
    obtain ⟨hdtoAt, rfl, _, _⟩ := readDtype_ok hdto
    obtain ⟨hrkAt, rfl, _, _⟩ := u32_ok hrk
    rw [forIn_range_eq] at hloopS
    have hinvS := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨b, p + 16 + 8 * st.1.length, s⟩ : Cur) ∧
        st.1.length + rest.length = rk ∧
        (∀ i, i < st.1.length → u64At b (p + 16 + 8 * i) (st.1.getD i 0)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨ev, ce, hev, hy⟩ := hbody
        obtain ⟨hevAt, rfl, _, _⟩ := u64_ok hev
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v => u64At b (p + 16 + 8 * i) v) hAt hevAt⟩)
      (⟨rfl, by simp, by simp⟩)
      hloopS
    obtain ⟨hclS, hcntS, hShAt⟩ := hinvS
    dsimp only [] at hclS hcntS hShAt
    subst hclS
    have hlenS : shape.length = rk := by simpa using hcntS
    obtain ⟨hinAt, rfl, _, _⟩ := u32_ok hin
    obtain ⟨hopAt, rfl, hops, hopb⟩ := u32_ok hop
    exact ⟨p + 16 + 8 * shape.length + 8, ⟨hrmAt', hrsvAt, htagAt, hdfAt, hdtoAt,
      by rw [hlenS]; exact hrkAt,
      p + 16 + 8 * shape.length, ⟨hShAt, by omega⟩,
      hinAt, by omega, hopAt, by omega, by omega⟩, by simp <;> omega,
      by omega, by omega⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, cx, ccx, hcx, h⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    obtain ⟨hcxAt, rfl, _, _⟩ := u32_ok hcx
    split at h
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h
    · rename_i w hw
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
        false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨inp, cin, hin, dli, ⟨hige, hidl⟩, nOut, cno, hno, hcnteq, outs, cend,
        hloop, ha, hc'⟩ := h
      subst hidl
      subst ha
      subst hc'
      obtain ⟨hinAt, rfl, _, _⟩ := u32_ok hin
      obtain ⟨hnoAt, rfl, hnos, hnob⟩ := u32_ok hno
      rw [forIn_range_eq] at hloop
      have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, p + 16 + 4 * st.1.length, s⟩ : Cur) ∧
          st.1.length + rest.length = nOut ∧
          (∀ i, i < st.1.length → u32At b (p + 16 + 4 * i) (st.1.getD i 0)) ∧
          (∀ x ∈ st.1, x < nW) ∧
          p + 16 + 4 * st.1.length ≤ s ∧ p + 16 + 4 * st.1.length ≤ b.size)
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt, hmem, hes, heb⟩ := hI
          subst hcc
          simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
            false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbody
          obtain ⟨wv, cw, hwv, dl, ⟨hwge, hdl⟩, hy⟩ := hbody
          subst hdl
          obtain ⟨hwvAt, rfl, hws, hwb⟩ := u32_ok hwv
          refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
            forall_getD_append (P := fun i v => u32At b (p + 16 + 4 * i) v) hAt hwvAt,
            forall_mem_append hmem (by omega), by simp <;> omega, by simp <;> omega⟩)
        (⟨rfl, by simp, by simp, by simp, by simpa using hnos, by simpa using hnob⟩)
        hloop
      obtain ⟨hcend, hcnt, hOutAt, hOutMem, hoes, hoeb⟩ := hinv
      dsimp only [] at hcend hcnt hOutAt hOutMem hoes hoeb
      subst hcend
      have hlenO : outs.length = nOut := by simpa using hcnt
      have hcxlt : cx < cxs.size := by
        rcases Nat.lt_or_ge cx cxs.size with hlt | hge
        · exact hlt
        · rw [Array.getElem?_eq_none hge] at hw
          cases hw
      have hgetD : cxs.toList.getD cx ⟨0, 0, #[], #[], #[]⟩ = w := by
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hw]
        rfl
      have hcntEq : nOut = w.cells.size := by
        simpa only [Bool.not_eq_true, bne_eq_false_iff_eq] using hcnteq
      refine ⟨p + 16 + 4 * outs.length, ⟨hrmAt', hrsvAt, htagAt, hex, hcxAt,
        by simpa using hcxlt, hinAt, by omega,
        by rw [hlenO]; exact hnoAt,
        by rw [hgetD, hlenO]; exact hcntEq,
        hOutMem, ⟨hOutAt, rfl⟩⟩, rfl, hoes, hoeb⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, rk, crk, hrk, shape, cls, hloopS, inp, cin, hin,
      dli, ⟨hige, hidl⟩, outp, cop, hop, dlo, ⟨hoge, hodl⟩, htail⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hidl
    subst hodl
    rcases htail with ⟨-, ha, hc'⟩ | ⟨hbad, -, -⟩
    · subst ha
      subst hc'
      obtain ⟨hrkAt, rfl, _, _⟩ := u32_ok hrk
      rw [forIn_range_eq] at hloopS
      have hinvS := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, p + 8 + 8 * st.1.length, s⟩ : Cur) ∧
          st.1.length + rest.length = rk ∧
          (∀ i, i < st.1.length → u64At b (p + 8 + 8 * i) (st.1.getD i 0)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
          obtain ⟨ev, ce, hev, hy⟩ := hbody
          obtain ⟨hevAt, rfl, _, _⟩ := u64_ok hev
          refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
            forall_getD_append (P := fun i v => u64At b (p + 8 + 8 * i) v) hAt hevAt⟩)
        (⟨rfl, by simp, by simp⟩)
        hloopS
      obtain ⟨hclS, hcntS, hShAt⟩ := hinvS
      dsimp only [] at hclS hcntS hShAt
      subst hclS
      have hlenS : shape.length = rk := by simpa using hcntS
      obtain ⟨hinAt, rfl, _, _⟩ := u32_ok hin
      obtain ⟨hopAt, rfl, hops, hopb⟩ := u32_ok hop
      exact ⟨p + 8 + 8 * shape.length + 8, ⟨hrmAt', hrsvAt, htagAt, hex,
        by rw [hlenS]; exact hrkAt,
        p + 8 + 8 * shape.length, ⟨hShAt, by omega⟩,
        hinAt, by omega, hopAt, by omega, by omega⟩, by simp <;> omega,
        by omega, by omega⟩
    · exact absurd (by decide : ((4 : Nat) == 4) = true) hbad
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, rk, crk, hrk, shape, cls, hloopS, inp, cin, hin,
      dli, ⟨hige, hidl⟩, outp, cop, hop, dlo, ⟨hoge, hodl⟩, htail⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hidl
    subst hodl
    rcases htail with ⟨hbad, -, -⟩ | ⟨-, ha, hc'⟩
    · exact absurd hbad (by decide)
    · subst ha
      subst hc'
      obtain ⟨hrkAt, rfl, _, _⟩ := u32_ok hrk
      rw [forIn_range_eq] at hloopS
      have hinvS := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
          st.2 = (⟨b, p + 8 + 8 * st.1.length, s⟩ : Cur) ∧
          st.1.length + rest.length = rk ∧
          (∀ i, i < st.1.length → u64At b (p + 8 + 8 * i) (st.1.getD i 0)))
        (by
          intro x rest st hI r hbody
          obtain ⟨acc, cc⟩ := st
          dsimp only [] at hI hbody
          obtain ⟨hcc, hcnt, hAt⟩ := hI
          subst hcc
          simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
          obtain ⟨ev, ce, hev, hy⟩ := hbody
          obtain ⟨hevAt, rfl, _, _⟩ := u64_ok hev
          refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
            forall_getD_append (P := fun i v => u64At b (p + 8 + 8 * i) v) hAt hevAt⟩)
        (⟨rfl, by simp, by simp⟩)
        hloopS
      obtain ⟨hclS, hcntS, hShAt⟩ := hinvS
      dsimp only [] at hclS hcntS hShAt
      subst hclS
      have hlenS : shape.length = rk := by simpa using hcntS
      obtain ⟨hinAt, rfl, _, _⟩ := u32_ok hin
      obtain ⟨hopAt, rfl, hops, hopb⟩ := u32_ok hop
      exact ⟨p + 8 + 8 * shape.length + 8, ⟨hrmAt', hrsvAt, htagAt, hex,
        by rw [hlenS]; exact hrkAt,
        p + 8 + 8 * shape.length, ⟨hShAt, by omega⟩,
        hinAt, by omega, hopAt, by omega, by omega⟩, by simp <;> omega,
        by omega, by omega⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, k, ck, hk, inp, cin, hin, dli, ⟨hige, hidl⟩,
      outs, cend, hloop, ha, hc'⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hidl
    subst ha
    subst hc'
    obtain ⟨hkAt, rfl, _, _⟩ := u32_ok hk
    obtain ⟨hinAt, rfl, hins, hinb⟩ := u32_ok hin
    rw [forIn_range_eq] at hloop
    have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨b, p + 12 + 4 * st.1.length, s⟩ : Cur) ∧
        st.1.length + rest.length = k ∧
        (∀ i, i < st.1.length → u32At b (p + 12 + 4 * i) (st.1.getD i 0)) ∧
        (∀ x ∈ st.1, x < nW) ∧
        p + 12 + 4 * st.1.length ≤ s ∧ p + 12 + 4 * st.1.length ≤ b.size)
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt, hmem, hes, heb⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
          false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨wv, cw, hwv, dl, ⟨hwge, hdl⟩, hy⟩ := hbody
        subst hdl
        obtain ⟨hwvAt, rfl, hws, hwb⟩ := u32_ok hwv
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v => u32At b (p + 12 + 4 * i) v) hAt hwvAt,
          forall_mem_append hmem (by omega), by simp <;> omega, by simp <;> omega⟩)
      (⟨rfl, by simp, by simp, by simp, by simpa using hins, by simpa using hinb⟩)
      hloop
    obtain ⟨hcend, hcnt, hOutAt, hOutMem, hoes, hoeb⟩ := hinv
    dsimp only [] at hcend hcnt hOutAt hOutMem hoes hoeb
    subst hcend
    have hlenO : outs.length = k := by simpa using hcnt
    refine ⟨p + 12 + 4 * outs.length, ⟨hrmAt', hrsvAt, htagAt, hex,
      by rw [hlenO]; exact hkAt, hinAt, by omega, hOutMem, ⟨hOutAt, rfl⟩⟩,
      rfl, hoes, hoeb⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, inp, cin, hin, dl, ⟨hige, hidl⟩, ha, hc'⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hidl
    subst ha
    subst hc'
    obtain ⟨hinAt, rfl, hins, hinb⟩ := u32_ok hin
    exact ⟨p + 8, ⟨hrmAt', hrsvAt, htagAt, hex, hinAt, by omega, rfl⟩, rfl, by omega, by omega⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, i1, ci1, hi1, i2, ci2, hi2, o1, co1, ho1, o2, co2, ho2,
      d1, ⟨hg1, hd1⟩, d2, ⟨hg2, hd2⟩, d3, ⟨hg3, hd3⟩, d4, ⟨hg4, hd4⟩, ha, hc'⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hd1
    subst hd2
    subst hd3
    subst hd4
    subst ha
    subst hc'
    obtain ⟨hi1At, rfl, _, _⟩ := u32_ok hi1
    obtain ⟨hi2At, rfl, _, _⟩ := u32_ok hi2
    obtain ⟨ho1At, rfl, _, _⟩ := u32_ok ho1
    obtain ⟨ho2At, rfl, ho2s, ho2b⟩ := u32_ok ho2
    exact ⟨p + 20, ⟨hrmAt', hrsvAt, htagAt, hex, hi1At, hi2At, ho1At, ho2At,
      by omega, by omega, by omega, by omega, rfl⟩, rfl, by omega, by omega⟩
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨u₁, ⟨hex, hu⟩, k, ck, hk, ins, cend, hloop, outp, cop, hop,
      dlo, ⟨hoge, hodl⟩, ha, hc'⟩ := h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hex
    subst hodl
    subst ha
    subst hc'
    obtain ⟨hkAt, rfl, _, _⟩ := u32_ok hk
    rw [forIn_range_eq] at hloop
    have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨b, p + 8 + 4 * st.1.length, s⟩ : Cur) ∧
        st.1.length + rest.length = k ∧
        (∀ i, i < st.1.length → u32At b (p + 8 + 4 * i) (st.1.getD i 0)) ∧
        (∀ x ∈ st.1, x < nW))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt, hmem⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, ite_eq_ok, throw_ne_ok,
          false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨wv, cw, hwv, dl, ⟨hwge, hdl⟩, hy⟩ := hbody
        subst hdl
        obtain ⟨hwvAt, rfl, _, _⟩ := u32_ok hwv
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun i v => u32At b (p + 8 + 4 * i) v) hAt hwvAt,
          forall_mem_append hmem (by omega)⟩)
      (⟨rfl, by simp, by simp, by simp⟩)
      hloop
    obtain ⟨hcend, hcnt, hInsAt, hInsMem⟩ := hinv
    dsimp only [] at hcend hcnt hInsAt hInsMem
    subst hcend
    have hlenI : ins.length = k := by simpa using hcnt
    obtain ⟨hopAt, rfl, hops, hopb⟩ := u32_ok hop
    exact ⟨p + 8 + 4 * ins.length + 4, ⟨hrmAt', hrsvAt, htagAt, hex,
      by rw [hlenI]; exact hkAt, hInsMem,
      p + 8 + 4 * ins.length, ⟨hInsAt, rfl⟩, hopAt, by omega, rfl⟩,
      rfl, by omega, by omega⟩
  ·
    simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h

theorem parseDiagram_ok {b : ByteArray} {hd : WHeader} {cxs : Array WComplex}
    {apps : List WApp}
    (h : parseDiagram b hd = .ok (cxs, apps)) : diagramAt b hd cxs.toList apps := by
  unfold parseDiagram at h
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok, false_and,
    and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq, Cur.at'] at h
  obtain ⟨nc, c₁, hnc, hnceq, cxsA, cEnd1, hloop1, na, c₂, hna, hnaeq, cEnd2, appsL, hloop2,
    hcxs, happs⟩ := h
  subst hcxs
  subst happs
  obtain ⟨hncAt, rfl, hst1, hsz1⟩ := u32_ok hnc
  rw [forIn_range_eq] at hloop1
  have hinv1 := forIn_list_inv (I := fun (st : Array WComplex × Cur) rest =>
      ∃ e, st.2 = (⟨b, e, hd.diagramOff + hd.diagramLen⟩ : Cur) ∧
        complexesAt b (hd.diagramOff + 4) st.1.toList e ∧
        st.1.size + rest.length = nc ∧ e ≤ hd.diagramOff + hd.diagramLen ∧ e ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨acc, cc⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨e, hcc, hcxAt, hcnt, hes, heb⟩ := hI
      subst hcc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
      obtain ⟨cx, ccx, hcx, hy⟩ := hbody
      obtain ⟨e2, hcxa, rfl, hes2, heb2⟩ := parseComplex_ok hcx
      refine ⟨_, hy.symm, e2, rfl, ?_, by simp at hcnt ⊢ <;> omega, hes2, heb2⟩
      rw [Array.toList_push]
      exact complexesAt_snoc hcxAt hcxa)
    (⟨hd.diagramOff + 4, rfl, complexesAt.nil _, by simp, hst1, hsz1⟩)
    hloop1
  obtain ⟨e1, hcEnd1, hcxsAt, hcnt1, hes1, heb1⟩ := hinv1
  dsimp only [] at hcEnd1 hcxsAt hcnt1
  subst hcEnd1
  obtain ⟨hnaAt, rfl, hst2, hsz2⟩ := u32_ok hna
  rw [forIn_range_eq] at hloop2
  have hinv2 := forIn_list_inv (I := fun (st : Cur × List WApp) rest =>
      ∃ e, st.1 = (⟨b, e, hd.diagramOff + hd.diagramLen⟩ : Cur) ∧
        appsAt b hd.nWires cxsA.toList (e1 + 4) st.2 e ∧
        st.2.length + rest.length = na ∧ e ≤ hd.diagramOff + hd.diagramLen ∧ e ≤ b.size)
    (by
      intro x rest st hI r hbody
      obtain ⟨cc, acc⟩ := st
      dsimp only [] at hI hbody
      obtain ⟨e, hcc, hapAt, hcnt, hes, heb⟩ := hI
      subst hcc
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
      obtain ⟨ap, cap, hap, hy⟩ := hbody
      obtain ⟨e2, hapa, rfl, hes2, heb2⟩ := parseApp_ok hap
      refine ⟨_, hy.symm, e2, rfl, ?_, by simp at hcnt ⊢ <;> omega, hes2, heb2⟩
      exact appsAt_snoc hapAt hapa)
    (⟨e1 + 4, rfl, appsAt.nil _, by simp, hst2, hsz2⟩)
    hloop2
  obtain ⟨e2, hcEnd2, happsAt, hcnt2, hes2, heb2⟩ := hinv2
  dsimp only [] at hcEnd2 happsAt hcnt2 hes2
  have hszA : cxsA.size = nc := by simpa using hcnt1
  have hlenL : appsL.length = na := by simpa using hcnt2
  have hnceq' : nc = hd.nComplexes := by simpa using hnceq
  have hnaeq' : na = hd.nApps := by simpa using hnaeq
  refine ⟨e1, e2, ?_, ?_, hcxsAt, ?_, ?_, happsAt, hes2⟩
  · rw [Array.length_toList, hszA]; exact hncAt
  · rw [Array.length_toList, hszA]; exact hnceq'
  · rw [hlenL]; exact hnaAt
  · rw [hlenL]; exact hnaeq'

theorem all_zero_getD {l : List UInt8} (hz : ∀ x ∈ l, x = 0) {i : Nat}
    (hi : i < l.length) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simpa using hz _ (List.getElem_mem hi)

theorem parseNodeList_sound (ctx : NodeCtx) (me : Nat)
    (IH : ∀ o, o < me → ∀ q, parseNode ctx o = .ok q →
      nodeAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps o q) :
    ∀ offs ps, parseNodeList ctx me offs = .ok ps →
      componentsAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps offs ps ∧
      ∀ o ∈ offs, o < me := by
  intro offs
  induction offs with
  | nil =>
    intro ps h
    unfold parseNodeList at h
    simp only [pure_eq_ok] at h
    subst h
    exact ⟨componentsAt.nil, by simp⟩
  | cons o os ih =>
    intro ps h
    unfold parseNodeList at h
    split at h
    · rename_i homem
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at h
      obtain ⟨q, hq, qs, hqs, hps⟩ := h
      subst hps
      obtain ⟨hcomp, hmem⟩ := ih qs hqs
      refine ⟨componentsAt.cons _ _ _ _ (IH o homem q hq) hcomp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact homem
      · exact hmem x hx'
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h

theorem parseBranches_sound (ctx : NodeCtx) (me : Nat)
    (IH : ∀ o, o < me → ∀ q, parseNode ctx o = .ok q →
      nodeAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps o q) :
    ∀ raw branches, parseBranches ctx me raw = .ok branches →
      ∀ q0, (∀ j, j < raw.length →
          u32At ctx.section' (q0 + 16 * j) (raw.getD j (0,0,0)).1 ∧
          u32At ctx.section' (q0 + 16 * j + 4) (raw.getD j (0,0,0)).2.1 ∧
          u64At ctx.section' (q0 + 16 * j + 8) (raw.getD j (0,0,0)).2.2) →
        branchesAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps me q0
          branches (q0 + 16 * raw.length) := by
  intro raw
  induction raw with
  | nil =>
    intro branches h q0 hpos
    unfold parseBranches at h
    simp only [pure_eq_ok] at h
    subst h
    exact branchesAt.nil me q0
  | cons t rest ih =>
    intro branches h q0 hpos
    obtain ⟨bs, be, bp⟩ := t
    unfold parseBranches at h
    split at h
    · rename_i hblt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at h
      obtain ⟨sr, hsr, er, her, child, hchild, ps, hps, hbr⟩ := h
      subst hbr
      have hrest := ih ps hps (q0 + 16) (by
        intro j hj
        have h3 := hpos (j + 1) (by simpa using hj)
        have e1 : q0 + 16 * (j + 1) = q0 + 16 + 16 * j := by omega
        rw [e1] at h3
        simpa using h3)
      have h0 := hpos 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      obtain ⟨hu1, hu2, hu3⟩ := h0
      have hgoal : q0 + 16 * ((bs, be, bp) :: rest).length = q0 + 16 + 16 * rest.length := by
        simp
        omega
      rw [hgoal]
      exact branchesAt.cons me q0 bs be bp sr er child ps _
        (by simpa using hu1) (by simpa using hu2) (by simpa using hu3) hblt
        (parseSimplexR_sound ctx.pool ctx.complexes bs hsr)
        (parseExtSetR_sound ctx.pool ctx.complexes be her)
        (IH bp hblt child hchild) hrest
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h

theorem parseBranches_length (ctx : NodeCtx) (me : Nat) :
    ∀ raw branches, parseBranches ctx me raw = .ok branches →
      branches.length = raw.length := by
  intro raw
  induction raw with
  | nil =>
    intro bs h
    unfold parseBranches at h
    simp only [pure_eq_ok] at h
    subst h
    rfl
  | cons t rest ih =>
    intro bs h
    obtain ⟨ts, te, tp⟩ := t
    unfold parseBranches at h
    split at h
    · simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at h
      obtain ⟨sr, hsr, er, her, child, hchild, ps, hps, hbs⟩ := h
      subst hbs
      simp only [List.length_cons, ih ps hps]
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h

theorem parseNode_sound (ctx : NodeCtx) :
    ∀ off q, parseNode ctx off = .ok q →
      nodeAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps off q := by
  refine strongNat (P := fun off => ∀ q, parseNode ctx off = .ok q →
    nodeAt ctx.section' ctx.pool ctx.nodesBase ctx.complexes.toList ctx.nApps off q) ?_
  intro off IH q h
  unfold parseNode at h
  try simp only [letFun] at h
  by_cases hg : (decide (off < ctx.nodesBase) || decide (off ≥ ctx.section'.size)) = true
  · rw [if_pos hg] at h
    simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h
  rw [if_neg hg] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hg
  obtain ⟨hbase1, hbase2⟩ := hg
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at h
  obtain ⟨tag, c₁, htag8, variant, c₂, hvar8, rsv, c₃, hrsv16, h⟩ := h
  obtain ⟨htagAt, rfl, _, _⟩ := u8_ok htag8
  obtain ⟨hvarAt, rfl, _, _⟩ := u8_ok hvar8
  obtain ⟨hrsvAt, rfl, _, _⟩ := u16_ok hrsv16
  by_cases hrg : (rsv != 0) = true
  · rw [if_pos hrg] at h
    simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at h
  rw [if_neg hrg] at h
  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hrg
  subst hrg
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at h
  obtain ⟨cj, c₄, hcj, j, hjud, hnode⟩ := h
  obtain ⟨hcjAt, rfl, _, _⟩ := u32_ok hcj
  have hj := parseJudgment_sound ctx.pool ctx.complexes cj hjud
  split at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [pure_bind, pure_eq_ok] at hnode
    subst hnode
    exact nodeAt.ax off cj j hbase1 htagAt hvarAt hrsvAt hcjAt hj
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, ex, c₆, hex, extra, hextra, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨hexAt, rfl, _, _⟩ := u32_ok hex
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.weaken off cj pr ex j q' extra hbase1 htagAt hvarAt hrsvAt hcjAt hj
        hprAt hexAt hplt (IH pr hplt q' hq')
        (parseFormula_sound ctx.pool ctx.complexes ex extra hextra)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨cf, c₅, hcf, cutF, hcutF, l, c₆, hl, r, c₇, hr, hnode⟩ := hnode
    obtain ⟨hcfAt, rfl, _, _⟩ := u32_ok hcf
    obtain ⟨hlAt, rfl, _, _⟩ := u64_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u64_ok hr
    split at hnode
    · rename_i hllt
      split at hnode
      · rename_i hrlt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pl, hpl, pr', hpr', hnode⟩ := hnode
        subst hnode
        exact nodeAt.cut off cj cf l r j cutF pl pr' hbase1 htagAt hvarAt hrsvAt hcjAt hj
          hcfAt (parseFormula_sound ctx.pool ctx.complexes cf cutF hcutF)
          hlAt hrAt hllt hrlt (IH l hllt pl hpl) (IH r hrlt pr' hpr')
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨l, c₅, hl, r, c₆, hr, hnode⟩ := hnode
    obtain ⟨hlAt, rfl, _, _⟩ := u64_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u64_ok hr
    split at hnode
    · rename_i hllt
      split at hnode
      · rename_i hrlt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pl, hpl, pr', hpr', hnode⟩ := hnode
        subst hnode
        exact nodeAt.andI off cj l r j pl pr' hbase1 htagAt hvarAt hrsvAt hcjAt hj
          hlAt hrAt hllt hrlt (IH l hllt pl hpl) (IH r hrlt pr' hpr')
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨l, c₅, hl, r, c₆, hr, path, c₇, hpath, hnode⟩ := hnode
    obtain ⟨hlAt, rfl, _, _⟩ := u64_ok hl
    obtain ⟨hrAt, rfl, _, _⟩ := u64_ok hr
    obtain ⟨hpathAt, rfl, _, _⟩ := readPath_ok hpath
    split at hnode
    · rename_i hllt
      split at hnode
      · rename_i hrlt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pl, hpl, pr', hpr', hnode⟩ := hnode
        subst hnode
        exact nodeAt.orE off cj l r j pl pr' path _ hbase1 htagAt hvarAt hrsvAt hcjAt hj
          hlAt hrAt hpathAt hllt hrlt (IH l hllt pl hpl) (IH r hrlt pr' hpr')
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨which, hside, pr, c₅, hpr, ot, c₆, hot, other, hother, hnode⟩ := hnode
    split at hside
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hside
    all_goals try simp only [pure_eq_ok] at hside
    all_goals subst hside
    all_goals obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    all_goals obtain ⟨hotAt, rfl, _, _⟩ := u32_ok hot
    all_goals split at hnode
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    all_goals rename_i hplt
    all_goals try simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
    all_goals obtain ⟨q', hq', hnode⟩ := hnode
    all_goals rw [if_pos (by decide)] at hnode
    all_goals simp only [pure_eq_ok] at hnode
    all_goals subst hnode
    · exact nodeAt.andE off cj pr ot j .left q' other hbase1 htagAt hvarAt hrsvAt hcjAt hj
        hprAt hotAt hplt (IH pr hplt q' hq')
        (parseFormula_sound ctx.pool ctx.complexes ot other hother)
    · exact nodeAt.andE off cj pr ot j .right q' other hbase1 htagAt hvarAt hrsvAt hcjAt hj
        hprAt hotAt hplt (IH pr hplt q' hq')
        (parseFormula_sound ctx.pool ctx.complexes ot other hother)
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨which, hside, pr, c₅, hpr, ot, c₆, hot, other, hother, hnode⟩ := hnode
    split at hside
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hside
    all_goals try simp only [pure_eq_ok] at hside
    all_goals subst hside
    all_goals obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    all_goals obtain ⟨hotAt, rfl, _, _⟩ := u32_ok hot
    all_goals split at hnode
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    all_goals rename_i hplt
    all_goals try simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
    all_goals obtain ⟨q', hq', hnode⟩ := hnode
    all_goals rw [if_neg (by decide)] at hnode
    all_goals simp only [pure_eq_ok] at hnode
    all_goals subst hnode
    · exact nodeAt.orI off cj pr ot j .left q' other hbase1 htagAt hvarAt hrsvAt hcjAt hj
        hprAt hotAt hplt (IH pr hplt q' hq')
        (parseFormula_sound ctx.pool ctx.complexes ot other hother)
    · exact nodeAt.orI off cj pr ot j .right q' other hbase1 htagAt hvarAt hrsvAt hcjAt hj
        hprAt hotAt hplt (IH pr hplt q' hq')
        (parseFormula_sound ctx.pool ctx.complexes ot other hother)
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨ep, c₅, hep, bp, c₆, hbp, w', c₇, hw, tt', c₈, htt, tu, c₉, htu, bf, c₁₀, hbf,
      termT, htermT, termU, htermU, bodyForm, hbodyForm, hnode⟩ := hnode
    obtain ⟨hepAt, rfl, _, _⟩ := u64_ok hep
    obtain ⟨hbpAt, rfl, _, _⟩ := u64_ok hbp
    obtain ⟨hwAt, rfl, _, _⟩ := u32_ok hw
    obtain ⟨httAt, rfl, _, _⟩ := u32_ok htt
    obtain ⟨htuAt, rfl, _, _⟩ := u32_ok htu
    obtain ⟨hbfAt, rfl, _, _⟩ := u32_ok hbf
    split at hnode
    · rename_i helt
      split at hnode
      · rename_i hblt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pe, hpe, pb, hpb, hnode⟩ := hnode
        subst hnode
        exact nodeAt.eqElim off cj ep bp w' tt' tu bf j pe pb termT termU bodyForm
          hbase1 htagAt hvarAt hrsvAt hcjAt hj hepAt hbpAt hwAt httAt htuAt hbfAt
          helt hblt (IH ep helt pe hpe) (IH bp hblt pb hpb)
          (parseTerm_sound ctx.pool tt' termT htermT)
          (parseTerm_sound ctx.pool tu termU htermU)
          (parseFormula_sound ctx.pool ctx.complexes bf bodyForm hbodyForm)
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, tm, c₆, htm, sp, c₇, hsp, es, c₈, hes, term, hterm, sr, hsr, er, her, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨htmAt, rfl, _, _⟩ := u32_ok htm
    obtain ⟨hspAt, rfl, _, _⟩ := u32_ok hsp
    obtain ⟨hesAt, rfl, _, _⟩ := u32_ok hes
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      rw [if_pos (by decide)] at hnode
      simp only [pure_eq_ok] at hnode
      subst hnode
      exact nodeAt.convIntro off cj pr tm sp es j q' term sr er
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt htmAt hspAt hesAt
        hplt (IH pr hplt q' hq')
        (parseTerm_sound ctx.pool tm term hterm)
        (parseSimplexR_sound ctx.pool ctx.complexes sp hsr)
        (parseExtSetR_sound ctx.pool ctx.complexes es her)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, tm, c₆, htm, sp, c₇, hsp, es, c₈, hes, term, hterm, sr, hsr, er, her, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨htmAt, rfl, _, _⟩ := u32_ok htm
    obtain ⟨hspAt, rfl, _, _⟩ := u32_ok hsp
    obtain ⟨hesAt, rfl, _, _⟩ := u32_ok hes
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      rw [if_neg (by decide)] at hnode
      simp only [pure_eq_ok] at hnode
      subst hnode
      exact nodeAt.convElim off cj pr tm sp es j q' term sr er
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt htmAt hspAt hesAt
        hplt (IH pr hplt q' hq')
        (parseTerm_sound ctx.pool tm term hterm)
        (parseSimplexR_sound ctx.pool ctx.complexes sp hsr)
        (parseExtSetR_sound ctx.pool ctx.complexes es her)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨dir, hside, pr, c₅, hpr, tl, c₆, htl, tr, c₇, htr, bv, c₈, hbv, hbvle,
      bt, hbt, pad, c₉, hpadtk, hpadz, termL, htermL, termR, htermR, hnode⟩ := hnode
    split at hside
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hside
    all_goals try simp only [pure_eq_ok] at hside
    all_goals subst hside
    all_goals obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    all_goals obtain ⟨htlAt, rfl, _, _⟩ := u32_ok htl
    all_goals obtain ⟨htrAt, rfl, _, _⟩ := u32_ok htr
    all_goals obtain ⟨hbvAt, rfl, _, _⟩ := u8_ok hbv
    all_goals obtain ⟨hpadS, hpadL, rfl, -, -⟩ := take_ok hpadtk
    all_goals have hz : ∀ x ∈ pad, x = 0 := by simpa using hpadz
    all_goals have hbtv := bowtieOf_ok hbt
    all_goals have hbtAt : u8At ctx.section' (off + 24) (bowtieCode bt) := by rw [hbtv]; exact hbvAt
    all_goals have hbtle : bowtieCode bt ≤ 4 := by rw [hbtv]; omega
    all_goals have hpz : ∀ i, i < 3 → u8At ctx.section' (off + 25 + i) 0 := by intro i hi; have h0 := sliceIs_index hpadS (show i < pad.length by omega); rwa [all_zero_getD hz (by omega)] at h0
    all_goals split at hnode
    all_goals try simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    all_goals rename_i hplt
    all_goals try simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
    all_goals obtain ⟨q', hq', hnode⟩ := hnode
    all_goals subst hnode
    · exact nodeAt.arithAtom off cj pr tl tr j .left q' termL termR bt
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt htlAt htrAt hbtAt hbtle
        (hpz 0 (by omega)) (hpz 1 (by omega)) (hpz 2 (by omega))
        hplt (IH pr hplt q' hq')
        (parseTerm_sound ctx.pool tl termL htermL)
        (parseTerm_sound ctx.pool tr termR htermR)
    · exact nodeAt.arithAtom off cj pr tl tr j .right q' termL termR bt
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt htlAt htrAt hbtAt hbtle
        (hpz 0 (by omega)) (hpz 1 (by omega)) (hpz 2 (by omega))
        hplt (IH pr hplt q' hq')
        (parseTerm_sound ctx.pool tl termL htermL)
        (parseTerm_sound ctx.pool tr termR htermR)
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨rp, c₅, hrp, tx, c₆, htx, sp, c₇, hsp, es, c₈, hes, deg, c₉, hdeg,
      poly, c₁₀, hpoly, pred, c₁₁, hpred, termX, htermX, sr, hsr, er, her,
      polynomial, hpolynomial, predicate, hpredicate, hnode⟩ := hnode
    obtain ⟨hrpAt, rfl, _, _⟩ := u64_ok hrp
    obtain ⟨htxAt, rfl, _, _⟩ := u32_ok htx
    obtain ⟨hspAt, rfl, _, _⟩ := u32_ok hsp
    obtain ⟨hesAt, rfl, _, _⟩ := u32_ok hes
    obtain ⟨hdegAt, rfl, _, _⟩ := u32_ok hdeg
    obtain ⟨hpolyAt, rfl, _, _⟩ := u32_ok hpoly
    obtain ⟨hpredAt, rfl, _, _⟩ := u32_ok hpred
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.bernCone off cj rp tx sp es deg poly pred j q' termX polynomial sr er predicate
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hrpAt htxAt hspAt hesAt hdegAt hpolyAt hpredAt
        hplt (IH rp hplt q' hq')
        (parseTerm_sound ctx.pool tx termX htermX)
        (parseSimplexR_sound ctx.pool ctx.complexes sp hsr)
        (parseExtSetR_sound ctx.pool ctx.complexes es her)
        (parseTerm_sound ctx.pool poly polynomial hpolynomial)
        (parseFormula_sound ctx.pool ctx.complexes pred predicate hpredicate)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨tl, c₅, htl, tr, c₆, htr, termL, htermL, termR, htermR, hnode⟩ := hnode
    obtain ⟨htlAt, rfl, _, _⟩ := u32_ok htl
    obtain ⟨htrAt, rfl, _, _⟩ := u32_ok htr
    subst hnode
    exact nodeAt.norm off cj tl tr j termL termR
      hbase1 htagAt hvarAt hrsvAt hcjAt hj htlAt htrAt
      (parseTerm_sound ctx.pool tl termL htermL)
      (parseTerm_sound ctx.pool tr termR htermR)
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨cc', c₅, hcc, k, c₆, hk, den, c₇, hden, combF, hcombF, concF, hconcF, hnode⟩ := hnode
    obtain ⟨hccAt, rfl, _, _⟩ := u32_ok hcc
    obtain ⟨hkAt, rfl, _, _⟩ := u32_ok hk
    obtain ⟨hdenAt, rfl, _, _⟩ := u64_ok hden
    subst hnode
    exact nodeAt.farkas off cj cc' k den j combF concF
      hbase1 htagAt hvarAt hrsvAt hcjAt hj hccAt hkAt hdenAt
      (parseTerm_sound ctx.pool cc' combF hcombF)
      (parseTerm_sound ctx.pool k concF hconcF)
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨rp, c₅, hrp, tx, c₆, htx, sp, c₇, hsp, es, c₈, hes, nb, c₉, hnb,
      termX, htermX, sr, hsr, er, her, raw, ccF, hloop, cov, c₁₀, hcov, den, c₁₁, hden,
      cover, hcover, branches, hbranches, hnode⟩ := hnode
    obtain ⟨hrpAt, rfl, _, _⟩ := u64_ok hrp
    obtain ⟨htxAt, rfl, _, _⟩ := u32_ok htx
    obtain ⟨hspAt, rfl, _, _⟩ := u32_ok hsp
    obtain ⟨hesAt, rfl, _, _⟩ := u32_ok hes
    obtain ⟨hnbAt, rfl, _, _⟩ := u32_ok hnb
    rw [forIn_range_eq] at hloop
    have hinv := forIn_list_inv (I := fun (st : List (Nat × Nat × Nat) × Cur) rest =>
        st.2 = (⟨ctx.section', off + 32 + 16 * st.1.length, ctx.section'.size⟩ : Cur) ∧
        st.1.length + rest.length = nb ∧
        (∀ jj, jj < st.1.length →
          u32At ctx.section' (off + 32 + 16 * jj) ((st.1.getD jj (0,0,0)).1) ∧
          u32At ctx.section' (off + 32 + 16 * jj + 4) ((st.1.getD jj (0,0,0)).2.1) ∧
          u64At ctx.section' (off + 32 + 16 * jj + 8) ((st.1.getD jj (0,0,0)).2.2)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨bs, cb₁, hbs, be, cb₂, hbe, bp, cb₃, hbp, hy⟩ := hbody
        obtain ⟨hbsAt, rfl, _, _⟩ := u32_ok hbs
        obtain ⟨hbeAt, rfl, _, _⟩ := u32_ok hbe
        obtain ⟨hbpAt, rfl, _, _⟩ := u64_ok hbp
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun jj (v : Nat × Nat × Nat) =>
            u32At ctx.section' (off + 32 + 16 * jj) v.1 ∧
            u32At ctx.section' (off + 32 + 16 * jj + 4) v.2.1 ∧
            u64At ctx.section' (off + 32 + 16 * jj + 8) v.2.2) hAt ⟨hbsAt, hbeAt, hbpAt⟩⟩)
      (⟨rfl, by simp, by simp⟩)
      hloop
    obtain ⟨hccF, hcntF, hAtF⟩ := hinv
    dsimp only [] at hccF hcntF hAtF
    subst hccF
    have hrawlen : raw.length = nb := by simpa using hcntF
    obtain ⟨hcovAt, rfl, _, _⟩ := u32_ok hcov
    obtain ⟨hdenAt, rfl, _, _⟩ := u64_ok hden
    have hbrs := parseBranches_sound ctx off IH raw branches hbranches (off + 32) hAtF
    have hblen : branches.length = raw.length := parseBranches_length ctx off raw branches hbranches
    have hnbAt' : u32At ctx.section' (off + 28) branches.length := by
      rw [hblen, hrawlen]; exact hnbAt
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.subdivide off cj rp tx sp es cov den (off + 32 + 16 * raw.length)
        j q' termX cover sr er branches
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hrpAt htxAt hspAt hesAt hnbAt'
        hbrs hcovAt hdenAt hplt (IH rp hplt q' hq')
        (parseTerm_sound ctx.pool tx termX htermX)
        (parseSimplexR_sound ctx.pool ctx.complexes sp hsr)
        (parseExtSetR_sound ctx.pool ctx.complexes es her)
        (parseTerm_sound ctx.pool cov cover hcover)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨lo, c₅, hlo, hi, c₆, hhi, pre, c₇, hpre, post, c₈, hpost, a, c₉, ha,
      bq, c₁₀, hbq, al, c₁₁, hal, be, c₁₂, hbe, ga, c₁₃, hga, de, c₁₄, hde,
      den, c₁₅, hden, hnode⟩ := hnode
    obtain ⟨hloAt, rfl, _, _⟩ := u64_ok hlo
    obtain ⟨hhiAt, rfl, _, _⟩ := u64_ok hhi
    obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre
    obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost
    obtain ⟨p₁, haAt, rfl, _, _, _⟩ := readRat_ok ha
    obtain ⟨p₂, hbqAt, rfl, _, _, _⟩ := readRat_ok hbq
    obtain ⟨p₃, halAt, rfl, _, _, _⟩ := readRat_ok hal
    obtain ⟨p₄, hbeAt, rfl, _, _, _⟩ := readRat_ok hbe
    obtain ⟨p₅, hgaAt, rfl, _, _, _⟩ := readRat_ok hga
    obtain ⟨p₆, hdeAt, rfl, _, _, _⟩ := readRat_ok hde
    obtain ⟨hdenAt, rfl, _, _⟩ := u64_ok hden
    split at hnode
    · rename_i hllt
      split at hnode
      · rename_i hhlt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pLo, hpLo, pHi, hpHi, hnode⟩ := hnode
        subst hnode
        exact nodeAt.lirpa off cj lo hi pre post den p₁ p₂ p₃ p₄ p₅ p₆ j pLo pHi a bq al be ga de
          hbase1 htagAt hvarAt hrsvAt hcjAt hj hloAt hhiAt hpreAt hpostAt
          haAt hbqAt halAt hbeAt hgaAt hdeAt hdenAt hllt hhlt
          (IH lo hllt pLo hpLo) (IH hi hhlt pHi hpHi)
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, pre, c₆, hpre, post, c₇, hpost, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre
    obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      rw [if_pos (by decide)] at hnode
      simp only [pure_eq_ok] at hnode
      subst hnode
      exact nodeAt.reluPos off cj pr pre post j q'
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt hpreAt hpostAt hplt (IH pr hplt q' hq')
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, pre, c₆, hpre, post, c₇, hpost, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre
    obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      rw [if_neg (by decide)] at hnode
      simp only [pure_eq_ok] at hnode
      subst hnode
      exact nodeAt.reluNeg off cj pr pre post j q'
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt hpreAt hpostAt hplt (IH pr hplt q' hq')
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pre, c₅, hpre, post, c₆, hpost, hnode⟩ := hnode
    obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre
    obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost
    rw [if_pos (by decide)] at hnode
    simp only [pure_eq_ok] at hnode
    subst hnode
    exact nodeAt.reluNN off cj pre post j
      hbase1 htagAt hvarAt hrsvAt hcjAt hj hpreAt hpostAt
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pre, c₅, hpre, post, c₆, hpost, hnode⟩ := hnode
    obtain ⟨hpreAt, rfl, _, _⟩ := u32_ok hpre
    obtain ⟨hpostAt, rfl, _, _⟩ := u32_ok hpost
    rw [if_neg (by decide)] at hnode
    simp only [pure_eq_ok] at hnode
    subst hnode
    exact nodeAt.reluAbove off cj pre post j
      hbase1 htagAt hvarAt hrsvAt hcjAt hj hpreAt hpostAt
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, ai, c₆, hai, hailt, wi, c₇, hwi, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨haiAt, rfl, _, _⟩ := u32_ok hai
    obtain ⟨hwiAt, rfl, _, _⟩ := u32_ok hwi
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.cellInInterior off cj pr ai wi j q'
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt haiAt hwiAt (by omega)
        hplt (IH pr hplt q' hq')
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, ite_eq_ok, throw_ne_ok,
      false_and, and_false, exists_false, false_or, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, ai, c₆, hai, hailt, wj, c₇, hwj, wv, c₈, hwv, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨haiAt, rfl, _, _⟩ := u32_ok hai
    obtain ⟨hwjAt, rfl, _, _⟩ := u32_ok hwj
    obtain ⟨hwvAt, rfl, _, _⟩ := u32_ok hwv
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.cellOut off cj pr ai wj wv j q'
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt haiAt hwjAt hwvAt (by omega)
        hplt (IH pr hplt q' hq')
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨tm, c₅, htm, term, hterm, hnode⟩ := hnode
    obtain ⟨htmAt, rfl, _, _⟩ := u32_ok htm
    subst hnode
    exact nodeAt.eqRefl off cj tm j term
      hbase1 htagAt hvarAt hrsvAt hcjAt hj htmAt
      (parseTerm_sound ctx.pool tm term hterm)
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨pr, c₅, hpr, tt', c₆, htt, tu, c₇, htu, termT, htermT, termU, htermU, hnode⟩ := hnode
    obtain ⟨hprAt, rfl, _, _⟩ := u64_ok hpr
    obtain ⟨httAt, rfl, _, _⟩ := u32_ok htt
    obtain ⟨htuAt, rfl, _, _⟩ := u32_ok htu
    split at hnode
    · rename_i hplt
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨q', hq', hnode⟩ := hnode
      subst hnode
      exact nodeAt.eqSym off cj pr tt' tu j q' termT termU
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hprAt httAt htuAt
        hplt (IH pr hplt q' hq')
        (parseTerm_sound ctx.pool tt' termT htermT)
        (parseTerm_sound ctx.pool tu termU htermU)
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨sup, c₅, hsup, con, c₆, hcon, cf, c₇, hcf, contract, hcontract,
      path, c₈, hpath, ni, c₉, hni, iface, ccF, hloop, hnode⟩ := hnode
    obtain ⟨hsupAt, rfl, _, _⟩ := u64_ok hsup
    obtain ⟨hconAt, rfl, _, _⟩ := u64_ok hcon
    obtain ⟨hcfAt, rfl, _, _⟩ := u32_ok hcf
    obtain ⟨hpathAt, rfl, _, _⟩ := readPath_ok hpath
    obtain ⟨hniAt, rfl, _, _⟩ := u32_ok hni
    rw [forIn_range_eq] at hloop
    have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨ctx.section', off + 28 + 4 + path.length + 4 + 4 * st.1.length,
          ctx.section'.size⟩ : Cur) ∧
        st.1.length + rest.length = ni ∧
        (∀ jj, jj < st.1.length →
          u32At ctx.section' (off + 28 + 4 + path.length + 4 + 4 * jj) (st.1.getD jj 0)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨wv, cb₁, hwv, hy⟩ := hbody
        obtain ⟨hwvAt, rfl, _, _⟩ := u32_ok hwv
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun jj v =>
            u32At ctx.section' (off + 28 + 4 + path.length + 4 + 4 * jj) v) hAt hwvAt⟩)
      (⟨rfl, by simp, by simp⟩)
      hloop
    obtain ⟨hccF, hcntF, hAtF⟩ := hinv
    dsimp only [] at hccF hcntF hAtF
    subst hccF
    have hilen : iface.length = ni := by simpa using hcntF
    have hniAt' : u32At ctx.section' (off + 28 + 4 + path.length) iface.length := by
      rw [hilen]; exact hniAt
    have hifaceAt : u32sAt ctx.section' (off + 28 + 4 + path.length + 4) iface
        (off + 28 + 4 + path.length + 4 + 4 * iface.length) := ⟨hAtF, rfl⟩
    split at hnode
    · rename_i hslt
      split at hnode
      · rename_i hclt
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
        obtain ⟨pSup, hpSup, pCon, hpCon, hnode⟩ := hnode
        subst hnode
        exact nodeAt.promise off cj sup con cf (off + 28 + 4 + path.length)
          j pSup pCon contract path iface
          hbase1 htagAt hvarAt hrsvAt hcjAt hj hsupAt hconAt hcfAt
          (parseFormula_sound ctx.pool ctx.complexes cf contract hcontract)
          hpathAt hniAt' hifaceAt hslt hclt
          (IH sup hslt pSup hpSup) (IH con hclt pCon hpCon)
      · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
  ·
    split at hnode
    · simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode
    rename_i hv0
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hv0
    subst hv0
    simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind, Prod.exists, Prod.mk.injEq] at hnode
    obtain ⟨nc, c₅, hnc, compOffs, ccF, hloop, comb, c₆, hcomb, conc, c₇, hconc,
      den, c₈, hden, th, c₉, hth32, combination, hcombination, conclusion, hconclusion,
      hnode⟩ := hnode
    obtain ⟨hncAt, rfl, _, _⟩ := u32_ok hnc
    rw [forIn_range_eq] at hloop
    have hinv := forIn_list_inv (I := fun (st : List Nat × Cur) rest =>
        st.2 = (⟨ctx.section', off + 12 + 8 * st.1.length, ctx.section'.size⟩ : Cur) ∧
        st.1.length + rest.length = nc ∧
        (∀ jj, jj < st.1.length →
          u64At ctx.section' (off + 12 + 8 * jj) (st.1.getD jj 0)))
      (by
        intro x rest st hI r hbody
        obtain ⟨acc, cc⟩ := st
        dsimp only [] at hI hbody
        obtain ⟨hcc, hcnt, hAt⟩ := hI
        subst hcc
        simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, Prod.exists, Prod.mk.injEq] at hbody
        obtain ⟨co, cb₁, hco, hy⟩ := hbody
        obtain ⟨hcoAt, rfl, _, _⟩ := u64_ok hco
        refine ⟨_, hy.symm, by simp <;> omega, by simp at hcnt ⊢ <;> omega,
          forall_getD_append (P := fun jj v =>
            u64At ctx.section' (off + 12 + 8 * jj) v) hAt hcoAt⟩)
      (⟨rfl, by simp, by simp⟩)
      hloop
    obtain ⟨hccF, hcntF, hAtF⟩ := hinv
    dsimp only [] at hccF hcntF hAtF
    subst hccF
    have hnclen : compOffs.length = nc := by simpa using hcntF
    obtain ⟨hcombAt, rfl, _, _⟩ := u32_ok hcomb
    obtain ⟨hconcAt, rfl, _, _⟩ := u32_ok hconc
    obtain ⟨hdenAt, rfl, _, _⟩ := u64_ok hden
    obtain ⟨hthAt, rfl, _, _⟩ := u32_ok hth32
    have hncAt' : u32At ctx.section' (off + 8) compOffs.length := by
      rw [hnclen]; exact hncAt
    have hoffsAt : u64sAt ctx.section' (off + 12) compOffs
        (off + 12 + 8 * compOffs.length) := ⟨hAtF, rfl⟩
    have hconcAt' : u32At ctx.section' (off + 16 + 8 * compOffs.length) conc := by
      rw [show off + 16 + 8 * compOffs.length = off + 12 + 8 * compOffs.length + 4 from by omega]
      exact hconcAt
    have hdenAt' : u64At ctx.section' (off + 20 + 8 * compOffs.length) den := by
      rw [show off + 20 + 8 * compOffs.length = off + 12 + 8 * compOffs.length + 4 + 4 from by omega]
      exact hdenAt
    have hthAt' : u32At ctx.section' (off + 28 + 8 * compOffs.length) th := by
      rw [show off + 28 + 8 * compOffs.length = off + 12 + 8 * compOffs.length + 4 + 4 + 8 from by omega]
      exact hthAt
    split at hnode
    ·
      rename_i hthh
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨components, hcomps, hnode⟩ := hnode
      subst hnode
      obtain ⟨hcompsAt, hoLt⟩ := parseNodeList_sound ctx off IH compOffs components hcomps
      exact nodeAt.syzygy off cj comb conc den th j compOffs components combination conclusion none
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hncAt' hoffsAt hcombAt hconcAt' hdenAt' hthAt'
        hoLt hcompsAt
        (parseTerm_sound ctx.pool comb combination hcombination)
        (parseTerm_sound ctx.pool conc conclusion hconclusion)
        (by simpa using hthh)
    ·
      rename_i hthh
      simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind] at hnode
      obtain ⟨thv, ⟨tq, hthq, hsome⟩, components, hcomps, hnode⟩ := hnode
      subst hsome
      subst hnode
      obtain ⟨hcompsAt, hoLt⟩ := parseNodeList_sound ctx off IH compOffs components hcomps
      exact nodeAt.syzygy off cj comb conc den th j compOffs components combination conclusion
        (some tq)
        hbase1 htagAt hvarAt hrsvAt hcjAt hj hncAt' hoffsAt hcombAt hconcAt' hdenAt' hthAt'
        hoLt hcompsAt
        (parseTerm_sound ctx.pool comb combination hcombination)
        (parseTerm_sound ctx.pool conc conclusion hconclusion)
        ⟨by simpa using hthh, parseThetaAt_sound hthq⟩
  ·
    simp only [bind_eq_ok, map_eq_ok, throw_ne_ok, false_and, and_false, exists_false] at hnode

end Soundness

/-- Refinement: every successful parse satisfies the encoding relation. -/
theorem parseWCert_sound (b : ByteArray) (c : WCert)
    (h : parseWCert b = .ok c) : Encodes b c := by
  unfold parseWCert at h
  simp only [map_eq_ok, bind_eq_ok, pure_eq_ok, pure_bind,
    ite_eq_ok, throw_ne_ok, false_and, and_false, exists_false, false_or,
    Prod.exists, Cur.at'] at h
  obtain ⟨hd, hhd, syms, hsyms, cxsA, apps, hdiag, poolLen, c₂, hpool, hple, root, hroot,
    htail⟩ := h
  obtain ⟨hpoolAt, rfl, _, _⟩ := u64_ok hpool
  rcases htail with ⟨hth, hc⟩ | ⟨hth, θv, ⟨tq, hthq, hsome⟩, hc⟩
  · subst hc
    exact ⟨parseHeader_ok hhd, parseSymtab_ok hsyms,
      parseDiagram_ok hdiag, poolLen, hpoolAt, (show 8 + poolLen ≤ hd.proofLen by omega),
      parseNode_sound _ _ _ hroot, by simpa using hth⟩
  · subst hsome
    subst hc
    exact ⟨parseHeader_ok hhd, parseSymtab_ok hsyms,
      parseDiagram_ok hdiag, poolLen, hpoolAt, (show 8 + poolLen ≤ hd.proofLen by omega),
      parseNode_sound _ _ _ hroot,
      by simpa using hth, parseThetaAt_sound hthq⟩

#print axioms parseWCert_sound

end Spec
end Wire
end PPLC
