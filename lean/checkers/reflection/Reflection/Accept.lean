import Qtsl.Soundness
import Reflection.CertRows
import Reflection.Elab
import Reflection.Valid
import Reflection.Container
import Reflection.EncValid

/-!
# Acceptance as a kernel theorem

The composition of the route: decoded container → certificate rows →
wire model → elevated hypernet and proof tree → runtime elaboration
into a proof object. A successful run *is* the reflection principle
discharged: the returned value contains a typed proof object, and the
established structural soundness theorem applies to it with no
further hypotheses.

`acceptGeolog_sound` is the route's soundness statement: whatever
claim this function accepts is semantically valid. Its proof is one
line, because every obligation was discharged during elaboration —
the decoder and reconstruction stages appear in the statement only
through the value they produced, so no stage of them is trusted.

The accepted fragment has two root arms: proof-calculus roots
(`Cert/root`) through the elevation-and-elaboration tail, and
enclosure-judgment roots (`Cert/rootEnc`) through the remainder-bound
obligation, whose validity proof is `encJCheck_sound` — the
established mathlib-backed enclosure soundness (`QtslAux.Enclosure`)
specialized to the canonical witness the judgment denotes
(`Reflection.EncValid`). The extended soundness statement is
`acceptBytesSealedAny_sound`; the legacy proof-arm entry points are
its restriction and remain byte-identical on proof-root certificates.
-/

namespace PPLC
namespace Geolog

open Wire

/-- An accepted claim: a hypernet, the root sequent, the goal split
(antecedent formula and succedent as framed by the certificate), and
the elaborated proof object. -/
structure Accepted where
  H       : Hypernet
  seq     : Sequent
  goalPre : Formula
  goalPost : Formula
  valid   : PLift (seq.semanticallyValid H)

/-- Accept an elevated certificate: root framing mirrors the
executable checker — the root antecedent must be the goal conjoined
with the hypernet's structural-fact conjunction, and the predicate
hole must be fresh — then the proof tree elaborates into a proof
object. -/
def acceptParsed (c : ParsedCert) : Option Accepted :=
  let seq := c.proof.concludes
  if seq.pre = .and c.goalPre c.hypernet.spConjunction then
    if seq.post = c.goalPost then
      if (c.hypernet.wireType predicateHole).isNone = true then
        match elabValid c.hypernet c.proof with
        | none => none
        | some v =>
          some ⟨c.hypernet, seq, c.goalPre, c.goalPost, v⟩
      else none
    else none
  else none

/-! ## The enclosure arm -/

/-- An accepted enclosure claim: the decoded judgment and the
validity proof constructed at acceptance. -/
structure AcceptedEnc where
  tag : Qtsl.Enclosure.FnTag
  n : Nat
  r : Rat
  cap : Rat
  valid : PLift (EncValid tag n r cap)

/-- An accepted claim of either arm. -/
inductive AcceptedAny where
  | proof (a : Accepted)
  | enc (e : AcceptedEnc)

/-- The claim an acceptance carries, by arm. -/
def AcceptedAny.claimValid : AcceptedAny → Prop
  | .proof a => a.seq.semanticallyValid a.H
  | .enc e => EncValid e.tag e.n e.r e.cap

/-- Accept a decoded enclosure certificate: resolve the wire tag
against the three-tag roster, then decide the judgment obligation
(`encJCheck`: radius and tail clauses in exact rational arithmetic);
success constructs the validity proof. -/
def acceptEnc (w : WEnc) : Option AcceptedEnc :=
  match fnTagOfWire w.func with
  | none => none
  | some t =>
    if h : encJCheck t w.n w.r w.cap = true then
      some ⟨t, w.n, w.r, w.cap, ⟨encJCheck_sound h⟩⟩
    else none

/-- Accept a decoded sealed container on the extended fragment:
proof roots through the established elevation-and-elaboration tail,
enclosure roots through the judgment obligation. -/
def acceptGeologAny (pins : List ((List Nat × Nat) × Vocab))
    (g : Geolog) : Option AcceptedAny :=
  match certOfRowsAny pins g with
  | .error _ => none
  | .ok (.proof w) =>
    match elabWCert w with
    | .error _ => none
    | .ok c => (acceptParsed c).map .proof
  | .ok (.enc e) => (acceptEnc e).map .enc

/-! ## Entry points and soundness -/

/-- Accept a decoded sealed container: reconstruct the certificate
from its rows, elevate, and elaborate the proof object. Defined as
the proof-arm restriction of the extended acceptance
(`acceptGeologAny`), so agreement between the two entry points is
definitional; behavior on proof-root certificates is the established
pipeline unchanged, and an enclosure-root certificate through this
legacy entry point is `none` (before the fragment extension it was a
scan refusal). -/
def acceptGeolog (pins : List ((List Nat × Nat) × Vocab)) (g : Geolog) :
    Option Accepted :=
  match acceptGeologAny pins g with
  | some (.proof a) => some a
  | _ => none

/-- Accept binary certificate bytes through the established wire
parser and the same elaboration tail: the byte-format twin of
`acceptGeolog`, giving the wire format the same theorem-backed
acceptance. -/
def acceptWireBytes (b : ByteArray) : Option Accepted :=
  match parseCertificate b with
  | .error _ => none
  | .ok c => acceptParsed c

theorem acceptWireBytes_sound (b : ByteArray) (a : Accepted)
    (_h : acceptWireBytes b = some a) :
    a.seq.semanticallyValid a.H :=
  a.valid.down

/-- Pure proof-object acceptance (the compositional fragment): the
same tail through `elabPO`, whose success constructs the dependent
proof object itself. Context-carrying disjunction elimination lies
outside this fragment; `acceptParsed` covers it through the
admissible-rule seam. -/
def acceptParsedPO (c : ParsedCert) : Option (ProofObject c.hypernet c.proof.concludes) :=
  let seq := c.proof.concludes
  if seq.pre = .and c.goalPre c.hypernet.spConjunction then
    if seq.post = c.goalPost then
      if (c.hypernet.wireType predicateHole).isNone = true then
        elabPO c.hypernet c.proof
      else none
    else none
  else none

def acceptWireBytesPO (b : ByteArray) : Bool :=
  match parseCertificate b with
  | .error _ => false
  | .ok c => (acceptParsedPO c).isSome

/-- Soundness of the route: an accepted claim is semantically valid.
The proof object returned by acceptance is itself the witness. -/
theorem acceptGeolog_sound (pins : List ((List Nat × Nat) × Vocab))
    (g : Geolog) (a : Accepted)
    (_h : acceptGeolog pins g = some a) :
    a.seq.semanticallyValid a.H :=
  a.valid.down

/-- The route end to end: container bytes in, accepted claim out —
the same bytes the certified checker consumes, loaded through the
sealed-artifact reader, reconstructed from rows, and elaborated to a
validity proof. -/
def acceptBytesSealed (bs : Bytes) : Option Accepted :=
  match readGeologSealed bs with
  | .err _ _ _ => none
  | .ok g => acceptGeolog stagedPins g

/-- Soundness of the byte route: an accepted claim is semantically
valid — the acceptance theorem of the reflection path. -/
theorem acceptBytesSealed_sound (bs : Bytes) (a : Accepted)
    (_h : acceptBytesSealed bs = some a) :
    a.seq.semanticallyValid a.H :=
  a.valid.down

/-- Boolean face of the byte route, for kernel-evaluation receipts. -/
def acceptBytesSealedB (bs : Bytes) : Bool :=
  (acceptBytesSealed bs).isSome

/-- Boolean face of acceptance, for kernel-evaluation receipts. -/
def acceptGeologB (pins : List ((List Nat × Nat) × Vocab))
    (g : Geolog) : Bool :=
  (acceptGeolog pins g).isSome

/-- The accepted claim of a decoded container, when acceptance holds. -/
def claimOf (pins : List ((List Nat × Nat) × Vocab)) (g : Geolog)
    (h : (acceptGeolog pins g).isSome) : Accepted :=
  (acceptGeolog pins g).get h

theorem claimOf_valid (pins : List ((List Nat × Nat) × Vocab))
    (g : Geolog) (h : (acceptGeolog pins g).isSome) :
    (claimOf pins g h).seq.semanticallyValid (claimOf pins g h).H :=
  (claimOf pins g h).valid.down

/-- The extended route end to end: container bytes in, accepted
claim (of either arm) out. -/
def acceptBytesSealedAny (bs : Bytes) : Option AcceptedAny :=
  match readGeologSealed bs with
  | .err _ _ _ => none
  | .ok g => acceptGeologAny stagedPins g

/-- Soundness of the extended byte route: an accepted claim is valid
— the proof arm's claim is the root sequent's semantic validity, the
enclosure arm's claim is the judgment's real-analytic enclosure. The
proof is one line per arm, because the accepted value carries the
validity proof constructed during acceptance. -/
theorem acceptBytesSealedAny_sound (bs : Bytes) (a : AcceptedAny)
    (_h : acceptBytesSealedAny bs = some a) : a.claimValid :=
  match a with
  | .proof p => p.valid.down
  | .enc e => e.valid.down

/-- Boolean face of the extended byte route, for kernel-evaluation
receipts. -/
def acceptBytesSealedAnyB (bs : Bytes) : Bool :=
  (acceptBytesSealedAny bs).isSome

/-- The legacy entry point is the proof-arm restriction of the
extended acceptance, by definition. -/
theorem acceptGeologAny_proof_agrees
    (pins : List ((List Nat × Nat) × Vocab)) (g : Geolog) (a : Accepted)
    (h : acceptGeolog pins g = some a) :
    acceptGeologAny pins g = some (.proof a) := by
  unfold acceptGeolog at h
  split at h
  · next b heq => cases h; exact heq
  · exact absurd h (by simp)

end Geolog
end PPLC
