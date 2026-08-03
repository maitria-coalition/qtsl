import Reflection.Types

/-!
# Geolog reader: byte-level codecs

The byte-level layer of the geolog container reader, ported faithfully
from the HOL4 reference reader (`geolog_readScript.sml` in the checker
development, itself differentially verified against the production
decoders): little-endian reads, byte-lexicographic order, minimal
LEB128 (unsigned and signed), the hexane run-length column codec with
its decode → re-encode fixed-point gate, UTF-8 validation, the
deterministic-CBOR head subset (RFC 8949 §4.2: minimal heads, definite
lengths only), and the minimal-length little-endian integer discipline
for cell payloads.

Everything is total over `List Nat` bytes, by structural recursion or
an explicit fuel parameter pre-bounded by the caller (LEB128's 10-byte
u64 ceiling, at least one byte per run, and so on), so the whole chain
reduces in the kernel. Fuel exhaustion lands in the refusing branch,
never an unsound accept.

All reader machinery lives in the `PPLC.Geolog.Read` sub-namespace;
only the four interface entry points (`rdBody`, `readGeolog`,
`readGeologSealed`, `renderRes`) are re-exported at `PPLC.Geolog`
level, so sibling modules in `PPLC.Geolog` can keep their own helper
names without collision.
-/

namespace PPLC
namespace Geolog
namespace Read

/-- Sum of a list of naturals (`foldr` spelling, matching the reference). -/
def natSum (xs : List Nat) : Nat := xs.foldr (· + ·) 0

/-! ## Bytes, little-endian, slicing -/

/-- Little-endian value of a byte list. -/
def leN : Bytes → Nat
  | [] => 0
  | b :: bs => b + 256 * leN bs

/-- `len` bytes at offset `off`, or `none` past the end. -/
def bytesAt (bs : Bytes) (off len : Nat) : Option Bytes :=
  if off + len ≤ bs.length then some ((bs.drop off).take len) else none

/-- Little-endian integer read at an absolute offset. -/
def rdLeAt (bs : Bytes) (off len : Nat) : Option Nat :=
  match bytesAt bs off len with
  | none => none
  | some chunk => some (leN chunk)

/-- Bytewise lexicographic `<` (prefix-first — matches `Vec<u8>` order
in the production decoders). -/
def lexLt : Bytes → Bytes → Bool
  | [], ys => decide (ys ≠ [])
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexLt xs ys)

/-- Bytewise lexicographic `≤`. -/
def lexLe (xs ys : Bytes) : Bool := lexLt xs ys || decide (xs = ys)

/-- Strictly ascending in `lexLt`. -/
def strictAsc : List Bytes → Bool
  | [] => true
  | x :: rest =>
    match rest with
    | [] => true
    | y :: _ => lexLt x y && strictAsc rest

/-- Weakly ascending in `lexLe`. -/
def sortedLexLe : List Bytes → Bool
  | [] => true
  | x :: rest =>
    match rest with
    | [] => true
    | y :: _ => lexLe x y && sortedLexLe rest

/-- Archive vec-ref check at absolute field position `fp`: the i32le
self-relative offset must denote exactly `target` (modulo 2^32) and
the u32le count must equal `count`. -/
def vecRefOK (bs : Bytes) (fp target count : Nat) : Bool :=
  match rdLeAt bs fp 4 with
  | none => false
  | some off =>
    match rdLeAt bs (fp + 4) 4 with
    | none => false
    | some cnt =>
      decide ((fp + off) % 4294967296 = target) && decide (cnt = count)

/-! ## Sorting and dedup

The reference reader sorts with quicksort. Every relation it sorts by
is a total order whose equal elements are identical values, so the
ordered permutation is unique and any correct sort is
output-identical; insertion sort is chosen here because it is
structurally recursive (kernel-reducible without well-founded
recursion). -/

/-- Insert `x` into a list ordered by `le`. -/
def insertLe (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertLe le x ys

/-- Insertion sort by `le`. -/
def sortLe (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertLe le x (sortLe le xs)

/-- Adjacent dedup on naturals. -/
def dedupAdj : List Nat → List Nat
  | [] => []
  | x :: rest =>
    match rest with
    | [] => [x]
    | y :: _ => if x = y then dedupAdj rest else x :: dedupAdj rest

/-- Adjacent dedup, generic. -/
def dedupAdjG [DecidableEq α] : List α → List α
  | [] => []
  | x :: rest =>
    match rest with
    | [] => [x]
    | y :: _ => if x = y then dedupAdjG rest else x :: dedupAdjG rest

/-- Merge walk over two `lexLt`-ascending lists: no element in common.
Fueled: each step drops one element from one list, so `|xs| + |ys|`
steps suffice and the fuel-0 both-nonempty arm is unreachable from the
entry point (it refuses, fail-closed). -/
def noCrossDupF : Nat → List Bytes → List Bytes → Bool
  | _, [], _ => true
  | _, _ :: _, [] => true
  | 0, _ :: _, _ :: _ => false
  | fuel + 1, x :: xs, y :: ys =>
    if x = y then false
    else if lexLt x y then noCrossDupF fuel xs (y :: ys)
    else noCrossDupF fuel (x :: xs) ys

/-- No element in common between two `lexLt`-ascending lists. -/
def noCrossDup (xs ys : List Bytes) : Bool :=
  noCrossDupF (xs.length + ys.length) xs ys

/-- Euclid's gcd, explicitly fueled (after the first step the first
argument strictly decreases, so `a + 1` steps always suffice; the
fuel-0 arm is unreachable from the entry point). Agrees with `Nat.gcd`;
spelled with fuel so it reduces structurally in the kernel. -/
def gcdF : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, a, b => if a = 0 then b else gcdF f (b % a) a

/-- `gcdN a b = Nat.gcd a b`, kernel-friendly spelling. -/
def gcdN (a b : Nat) : Nat := gcdF (a + 1) a b

/-! ## Minimal LEB128 -/

/-- Unsigned LEB128, minimal form, value < 2^64; returns
`(value, next position)`. Fuel 10 is the 10-byte u64 ceiling.
Minimality: a terminal 0x00 byte is only legal as the whole
(single-byte) encoding. -/
def rdUlebLoop (bs : Bytes) (pos shift acc fuel : Nat) : Option (Nat × Nat) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match bs[pos]? with
    | none => none
    | some b =>
      if b < 128 then
        if b = 0 ∧ 0 < shift then none
        else
          let v := acc + b * 2 ^ shift
          if v < 18446744073709551616 then some (v, pos + 1) else none
      else rdUlebLoop bs (pos + 1) (shift + 7) (acc + (b - 128) * 2 ^ shift) f

/-- Minimal unsigned LEB128 read. -/
def rdUleb (bs : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  rdUlebLoop bs pos 0 0 10

/-- Minimal ULEB128 encoder; fuel 10 covers every value < 2^64 (the
only values ever passed); fuel exhaustion yields `[]`, which no
fixed-point gate can match — fail-closed. -/
def encUlebF : Nat → Nat → Bytes
  | 0, _ => []
  | f + 1, v => if v < 128 then [v] else (v % 128 + 128) :: encUlebF f (v / 128)

/-- Minimal ULEB128 encoding. -/
def encUleb (v : Nat) : Bytes := encUlebF 10 v

/-- Final byte of a signed LEB128 read: sign from bit 6 of the last
data byte, sign-magnitude result `(isNeg, magnitude, next position)`,
magnitude bounded to i64. -/
def rdSlebFin (b shift acc pos : Nat) : Option (Bool × Nat × Nat) :=
  let raw := acc + b * 2 ^ shift
  let nbits := shift + 7
  if (b / 64) % 2 = 1 then
    let mag := 2 ^ nbits - raw
    if mag ≤ 9223372036854775808 then some (true, mag, pos + 1) else none
  else
    if raw < 9223372036854775808 then some (false, raw, pos + 1) else none

/-- Signed LEB128, minimal form. `prev` tracks the previous data byte
for the minimality rule: a redundant final byte is 0x00 after a clear
bit 6, or 0x7F after a set bit 6. -/
def rdSlebLoop (bs : Bytes) (pos shift acc : Nat) (prev : Option Nat)
    (fuel : Nat) : Option (Bool × Nat × Nat) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match bs[pos]? with
    | none => none
    | some b =>
      if b < 128 then
        match prev with
        | some pb =>
          if (b = 0 ∧ (pb / 64) % 2 = 0) ∨ (b = 127 ∧ (pb / 64) % 2 = 1)
          then none
          else rdSlebFin b shift acc pos
        | none => rdSlebFin b shift acc pos
      else rdSlebLoop bs (pos + 1) (shift + 7) (acc + (b - 128) * 2 ^ shift) (some b) f

/-- Minimal signed LEB128 read, sign-magnitude. -/
def rdSleb (bs : Bytes) (pos : Nat) : Option (Bool × Nat × Nat) :=
  rdSlebLoop bs pos 0 0 none 10

/-- Minimal signed LEB128 encoder for `+v`, fueled like `encUleb`. -/
def encSlebPosF : Nat → Nat → Bytes
  | 0, _ => []
  | f + 1, v =>
    let g := v % 128
    let rest := v / 128
    if rest = 0 ∧ g < 64 then [g]
    else (g + 128) :: encSlebPosF f rest

/-- Minimal signed LEB128 encoding of `+v`. -/
def encSlebPos (v : Nat) : Bytes := encSlebPosF 10 v

/-- Minimal signed LEB128 encoder for `-m` (`m ≥ 1`): group
`g = (-m) mod 128`; next remaining magnitude `⌈m/128⌉`; terminal when
the remaining value is −1 (`rest = 1`) and the group's bit 6 is set. -/
def encSlebNegF : Nat → Nat → Bytes
  | 0, _ => []
  | f + 1, m =>
    let g := (128 - m % 128) % 128
    let rest := (m + 127) / 128
    if rest = 1 ∧ 64 ≤ g then [g]
    else if rest = 0 then [g]
    else (g + 128) :: encSlebNegF f rest

/-- Minimal signed LEB128 encoding of `-m`. -/
def encSlebNeg (m : Nat) : Bytes := encSlebNegF 10 m

/-! ## Hexane run-length columns

Column wire: a sequence of runs — repeat = `sleb128(count > 0)` then
one packed value; literal = `sleb128(-n)` then `n` packed values; null
runs (`sleb128(0)`) are refused, both column types here being
non-nullable. Values: u64 = minimal ULEB128; byte rows = minimal
ULEB128 length then bytes. The saved stream is the single-stream
greedy encoding `hexSave` reproduces, and every column read ends in a
decode → re-encode → byte-compare fixed-point gate. -/

/-- A decoded run: a repeated value or a literal stretch. -/
inductive HexRun (α : Type) where
  | rep (n : Nat) (v : α)
  | lit (vs : List α)
  deriving Repr

/-- Row count a run contributes. -/
def runCount : HexRun α → Nat
  | .rep n _ => n
  | .lit vs => vs.length

/-- Packed u64 value: minimal ULEB128. -/
def rdHexU64 (bs : Bytes) (pos : Nat) : Option (Nat × Nat) := rdUleb bs pos

/-- Packed byte row: minimal ULEB128 length, then the bytes. -/
def rdHexBytes (bs : Bytes) (pos : Nat) : Option (Bytes × Nat) :=
  match rdUleb bs pos with
  | none => none
  | some (len, p1) =>
    match bytesAt bs p1 len with
    | none => none
    | some chunk => some (chunk, p1 + len)

/-- `k` consecutive values (literal-run bodies); `k` is pre-bounded by
the caller against remaining bytes (at least one byte per value). -/
def rdHexValsKA (rd : Bytes → Nat → Option (α × Nat)) (bs : Bytes)
    (pos k : Nat) (acc : List α) : Option (List α × Nat) :=
  match k with
  | 0 => some (acc.reverse, pos)
  | k' + 1 =>
    match rd bs pos with
    | none => none
    | some (v, p1) => rdHexValsKA rd bs p1 k' (v :: acc)

/-- `k` consecutive values. -/
def rdHexValsK (rd : Bytes → Nat → Option (α × Nat)) (bs : Bytes)
    (pos k : Nat) : Option (List α × Nat) :=
  rdHexValsKA rd bs pos k []

/-- The run-stream parse. Fuel = input length (every run consumes at
least one byte). -/
def rdHexRunsF (rd : Bytes → Nat → Option (α × Nat)) (bs : Bytes)
    (pos fuel : Nat) (acc : List (HexRun α)) : Option (List (HexRun α)) :=
  match fuel with
  | 0 => if bs.length ≤ pos then some acc.reverse else none
  | f + 1 =>
    if bs.length ≤ pos then some acc.reverse
    else
      match rdSleb bs pos with
      | none => none
      | some (neg, mag, p1) =>
        if neg then
          if bs.length < p1 + mag then none
          else
            match rdHexValsK rd bs p1 mag with
            | none => none
            | some (vs, p2) => rdHexRunsF rd bs p2 f (.lit vs :: acc)
        else
          if mag = 0 then none
          else
            match rd bs p1 with
            | none => none
            | some (v, p2) => rdHexRunsF rd bs p2 f (.rep mag v :: acc)

/-- Parse a whole column byte string as a run stream. -/
def rdHexRuns (rd : Bytes → Nat → Option (α × Nat)) (bs : Bytes) :
    Option (List (HexRun α)) :=
  rdHexRunsF rd bs 0 bs.length []

/-- Total row count a run stream claims (pre-materialization). -/
def hexClaim (runs : List (HexRun α)) : Nat :=
  natSum (runs.map runCount)

/-- Materialize a run stream. -/
def hexExpand : List (HexRun α) → List α
  | [] => []
  | r :: rest =>
    (match r with
     | .rep n v => List.replicate n v
     | .lit vs => vs) ++ hexExpand rest

/-- Group maximal equal-value runs (accumulator worker). -/
def groupRunsA [DecidableEq α] (xs : List α) (cur : α) (cnt : Nat)
    (acc : List (α × Nat)) : List (α × Nat) :=
  match xs with
  | [] => ((cur, cnt) :: acc).reverse
  | v :: vs =>
    if v = cur then groupRunsA vs cur (cnt + 1) acc
    else groupRunsA vs v 1 ((cur, cnt) :: acc)

/-- Group a value sequence into maximal `(value, count)` runs. -/
def groupRuns [DecidableEq α] : List α → List (α × Nat)
  | [] => []
  | v :: vs => groupRunsA vs v 1 []

/-- Emit a pending literal stretch, if any. -/
def flushLit (enc : α → Bytes) (pend : List α) : Bytes :=
  if pend.isEmpty then []
  else encSlebNeg pend.length ++ (pend.map enc).flatten

/-- Canonical greedy run emission: count ≥ 2 groups become repeat
runs; maximal stretches of count-1 groups coalesce into single
literal runs. -/
def emitRuns (enc : α → Bytes) : List (α × Nat) → List α → Bytes
  | [], pend => flushLit enc pend
  | (v, n) :: rest, pend =>
    if n = 1 then emitRuns enc rest (pend ++ [v])
    else flushLit enc pend ++ encSlebPos n ++ enc v ++ emitRuns enc rest []

/-- The canonical single-stream greedy encoding of a value sequence —
exactly the saved form of the production column writer (which
re-merges slab boundaries, so the single-stream form is its output). -/
def hexSave [DecidableEq α] (enc : α → Bytes) (vals : List α) : Bytes :=
  emitRuns enc (groupRuns vals) []

/-- u64 value writer. -/
def encHexU64 (v : Nat) : Bytes := encUleb v

/-- Byte-row value writer. -/
def encHexBytes (b : Bytes) : Bytes := encUleb b.length ++ b

/-- Cap on every column's claimed row count and on the body-wide op
total, enforced before materialization. -/
def MAX_BODY_OPS : Nat := 1048576

/-- Full column read with the fixed-point gate: parse runs (cheap, no
materialization), cap the claim, then expand, re-encode through the
canonical writer, and byte-compare. `none` is refusal (the caller
names it). -/
def readCol [DecidableEq α] (rd : Bytes → Nat → Option (α × Nat))
    (enc : α → Bytes) (bs : Bytes) : Option (List α) :=
  match rdHexRuns rd bs with
  | none => none
  | some runs =>
    if MAX_BODY_OPS < hexClaim runs then none
    else
      let vals := hexExpand runs
      if hexSave enc vals = bs then some vals else none

/-- u64 column read. -/
def readU64Col (bs : Bytes) : Option (List Nat) :=
  readCol rdHexU64 encHexU64 bs

/-- Byte-rows column read. -/
def readBytesCol (bs : Bytes) : Option (List Bytes) :=
  readCol rdHexBytes encHexBytes bs

/-! ## UTF-8 -/

/-- Continuation byte. -/
def contB (b : Nat) : Bool := decide (128 ≤ b ∧ b < 192)

/-- Strict UTF-8 validity (shortest forms only; surrogates and values
above U+10FFFF excluded). -/
def utf8Ok : Bytes → Bool
  | [] => true
  | b :: rest =>
    if b < 128 then utf8Ok rest
    else if b < 194 then false
    else if b < 224 then
      match rest with
      | b1 :: rest' => contB b1 && utf8Ok rest'
      | _ => false
    else if b < 240 then
      match rest with
      | b1 :: b2 :: rest' =>
        contB b1 && contB b2 &&
        decide (b = 224 → 160 ≤ b1) &&
        decide (b = 237 → b1 < 160) &&
        utf8Ok rest'
      | _ => false
    else if b < 245 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        contB b1 && contB b2 && contB b3 &&
        decide (b = 240 → 144 ≤ b1) &&
        decide (b = 244 → b1 < 144) &&
        utf8Ok rest'
      | _ => false
    else false

/-! ## Deterministic CBOR (RFC 8949 §4.2 subset) -/

def MAJ_UINT : Nat := 0
def MAJ_BYTES : Nat := 2
def MAJ_TEXT : Nat := 3
def MAJ_ARRAY : Nat := 4
def MAJ_MAP : Nat := 5

/-- Major type of the byte at `pos`. -/
def peekMajor (bs : Bytes) (pos : Nat) : Option Nat :=
  match bs[pos]? with
  | none => none
  | some b => some (b / 32)

/-- One CBOR head, requiring major `m`; minimal-form argument;
definite lengths only. Returns `(argument, next position)`. -/
def rdHead (bs : Bytes) (pos m : Nat) : Option (Nat × Nat) :=
  match bs[pos]? with
  | none => none
  | some ib =>
    if ib / 32 ≠ m then none
    else
      let ai := ib % 32
      if ai < 24 then some (ai, pos + 1)
      else if ai = 24 then
        match bs[pos + 1]? with
        | none => none
        | some v => if v < 24 then none else some (v, pos + 2)
      else if ai = 25 then
        match bytesAt bs (pos + 1) 2 with
        | some [b1, b0] =>
          let v := b1 * 256 + b0
          if v ≤ 255 then none else some (v, pos + 3)
        | _ => none
      else if ai = 26 then
        match bytesAt bs (pos + 1) 4 with
        | some [b3, b2, b1, b0] =>
          let v := ((b3 * 256 + b2) * 256 + b1) * 256 + b0
          if v ≤ 65535 then none else some (v, pos + 5)
        | _ => none
      else if ai = 27 then
        match bytesAt bs (pos + 1) 8 with
        | some [b7, b6, b5, b4, b3, b2, b1, b0] =>
          let v := ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3)
                     * 256 + b2) * 256 + b1) * 256 + b0
          if v ≤ 4294967295 then none else some (v, pos + 9)
        | _ => none
      else none

/-- Unsigned integer head. -/
def rdUintC (bs : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  rdHead bs pos MAJ_UINT

/-- Definite byte string: head then content. -/
def rdBstrC (bs : Bytes) (pos : Nat) : Option (Bytes × Nat) :=
  match rdHead bs pos MAJ_BYTES with
  | none => none
  | some (len, p1) =>
    match bytesAt bs p1 len with
    | none => none
    | some chunk => some (chunk, p1 + len)

/-- Definite array head. -/
def rdArrC (bs : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  rdHead bs pos MAJ_ARRAY

/-- Definite map head. -/
def rdMapC (bs : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  rdHead bs pos MAJ_MAP

/-! ## Minimal-length little-endian integers (cell payload discipline) -/

/-- Minimal unsigned LE bytes: nonempty, no redundant zero high byte. -/
def minLeU (b : Bytes) : Bool :=
  decide (b ≠ [] ∧ (b.length = 1 ∨ b.getLastD 0 ≠ 0))

/-- Minimal signed (two's-complement) LE bytes: nonempty, no redundant
sign-extension byte. -/
def minLeS (b : Bytes) : Bool :=
  decide (b ≠ [] ∧
    (b.length = 1 ∨
     ¬((b.getLastD 0 = 0 ∧ (b.getD (b.length - 2) 0) / 128 = 0) ∨
       (b.getLastD 0 = 255 ∧ (b.getD (b.length - 2) 0) / 128 = 1))))

/-- Magnitude of a signed LE byte string (two's complement). -/
def sgnMagLe (b : Bytes) : Nat :=
  let v := leN b
  let n := b.length
  if b ≠ [] ∧ (b.getLastD 0) / 128 = 1 then 2 ^ (8 * n) - v else v

/-! ## Write-side primitive encoders -/

/-- Minimal CBOR head for major `m`, argument `n`. -/
def encCborHead (m n : Nat) : Bytes :=
  if n < 24 then [32 * m + n]
  else if n < 256 then [32 * m + 24, n]
  else if n < 65536 then [32 * m + 25, n / 256, n % 256]
  else if n < 4294967296 then
    [32 * m + 26, (n / 16777216) % 256, (n / 65536) % 256,
     (n / 256) % 256, n % 256]
  else
    [32 * m + 27,
     (n / 72057594037927936) % 256,
     (n / 281474976710656) % 256,
     (n / 1099511627776) % 256,
     (n / 4294967296) % 256,
     (n / 16777216) % 256, (n / 65536) % 256,
     (n / 256) % 256, n % 256]

/-- CBOR unsigned integer. -/
def encCborUint (n : Nat) : Bytes := encCborHead MAJ_UINT n

/-- CBOR definite byte string. -/
def encBstr (p : Bytes) : Bytes := encCborHead MAJ_BYTES p.length ++ p

/-- CBOR definite array head. -/
def encArrHead (n : Nat) : Bytes := encCborHead MAJ_ARRAY n

/-- Minimal-length unsigned LE bytes: no trailing zero high byte;
zero is `[0]`. Fuel 9 covers u64. -/
def minLeBytesF : Nat → Nat → Bytes
  | 0, _ => []
  | f + 1, v => if v < 256 then [v] else v % 256 :: minLeBytesF f (v / 256)

/-- Minimal-length unsigned LE bytes. -/
def minLeBytes (v : Nat) : Bytes := minLeBytesF 9 v

/-- Two-byte little-endian. -/
def encLe2 (n : Nat) : Bytes := [n % 256, (n / 256) % 256]

/-- Four-byte little-endian. -/
def encLe4 (n : Nat) : Bytes :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

end Read
end Geolog
end PPLC
