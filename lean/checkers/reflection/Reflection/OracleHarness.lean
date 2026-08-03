import Reflection.Accept

/-!
# Row-path harness over rendered op dumps

Test instrument (never on any trust path): parses the reference
implementation's structural dump of a sealed certificate commit into
the op model, then drives the rows→certificate→validity pipeline on
it. This exercises everything downstream of the byte reader — row
scanning, certificate reconstruction, elevation, and validity
elaboration — against real certificate content, with wall-clock
timings per stage.
-/

open PPLC PPLC.Wire PPLC.Geolog

namespace OracleHarness

/-- Substring helpers over the slice-returning primitives. -/
def sdrop (s : String) (n : Nat) : String := (s.drop n).toString
def sdropR (s : String) (n : Nat) : String := s.dropRight n

/-- Split a comma-separated value list at paren depth zero. -/
def splitTop (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur : String := ""
  let mut depth : Nat := 0
  for c in s.toList do
    if c == '(' then
      depth := depth + 1
      cur := cur.push c
    else if c == ')' then
      depth := depth - 1
      cur := cur.push c
    else if c == ',' ∧ depth == 0 then
      out := cur :: out
      cur := ""
    else
      cur := cur.push c
  if cur != "" then out := cur :: out
  return out.reverse

def parseHexBytes (s : String) : Option (List Nat) := Id.run do
  let hv : Char → Option Nat := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else none
  let cs := s.toList
  if cs.length % 2 != 0 then return none
  let mut out : List Nat := []
  let mut rest := cs
  while h : rest.length ≥ 2 do
    let c1 := rest[0]
    let c2 := rest[1]
    match hv c1, hv c2 with
    | some a, some b => out := (16 * a + b) :: out
    | _, _ => return none
    rest := rest.drop 2
  return some out.reverse

/-- `L(n)` or `E(d,c)`. -/
def parseRef (s : String) : Option ElemRef :=
  if s.startsWith "L(" ∧ s.endsWith ")" then
    (sdropR (sdrop s 2) 1).toNat?.map .loc
  else if s.startsWith "E(" ∧ s.endsWith ")" then
    match (sdropR (sdrop s 2) 1).splitOn "," with
    | [d, c] =>
      match d.toNat?, c.toNat? with
      | some dv, some cv => some (.ext dv cv)
      | _, _ => none
    | _ => none
  else none

def parseVal (s : String) : Option GValue :=
  if s.startsWith "lit(" ∧ s.endsWith ")" then
    match (sdropR (sdrop s 4) 1).splitOn ",0x" with
    | [c, p] =>
      match c.toNat?, parseHexBytes p with
      | some cv, some pv => some (.lit cv pv)
      | _, _ => none
    | _ => none
  else if s.startsWith "cid(" ∧ s.endsWith ")" then
    (sdropR (sdrop s 4) 1).toNat?.map .commitId
  else if s.startsWith "ext(" ∧ s.endsWith ")" then
    match (sdropR (sdrop s 4) 1).splitOn ",0x" with
    | [c, p] =>
      match c.toNat?, parseHexBytes p with
      | some cv, some pv => some (.extBand cv pv)
      | _, _ => none
    | _ => none
  else if s.startsWith "abs(" ∧ s.endsWith ")" then
    match (sdropR (sdrop s 4) 1).splitOn ",0x" with
    | [c, p] =>
      match c.toNat?, parseHexBytes p with
      | some cv, some pv => some (.absence cv pv)
      | _, _ => none
    | _ => none
  else (parseRef s).map .ref

def parseVals (s : String) : Option (List GValue) :=
  if s == "" then some []
  else (splitTop s).mapM parseVal

/-- One `op N: …` line body (after the colon and space). -/
def parseOp (s : String) : Option GOp :=
  if s.startsWith "elta sort=" then
    (parseRef (sdrop s 10)).map .elta
  else if s.startsWith "rela rel=" then
    match (sdrop s 9).splitOn " args=[" with
    | [r, rest] =>
      if rest.endsWith "]" then
        match parseRef r, parseVals (sdropR rest 1) with
        | some rv, some avs => some (.rela rv avs)
        | _, _ => none
      else none
    | _ => none
  else if s.startsWith "funa fun=" then
    match (sdrop s 9).splitOn " args=[" with
    | [r, rest] =>
      match rest.splitOn "] value=" with
      | [avs, v] =>
        match parseRef r, parseVals avs, parseVal v with
        | some rv, some avsv, some vv => some (.funa rv avsv vv)
        | _, _, _ => none
      | _ => none
    | _ => none
  else none

def parseOracle (text : String) : Option (List GOp) := Id.run do
  let mut ops : List GOp := []
  for line in text.splitOn "\n" do
    if line.startsWith "op " then
      match line.splitOn ": " with
      | _ :: rest =>
        let body := String.intercalate ": " rest
        match parseOp body with
        | some op => ops := op :: ops
        | none => return none
      | [] => return none
  return some ops.reverse

/-- Synthetic one-commit container around an op list, deps in the
staged skeleton order (formats, stack, certificate theory). -/
def wrapOps (ops : List GOp) : Geolog :=
  { prereqs := [],
    commits := [{
      sigBytes := [], skelBytes := [],
      cskel := {
        author := List.replicate 32 0,
        deps := [chid_groundFormats, chid_blstack, chid_certTheory],
        parentCount := 0, tsClaim := 0, message := none,
        bodyHash := List.replicate 32 0 },
      bodyBytes := [],
      cbody := { ops := ops, zoneRuns := [] } }] }

def timeMs (act : IO α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  pure (r, (Float.ofNat (t1 - t0)) / 1000000.0)

end OracleHarness

open OracleHarness in
def main (args : List String) : IO UInt32 := do
  let mut bad : UInt32 := 0
  for path in args do
    let name := (path.splitOn "/").getLastD path
    let text ← IO.FS.readFile path
    match parseOracle text with
    | none =>
      IO.println s!"{name}: DUMP-PARSE-FAILED"
      bad := bad + 1
    | some ops => do
      IO.println s!"{name}: {ops.length} ops"
      let g := wrapOps ops
      let (res, tRows) ← timeMs (IO.lazyPure (fun _ => certOfRowsAny stagedPins g))
      match res with
      | .error (c, tag, w) =>
        IO.println s!"  rows: REFUSE {repr c} {tag} {w}  ({tRows} ms)"
        bad := bad + 1
      | .ok (.proof wcert) => do
        IO.println s!"  rows→wire: ok ({tRows} ms)"
        let (elev, tElev) ← timeMs (IO.lazyPure (fun _ => elabWCert wcert))
        match elev with
        | .error e =>
          IO.println s!"  elevation: REFUSE {repr e} ({tElev} ms)"
          bad := bad + 1
        | .ok c => do
          IO.println s!"  elevation: ok ({tElev} ms)"
          let (acc, tAcc) ← timeMs (IO.lazyPure (fun _ => (acceptParsed c).isSome))
          IO.println s!"  validity: {if acc then "ACCEPT" else "REFUSE"} ({tAcc} ms)"
          let (e2e, tAll) ← timeMs (IO.lazyPure (fun _ =>
            (acceptGeolog stagedPins g).isSome))
          IO.println s!"  end-to-end (rows onward): {e2e} ({tAll} ms)"
          if !acc then bad := bad + 1
      | .ok (.enc w) => do
        IO.println s!"  rows→wire: ok ({tRows} ms)"
        let (acc, tAcc) ← timeMs (IO.lazyPure (fun _ => (acceptEnc w).isSome))
        IO.println s!"  enclosure judgment: func={w.func} n={w.n} r={w.r} cap={w.cap}; validity: {if acc then "ACCEPT" else "REFUSE"} ({tAcc} ms)"
        let (e2e, tAll) ← timeMs (IO.lazyPure (fun _ =>
          (acceptGeologAny stagedPins g).isSome))
        IO.println s!"  end-to-end (rows onward): {e2e} ({tAll} ms)"
        if !acc then bad := bad + 1
  pure bad
