import Reflection.Accept
import Reflection.Render

/-!
# File-driven reflection-route verdicts

Entry point of the `geolog_reflect` executable: sealed container file
paths in, one verdict block per file out. For each file the route
reports the reader verdict, the rows→certificate reconstruction, and
the validity elaboration, with wall-clock timings per stage and for
the end-to-end acceptance. Exit code is the number of non-accepted
files.
-/

open PPLC PPLC.Wire PPLC.Geolog

def timeMs' (act : IO α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  pure (r, (Float.ofNat (t1 - t0)) / 1000000.0)

/-- Claim-agreement differential: the same certificate through the
binary wire parser and through the sealed-container rows path must
reconstruct identical claims (root sequent, goal split, θ). -/
def runAgainst (containerPath bernPath : String) : IO UInt32 := do
  let raw ← IO.FS.readBinFile containerPath
  let bs : Bytes := raw.toList.map UInt8.toNat
  let bern ← IO.FS.readBinFile bernPath
  match acceptBytesSealed bs, acceptWireBytes bern with
  | some a, some b =>
    let seqEq := a.seq.pre == b.seq.pre && a.seq.post == b.seq.post
    let goalEq := a.goalPre == b.goalPre && a.goalPost == b.goalPost
    IO.println s!"claims: rows-path ACCEPT, wire-path ACCEPT; sequent-equal={seqEq} goal-equal={goalEq}"
    pure (if seqEq && goalEq then 0 else 1)
  | some _, none =>
    IO.println "claims: rows-path ACCEPT, wire-path REFUSE — DISAGREE"
    pure 1
  | none, some _ =>
    IO.println "claims: rows-path REFUSE, wire-path ACCEPT — DISAGREE"
    pure 1
  | none, none =>
    IO.println "claims: both REFUSE (agreeing refusal)"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--against", c, b] => return (← runAgainst c b)
  | _ => pure ()
  if args.isEmpty then
    IO.println "usage: geolog_reflect FILE.geolog [...] | --against FILE.geolog FILE.bernfmt"
    return 2
  let mut bad : UInt32 := 0
  for path in args do
    let name := (path.splitOn "/").getLastD path
    let raw ← IO.FS.readBinFile path
    let bs : Bytes := (raw.toList.map UInt8.toNat)
    IO.println s!"{name}: {bs.length} bytes"
    let (rres, tRead) ← timeMs' (IO.lazyPure (fun _ => readGeologSealed bs))
    match rres with
    | .err c tag w =>
      IO.println s!"  reader: REFUSE {repr c} {tag} {w} ({tRead} ms)"
      bad := bad + 1
    | .ok g => do
      IO.println s!"  reader: ok ({tRead} ms)"
      let (rows, tRows) ← timeMs' (IO.lazyPure (fun _ => certOfRowsAny stagedPins g))
      match rows with
      | .error (c, tag, w) =>
        IO.println s!"  rows: REFUSE {repr c} {tag} {w} ({tRows} ms)"
        bad := bad + 1
      | .ok (.proof w) => do
        IO.println s!"  rows→wire: ok ({tRows} ms)"
        let (elev, tElev) ← timeMs' (IO.lazyPure (fun _ => elabWCert w))
        match elev with
        | .error e =>
          IO.println s!"  elevation: REFUSE {repr e} ({tElev} ms)"
          bad := bad + 1
        | .ok c => do
          let (acc, tAcc) ← timeMs' (IO.lazyPure (fun _ => (acceptParsed c).isSome))
          IO.println s!"  elevation: ok ({tElev} ms); validity: {if acc then "ACCEPT" else "REFUSE"} ({tAcc} ms)"
          let (e2e, tAll) ← timeMs' (IO.lazyPure (fun _ => acceptBytesSealedAnyB bs))
          IO.println s!"  end-to-end: {if e2e then "ACCEPT" else "REFUSE"} ({tAll} ms)"
          if !e2e then bad := bad + 1
      | .ok (.enc w) => do
        IO.println s!"  rows→wire: ok ({tRows} ms)"
        let (acc, tAcc) ← timeMs' (IO.lazyPure (fun _ => (acceptEnc w).isSome))
        IO.println s!"  enclosure judgment: func={w.func} n={w.n} r={w.r} cap={w.cap}; validity: {if acc then "ACCEPT" else "REFUSE"} ({tAcc} ms)"
        let (e2e, tAll) ← timeMs' (IO.lazyPure (fun _ => acceptBytesSealedAnyB bs))
        IO.println s!"  end-to-end: {if e2e then "ACCEPT" else "REFUSE"} ({tAll} ms)"
        if !e2e then bad := bad + 1
  pure bad
