import Reflection.Accept
import QtslabLean.Render

/-!
# Entry point of the program route

Certificate container files in; on acceptance, the accepted sequent
out. The check is `Reflection.acceptBytesSealed` — byte-identical
logic to the reflection route — and `acceptBytesSealed_sound` is the
statement that whatever this program prints as a sequent is
semantically valid (modulo the package README's trust statement:
Lean's code generator and below are trusted here, not proven).

Stdout carries only verdicts and sequents; stage timings go to
stderr. Exit code is the number of non-accepted files.
-/

open PPLC PPLC.Geolog QtslabLean

def timeMs (act : IO α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  pure (r, (Float.ofNat (t1 - t0)) / 1000000.0)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "usage: qtslab_lean CERT.geolog [...]"
    return 2
  let mut bad : UInt32 := 0
  for path in args do
    let name := (path.splitOn "/").getLastD path
    let raw ← IO.FS.readBinFile path
    let bs : Bytes := raw.toList.map UInt8.toNat
    let (res, tCheck) ← timeMs (IO.lazyPure (fun _ => acceptBytesSealed bs))
    match res with
    | none =>
      IO.println s!"REFUSE {name}"
      (← IO.getStderr).putStrLn s!"{name}: bytes={bs.length} t_check_ms={tCheck}"
      bad := bad + 1
    | some a =>
      let (rendered, tRender) ← timeMs (IO.lazyPure (fun _ => renderSequent a.seq))
      IO.println s!"ACCEPT {name}"
      IO.println rendered
      (← IO.getStderr).putStrLn
        s!"{name}: bytes={bs.length} t_check_ms={tCheck} t_render_ms={tRender}"
  pure bad
